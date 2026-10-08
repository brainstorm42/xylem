import Percolation.Continuity.HullPort.TADefs
import Percolation.Literature.TwoSetExchange
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH: Lemma Φ (the residual functional of the world-wise unfolding is nonnegative and increasing)

Setting: bond percolation `prodBernoulli w` with arbitrary pair probabilities on a finite vertex type; an OWNER `s`, an
AVOIDED set `X`; for a vertex set `K` the configuration "off `K`" is `ω ∖ edgesOf K` (delete the pairs meeting `K`), and
`HullPort.cut X ω` is the set of pairs meeting the open vertex cluster of `X`.  The world-wise unfolding of the conditioned
slack hierarchy produces, for every increasing functional `g` of the open edge cluster of the owner, the
residual functional

  `Φ(K) = ∫ 1{s ↮ X off K} · ( g(C_s(ω ∖ cut_X(ω off K))) − g(C_s(ω off K)) ) dμ(ω)`

("explore the cluster of `X` off `K`; compare the cluster of `s` outside that explored set, which may use `K`, with the
cluster of `s` off `K`").  LEMMA Φ: the integrand is pointwise nonnegative and pointwise increasing in `K`,
hence `Φ ≥ 0` and `Φ` is increasing — so `Φ` is an admissible functional for the lower-level conditioned covariance
transfers (COV(τ) with avoided sets, `CovTau.markerDominanceAvoid`), which is what completes the induction on the number of
decoys.  This file: `edgesOf`, `phiIntegrand`, `phiFun` and the four order lemmas.  (The identification of `Φ(K)` with the
conditional mean of the telescoping residual given `C_d = K` is the Markov property, `Continuity/CSH/PhiMarkov.lean`.)
[cite: VandenbergHaggstromKahn2005, §1 pp. 3–5 (clusters in `G − Z`; induced model)] -/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

namespace CSH

variable {V : Type*}

/-- The pairs meeting the vertex set `K` (deleting them is "percolation off `K`", i.e. on `G − K`).
[cite: VandenbergHaggstromKahn2005, §1 p. 4 (the graph `G − Z`)] -/
def edgesOf (K : Set V) : Set (Sym2 V) := {e | ∃ u ∈ e, u ∈ K}

/-- `edgesOf` is monotone. [folklore] -/
theorem edgesOf_mono {K K' : Set V} (h : K ⊆ K') : edgesOf K ⊆ edgesOf K' :=
  fun _ ⟨u, hue, huK⟩ => ⟨u, hue, h huK⟩

/-- Deleting more pairs shrinks the configuration: `ω ∖ edgesOf K' ⊆ ω ∖ edgesOf K` for `K ⊆ K'`. [folklore] -/
theorem sdiff_edgesOf_anti (ω : Set (Sym2 V)) {K K' : Set V} (h : K ⊆ K') :
    ω \ edgesOf K' ⊆ ω \ edgesOf K :=
  fun _ he => ⟨he.1, fun h' => he.2 (edgesOf_mono h h')⟩

/-- `HullPort.cut X` is monotone in the configuration. [folklore] -/
theorem cut_mono (X : Set V) {ω ω' : Set (Sym2 V)} (h : ω ⊆ ω') : HullPort.cut X ω ⊆ HullPort.cut X ω' :=
  fun _ ⟨v, hve, x, hxX, hxv⟩ => ⟨v, hve, x, hxX, hxv.mono (SimpleGraph.fromEdgeSet_mono h)⟩

/-- **The integrand of Lemma Φ**:
`I_K(ω) = 1{s ↮ X off K} · ( g(C_s(ω ∖ cut_X(ω off K))) − g(C_s(ω off K)) )`, where "off `K`" deletes the pairs meeting `K`
and `C_s` is the open edge cluster. [folklore] -/
def phiIntegrand (s : V) (X K : Set V) (g : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) : ℝ :=
  if (∀ x ∈ X, ¬ (openGraph (ω \ edgesOf K)).Reachable s x) then
    g (openEdgeCluster (ω \ HullPort.cut X (ω \ edgesOf K)) s) - g (openEdgeCluster (ω \ edgesOf K) s)
  else 0

/-- On `{s ↮ X off K}` the edge cluster of `s` off `K` avoids the pairs meeting the cluster of `X` off `K`, hence lies in
the edge cluster of `s` in `ω ∖ cut_X(ω off K)`. [folklore] -/
theorem openEdgeCluster_off_subset (s : V) (X K : Set V) (ω : Set (Sym2 V))
    (havoid : ∀ x ∈ X, ¬ (openGraph (ω \ edgesOf K)).Reachable s x) :
    openEdgeCluster (ω \ edgesOf K) s ⊆ openEdgeCluster (ω \ HullPort.cut X (ω \ edgesOf K)) s := by
  refine TwoSetExchange.openEdgeCluster_subset_of_subset fun e he => ?_
  obtain ⟨heω, -, hreach⟩ := (mem_openEdgeCluster_iff _ s e).1 he
  refine ⟨heω.1, ?_⟩
  rintro ⟨v, hve, x, hxX, hxv⟩
  exact havoid x hxX ((hreach v hve).trans hxv.symm)

/-- **Lemma Φ, pointwise nonnegativity**: `0 ≤ I_K(ω)` for every monotone `g`. [folklore] -/
theorem phiIntegrand_nonneg (s : V) (X K : Set V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g) (ω : Set (Sym2 V)) :
    0 ≤ phiIntegrand s X K g ω := by
  unfold phiIntegrand
  split_ifs with havoid
  · exact sub_nonneg.2 (hg (openEdgeCluster_off_subset s X K ω havoid))
  · exact le_rfl

/-- **Lemma Φ, pointwise monotonicity**: `K ⊆ K' ⟹ I_K(ω) ≤ I_{K'}(ω)` for every monotone `g`: deleting more pairs shrinks
the explored cluster of `X` (so the outside cluster of `s` grows), shrinks the cluster of `s` off `K`, and enlarges the
event `{s ↮ X off K}` (on whose complement `I_K = 0 ≤ I_{K'}`). [folklore] -/
theorem phiIntegrand_mono (s : V) (X : Set V) {K K' : Set V} (hKK' : K ⊆ K') {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (ω : Set (Sym2 V)) : phiIntegrand s X K g ω ≤ phiIntegrand s X K' g ω := by
  have hsub : ω \ edgesOf K' ⊆ ω \ edgesOf K := sdiff_edgesOf_anti ω hKK'
  by_cases havoid : ∀ x ∈ X, ¬ (openGraph (ω \ edgesOf K)).Reachable s x
  · have havoid' : ∀ x ∈ X, ¬ (openGraph (ω \ edgesOf K')).Reachable s x :=
      fun x hx h => havoid x hx (h.mono (SimpleGraph.fromEdgeSet_mono hsub))
    unfold phiIntegrand
    rw [if_pos havoid, if_pos havoid']
    have h1 : g (openEdgeCluster (ω \ HullPort.cut X (ω \ edgesOf K)) s) ≤
        g (openEdgeCluster (ω \ HullPort.cut X (ω \ edgesOf K')) s) :=
      hg (BHK2006.openEdgeCluster_mono
        (show ω \ HullPort.cut X (ω \ edgesOf K) ⊆ ω \ HullPort.cut X (ω \ edgesOf K') from
          fun _ he => ⟨he.1, fun h' => he.2 (cut_mono X hsub h')⟩) s)
    have h2 : g (openEdgeCluster (ω \ edgesOf K') s) ≤ g (openEdgeCluster (ω \ edgesOf K) s) :=
      hg (BHK2006.openEdgeCluster_mono hsub s)
    linarith
  · have h0 : phiIntegrand s X K g ω = 0 := by
      unfold phiIntegrand
      rw [if_neg havoid]
    rw [h0]
    exact phiIntegrand_nonneg s X K' hg ω

/-- **The residual functional `Φ` of the world-wise unfolding**:
`Φ(K) = ∫ I_K dμ_w`. [folklore] -/
def phiFun (w : Sym2 V → unitInterval) (s : V) (X : Set V) (g : Set (Sym2 V) → ℝ) (K : Set V) : ℝ :=
  ∫ ω, phiIntegrand s X K g ω ∂(prodBernoulli w)

/-- **Lemma Φ**: `Φ ≥ 0`. [folklore] -/
theorem phiFun_nonneg (w : Sym2 V → unitInterval) (s : V) (X : Set V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (K : Set V) : 0 ≤ phiFun w s X g K :=
  integral_nonneg fun ω => phiIntegrand_nonneg s X K hg ω

/-- **Lemma Φ**: `Φ` is increasing (`K ⊆ K' ⟹ Φ(K) ≤ Φ(K')`), for every weight vector and every monotone `g`.
[folklore] -/
theorem phiFun_mono [Fintype V] (w : Sym2 V → unitInterval) (s : V) (X : Set V) {g : Set (Sym2 V) → ℝ} (hg : Monotone g) :
    Monotone (phiFun w s X g) := by
  intro K K' hKK'
  exact integral_mono (Integrable.of_finite) (Integrable.of_finite) fun ω => phiIntegrand_mono s X hKK' hg ω

end CSH

end Percolation.Continuity
