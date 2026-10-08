import Percolation.Continuity.CSH.Phi
import Percolation.Continuity.HullPort.TACond
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH: Lemma Φ(a) (the residual functional as a conditional mean: Markov property at the cluster of the avoided set, off `K`)

No definitions besides the sum-level abbreviation `wmeanOff`.

* `CSH.set_sum_cond_sdiff_off` — BHK's Lemma 2.4 / display (10) for the cluster of a vertex set `S` explored in the
  configuration OFF a fixed pair set `B` (`ω ∖ B`), the world being the FULL configuration minus the pairs meeting
  `S ∪ V(C_S(ω ∖ B))`: for every kernel `K`,
  `Σ_ω w(ω) K(C_S(ω∖B), ω ∖ X̄) = Σ_ω w(ω) Σ_η w(η) K(C_S(ω∖B), η ∖ X̄)`  (the event `{C_S(ω∖B) = W}` reads only the pairs of
  `X̄(W) ∖ B`, the world only the pairs off `X̄(W)`: block independence, `BHK2006.blockFubini`).  `B = ∅` is
  `HullPort.set_sum_cond_sdiff`.
* `CSH.sum_phiIntegrand_eq` — LEMMA Φ(a):  `Σ_η w(η) Φ-integrand_K(η) = Σ_η w(η) 1{s ↮ X off K}(η) · ( ḡ(C_X(η off K)) − g(C_s(η off K)) )`
  where `ḡ` is the world mean of `g(C_s)` given the cluster of `X` (computed with the FULL weight, i.e. in `G`, not in `G − K`):
  the first term of `Φ` is the conditional mean of the world mean.  This identifies `Φ(K)` with (minus) the conditional mean,
  given `C_d = K`, of the telescoping residual `Θ = (g(C_s) − ḡ(C_X))·1{s↮X}`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 pp. 7–8, display (10) — corollaries]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open BHK2006 DecisionTree HullPort

namespace CSH

variable {V : Type*} [Fintype V]

/-- **Conditioning on the cluster of `S` explored off a fixed pair set `B`.** For every kernel `K`:
`Σ_ω w(ω) K(C_S(ω ∖ B), ω ∖ X̄_S(C_S(ω ∖ B))) = Σ_ω w(ω) Σ_η w(η) K(C_S(ω ∖ B), η ∖ X̄_S(C_S(ω ∖ B)))`: given the cluster `W` of `S`
in `ω ∖ B` (a cylinder event on `X̄_S(W) ∖ B`), the configuration off `X̄_S(W)` — which may contain pairs of `B` — is fresh.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollary] -/
theorem set_sum_cond_sdiff_off (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (S : Set V) (B : Set (Sym2 V))
    (K : Set (Sym2 V) → Set (Sym2 V) → ℝ) :
    ∑ ω, weight w ω * K (setCl (ω \ B) S) (ω \ barOf S (setCl (ω \ B) S)) =
      ∑ ω, weight w ω * ∑ η, weight w η * K (setCl (ω \ B) S) (η \ barOf S (setCl (ω \ B) S)) := by
  classical
  -- the cylinder property of `{C_S(ω ∖ B) = W}` on `A = barOf S W`: it reads only `ω ∩ A`
  have hcyl : ∀ (W ω : Set (Sym2 V)), setCl ((ω ∩ barOf S W) \ B) S = W ↔ setCl (ω \ B) S = W := by
    intro W ω
    have h1 : (ω ∩ barOf S W) \ B = (ω \ B) ∩ barOf S W := by
      ext e; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [h1, setCl_inter_barOf_eq_iff]
  have key : ∀ W : Set (Sym2 V),
      ∑ ω, (if setCl (ω \ B) S = W then weight w ω * K W (ω \ barOf S W) else 0) =
      ∑ ω, (if setCl (ω \ B) S = W then weight w ω * ∑ η, weight w η * K W (η \ barOf S W) else 0) := by
    intro W
    set A : Set (Sym2 V) := barOf S W with hA
    set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η => if setCl (ζ \ B) S = W then K W η else 0 with hΦ
    have h1 : ∀ ω, (if setCl (ω \ B) S = W then weight w ω * K W (ω \ A) else 0) = weight w ω * Φ (ω ∩ A) (ω \ A) := by
      intro ω
      simp only [hΦ, hA, hcyl]
      split_ifs with hW
      · rfl
      · rw [mul_zero]
    have h2 : ∀ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) =
        (if setCl (ω \ B) S = W then weight w ω * ∑ η, weight w η * K W (η \ A) else 0) := by
      intro ω
      simp only [hΦ, hA, hcyl]
      split_ifs with hW
      · rfl
      · simp
    calc ∑ ω, (if setCl (ω \ B) S = W then weight w ω * K W (ω \ A) else 0)
        = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
          rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
      _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
      _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
  calc ∑ ω, weight w ω * K (setCl (ω \ B) S) (ω \ barOf S (setCl (ω \ B) S))
      = ∑ ω, ∑ W, (if setCl (ω \ B) S = W then weight w ω * K W (ω \ barOf S W) else 0) :=
        Finset.sum_congr rfl fun ω _ =>
          (Fintype.sum_ite_eq (setCl (ω \ B) S) fun W => weight w ω * K W (ω \ barOf S W)).symm
    _ = ∑ W, ∑ ω, (if setCl (ω \ B) S = W then weight w ω * K W (ω \ barOf S W) else 0) := Finset.sum_comm
    _ = ∑ W, ∑ ω, (if setCl (ω \ B) S = W then weight w ω * ∑ η, weight w η * K W (η \ barOf S W) else 0) :=
        Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω, ∑ W, (if setCl (ω \ B) S = W then weight w ω * ∑ η, weight w η * K W (η \ barOf S W) else 0) :=
        Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun ω _ =>
        Fintype.sum_ite_eq (setCl (ω \ B) S) fun W => weight w ω * ∑ η, weight w η * K W (η \ barOf S W)

/-- **The world mean** of `g(C_s)` given the cluster of `X` in `ζ`: `ḡ(ζ) = Σ_η w(η) g(C_s(η ∖ cut_X(ζ)))` (sum level; the world
deletes the pairs meeting `X ∪ V(C_X(ζ))`). [folklore] -/
def wmeanOff (w : Sym2 V → ℝ) (X : Set V) (φ : Set (Sym2 V) → ℝ) (ζ : Set (Sym2 V)) : ℝ :=
  ∑ η, weight w η * φ (η \ cut X ζ)

omit [Fintype V] in
/-- `{s ↮ X}` in `ζ` iff `s ∉ X ∪ V(C_X(ζ))`. [cite: VandenbergHaggstromKahn2005, §2.1 p. 10 (sentence before Lemma 2.4)] -/
theorem mem_avoidEv_iff_notMem_span (s : V) (X : Set V) (ζ : Set (Sym2 V)) :
    ζ ∈ avoidEv s X ↔ ¬ (s ∈ X ∨ ∃ e ∈ setCl ζ X, s ∈ e) := by
  rw [← setReach_iff]
  constructor
  · rintro h ⟨x, hx, hxs⟩; exact h x hx hxs.symm
  · intro h x hx hsx; exact h ⟨x, hx, hsx.symm⟩

/-- **Lemma Φ(a)**, sum level: for every weight `w` (`Σ weight = 1`), owner `s`, avoided
set `X`, vertex set `K` and functional `g`,
`Σ_η w(η)·I_K(η) = Σ_η w(η)·1{s ↮ X off K}(η)·( ḡ(η off K) − g(C_s(η off K)) )`,
`ḡ = wmeanOff w X (g ∘ C_s)` the world mean in `G` (NOT in `G − K`).  Proof: the first term of `I_K` is
`g(C_s(η ∖ cut_X(η off K)))`; by `set_sum_cond_sdiff_off` (cluster of `X` explored off `edgesOf K`, world = full configuration off
the cut) its weighted sum equals that of the world mean.
[folklore] -/
theorem sum_phiIntegrand_eq (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (s : V) (X K : Set V)
    (g : Set (Sym2 V) → ℝ) :
    ∑ η, weight w η * phiIntegrand s X K g η =
      ∑ η, weight w η * (ind (avoidEv s X) (η \ edgesOf K) *
        (wmeanOff w X (fun β => g (openEdgeCluster β s)) (η \ edgesOf K) - g (openEdgeCluster (η \ edgesOf K) s))) := by
  classical
  -- unfold the integrand as an indicator times a difference
  have hI : ∀ η, phiIntegrand s X K g η = ind (avoidEv s X) (η \ edgesOf K) *
      (g (openEdgeCluster (η \ cut X (η \ edgesOf K)) s) - g (openEdgeCluster (η \ edgesOf K) s)) := by
    intro η
    unfold phiIntegrand
    by_cases h : ∀ x ∈ X, ¬ (openGraph (η \ edgesOf K)).Reachable s x
    · rw [if_pos h, ind_of_mem (show η \ edgesOf K ∈ avoidEv s X from h), one_mul]
    · rw [if_neg h, ind_of_not_mem (show η \ edgesOf K ∉ avoidEv s X from h), zero_mul]
  simp_rw [hI, mul_sub, Finset.sum_sub_distrib]
  congr 1
  -- the Markov identity for the first term, kernel `K(W, β) = 1{s ∉ X ∪ V(W)} · g(C_s(β))`
  set Kk : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun W β =>
    (if (s ∈ X ∨ ∃ e ∈ W, s ∈ e) then 0 else 1) * g (openEdgeCluster β s) with hKk
  have hind : ∀ ζ : Set (Sym2 V), ind (avoidEv s X) ζ = (if (s ∈ X ∨ ∃ e ∈ setCl ζ X, s ∈ e) then 0 else 1) := by
    intro ζ
    by_cases h : (s ∈ X ∨ ∃ e ∈ setCl ζ X, s ∈ e)
    · rw [if_pos h, ind_of_not_mem (fun h' => (mem_avoidEv_iff_notMem_span s X ζ).1 h' h)]
    · rw [if_neg h, ind_of_mem ((mem_avoidEv_iff_notMem_span s X ζ).2 h)]
  have key := set_sum_cond_sdiff_off w hm X (edgesOf K) Kk
  have lhs : ∀ η, weight w η * (ind (avoidEv s X) (η \ edgesOf K) * g (openEdgeCluster (η \ cut X (η \ edgesOf K)) s)) =
      weight w η * Kk (setCl (η \ edgesOf K) X) (η \ barOf X (setCl (η \ edgesOf K) X)) := by
    intro η; rw [hKk, hind, cut_eq_barOf]
  have rhs : ∀ η, weight w η * (ind (avoidEv s X) (η \ edgesOf K) *
      wmeanOff w X (fun β => g (openEdgeCluster β s)) (η \ edgesOf K)) =
      weight w η * ∑ η', weight w η' * Kk (setCl (η \ edgesOf K) X) (η' \ barOf X (setCl (η \ edgesOf K) X)) := by
    intro η
    rw [hind, wmeanOff, Finset.mul_sum, cut_eq_barOf]
    congr 1
    refine Finset.sum_congr rfl fun η' _ => ?_
    rw [hKk]; ring
  rw [Finset.sum_congr rfl fun η _ => lhs η, key]
  exact (Finset.sum_congr rfl fun η _ => rhs η).symm

end CSH

end Percolation.Continuity
