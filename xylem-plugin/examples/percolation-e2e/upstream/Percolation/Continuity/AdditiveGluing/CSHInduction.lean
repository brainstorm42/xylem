import Percolation.Continuity.CSH.LemmaT
import Percolation.Continuity.CovTau.OfTA
import Percolation.Literature.LatticeModels.ProdBernoulliWeightContinuity
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH for EVERY decoy list from the one-level UNFOLDING step — the induction skeleton of Theorem 1 of the (S5)-all-r proof of `Percolation.Continuity.Statements.AdditiveGluing`

THE INDUCTION.  Fix a finite vertex type, NON-DEGENERATE weights `w` (all pair probabilities in `(0,1)`), and call
CSH(Y; x; D; o, v) the statement `0 ≤ CSH.cshMargin w x Y D o v f` for every monotone `f` (owner `x`, avoided set `Y`, decoy list `D`,
observers `o, v`, all named vertices distinct).  Level `D = []` is MDL(X) = COV(τ)-with-avoided-set
(`CovTau.markerDominanceAvoid`): `cshMargin_nil_nonneg`.  For `D ≠ []`, Lemma T (`CSH.cshMargin_nonneg_of_within`)
reduces CSH(Y; x; D; o, v) to the WORLD-WISE ("within") margin `W[g] ≥ 0` for every monotone `g ≥ 0`; Lemmas U + H
(world-wise unfolding = Hpart ≥ 0 plus a nonnegative combination of LOWER-LEVEL margins CSH(Y_j; d_j; D_{>j}; o, v)[Φ_j],
`Y_j = {x} ∪ Y ∪ D_{<j}`, `Φ_j` monotone ≥ 0 by `CSH.phiFun_mono`/`phiFun_nonneg`) give `W[g] ≥ 0` from the lower levels.  This file is
the skeleton that turns that ONE-LEVEL UNFOLDING STEP — stated as the hypothesis `hU` below, in the verbatim vocabulary of
`CSH.cshMargin_nonneg_of_within` (worlds = weights zeroed on the pairs meeting the open vertex cluster of `Y`) — into CSH for EVERY decoy
list by strong induction on the length of the list (`cshMargin_nonneg_of_unfold`).  So THEOREM 1 (CSH for all data) = `hU`; with peeling
(`0 ≤ CSH.surplusMargin … []` from CSH) and `CSH.additiveGluing_of_surplusMargin_nondegenerate`, `AdditiveGluing` follows.
[cite: VandenbergHaggstromKahn2005, §2.1 (pp. 9–13)] [cite: KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity.CSH

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli prodBernoulli_real_pos_of_nonempty)
open Percolation.Literature
open scoped Classical

variable {V : Type*} [Fintype V]

/-- **Level zero of the hierarchy is MDL(X)** (`CovTau.markerDominanceAvoid`, divided by `μ(v ↮ {x} ∪ Y) > 0`): for non-degenerate
weights, `x ≠ v`, and every monotone `f`, `0 ≤ CSH.cshMargin w x Y [] o v f = cov_D(f, 1{x↔o}) − μ(o↔v | v↮{x}∪Y)·cov_D(f, 1{x↔v})`.
[cite: VandenbergHaggstromKahn2005, §2.1 (pp. 9–13)] -/
theorem cshMargin_nil_nonneg (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (o v : V)
    (hv : v ∉ insert x Y) (f : Set (Sym2 V) → ℝ) (hf : Monotone f) :
    0 ≤ cshMargin w x Y [] o v f := by
  have hxv : x ≠ v := fun h => hv (h ▸ Set.mem_insert x Y)
  have hmd := CovTau.markerDominanceAvoid w x v o Y hxv f hf
  set M := (prodBernoulli w).real {ω : BondConfig V | ∀ x' ∈ insert x Y, ¬ (openGraph ω).Reachable v x'} with hM
  set E := (prodBernoulli w).real ({ω : BondConfig V | ∀ x' ∈ insert x Y, ¬ (openGraph ω).Reachable v x'} ∩ openConn v o)
    with hE
  have hMpos : 0 < M := by
    refine prodBernoulli_real_pos_of_nonempty hw ⟨∅, fun a ha hreach => ?_⟩
    have hbot : openGraph (∅ : BondConfig V) = ⊥ := by
      unfold openGraph; exact SimpleGraph.fromEdgeSet_empty
    rw [hbot, SimpleGraph.reachable_bot] at hreach
    exact hv (hreach ▸ ha)
  -- unfold the level-zero margin
  have hset : insert x Y ∪ {d : V | d ∈ ([] : List V)} = insert x Y := by
    ext u; simp
  have hobs : obsConst w o v (insert x Y ∪ {d : V | d ∈ ([] : List V)}) = E / M := by
    rw [hset]; unfold obsConst; rw [KNPreFKG.openConn_symm o v]
  have hmargin : cshMargin w x Y [] o v f = covD w x Y f o - E / M * covD w x Y f v := by
    simp only [cshMargin, decoyList, cshMarg_nil, hobs]
  rw [hmargin]
  -- `markerDominanceAvoid`: `E · covD v ≤ M · covD o`
  change E * covD w x Y f v ≤ M * covD w x Y f o at hmd
  have h1 : M * (covD w x Y f o - E / M * covD w x Y f v) = M * covD w x Y f o - E * covD w x Y f v := by
    field_simp
  have h2 : 0 ≤ M * (covD w x Y f o - E / M * covD w x Y f v) := by rw [h1]; linarith
  exact nonneg_of_mul_nonneg_right h2 hMpos

/-- **Theorem 1 (CSH for all data) from the one-level unfolding step** (strong induction on the number of decoys).  Fix non-degenerate weights.
HYPOTHESIS `hU` (= Lemmas U + H): for every datum (owner `x`, avoided set `Y`, NONEMPTY
decoy list `D`, observers `o, v`, all distinct), IF every lower-level margin `CSH.cshMargin w d ({x} ∪ Y ∪ pre) ds' o v h` (`D = pre ++ d :: ds'`,
`h` monotone `≥ 0`) is nonnegative, THEN the world-wise margin `W[g]` of `CSH.cshMargin_nonneg_of_within` is nonnegative for every monotone `g ≥ 0`.
CONCLUSION: `0 ≤ CSH.cshMargin w x Y D o v f` for every datum with distinct named vertices and every monotone `f`.
[cite: VandenbergHaggstromKahn2005, §2.1 (pp. 9–13)] [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem cshMargin_nonneg_of_unfold (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (hU : ∀ (x : V) (Y : Set V) (D : List V) (o v : V),
      x ∉ Y → o ∉ insert x Y → v ∉ insert x Y → o ≠ v → D ≠ [] → D.Nodup → (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) →
      (∀ (pre : List V) (d : V) (ds' : List V), D = pre ++ d :: ds' →
        ∀ h : Set (Sym2 V) → ℝ, Monotone h → (∀ C, 0 ≤ h C) →
          0 ≤ cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds' o v h) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
        cshMarg (decoyList w (insert x Y) D) (obsConst w o v (insert x Y ∪ {d | d ∈ D})) o v
          (fun u => (∫ η in (openConn x u : Set (BondConfig V)), g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) -
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) *
              (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e).real (openConn x u : Set (BondConfig V)))
        ∂(prodBernoulli w)) :
    ∀ (D : List V) (x : V) (Y : Set V) (o v : V),
      x ∉ Y → o ∉ insert x Y → v ∉ insert x Y → o ≠ v → D.Nodup → (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) →
      ∀ f : Set (Sym2 V) → ℝ, Monotone f → 0 ≤ cshMargin w x Y D o v f := by
  -- strong induction on the length of the decoy list
  suffices hk : ∀ (k : ℕ) (D : List V), D.length ≤ k → ∀ (x : V) (Y : Set V) (o v : V),
      x ∉ Y → o ∉ insert x Y → v ∉ insert x Y → o ≠ v → D.Nodup → (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) →
      ∀ f : Set (Sym2 V) → ℝ, Monotone f → 0 ≤ cshMargin w x Y D o v f from
    fun D => hk D.length D le_rfl
  intro k
  induction k with
  | zero =>
    intro D hD x Y o v _ _ hv hov _ _ f hf
    have hD0 : D = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hD)
    subst hD0
    exact cshMargin_nil_nonneg w hw x Y o v hv f hf
  | succ k ih =>
    intro D hD x Y o v hxY ho hv hov hnd hdis f hf
    by_cases hnil : D = []
    · subst hnil
      exact cshMargin_nil_nonneg w hw x Y o v hv f hf
    -- Lemma T: reduce to the world-wise margin
    have hY : ∀ e : Sym2 V, ¬ e.IsDiag → (∃ u ∈ e, u ∈ Y) → (w e : ℝ) < 1 :=
      fun e _ _ => unitInterval.coe_lt_one.2 (hw e).2
    refine cshMargin_nonneg_of_within w x Y D o v hY (fun g hg hg0 => ?_) f hf
    refine hU x Y D o v hxY ho hv hov hnil hnd hdis (fun pre d ds' hsplit h hh hh0 => ?_) g hg hg0
    -- the lower level `(d | {x} ∪ Y ∪ pre ; ds')` has fewer decoys: induction hypothesis
    have hlen : ds'.length ≤ k := by
      have : D.length = pre.length + (ds'.length + 1) := by rw [hsplit, List.length_append, List.length_cons]
      omega
    have hdD : d ∈ D := by rw [hsplit]; exact List.mem_append_right pre List.mem_cons_self
    have hpreD : ∀ e ∈ pre, e ∈ D := fun e he => by rw [hsplit]; exact List.mem_append_left _ he
    have hds'D : ∀ e ∈ ds', e ∈ D := fun e he => by rw [hsplit]; exact List.mem_append_right pre (List.mem_cons_of_mem d he)
    -- nodup bookkeeping along `pre ++ d :: ds'`
    have hnd' : (pre ++ d :: ds').Nodup := hsplit ▸ hnd
    have hnd_ds' : ds'.Nodup := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).2
    have hd_notin_ds' : d ∉ ds' := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
    have hd_notin_pre : d ∉ pre := fun hdp =>
      (List.nodup_append.1 hnd').2.2 d hdp d List.mem_cons_self rfl
    have hds'_notin_pre : ∀ e ∈ ds', e ∉ pre := fun e he hep =>
      (List.nodup_append.1 hnd').2.2 e hep e (List.mem_cons_of_mem d he) rfl
    -- the new avoided set
    set Y' : Set V := insert x Y ∪ {e | e ∈ pre} with hY'
    have hdY' : d ∉ Y' := by
      rintro (h1 | h2)
      · exact (hdis d hdD).1 h1
      · exact hd_notin_pre h2
    have hoY' : o ∉ insert d Y' := by
      rintro (h0 | h1 | h2)
      · exact (hdis d hdD).2.1 h0.symm
      · exact ho h1
      · exact (hdis o (hpreD o h2)).2.1 rfl
    have hvY' : v ∉ insert d Y' := by
      rintro (h0 | h1 | h2)
      · exact (hdis d hdD).2.2 h0.symm
      · exact hv h1
      · exact (hdis v (hpreD v h2)).2.2 rfl
    have hdis' : ∀ e ∈ ds', e ∉ insert d Y' ∧ e ≠ o ∧ e ≠ v := by
      intro e he
      refine ⟨?_, (hdis e (hds'D e he)).2.1, (hdis e (hds'D e he)).2.2⟩
      rintro (h0 | h1 | h2)
      · exact hd_notin_ds' (h0 ▸ he)
      · exact (hdis e (hds'D e he)).1 h1
      · exact hds'_notin_pre e he h2
    exact ih ds' hlen d Y' o v hdY' hoY' hvY' hov hnd_ds' hdis' h hh

/-- **`CSHHolds` for every datum from the one-level unfolding step** (wrapper of `cshMargin_nonneg_of_unfold` in `CSH.CSHHolds`
vocabulary, the hypothesis shape of the peeling theorem P7). [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem cshHolds_of_unfold (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1)
    (hU : ∀ (x : V) (Y : Set V) (D : List V) (o v : V),
      x ∉ Y → o ∉ insert x Y → v ∉ insert x Y → o ≠ v → D ≠ [] → D.Nodup → (∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) →
      (∀ (pre : List V) (d : V) (ds' : List V), D = pre ++ d :: ds' →
        ∀ h : Set (Sym2 V) → ℝ, Monotone h → (∀ C, 0 ≤ h C) →
          0 ≤ cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds' o v h) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
        cshMarg (decoyList w (insert x Y) D) (obsConst w o v (insert x Y ∪ {d | d ∈ D})) o v
          (fun u => (∫ η in (openConn x u : Set (BondConfig V)), g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) -
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) *
              (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e).real (openConn x u : Set (BondConfig V)))
        ∂(prodBernoulli w))
    (x : V) (Y : Set V) (D : List V) (o v : V)
    (hxY : x ∉ Y) (ho : o ∉ insert x Y) (hv : v ∉ insert x Y) (hov : o ≠ v) (hnd : D.Nodup)
    (hdis : ∀ d ∈ D, d ∉ insert x Y ∧ d ≠ o ∧ d ≠ v) :
    CSHHolds w x Y D o v :=
  fun f hf => cshMargin_nonneg_of_unfold w hw hU D x Y o v hxY ho hv hov hnd hdis f hf

end Percolation.Continuity.CSH

end
