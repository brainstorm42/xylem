import Percolation.Continuity.CSH.Defs
import Percolation.Literature.TwoClusterGibbsCovariance
import Percolation.Util.Linter

/-!
# Conditioned slack hierarchy: LEMMA T (the Gibbs-sampler reduction of a CSH margin to its world-wise form)

Lemma T: the CSH margin `Marg[u ↦ cov_D(f(C_x), 1{x↔u})]` (`D = {x ↮ Y}`, `Marg` the level form of the decoy
list, `CSH.cshMargin`) is nonnegative for every monotone `f` as soon as its WORLD-WISE version
`∫_D Marg[u ↦ Cov_{w^ω}(g(C_x), 1{x↔u})] dμ(ω) ≥ 0` holds for every monotone `g ≥ 0`, where `w^ω` are the weights zeroed on
the pairs meeting the open vertex cluster of `Y` (percolation on `G ∖ C_Y(ω)`, vdBHK Lemma 2.4).  This is the
multi-marker reduction theorem `BHK2006_multiMarkerCov_nonneg_of_within` (law of total covariance along `σ(C_Y)`, BHK's
two-step chain, contraction) applied to the linear form `Marg`, whose coefficients are read off by linearity
(`cshMarg_eq_sum`: `Marg[f] = Σ_u Marg[δ_u]·f(u)`).

* `CSH.cshMarg_finset_sum`, `CSH.cshMarg_eq_sum` — linearity bookkeeping;
* `CSH.cshMargin_nonneg_of_within` — Lemma T at fixed weights (`w e < 1` on the non-loop pairs meeting `Y`, e.g. any
  non-degenerate `w`; for `Y = ∅` no condition).
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13, Lemma 2.4 (p. 10)] [cite: KozmaNitzan2024, Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

namespace CSH

variable {V : Type*}

/-- `Marg[0] = 0`. [folklore] -/
theorem cshMarg_zero (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) : cshMarg L p o v (0 : V → ℝ) = 0 := by
  have h := cshMarg_smul L p o v 0 (0 : V → ℝ)
  rwa [zero_smul, zero_mul] at h

/-- `Marg` commutes with finite sums. [folklore] -/
theorem cshMarg_finset_sum {ι : Type*} (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (s : Finset ι) (g : ι → V → ℝ) :
    cshMarg L p o v (∑ i ∈ s, g i) = ∑ i ∈ s, cshMarg L p o v (g i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, cshMarg_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, cshMarg_add, ih]

/-- **The coefficients of the margin**: `Marg[f] = Σ_u Marg[δ_u] · f(u)` (finite vertex type). [folklore] -/
theorem cshMarg_eq_sum [Fintype V] (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f : V → ℝ) :
    cshMarg L p o v f = ∑ u, cshMarg L p o v (Pi.single u 1) * f u := by
  have hf : f = ∑ u, f u • (Pi.single u (1 : ℝ) : V → ℝ) := by
    funext z
    rw [Finset.sum_apply, Finset.sum_eq_single z]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro u _ huz
      simp only [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm huz), smul_eq_mul, mul_zero]
    · intro hz; exact absurd (Finset.mem_univ z) hz
  conv_lhs => rw [hf]
  rw [cshMarg_finset_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [cshMarg_smul, mul_comm]

variable [Fintype V]

/-- **Lemma T for the conditioned slack hierarchy (fixed weights).** Owner `x`, avoided set `Y` with `w e < 1` on the
non-loop pairs meeting `Y`, decoys `D`, observers `o, v`; `L`, `p` the decoy list and observers' constant of `CSH.cshMargin`.
IF for every monotone `g ≥ 0` the world-wise margin is nonnegative,
`0 ≤ ∫_{x↮Y} Marg_L,p[u ↦ ∫_{x↔u} g(C_x) dμ_{w^ω} − (∫ g(C_x) dμ_{w^ω})·μ_{w^ω}(x↔u)] dμ_w(ω)`
(`w^ω` = `w` zeroed on the pairs meeting the open vertex cluster of `Y`), THEN `0 ≤ CSH.cshMargin w x Y D o v f` for every
monotone `f`. [cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13, Lemma 2.4 (p. 10)] -/
theorem cshMargin_nonneg_of_within (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (D : List V) (o v : V)
    (hY : ∀ e : Sym2 V, ¬ e.IsDiag → (∃ u ∈ e, u ∈ Y) → (w e : ℝ) < 1)
    (hW : ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
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
    (f : Set (Sym2 V) → ℝ) (hf : Monotone f) :
    0 ≤ cshMargin w x Y D o v f := by
  set L := decoyList w (insert x Y) D with hL
  set p := obsConst w o v (insert x Y ∪ {d | d ∈ D}) with hp
  set Λ : V → ℝ := fun u => cshMarg L p o v (Pi.single u 1) with hΛ
  have hmain := BHK2006_multiMarkerCov_nonneg_of_within w x Y hY Finset.univ Λ (fun g hg hg0 => by
    have h := hW g hg hg0
    have e : ∀ ω : BondConfig V, cshMarg L p o v
        (fun u => (∫ η in (openConn x u : Set (BondConfig V)), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                then (0 : unitInterval) else w e)) -
            (∫ η, g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                then (0 : unitInterval) else w e)) *
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                then (0 : unitInterval) else w e).real (openConn x u : Set (BondConfig V))) =
        ∑ u, Λ u * ((∫ η in (openConn x u : Set (BondConfig V)), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                then (0 : unitInterval) else w e)) -
            (∫ η, g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                then (0 : unitInterval) else w e)) *
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                then (0 : unitInterval) else w e).real (openConn x u : Set (BondConfig V))) :=
      fun ω => cshMarg_eq_sum L p o v _
    simp only [e] at h
    exact h) f hf
  have hconc : cshMargin w x Y D o v f = ∑ u, Λ u * covD w x Y f u := by
    rw [cshMargin, ← hL, ← hp, cshMarg_eq_sum]
  rw [hconc]
  exact hmain

end CSH

end Percolation.Continuity

end
