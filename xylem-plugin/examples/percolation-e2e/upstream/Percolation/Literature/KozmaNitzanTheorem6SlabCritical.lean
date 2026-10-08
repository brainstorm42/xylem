import Percolation.Literature.HalfSpaceProofs
import Percolation.Literature.KozmaNitzanTheorem6OfSlab
import Percolation.Util.Linter

/-!
# No slab percolates at `p_c(ℤ^d)`, in every dimension, and Kozma–Nitzan's Theorem 6 unconditionally

The statement `Percolation.Literature.theta_slab_criticalProb_zd_eq_zero` of
`Literature/KozmaNitzanTheorem6OfSlab.lean` — for `d ≥ 3` and `k ≥ 1`, `θ_{S_k}(p_c(ℤ^d)) = 0` for the slab
`S_k = {x ∈ ℤ^d | 0 ≤ x₀ ≤ k}` (Grimmett 1999, (7.38) p. 165: "`P_{p_c}(b(0) ↔ ∞ in S_h) = 0` for
all `h`") — is proved here, `theta_slab_criticalProb_zd_eq_zero_holds`, and with it Kozma–Nitzan's
Theorem 6 (arXiv:2401.12397, Thm 6 p. 15: "If conjecture 3 holds then `P(|C(0)| = ∞) = 0` at the
critical probability for `ℤ^d` for any `d ≥ 2`") becomes an unconditional theorem,
`KozmaNitzan2024_thm6_holds` (through `KozmaNitzan2024_thm6_of_slabCritical`, whose other input,
the same-`p` slab percolation of §4, is proved in `Literature/KozmaNitzanTheorem6OfSlab.lean`).

## The proof, and what it does NOT need

Grimmett (p. 165) reads (7.38) off the strict inequality `p_c(S_h) > p_c` of Aizenman–Grimmett
(essential enhancements, §3.3 Thm. (3.16) with item C "Slabs", pp. 65–66), and the statement's
docstring records that pointer. The proof here does not need it: the slab is a subset of the half-space,
`S_k ⊆ ℍ = {x | 0 ≤ x₀}`, so by the subgraph coupling (Grimmett §7.1 (7.1) p. 146,
`theta_induce_mono_holds` of `SubgraphMonotonicity.lean`) `θ_{S_k}(p) ≤ θ_ℍ(p)` for every `p`, and
`θ_ℍ(p_c(ℤ^d)) = 0` for every `d ≥ 2` is the Barsky–Grimmett–Newman theorem (Grimmett Thm. (7.35)
p. 163), proved in every dimension as `BarskyGrimmettNewman1991_holds`
(`HalfSpaceProofs.lean`: the dynamic renormalisation of §7.3 pp. 163–176 in `ℤ^d`, `d ≥ 3`, and
Harris–Kesten at `d = 2`). Hence `0 ≤ θ_{S_k}(p_c) ≤ θ_ℍ(p_c) = 0`, for every `d ≥ 2` and every
`k` (`theta_slab_criticalProbI_eq_zero_of_two_le`). Neither the Aizenman–Grimmett strict inequality
nor the Grimmett–Marstrand slab limit `p_c(S_k) ↓ p_c` enters.

## Content

* `slab_subset_halfSpace`, `theta_slab_le_theta_halfSpace` — `S_k ⊆ ℍ` and `θ_{S_k} ≤ θ_ℍ`.
* `theta_slab_criticalProbI_eq_zero_of_two_le` — `θ_{S_k}(p_c(ℤ^d)) = 0` for `d ≥ 2`, all `k`.
* `theta_slab_criticalProb_zd_eq_zero_holds` — the statement in its printed range `d ≥ 3`, `k ≥ 1`.
* `KozmaNitzan2024_thm6_holds` — `KozmaNitzan2024_conjecture3 → ∀ d ≥ 2, PercolationContinuity d`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999 [GrimmettPercolation1999]:
  §7.1 (7.1) p. 146 (`S_k ⊆ S_{k+1} ⊆ ℤ^d`), §7.3 Thm. (7.35) p. 163 (`θ_ℍ(p_c) = 0`, `d ≥ 2`),
  (7.38) p. 165; §3.3 Thm. (3.16) and item C, pp. 65–66 (the printed provenance, not used).
* D. J. Barsky, G. R. Grimmett, C. M. Newman, *Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability*, Probab. Theory Related Fields 90 (1991)
  111–148, Thm. 1.1 (i). [BarskyGrimmettNewman1991]
* G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a conjectured inequality*,
  arXiv:2401.12397 (2024), Thm 6 p. 15, proof p. 25. [KozmaNitzan2024]
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels

/-- The slab lies in the half-space: `S_k = {0 ≤ x₀ ≤ k} ⊆ ℍ = {0 ≤ x₀}` (Grimmett 1999, §7.1
p. 146 and §7.3 p. 165, `S_h ⊆ ℍ`). [cite: GrimmettPercolation1999, §7.3 p. 165] -/
theorem slab_subset_halfSpace (d : ℕ) [NeZero d] (k : ℕ) : slab d k ⊆ halfSpace d :=
  fun _ hx => hx.1

/-- **`θ_{S_k}(p) ≤ θ_ℍ(p)`**: percolation in the slab is dominated by percolation in the
half-space containing it (the subgraph coupling, Grimmett 1999, §7.1 (7.1) p. 146:
"`p_c(S_k) ≥ p_c(S_{k+1}) ≥ p_c`"). [cite: GrimmettPercolation1999, §7.1 (7.1) p. 146] -/
theorem theta_slab_le_theta_halfSpace (d : ℕ) [NeZero d] (k : ℕ) (p : unitInterval) :
    theta (slabGraph d k) (slabOrigin d k) p ≤ theta (halfSpaceGraph d) (halfSpaceOrigin d) p :=
  theta_induce_mono_holds (zdGraph d) (slab_subset_halfSpace d k) 0 (zero_mem_slab d k) p

/-- **No slab percolates at `p_c(ℤ^d)`, for every `d ≥ 2` and every width `k`**:
`θ_{S_k}(p_c(ℤ^d)) = 0` (Grimmett 1999, (7.38) p. 165), from `0 ≤ θ_{S_k}(p_c) ≤ θ_ℍ(p_c) = 0`,
the last equality being the Barsky–Grimmett–Newman theorem (Thm. (7.35) p. 163),
`BarskyGrimmettNewman1991_holds`, for all `d ≥ 2`. [cite: GrimmettPercolation1999, §7.3 (7.38) p. 165 and Thm. (7.35) p. 163] -/
theorem theta_slab_criticalProbI_eq_zero_of_two_le {d : ℕ} [NeZero d] (hd : 2 ≤ d) (k : ℕ) :
    theta (slabGraph d k) (slabOrigin d k) (criticalProbI d) = 0 :=
  le_antisymm
    ((theta_slab_le_theta_halfSpace d k (criticalProbI d)).trans
      (BarskyGrimmettNewman1991_holds d hd).le)
    measureReal_nonneg

/-- **`theta_slab_criticalProb_zd_eq_zero` holds**: for `d ≥ 3` and `k ≥ 1`,
`θ_{S_k}(p_c(ℤ^d)) = 0` (Grimmett 1999, (7.38) p. 165; the step "percolation in some slab at `p`
will imply, by Aizenman–Grimmett, that `p > p_c`" of Kozma–Nitzan's proof of Thm 6, p. 25). Proved
from the Barsky–Grimmett–Newman theorem by `θ_{S_k} ≤ θ_ℍ` (`theta_slab_criticalProbI_eq_zero_of_two_le`),
not from the Aizenman–Grimmett strict inequality cited in print.
[cite: GrimmettPercolation1999, §7.3 (7.38) p. 165] -/
theorem theta_slab_criticalProb_zd_eq_zero_holds : theta_slab_criticalProb_zd_eq_zero :=
  fun _ _ hd k _ => theta_slab_criticalProbI_eq_zero_of_two_le (le_of_lt hd) k

/-- **Kozma–Nitzan 2024, Theorem 6, UNCONDITIONALLY (as the printed implication)**: "If conjecture 3
holds then `P(|C(0)| = ∞) = 0` at the critical probability for `ℤ^d` for any `d ≥ 2`"
(arXiv:2401.12397, Thm 6 p. 15) — the statement `KozmaNitzan2024_thm6` of `KozmaNitzanReduction.lean`,
proved by `KozmaNitzan2024_thm6_of_slabCritical` (same-`p` slab percolation, §4 pp. 25–31, proved in
`Literature/KozmaNitzanTheorem6OfSlab.lean`) fed with `theta_slab_criticalProb_zd_eq_zero_holds`.
[cite: KozmaNitzan2024, Thm 6 (p. 15; proof pp. 25–31)] -/
theorem KozmaNitzan2024_thm6_holds : KozmaNitzan2024_thm6 :=
  KozmaNitzan2024_thm6_of_slabCritical theta_slab_criticalProb_zd_eq_zero_holds

end Percolation.Literature

end
