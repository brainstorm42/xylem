import Percolation.Literature.RussoFormula
import Percolation.Util.Linter

/-!
# The multi-valued map principle (Duminil-Copin–Sidoravicius–Tassion 2016, Lemma 7)

Part of the bottom-up decomposition of the named
fact `DuminilCopinSidoraviciusTassion2016` (`HalfSpace.lean`; DST 2016, Thm. 1, no percolation
at criticality on slabs): the counting lemma behind the gluing Lemma 6 of the paper (§2.3),
proved here in its finite form.

**DST 2016, Lemma 7** (p. 6). Let `s, t > 0`. Consider two events `𝒜`, `ℬ` and a map `Φ` from
`𝒜` into the set of subevents of `ℬ`, such that (i) `|Φ(ω)| ≥ t` for all `ω ∈ 𝒜`, and (ii) for
every `ω' ∈ ℬ` there is a set `S` of at most `s` edges such that every `ω` with `ω' ∈ Φ(ω)`
agrees with `ω'` off `S`. Then `P_p[𝒜] ≤ (2 / min{p, 1-p})^s / t · P_p[ℬ]`. *Proof* (printed,
eqs. (14)–(16)): exchange the summations over `ω` and `ω' ∈ Φ(ω)`; a configuration agreeing
with `ω'` off `S` has weight at most `P[ω'] / min{p,1-p}^s`, and at most `2^s` configurations
agree with `ω'` off `S`.

The printed proof sums `P[ω]` over single configurations, i.e. it takes place on a finite product
space `{0,1}^E`.

Hypothesis (ii) is taken with `|S| ≤ s` ("less than `s` edges" in the paper; the weak
inequality gives the formally stronger statement, with the same proof), and `t` is any positive
real.

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: Lemma 7 and its proof, eqs. (14)–(16) (p. 6).
* L. Russo, Z. Wahrsch. Verw. Gebiete 56 (1981), §4 (cylinder probabilities as products of
  one-coordinate weights; `Russo.setBernoulli_real_localCylinder` of `RussoFormula.lean`).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Finset LatticeModels
open scoped ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Bernoulli weights of single configurations -/

omit [Fintype ι] in
/-- At most `2^{|S|}` configurations of a family agree with a given `ω'` off `S` (they are
determined by their trace on `S`). [cite: DuminilCopinSidoraviciusTassion2016, Lemma 7 (proof, eq. (16))] -/
theorem card_filter_agree_off_le (A : Finset (Finset ι)) (ω' S : Finset ι) (P : Finset ι → Prop)
    [DecidablePred P] (hP : ∀ ω ∈ A, P ω → ∀ i, i ∉ S → (i ∈ ω ↔ i ∈ ω')) :
    (A.filter P).card ≤ 2 ^ S.card := by
  rw [← card_powerset]
  refine card_le_card_of_injOn (fun ω => ω ∩ S) (fun ω hω => ?_) ?_
  · simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset]
    exact inter_subset_right
  · intro ω₁ h₁ ω₂ h₂ heq
    simp only [coe_filter, Set.mem_setOf_eq] at h₁ h₂
    have a₁ := hP ω₁ h₁.1 h₁.2
    have a₂ := hP ω₂ h₂.1 h₂.2
    ext i
    by_cases hi : i ∈ S
    · have := Finset.ext_iff.1 heq i
      simpa [mem_inter, hi] using this
    · rw [a₁ i hi, a₂ i hi]

end Percolation.Literature

end
