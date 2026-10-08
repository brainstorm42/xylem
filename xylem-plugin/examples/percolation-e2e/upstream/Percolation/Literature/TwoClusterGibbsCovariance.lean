import Percolation.Literature.LatticeModels.ProdBernoulliWeightContinuity
import Percolation.Literature.TwoClusterGibbsSampler
import Percolation.Util.Linter

/-!
# Covariances along the two-cluster Gibbs sampler of van den Berg–Häggström–Kahn (2006), §2.1: the one-step covariance decomposition and the reduction of a conditional covariance sign to the sign of the averaged one-step ("within") covariances

Companion of `TwoClusterGibbsSampler.lean` (the chain
`(C_S, C_T) ↦ (C_S', C_T')` of BHK §2.1 at `q = 1`: `BHK2006.halfT`, `BHK2006.halfS`, `BHK2006.gibbsE`,
the half-step identities `BHK2006.set_sum_cond_cluster(')` = Lemma 2.4 summed, stationarity, and the
regeneration contraction `BHK2006.gibbsE_iterate_sub_le`).  All declarations are definitions with bodies or
theorems.

## The mathematics (BHK's chain, read on functions of `C_S` only)

Bond percolation with pair probabilities `w` on a finite vertex type, vertex sets `S, T`, `D = {S ↮ T}`.
For a function `φ` of `C_S` put `(A φ)(B) = E[φ(C_S) | C_T = B]` (the `S`-half-step: the cluster of `S` in a
fresh configuration with the pairs meeting `T ∪ V(B)` deleted, Lemma 2.4) and
`(𝑇 φ)(C) = E[(A φ)(C_T) | C_S = C]` (the `T`-half-step followed by the `S`-half-step; `𝑇` is BHK's
one-step operator `gibbsE` on functions of the first coordinate, `BHK2006.gibbsE_comp_fst`).  With
`cov_D(φ, h) = P(D)·E[φ h 1_D] − E[φ 1_D]·E[h 1_D]` (denominator-free conditional covariance of two functions
of `C_S`) and the averaged conditional ("within") covariance
`R(φ) = E[ (A(φh) − Aφ·Ah)(C_T) 1_D ] = E[ Cov(φ(C_S), h(C_S) | C_T) ; D ]`, the two half-step identities give
the exact ONE-STEP DECOMPOSITION (law of total covariance along `σ(C_T)`, then Lemma 2.4 once more)

  `cov_D(φ, h) = P(D)·R(φ) + cov_D(𝑇φ, h)`        (`BHK2006.covD_eq_withinD_add`),

hence `cov_D(φ,h) = P(D) Σ_{k<n} R(𝑇ᵏφ) + cov_D(𝑇ⁿφ, h)`. `𝑇` preserves monotonicity and
nonnegativity (Remark 2.8) and contracts oscillations by `1 − ε`, `ε = ∏_{e non-loop, e meets T} (1
− w e)` (the regeneration bound of the companion file), so `|cov_D(𝑇ⁿφ, h)| ≤ 2 (1−ε)ⁿ osc(φ) ‖h‖_∞
→ 0`. THEOREM (`BHK2006.covD_nonneg_of_withinD_nonneg`): if every non-loop pair meeting `T` has `w e
< 1` and `R(g) ≥ 0` for every monotone nonnegative `g`, then `cov_D(f, h) ≥ 0` for every monotone
`f`.

Not in print in this form; it is BHK's proof scheme of Thm. 2.1 ("`φ̂` is stationary for this chain … so
to prove Theorem 2.1 it's enough to show Claim 2.5", pp. 10–11) with Harris' inequality replaced by an
abstract hypothesis on the one-step conditional covariances, derived here.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 9–13 (Lemmas 2.3–2.4, the chain, Claim 2.5, Remark 2.8)]
-/

noncomputable section

open MeasureTheory unitInterval
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

namespace BHK2006

open scoped Classical
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)

section Sums

variable {V : Type*} [Fintype V]

/-! ### The half-step and one-step operators on functions of `C_S` -/

/-- **`E[φ(C_S) | C_T = B]`** (the `S`-half-step of BHK's chain applied to a function of `C_S`): the
expectation of `φ` of the cluster of `S` in a fresh configuration with the pairs meeting `T ∪ V(B)` deleted.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10), p. 11 (`Pr(C_S^i = ·) = φ(C_S = · | C_T = C_T^i)`)] -/
def condS (w : Sym2 V → ℝ) (S T : Set V) (φ : Set (Sym2 V) → ℝ) (B : Set (Sym2 V)) : ℝ :=
  ∑ η, weight w η * φ (halfS S T B η)

/-- **BHK's one-step operator on functions of `C_S`**: `(𝑇φ)(C) = E[ E[φ(C_S') | C_T'] | C_S = C]`
(resample `C_T` given `C_S = C`, then `C_S` given the new `C_T`).
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11 (definition of the chain)] -/
def gibbsT (w : Sym2 V → ℝ) (S T : Set V) (φ : Set (Sym2 V) → ℝ) (A : Set (Sym2 V)) : ℝ :=
  ∑ η, weight w η * condS w S T φ (halfT S T A η)

/-- **Conditional covariance given `C_T = B`** of two functions of `C_S`:
`E[φh | C_T = B] − E[φ | C_T = B] E[h | C_T = B]`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
def condCov (w : Sym2 V → ℝ) (S T : Set V) (φ h : Set (Sym2 V) → ℝ) (B : Set (Sym2 V)) : ℝ :=
  condS w S T (fun A => φ A * h A) B - condS w S T φ B * condS w S T h B

/-- **The averaged one-step ("within") covariance** `R(φ) = E[ Cov(φ(C_S), h(C_S) | C_T) 1_D ]`
(denominator-free: not divided by `P(D)`). [cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11] -/
def withinD (w : Sym2 V → ℝ) (S T : Set V) (D : Set (Set (Sym2 V))) (φ h : Set (Sym2 V) → ℝ) : ℝ :=
  ∑ ω, weight w ω * (condCov w S T φ h (setCl ω T) * ind D ω)

/-- **Denominator-free conditional covariance on `D`** of two functions of `C_S`:
`cov_D(φ, h) = P(D)·E[φ(C_S) h(C_S) 1_D] − E[φ(C_S) 1_D]·E[h(C_S) 1_D]` (`= P(D)² Cov(φ, h | D)`; the
denominator-free form of conditional covariances used in BHK's (9)).
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 eq. (9) (p. 7)] -/
def covD (w : Sym2 V → ℝ) (S : Set V) (D : Set (Set (Sym2 V))) (φ h : Set (Sym2 V) → ℝ) : ℝ :=
  (∑ ω, weight w ω * ind D ω) * (∑ ω, weight w ω * (φ (setCl ω S) * h (setCl ω S) * ind D ω)) -
    (∑ ω, weight w ω * (φ (setCl ω S) * ind D ω)) * (∑ ω, weight w ω * (h (setCl ω S) * ind D ω))

/-- `𝑇` is BHK's one-step operator `gibbsE` restricted to functions of the first coordinate `C_S`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11] -/
theorem gibbsE_comp_fst (w : Sym2 V → ℝ) (S T : Set V) (φ : Set (Sym2 V) → ℝ) :
    gibbsE w S T (φ ∘ Prod.fst) = gibbsT w S T φ ∘ Prod.fst := by
  funext x
  rfl

/-- Iterates: `gibbsEⁿ (φ ∘ fst) = (𝑇ⁿ φ) ∘ fst`. [cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11] -/
theorem gibbsE_iterate_comp_fst (w : Sym2 V → ℝ) (S T : Set V) (n : ℕ) (φ : Set (Sym2 V) → ℝ) :
    (gibbsE w S T)^[n] (φ ∘ Prod.fst) = (gibbsT w S T)^[n] φ ∘ Prod.fst := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, gibbsE_comp_fst, ih]

/-! ### Monotonicity, positivity and contraction of the operators -/

/-- `E[φ(C_S) | C_T = B]` is DECREASING in `B` for increasing `φ` (the new `C_S` is decreasing in the
conditioning cluster, Remark 2.8). [cite: VandenbergHaggstromKahn2005, §2.1 Remark 2.8 (p. 12)] -/
theorem condS_antitone {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (S T : Set V)
    {φ : Set (Sym2 V) → ℝ} (hφ : Monotone φ) : Antitone (condS w S T φ) := by
  intro B B' hBB'
  exact Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left
    (hφ (halfS_mono S T hBB' le_rfl)) (weight_nonneg hw0 hw1 η)

/-- `E[φ(C_S) | C_T = B] ≥ 0` for `φ ≥ 0`. [folklore] -/
private theorem condS_nonneg {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (S T : Set V)
    {φ : Set (Sym2 V) → ℝ} (hφ0 : ∀ A, 0 ≤ φ A) (B : Set (Sym2 V)) : 0 ≤ condS w S T φ B :=
  Finset.sum_nonneg fun η _ => mul_nonneg (weight_nonneg hw0 hw1 η) (hφ0 _)

/-- **`𝑇` preserves monotonicity** ("`C_S^n` is increasing in … " — the new `C_S` is increasing in the
old one). [cite: VandenbergHaggstromKahn2005, §2.1 Remark 2.8 (p. 12)] -/
theorem gibbsT_mono {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (S T : Set V)
    {φ : Set (Sym2 V) → ℝ} (hφ : Monotone φ) : Monotone (gibbsT w S T φ) := by
  intro A A' hAA'
  exact Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left
    (condS_antitone hw0 hw1 S T hφ (halfT_mono S T hAA' le_rfl)) (weight_nonneg hw0 hw1 η)

/-- `𝑇` preserves nonnegativity. [folklore] -/
private theorem gibbsT_nonneg {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (S T : Set V)
    {φ : Set (Sym2 V) → ℝ} (hφ0 : ∀ A, 0 ≤ φ A) (A : Set (Sym2 V)) : 0 ≤ gibbsT w S T φ A :=
  Finset.sum_nonneg fun η _ => mul_nonneg (weight_nonneg hw0 hw1 η) (condS_nonneg hw0 hw1 S T hφ0 _)

/-- The iterates `𝑇ⁿ φ` of a monotone nonnegative `φ` are monotone and nonnegative.
[cite: VandenbergHaggstromKahn2005, §2.1 Remark 2.8 (p. 12)] -/
theorem gibbsT_iterate_mono_nonneg {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (S T : Set V) {φ : Set (Sym2 V) → ℝ} (hφ : Monotone φ) (hφ0 : ∀ A, 0 ≤ φ A) (n : ℕ) :
    Monotone ((gibbsT w S T)^[n] φ) ∧ ∀ A, 0 ≤ (gibbsT w S T)^[n] φ A := by
  induction n with
  | zero => exact ⟨hφ, hφ0⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨gibbsT_mono hw0 hw1 S T ih.1, gibbsT_nonneg hw0 hw1 S T ih.2⟩

/-- **Regeneration contraction for `𝑇`**: `osc(𝑇ⁿ φ) ≤ (1 − ε)ⁿ osc(φ)`, `ε = regenWeight w T` (from
`gibbsE_iterate_sub_le` of the companion file). [folklore] (Doeblin coupling)
[cite: VandenbergHaggstromKahn2005, §2.1 p. 11 (convergence of the chain)] -/
theorem gibbsT_iterate_sub_le {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (S T : Set V) (n : ℕ) {φ : Set (Sym2 V) → ℝ} {c : ℝ}
    (hφ : ∀ A A', φ A - φ A' ≤ c) (A A' : Set (Sym2 V)) :
    (gibbsT w S T)^[n] φ A - (gibbsT w S T)^[n] φ A' ≤ (1 - regenWeight w T) ^ n * c := by
  have h := gibbsE_iterate_sub_le hw0 hw1 hm S T n (Φ := φ ∘ Prod.fst) (c := c)
    (fun x y => hφ x.1 y.1) (A, ∅) (A', ∅)
  rwa [gibbsE_iterate_comp_fst] at h

/-! ### The one-step covariance decomposition and its telescoped form -/

/-- **One-step covariance decomposition along BHK's chain** (law of total covariance along `σ(C_T)`,
then Lemma 2.4 for the `T`-half-step): for any functions `φ, h` of `C_S`,
`cov_D(φ, h) = P(D) · R(φ) + cov_D(𝑇φ, h)` — an exact identity.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) and pp. 10–11 (the chain; "φ̂ is stationary") — corollary, derived here] -/
theorem covD_eq_withinD_add (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (S T : Set V)
    {D : Set (Set (Sym2 V))} (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t)
    (φ h : Set (Sym2 V) → ℝ) :
    covD w S D φ h = (∑ ω, weight w ω * ind D ω) * withinD w S T D φ h + covD w S D (gibbsT w S T φ) h := by
  -- (e1)–(e3): `E[ψ(C_S) 1_D] = E[(Aψ)(C_T) 1_D]` for `ψ = φh, φ, h`
  have e1 : ∑ ω, weight w ω * (φ (setCl ω S) * h (setCl ω S) * ind D ω) =
      ∑ ω, weight w ω * (condS w S T (fun A => φ A * h A) (setCl ω T) * ind D ω) :=
    set_sum_cond_cluster' w hm S T (fun A _ => φ A * h A) hD
  have e2 : ∑ ω, weight w ω * (φ (setCl ω S) * ind D ω) =
      ∑ ω, weight w ω * (condS w S T φ (setCl ω T) * ind D ω) :=
    set_sum_cond_cluster' w hm S T (fun A _ => φ A) hD
  have e3 : ∑ ω, weight w ω * (h (setCl ω S) * ind D ω) =
      ∑ ω, weight w ω * (condS w S T h (setCl ω T) * ind D ω) :=
    set_sum_cond_cluster' w hm S T (fun A _ => h A) hD
  -- (e4): `E[(𝑇φ)(C_S) h(C_S) 1_D] = E[(Aφ)(C_T) h(C_S) 1_D]` (the `T`-half-step)
  have e4 : ∑ ω, weight w ω * (gibbsT w S T φ (setCl ω S) * h (setCl ω S) * ind D ω) =
      ∑ ω, weight w ω * (condS w S T φ (setCl ω T) * h (setCl ω S) * ind D ω) := by
    rw [set_sum_cond_cluster w hm S T (fun A B => condS w S T φ B * h A) hD]
    refine Finset.sum_congr rfl fun ω _ => ?_
    simp only [gibbsT, halfT, Finset.sum_mul, mul_assoc]
  -- (e5): `E[(Aφ)(C_T) h(C_S) 1_D] = E[(Aφ)(C_T) (Ah)(C_T) 1_D]` (the `S`-half-step)
  have e5 : ∑ ω, weight w ω * (condS w S T φ (setCl ω T) * h (setCl ω S) * ind D ω) =
      ∑ ω, weight w ω * (condS w S T φ (setCl ω T) * condS w S T h (setCl ω T) * ind D ω) := by
    rw [set_sum_cond_cluster' w hm S T (fun A B => condS w S T φ B * h A) hD]
    refine Finset.sum_congr rfl fun ω _ => ?_
    congr 1
    congr 1
    have hc : condS w S T h (setCl ω T) = ∑ η, weight w η * h (halfS S T (setCl ω T) η) := rfl
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    simp only [halfS]
    ring
  -- (e6): `E[(𝑇φ)(C_S) 1_D] = E[(Aφ)(C_T) 1_D]`
  have e6 : ∑ ω, weight w ω * (gibbsT w S T φ (setCl ω S) * ind D ω) =
      ∑ ω, weight w ω * (condS w S T φ (setCl ω T) * ind D ω) :=
    (set_sum_cond_cluster w hm S T (fun _ B => condS w S T φ B) hD).symm
  -- the within part as a difference
  have hW : withinD w S T D φ h =
      (∑ ω, weight w ω * (condS w S T (fun A => φ A * h A) (setCl ω T) * ind D ω)) -
        ∑ ω, weight w ω * (condS w S T φ (setCl ω T) * condS w S T h (setCl ω T) * ind D ω) := by
    rw [withinD, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => by rw [condCov]; ring
  rw [covD, covD, e1, e2, e3, e4, e5, e6, hW]
  ring

/-- **Telescoped form**: `cov_D(φ, h) = P(D) Σ_{k<n} R(𝑇ᵏφ) + cov_D(𝑇ⁿφ, h)` for every `n`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–11 — corollary, derived here] -/
theorem covD_eq_sum_withinD_add (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (S T : Set V)
    {D : Set (Set (Sym2 V))} (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t)
    (φ h : Set (Sym2 V) → ℝ) (n : ℕ) :
    covD w S D φ h = (∑ ω, weight w ω * ind D ω) *
        ∑ k ∈ Finset.range n, withinD w S T D ((gibbsT w S T)^[k] φ) h +
      covD w S D ((gibbsT w S T)^[n] φ) h := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, Function.iterate_succ_apply', ih,
      covD_eq_withinD_add w hm S T hD ((gibbsT w S T)^[n] φ) h]
    ring

/-! ### Two elementary properties of `cov_D` -/

/-- `cov_D` is unchanged when a constant is subtracted from the first function. [folklore] -/
private theorem covD_sub_const (w : Sym2 V → ℝ) (S : Set V) (D : Set (Set (Sym2 V)))
    (φ h : Set (Sym2 V) → ℝ) (c : ℝ) :
    covD w S D (fun A => φ A - c) h = covD w S D φ h := by
  have h1 : ∀ ω : Set (Sym2 V), weight w ω * ((φ (setCl ω S) - c) * h (setCl ω S) * ind D ω) =
      weight w ω * (φ (setCl ω S) * h (setCl ω S) * ind D ω) -
        c * (weight w ω * (h (setCl ω S) * ind D ω)) := fun ω => by ring
  have h2 : ∀ ω : Set (Sym2 V), weight w ω * ((φ (setCl ω S) - c) * ind D ω) =
      weight w ω * (φ (setCl ω S) * ind D ω) - c * (weight w ω * ind D ω) := fun ω => by ring
  simp only [covD, h1, h2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- `|E[g 1_D]| ≤ c · P(D)` when `|g| ≤ c` on the configurations. [folklore] -/
private theorem abs_sum_ind_le {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (D : Set (Set (Sym2 V))) {g : Set (Sym2 V) → ℝ} {c : ℝ} (hg : ∀ ω, |g ω| ≤ c) :
    |∑ ω, weight w ω * (g ω * ind D ω)| ≤ c * ∑ ω, weight w ω * ind D ω := by
  calc |∑ ω, weight w ω * (g ω * ind D ω)| ≤ ∑ ω, |weight w ω * (g ω * ind D ω)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, c * (weight w ω * ind D ω) := Finset.sum_le_sum fun ω _ => by
        rw [abs_mul, abs_mul, abs_of_nonneg (weight_nonneg hw0 hw1 ω), abs_of_nonneg (ind_nonneg D ω)]
        calc weight w ω * (|g ω| * ind D ω) ≤ weight w ω * (c * ind D ω) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hg ω) (ind_nonneg D ω))
                (weight_nonneg hw0 hw1 ω)
          _ = c * (weight w ω * ind D ω) := by ring
    _ = c * ∑ ω, weight w ω * ind D ω := by rw [Finset.mul_sum]

/-- **Small oscillation ⟹ small covariance**: if `φ A − φ A' ≤ δ` for all `A, A'` and `|h| ≤ M`, then
`|cov_D(φ, h)| ≤ 2 δ M`. [folklore] -/
private theorem abs_covD_le {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (S : Set V) (D : Set (Set (Sym2 V))) {φ h : Set (Sym2 V) → ℝ}
    {δ M : ℝ} (hφ : ∀ A A', φ A - φ A' ≤ δ) (hM : ∀ A, |h A| ≤ M) :
    |covD w S D φ h| ≤ 2 * δ * M := by
  have hδ : 0 ≤ δ := by simpa using hφ ∅ ∅
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM ∅)
  set mD : ℝ := ∑ ω, weight w ω * ind D ω with hmD
  have hmD0 : 0 ≤ mD := Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg D ω)
  have hmD1 : mD ≤ 1 := by
    calc mD ≤ ∑ ω, weight w ω := Finset.sum_le_sum fun ω _ => by
            simpa using mul_le_mul_of_nonneg_left (ind_le_one D ω) (weight_nonneg hw0 hw1 ω)
      _ = 1 := hm
  rw [← covD_sub_const w S D φ h (φ ∅)]
  set ψ : Set (Sym2 V) → ℝ := fun A => φ A - φ ∅ with hψ
  have hψb : ∀ A, |ψ A| ≤ δ := fun A => abs_sub_le_iff.2 ⟨hφ A ∅, by linarith [hφ ∅ A]⟩
  have b1 : |∑ ω, weight w ω * (ψ (setCl ω S) * h (setCl ω S) * ind D ω)| ≤ δ * M * mD := by
    have := abs_sum_ind_le hw0 hw1 D (g := fun ω => ψ (setCl ω S) * h (setCl ω S)) (c := δ * M)
      (fun ω => by rw [abs_mul]; exact mul_le_mul (hψb _) (hM _) (abs_nonneg _) hδ)
    simpa only [hmD] using this
  have b2 : |∑ ω, weight w ω * (ψ (setCl ω S) * ind D ω)| ≤ δ * mD :=
    abs_sum_ind_le hw0 hw1 D (g := fun ω => ψ (setCl ω S)) (fun ω => hψb _)
  have b3 : |∑ ω, weight w ω * (h (setCl ω S) * ind D ω)| ≤ M * mD :=
    abs_sum_ind_le hw0 hw1 D (g := fun ω => h (setCl ω S)) (fun ω => hM _)
  have hcov : covD w S D ψ h =
      mD * (∑ ω, weight w ω * (ψ (setCl ω S) * h (setCl ω S) * ind D ω)) -
        (∑ ω, weight w ω * (ψ (setCl ω S) * ind D ω)) *
          (∑ ω, weight w ω * (h (setCl ω S) * ind D ω)) := rfl
  rw [hcov]
  have t1 : |mD * ∑ ω, weight w ω * (ψ (setCl ω S) * h (setCl ω S) * ind D ω)| ≤ δ * M := by
    rw [abs_mul, abs_of_nonneg hmD0]
    calc mD * |∑ ω, weight w ω * (ψ (setCl ω S) * h (setCl ω S) * ind D ω)| ≤ 1 * (δ * M * mD) :=
          mul_le_mul hmD1 b1 (abs_nonneg _) zero_le_one
      _ ≤ δ * M := by rw [one_mul]; exact mul_le_of_le_one_right (mul_nonneg hδ hM0) hmD1
  have t2 : |(∑ ω, weight w ω * (ψ (setCl ω S) * ind D ω)) *
      (∑ ω, weight w ω * (h (setCl ω S) * ind D ω))| ≤ δ * M := by
    rw [abs_mul]
    calc |∑ ω, weight w ω * (ψ (setCl ω S) * ind D ω)| * |∑ ω, weight w ω * (h (setCl ω S) * ind D ω)|
        ≤ (δ * mD) * (M * mD) := mul_le_mul b2 b3 (abs_nonneg _) (by positivity)
      _ ≤ δ * M := by nlinarith [mul_nonneg hδ hM0, mul_le_one₀ hmD1 hmD0 hmD1]
  calc |mD * (∑ ω, weight w ω * (ψ (setCl ω S) * h (setCl ω S) * ind D ω)) -
        (∑ ω, weight w ω * (ψ (setCl ω S) * ind D ω)) *
          (∑ ω, weight w ω * (h (setCl ω S) * ind D ω))|
      ≤ |mD * ∑ ω, weight w ω * (ψ (setCl ω S) * h (setCl ω S) * ind D ω)| +
          |(∑ ω, weight w ω * (ψ (setCl ω S) * ind D ω)) *
            (∑ ω, weight w ω * (h (setCl ω S) * ind D ω))| := abs_sub _ _
    _ ≤ 2 * δ * M := by linarith

/-- `regenWeight w T ≤ 1` (it is the weight of an event). [folklore] -/
private theorem regenWeight_le_one' {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (T : Set V) : regenWeight w T ≤ 1 := by
  calc regenWeight w T ≤ ∑ η, weight w η := Finset.sum_le_sum fun η _ => by
          simpa using mul_le_mul_of_nonneg_left (ind_le_one (regenT T) η) (weight_nonneg hw0 hw1 η)
    _ = 1 := hm

/-! ### The reduction theorem -/

/-- **Reduction of a conditional covariance sign to the averaged one-step covariances.** Bond
percolation with pair probabilities `w ∈ [0,1]` on a finite vertex type such that every non-loop pair
meeting `T` has `w e < 1` (positive regeneration weight `ε`); `D = {S ↮ T}`; `h` ANY function of `C_S`.
If `R(g) = E[Cov(g(C_S), h(C_S) | C_T); D] ≥ 0` for every monotone nonnegative `g`, then
`cov_D(f, h) = P(D)E[f h 1_D] − E[f 1_D]E[h 1_D] ≥ 0` for every monotone `f`.
Proof: `cov_D(f,h) = cov_D(f − f(∅), h) = P(D) Σ_{k<n} R(𝑇ᵏ(f − f ∅)) + cov_D(𝑇ⁿ(f − f ∅), h)`, the sum is
`≥ 0` (the iterates are monotone and nonnegative) and the last term is `O((1−ε)ⁿ)`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13 (the chain, Claim 2.5, Remark 2.8) — corollary, derived here] -/
theorem covD_nonneg_of_withinD_nonneg {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (S T : Set V) {D : Set (Set (Sym2 V))}
    (hD : ∀ ω, ω ∈ D ↔ ∀ s ∈ S, ∀ t ∈ T, ¬ (openGraph ω).Reachable s t)
    (hε : 0 < regenWeight w T) (h : Set (Sym2 V) → ℝ)
    (hR : ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ A, 0 ≤ g A) → 0 ≤ withinD w S T D g h)
    {f : Set (Sym2 V) → ℝ} (hf : Monotone f) : 0 ≤ covD w S D f h := by
  set f₀ : Set (Sym2 V) → ℝ := fun A => f A - f ∅ with hf₀
  have hf₀m : Monotone f₀ := fun A A' hAA' => sub_le_sub_right (hf hAA') _
  have hf₀0 : ∀ A, 0 ≤ f₀ A := fun A => sub_nonneg.2 (hf (Set.empty_subset A))
  set c : ℝ := f Set.univ - f ∅ with hc
  have hosc : ∀ A A', f₀ A - f₀ A' ≤ c := fun A A' => by
    simp only [hf₀, hc]
    linarith [hf (Set.subset_univ A), hf (Set.empty_subset A')]
  set M : ℝ := ∑ A : Set (Sym2 V), |h A| with hMdef
  have hM : ∀ A, |h A| ≤ M := fun A =>
    Finset.single_le_sum (f := fun A => |h A|) (fun _ _ => abs_nonneg _) (Finset.mem_univ A)
  set mD : ℝ := ∑ ω, weight w ω * ind D ω with hmD
  have hmD0 : 0 ≤ mD := Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg D ω)
  set ρ : ℝ := 1 - regenWeight w T with hρ
  have hρ0 : 0 ≤ ρ := sub_nonneg.2 (regenWeight_le_one' hw0 hw1 hm T)
  have hρ1 : ρ < 1 := by simp only [hρ]; linarith
  -- the lower bound for every `n`
  have key : ∀ n : ℕ, -(2 * (ρ ^ n * c) * M) ≤ covD w S D f₀ h := by
    intro n
    rw [covD_eq_sum_withinD_add w hm S T hD f₀ h n]
    have h1 : 0 ≤ mD * ∑ k ∈ Finset.range n, withinD w S T D ((gibbsT w S T)^[k] f₀) h :=
      mul_nonneg hmD0 (Finset.sum_nonneg fun k _ =>
        hR _ (gibbsT_iterate_mono_nonneg hw0 hw1 S T hf₀m hf₀0 k).1
          (gibbsT_iterate_mono_nonneg hw0 hw1 S T hf₀m hf₀0 k).2)
    have h2 : |covD w S D ((gibbsT w S T)^[n] f₀) h| ≤ 2 * (ρ ^ n * c) * M :=
      abs_covD_le hw0 hw1 hm S D (gibbsT_iterate_sub_le hw0 hw1 hm S T n hosc) hM
    linarith [neg_abs_le (covD w S D ((gibbsT w S T)^[n] f₀) h)]
  -- let `n → ∞`
  have hlim : Filter.Tendsto (fun n : ℕ => -(2 * (ρ ^ n * c) * M)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ρ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have : Filter.Tendsto (fun n : ℕ => -(2 * (ρ ^ n * c) * M)) Filter.atTop
        (nhds (-(2 * (0 * c) * M))) :=
      (((h0.mul_const c).const_mul 2).mul_const M).neg
    simpa using this
  have hge : 0 ≤ covD w S D f₀ h := le_of_tendsto' hlim key
  rwa [hf₀, covD_sub_const] at hge

end Sums

end BHK2006

/-! ### Deleting a set of pairs is zeroing their weights; forcing pairs open; conditioning on one pair -/

section Zeroing

variable {ι : Type*}

open scoped Classical
open Percolation.Literature.LatticeModels (prodBernoulli_eq_map prodBernoulli_real_setOf_mem)
open BHK2006 DecisionTree

/-- `ω ↦ ω ∖ A` is measurable. [folklore] -/
private theorem measurable_sdiff_const' (A : Set ι) : Measurable fun ω : Set ι => ω \ A := by
  refine measurable_set_iff.2 fun i => ?_
  exact (measurable_set_mem i).and measurable_const

/-- **Closing the pairs of `A`**: the image of `P_p` under `ω ↦ ω ∖ A` is the product measure with the
weights of `A` set to `0` ("the restriction of our percolation model to the graph obtained from `G` by
deleting all edges in `W̄`"; product measures, one factor at a time replaced by `δ_closed`).
[cite: VandenbergHaggstromKahn2005, §1 p. 8 and §2.1 Lemma 2.3 (p. 10); GrimmettPercolation1999, §1.3 p. 10 (product measure)] -/
theorem BHK2006.prodBernoulli_map_sdiff (p : ι → unitInterval) (A : Set ι) :
    (prodBernoulli p).map (fun ω : Set ι => ω \ A) =
      prodBernoulli (fun i => if i ∈ A then (0 : unitInterval) else p i) := by
  classical
  set μ : (ι → unitInterval) → ι → Measure Prop := fun r i =>
    unitInterval.toNNReal (r i) • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm (r i)) • Measure.dirac False with hμ
  haveI hprob : ∀ r i, IsProbabilityMeasure (μ r i) := fun r i => by
    simp only [hμ]; infer_instance
  have h1 : ∀ r, prodBernoulli r = (Measure.infinitePi (μ r)).map (fun q : ι → Prop => {i | q i}) :=
    fun r => prodBernoulli_eq_map r
  have hf : ∀ i : ι, Measurable (fun x : Prop => x ∧ i ∉ A) := fun i => measurable_from_top
  have hcomp : (fun ω : Set ι => ω \ A) ∘ (fun q : ι → Prop => {i | q i}) =
      (fun q : ι → Prop => {i | q i}) ∘ (fun (q : ι → Prop) (i : ι) => q i ∧ i ∉ A) := by
    funext q
    ext i
    simp
  have hg : Measurable (fun (q : ι → Prop) (i : ι) => q i ∧ i ∉ A) :=
    measurable_pi_lambda _ fun i => (hf i).comp (measurable_pi_apply i)
  rw [h1, h1, Measure.map_map (measurable_sdiff_const' _) measurable_setOf, hcomp,
    ← Measure.map_map measurable_setOf hg, Measure.infinitePi_map_pi _ hf]
  have hfun : (fun i => Measure.map (fun x : Prop => x ∧ i ∉ A) (μ p i)) =
      μ (fun i => if i ∈ A then (0 : unitInterval) else p i) := by
    funext i
    by_cases hi : i ∈ A
    · have hc : (fun x : Prop => x ∧ i ∉ A) = fun _ => False := by
        funext x; exact propext ⟨fun h => h.2 hi, False.elim⟩
      rw [hc, Measure.map_const, measure_univ, one_smul]
      simp [hμ, hi]
    · have hid : (fun x : Prop => x ∧ i ∉ A) = id := by
        funext x; exact propext ⟨fun h => h.1, fun h => ⟨h, hi⟩⟩
      rw [hid, Measure.map_id]
      simp [hμ, hi]
  congr 1
  convert rfl using 2
  exact hfun.symm

/-- **Expectations in a thinned configuration are expectations for the zeroed weights**:
`∫ F(η ∖ A) dP_p(η) = ∫ F dP_{p·1_{Aᶜ}}` — percolation "on `G` with the pairs of `A` deleted" is
percolation with the weights of `A` set to `0`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3 (p. 10); GrimmettPercolation1999, §1.3 p. 10] -/
theorem BHK2006.integral_comp_sdiff_prodBernoulli [Fintype ι] (p : ι → unitInterval) (A : Set ι)
    (F : Set ι → ℝ) :
    ∫ η, F (η \ A) ∂(prodBernoulli p) =
      ∫ η, F η ∂(prodBernoulli (fun i => if i ∈ A then (0 : unitInterval) else p i)) := by
  rw [← BHK2006.prodBernoulli_map_sdiff,
    integral_map (measurable_sdiff_const' A).aemeasurable (Measurable.of_discrete).aestronglyMeasurable]

/-- The same with the zeroed weight function given by its values (no `if` in the statement): if
`p' = 0` on `A` and `p' = p` off `A`, then `∫ F(η ∖ A) dP_p(η) = ∫ F dP_{p'}`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.3 (p. 10); GrimmettPercolation1999, §1.3 p. 10] -/
theorem BHK2006.integral_comp_sdiff_prodBernoulli' [Fintype ι] (p p' : ι → unitInterval) (A : Set ι)
    (hA : ∀ i ∈ A, p' i = 0) (hA' : ∀ i ∉ A, p' i = p i) (F : Set ι → ℝ) :
    ∫ η, F (η \ A) ∂(prodBernoulli p) = ∫ η, F η ∂(prodBernoulli p') := by
  have hp' : p' = fun i => if i ∈ A then (0 : unitInterval) else p i := by
    funext i
    by_cases hi : i ∈ A
    · rw [if_pos hi, hA i hi]
    · rw [if_neg hi, hA' i hi]
  rw [hp']
  exact BHK2006.integral_comp_sdiff_prodBernoulli p A F

end Zeroing

/-! ### Measure-level statements for `prodBernoulli w`, one source vertex `s`, target set `X` -/

section Measure

variable {V : Type*} [Fintype V]

open scoped Classical
open BHK2006 DecisionTree

/-- The product weight `∏ (p i or 1 - p i)` of a configuration is a continuous function of the weights ("a
finite polynomial in `p`, and therefore a continuous function"). [cite: GrimmettPercolation1999, §7.3 p. 162] -/
theorem BHK2006.continuous_weight {ι : Type*} [Fintype ι] (ω : Set ι) :
    Continuous fun p : ι → unitInterval => weight (fun e => (p e : ℝ)) ω := by
  classical
  unfold weight
  refine continuous_finsetProd _ fun e _ => ?_
  by_cases he : e ∈ ω
  · simp only [he, if_true]
    exact continuous_subtype_val.comp (continuous_apply e)
  · simp only [he, if_false]
    exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply e))

omit [Fintype V] in
/-- `C_{{s}} = C_s` (BHK's `C_S` for a one-point `S`). [cite: VandenbergHaggstromKahn2005, §2.1 p. 9 (definition of `C_S`)] -/
theorem BHK2006.setCl_singleton (ω : BondConfig V) (s : V) : setCl ω {s} = openEdgeCluster ω s := by
  rw [setCl, Set.biUnion_singleton]

omit [Fintype V] in
/-- The pairs meeting `X ∪ V(C_X)` (BHK's `W̄` for `W = C_X`, plus the pairs at `X`) are the pairs meeting the
open vertex cluster of `X`. [cite: VandenbergHaggstromKahn2005, §1 p. 8 (definition of `W̄`), §2.1 Lemma 2.3 (p. 10)] -/
theorem BHK2006.barOf_setCl_eq (ω : BondConfig V) (X : Set V) :
    barOf X (setCl ω X) = {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v} := by
  ext e
  simp only [mem_barOf_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (setReach_iff ω X v).2 h⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (setReach_iff ω X v).1 h⟩

omit [Fintype V] in
/-- `D = {s ↮ X}` in the two-set form. [folklore] -/
private theorem mem_D_iff (s : V) (X : Set V) (ω : BondConfig V) :
    ω ∈ {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ↔
      ∀ s' ∈ ({s} : Set V), ∀ t ∈ X, ¬ (openGraph ω).Reachable s' t := by
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq]

/-- Total mass of the product weights is `1`. [folklore] -/
private theorem sum_weight_eq_one (w : Sym2 V → unitInterval) :
    ∑ ω : Set (Sym2 V), weight (fun e => (w e : ℝ)) ω = 1 := by
  have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  exact h1.symm

/-- `μ(D)` as a weighted sum. [folklore] -/
private theorem real_D_eq_sum (w : Sym2 V → unitInterval) (s : V) (X : Set V) :
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} =
      ∑ ω, weight (fun e => (w e : ℝ)) ω *
        ind {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ω := by
  rw [← integral_indicator_one (MeasurableSet.of_discrete), integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω ∈ {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x}
  · rw [Set.indicator_of_mem hω, ind_of_mem hω, Pi.one_apply]
  · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω, mul_zero]

/-- `∫_D ψ(C_s) dμ` as a weighted sum. [folklore] -/
private theorem setIntegral_D_eq_sum (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (ψ : Set (Sym2 V) → ℝ) :
    ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x}, ψ (openEdgeCluster ω s)
        ∂(prodBernoulli w) =
      ∑ ω, weight (fun e => (w e : ℝ)) ω * (ψ (setCl ω {s}) *
        ind {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ω) := by
  rw [← integral_indicator (MeasurableSet.of_discrete), integral_prodBernoulli_eq_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [setCl_singleton]
  by_cases hω : ω ∈ {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x}
  · rw [Set.indicator_of_mem hω, ind_of_mem hω, mul_one]
  · simp only [Set.indicator_of_notMem hω, ind_of_not_mem hω, mul_zero]

/-- **The fresh expectation on `G − (pairs meeting the cluster of X)` is `E[· | C_X]`**:
`∫ φ(C_s(η ∖ A_X(ω))) dμ(η) = condS w {s} X φ (C_X ω)`, `A_X(ω)` the pairs meeting the open vertex cluster
of `X`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
theorem BHK2006.integral_sdiff_eq_condS (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (φ : Set (Sym2 V) → ℝ) (ω : BondConfig V) :
    ∫ η, φ (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
        ∂(prodBernoulli w) =
      condS (fun e => (w e : ℝ)) {s} X φ (setCl ω X) := by
  rw [integral_prodBernoulli_eq_sum, condS]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [halfS, barOf_setCl_eq, setCl_singleton]

/-- **Reduction theorem, measure form.** Bond percolation `μ = prodBernoulli w` on a finite vertex type,
a vertex `s`, a vertex set `X` such that every non-loop pair meeting `X` has `w e < 1`, `D = {s ↮ X}`,
`C_s` the open edge cluster of `s`, `A_X(ω)` the pairs meeting the open vertex cluster of `X`, and ANY
`h : Set (Sym2 V) → ℝ`.  If for every monotone nonnegative `g`
`0 ≤ ∫_D ( E_η[(g h)(C_s(η ∖ A_X ω))] − E_η[g(C_s(η ∖ A_X ω))] · E_η[h(C_s(η ∖ A_X ω))] ) dμ(ω)`
("the conditional covariance of `g(C_s)` and `h(C_s)` given the cluster of `X`, averaged over `D`, is
`≥ 0`" — given `C_X`, the configuration off `A_X` is fresh, Lemma 2.4), then for every monotone `f`
`0 ≤ μ(D) ∫_D f(C_s) h(C_s) dμ − (∫_D f(C_s) dμ)(∫_D h(C_s) dμ)`.
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13 — corollary, derived here] -/
theorem BHK2006_clusterConditionalCov_nonneg_of_within (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (hX : ∀ e : Sym2 V, ¬ e.IsDiag → (∃ v ∈ e, v ∈ X) → (w e : ℝ) < 1)
    (h : Set (Sym2 V) → ℝ)
    (hR : ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        ((∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) *
              h (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli w)) -
          (∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli w)) *
          (∫ η, h (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli w))) ∂(prodBernoulli w))
    (f : Set (Sym2 V) → ℝ) (hf : Monotone f) :
    0 ≤ (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          f (openEdgeCluster ω s) * h (openEdgeCluster ω s) ∂(prodBernoulli w)) -
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          f (openEdgeCluster ω s) ∂(prodBernoulli w)) *
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          h (openEdgeCluster ω s) ∂(prodBernoulli w)) := by
  classical
  set D : Set (BondConfig V) := {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} with hDdef
  set w' : Sym2 V → ℝ := fun e => (w e : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  have hm : ∑ ω, weight w' ω = 1 := sum_weight_eq_one w
  have hD : ∀ ω, ω ∈ D ↔ ∀ s' ∈ ({s} : Set V), ∀ t ∈ X, ¬ (openGraph ω).Reachable s' t :=
    mem_D_iff s X
  -- positivity of the regeneration weight
  have hε : 0 < regenWeight w' X := by
    rw [hw', regenWeight_eq_prod w X]
    refine Finset.prod_pos fun e he => ?_
    obtain ⟨hd, hv⟩ := (Finset.mem_filter.1 he).2
    exact sub_pos.2 (hX e hd hv)
  -- the conclusion in sum form
  have hcov : (prodBernoulli w).real D * (∫ ω in D, f (openEdgeCluster ω s) * h (openEdgeCluster ω s)
      ∂(prodBernoulli w)) - (∫ ω in D, f (openEdgeCluster ω s) ∂(prodBernoulli w)) *
        (∫ ω in D, h (openEdgeCluster ω s) ∂(prodBernoulli w)) = covD w' {s} D f h := by
    rw [covD, real_D_eq_sum w s X, setIntegral_D_eq_sum w s X (fun C => f C * h C),
      setIntegral_D_eq_sum w s X f, setIntegral_D_eq_sum w s X h]
  rw [hcov]
  refine covD_nonneg_of_withinD_nonneg hw0 hw1 hm {s} X hD hε h (fun g hg hg0 => ?_) hf
  -- the hypothesis in sum form
  have hwithin : ∫ ω in D,
      ((∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) *
            h (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli w)) -
        (∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli w)) *
        (∫ η, h (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli w))) ∂(prodBernoulli w) = withinD w' {s} X D g h := by
    rw [withinD, ← integral_indicator (MeasurableSet.of_discrete), integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, mul_one, condCov,
        integral_sdiff_eq_condS w s X (fun A => g A * h A) ω, integral_sdiff_eq_condS w s X g ω,
        integral_sdiff_eq_condS w s X h ω]
    · simp only [Set.indicator_of_notMem hω, ind_of_not_mem hω, mul_zero]
  rw [← hwithin]
  exact hR g hg hg0

/-- **Reduction theorem, all weights** (closure over degenerate weights).  Let the test function
`h_p : Set (Sym2 V) → ℝ` depend continuously on the weights `p ∈ [0,1]^{Sym2 V}`.  If the averaged
conditional covariance hypothesis of `BHK2006_clusterConditionalCov_nonneg_of_within` holds (with `h_p`)
for every NON-DEGENERATE `p` (all `p e ∈ (0,1)`), then the conclusion holds (with `h_w`) for EVERY
`w : Sym2 V → [0,1]`: both sides are polynomials in the weights and the non-degenerate weights are dense
(`Percolation.Literature.LatticeModels.weights_le_of_forall_pos_lt_one`).
[cite: VandenbergHaggstromKahn2005, §2.1 pp. 10–13 — corollary, derived here; GrimmettPercolation1999, §7.3 p. 162 (continuity in the weights)] -/
theorem BHK2006_clusterConditionalCov_nonneg_of_within_of_forall_nondegenerate (w : Sym2 V → unitInterval)
    (s : V) (X : Set V) (h : (Sym2 V → unitInterval) → Set (Sym2 V) → ℝ)
    (hcont : ∀ C, Continuous fun p => h p C)
    (hR : ∀ p : Sym2 V → unitInterval, (∀ e, 0 < p e ∧ p e < 1) →
      ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        ((∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) *
              h p (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli p)) -
          (∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli p)) *
          (∫ η, h p (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
            ∂(prodBernoulli p))) ∂(prodBernoulli p))
    (f : Set (Sym2 V) → ℝ) (hf : Monotone f) :
    0 ≤ (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          f (openEdgeCluster ω s) * h w (openEdgeCluster ω s) ∂(prodBernoulli w)) -
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          f (openEdgeCluster ω s) ∂(prodBernoulli w)) *
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          h w (openEdgeCluster ω s) ∂(prodBernoulli w)) := by
  classical
  set D : Set (BondConfig V) := {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} with hDdef
  -- the conclusion as a function of the weights, in sum form
  set G : (Sym2 V → unitInterval) → ℝ := fun p => covD (fun e => (p e : ℝ)) {s} D f (h p) with hG
  have hGeq : ∀ p : Sym2 V → unitInterval, (prodBernoulli p).real D *
      (∫ ω in D, f (openEdgeCluster ω s) * h p (openEdgeCluster ω s) ∂(prodBernoulli p)) -
      (∫ ω in D, f (openEdgeCluster ω s) ∂(prodBernoulli p)) *
        (∫ ω in D, h p (openEdgeCluster ω s) ∂(prodBernoulli p)) = G p := fun p => by
    show _ = covD (fun e => (p e : ℝ)) {s} D f (h p)
    rw [covD, real_D_eq_sum p s X, setIntegral_D_eq_sum p s X (fun C => f C * h p C),
      setIntegral_D_eq_sum p s X f, setIntegral_D_eq_sum p s X (h p)]
  have hGc : Continuous G := by
    simp only [hG, covD]
    refine Continuous.sub (Continuous.mul ?_ ?_) (Continuous.mul ?_ ?_)
    · exact continuous_finsetSum _ fun ω _ => (continuous_weight ω).mul continuous_const
    · exact continuous_finsetSum _ fun ω _ => (continuous_weight ω).mul
        ((continuous_const.mul (hcont _)).mul continuous_const)
    · exact continuous_finsetSum _ fun ω _ => (continuous_weight ω).mul continuous_const
    · exact continuous_finsetSum _ fun ω _ => (continuous_weight ω).mul
        ((hcont _).mul continuous_const)
  rw [hGeq w]
  refine Percolation.Literature.LatticeModels.weights_le_of_forall_pos_lt_one (f := fun _ => (0 : ℝ))
    continuous_const hGc (fun p hp => ?_) w
  rw [← hGeq p]
  have hX : ∀ e : Sym2 V, ¬ e.IsDiag → (∃ v ∈ e, v ∈ X) → (p e : ℝ) < 1 := fun e _ _ => by
    have h1 : p e < 1 := (hp e).2
    exact_mod_cast h1
  exact BHK2006_clusterConditionalCov_nonneg_of_within p s X hX (h p) (hR p hp) f hf

end Measure

/-! ### The two-marker form: `h = a·1{s ↔ z} − b·1{s ↔ y}` (the shape of the marker-dominance lemma) -/

section TwoMarkers

variable {V : Type*} [Fintype V]

open scoped Classical
open BHK2006 DecisionTree

/-- `1{v = s ∨ v ∈ V(C_s)}` read on the edge cluster is the indicator of `{s ↔ v}`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3 ("A simple example of such an event is {s ↔ a}")] -/
theorem BHK2006.ite_mem_openEdgeCluster_eq_indicator (ω : BondConfig V) (s v : V) :
    (if (v = s ∨ ∃ e ∈ openEdgeCluster ω s, v ∈ e) then (1 : ℝ) else 0) =
      (openConn s v : Set (BondConfig V)).indicator 1 ω := by
  by_cases h : (openGraph ω).Reachable s v
  · rw [if_pos ((reachable_iff_exists_mem_openEdgeCluster ω s v).1 h),
      Set.indicator_of_mem (show ω ∈ openConn s v from h), Pi.one_apply]
  · rw [if_neg (fun hh => h ((reachable_iff_exists_mem_openEdgeCluster ω s v).2 hh)),
      Set.indicator_of_notMem (show ω ∉ openConn s v from h)]

/-- `∫_D F · 1_A = ∫_{D ∩ A} F`. [folklore] -/
private theorem setIntegral_mul_indicator_one (μ : Measure (BondConfig V)) (D A : Set (BondConfig V))
    (F : BondConfig V → ℝ) :
    ∫ ω in D, F ω * A.indicator 1 ω ∂μ = ∫ ω in D ∩ A, F ω ∂μ := by
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have e : (fun ω => F ω * A.indicator (1 : BondConfig V → ℝ) ω) = A.indicator F := by
    funext ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]
  rw [e, setIntegral_indicator hA]

/-- `∫ F · 1_A = ∫_A F`. [folklore] -/
private theorem integral_mul_indicator_one (μ : Measure (BondConfig V)) (A : Set (BondConfig V))
    (F : BondConfig V → ℝ) :
    ∫ ω, F ω * A.indicator 1 ω ∂μ = ∫ ω in A, F ω ∂μ := by
  have h := setIntegral_mul_indicator_one μ Set.univ A F
  rwa [Measure.restrict_univ, Set.univ_inter] at h

end TwoMarkers

/-! ### Gluing a weight-one pair into the avoided set (the endpoint of the one-pair induction) -/

/-! ### Class-restricted reduction: the hypothesis only for functionals that factor through the deleted set

The reduction theorems above ask the averaged one-step covariance hypothesis for EVERY monotone
nonnegative `g`. Their proofs use it only along the orbit `𝑇ᵏ(f − f ∅)` of BHK's one-step operator,
and `𝑇φ` depends on its argument `A` only through the deleted set `barOf S A` (the pairs meeting `S
∪ V(A)`). Hence the hypothesis may be restricted to any class of functionals stable under `𝑇`
containing `f − f ∅` — in particular to the functionals of `C_s` that FACTOR THROUGH `barOf {s} ·`,
i.e. through the vertex span `{s} ∪ V(C_s)` (functions of the open VERTEX cluster, Kozma–Nitzan's
cluster functionals).
-/

/-! ### The multi-marker form: `h = Σ_{u ∈ T} Λ(u)·1{s ↔ u}` (the shape of the conditioned slack hierarchy)

The reduction theorem applies verbatim: it suffices to check the world-wise statement for monotone
nonnegative `g`.
-/

section MultiMarkers

variable {V : Type*} [Fintype V]

open scoped Classical
open BHK2006 DecisionTree

/-- The multi-marker bookkeeping, fresh-configuration side: with `H = Σ_{u∈T} c(u)·χ_u` read on the edge cluster,
`E_η[(gH)(C_s(η∖A_X ω))] − E_η[g]E_η[H] = Σ_{u∈T} c(u)·[∫_{s↔u} g dμ_{w^ω} − (∫ g dμ_{w^ω}) μ_{w^ω}(s↔u)]`,
`w^ω` the weights zeroed on the pairs meeting the cluster of `X`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10)] -/
private theorem multiMarker_fresh_eq (w : Sym2 V → unitInterval) (s : V) (X : Set V) (T : Finset V)
    (c : V → ℝ) (g : Set (Sym2 V) → ℝ) (ω : BondConfig V) :
    ((∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s) *
          (fun C : Set (Sym2 V) => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0))
            (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli w)) -
      (∫ η, g (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli w)) *
      (∫ η, (fun C : Set (Sym2 V) => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0))
            (openEdgeCluster (η \ {e | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}) s)
          ∂(prodBernoulli w))) =
    ∑ u ∈ T, c u * ((∫ η in (openConn s u : Set (BondConfig V)), g (openEdgeCluster η s)
            ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
              then (0 : unitInterval) else w e)) -
          (∫ η, g (openEdgeCluster η s)
            ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
              then (0 : unitInterval) else w e)) *
          (prodBernoulli fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
              then (0 : unitInterval) else w e).real (openConn s u : Set (BondConfig V))) := by
  set wX : Sym2 V → unitInterval := fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
    then (0 : unitInterval) else w e with hwX
  set H : Set (Sym2 V) → ℝ := fun C => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0)
    with hH
  have hHω : ∀ η : BondConfig V, H (openEdgeCluster η s) =
      ∑ u ∈ T, c u * (openConn s u : Set (BondConfig V)).indicator 1 η := fun η => by
    simp only [hH, ite_mem_openEdgeCluster_eq_indicator]
  have h0 : ∀ e ∈ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}, wX e = 0 :=
    fun e he => by simp only [hwX]; exact if_pos he
  have h1 : ∀ e ∉ {e : Sym2 V | ∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v}, wX e = w e :=
    fun e he => by simp only [hwX]; exact if_neg he
  have splitU : ∀ G : BondConfig V → ℝ, ∫ η, G η * H (openEdgeCluster η s) ∂(prodBernoulli wX) =
      ∑ u ∈ T, c u * (∫ η in openConn s u, G η ∂(prodBernoulli wX)) := by
    intro G
    have e1 : (fun η => G η * H (openEdgeCluster η s)) = fun η =>
        ∑ u ∈ T, c u * (G η * (openConn s u : Set (BondConfig V)).indicator 1 η) := by
      funext η
      rw [hHω, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e1, integral_finsetSum _ fun u _ => Integrable.of_finite]
    exact Finset.sum_congr rfl fun u _ => by rw [integral_const_mul, integral_mul_indicator_one]
  have massU : ∫ η, H (openEdgeCluster η s) ∂(prodBernoulli wX) =
      ∑ u ∈ T, c u * (prodBernoulli wX).real (openConn s u : Set (BondConfig V)) := by
    have h2 := splitU (fun _ => (1 : ℝ))
    simp only [one_mul] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun u _ => by rw [setIntegral_const, smul_eq_mul, mul_one]
  rw [integral_comp_sdiff_prodBernoulli' w wX _ h0 h1
      (fun η => g (openEdgeCluster η s) * H (openEdgeCluster η s)),
    integral_comp_sdiff_prodBernoulli' w wX _ h0 h1 (fun η => g (openEdgeCluster η s)),
    integral_comp_sdiff_prodBernoulli' w wX _ h0 h1 (fun η => H (openEdgeCluster η s)),
    splitU, massU, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- The multi-marker bookkeeping, conclusion side: with `H = Σ_{u∈T} c(u)·χ_u`,
`μ(D)∫_D fH − (∫_D f)(∫_D H) = Σ_{u∈T} c(u)·[μ(D)∫_{D∩{s↔u}} f − (∫_D f) μ(D∩{s↔u})]`. [folklore] -/
private theorem multiMarker_conclusion_eq (w : Sym2 V → unitInterval) (s : V) (X : Set V) (T : Finset V)
    (c : V → ℝ) (f : Set (Sym2 V) → ℝ) :
    (prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          f (openEdgeCluster ω s) *
            (fun C : Set (Sym2 V) => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0))
              (openEdgeCluster ω s) ∂(prodBernoulli w)) -
      (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          f (openEdgeCluster ω s) ∂(prodBernoulli w)) *
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
          (fun C : Set (Sym2 V) => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0))
            (openEdgeCluster ω s) ∂(prodBernoulli w)) =
    ∑ u ∈ T, c u * ((prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
          (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s u,
            f (openEdgeCluster ω s) ∂(prodBernoulli w)) -
        (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
            f (openEdgeCluster ω s) ∂(prodBernoulli w)) *
          (prodBernoulli w).real
            ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s u)) := by
  set μ := prodBernoulli w with hμ
  set D : Set (BondConfig V) := {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} with hDdef
  set H : Set (Sym2 V) → ℝ := fun C => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0)
    with hH
  have hHω : ∀ η : BondConfig V, H (openEdgeCluster η s) =
      ∑ u ∈ T, c u * (openConn s u : Set (BondConfig V)).indicator 1 η := fun η => by
    simp only [hH, ite_mem_openEdgeCluster_eq_indicator]
  have split : ∀ G : BondConfig V → ℝ, ∫ ω in D, G ω * H (openEdgeCluster ω s) ∂μ =
      ∑ u ∈ T, c u * (∫ ω in D ∩ openConn s u, G ω ∂μ) := by
    intro G
    have e1 : (fun ω => G ω * H (openEdgeCluster ω s)) = fun ω =>
        ∑ u ∈ T, c u * (G ω * (openConn s u : Set (BondConfig V)).indicator 1 ω) := by
      funext ω
      rw [hHω, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [e1, integral_finsetSum _ fun u _ => Integrable.of_finite]
    exact Finset.sum_congr rfl fun u _ => by rw [integral_const_mul, setIntegral_mul_indicator_one]
  have massD : ∫ ω in D, H (openEdgeCluster ω s) ∂μ = ∑ u ∈ T, c u * μ.real (D ∩ openConn s u) := by
    have h2 := split (fun _ => (1 : ℝ))
    simp only [one_mul] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun u _ => by rw [setIntegral_const, smul_eq_mul, mul_one]
  rw [split, massD, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

/-- (`BHK2006_clusterConditionalCov_nonneg_of_within` for `h = Σ_u c(u)·1{s↔u}`.) [cite:
 VandenbergHaggstromKahn2005, §2.1 pp. 10–13 (the chain) and Lemma 2.4 (p. 10) — corollary, derived
 here]
-/
theorem BHK2006_multiMarkerCov_nonneg_of_within (w : Sym2 V → unitInterval) (s : V) (X : Set V)
    (hX : ∀ e : Sym2 V, ¬ e.IsDiag → (∃ v ∈ e, v ∈ X) → (w e : ℝ) < 1) (T : Finset V) (c : V → ℝ)
    (hR : ∀ g : Set (Sym2 V) → ℝ, Monotone g → (∀ C, 0 ≤ g C) →
      0 ≤ ∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
        (∑ u ∈ T, c u * ((∫ η in (openConn s u : Set (BondConfig V)), g (openEdgeCluster η s)
                ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
                  then (0 : unitInterval) else w e)) -
              (∫ η, g (openEdgeCluster η s)
                ∂(prodBernoulli fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
                  then (0 : unitInterval) else w e)) *
              (prodBernoulli fun e => if (∃ v ∈ e, ∃ x ∈ X, (openGraph ω).Reachable x v)
                  then (0 : unitInterval) else w e).real (openConn s u : Set (BondConfig V))))
        ∂(prodBernoulli w))
    (f : Set (Sym2 V) → ℝ) (hf : Monotone f) :
    0 ≤ ∑ u ∈ T, c u *
        ((prodBernoulli w).real {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} *
            (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s u,
              f (openEdgeCluster ω s) ∂(prodBernoulli w)) -
          (∫ ω in {ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x},
              f (openEdgeCluster ω s) ∂(prodBernoulli w)) *
            (prodBernoulli w).real
              ({ω : BondConfig V | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} ∩ openConn s u)) := by
  have main := BHK2006_clusterConditionalCov_nonneg_of_within w s X hX
    (fun C : Set (Sym2 V) => ∑ u ∈ T, c u * (if (u = s ∨ ∃ e ∈ C, u ∈ e) then (1 : ℝ) else 0))
    (fun g hg hg0 => by
      rw [funext (multiMarker_fresh_eq w s X T c g)]
      exact hR g hg hg0) f hf
  rw [multiMarker_conclusion_eq w s X T c f] at main
  exact main

end MultiMarkers

end Percolation.Literature

end
