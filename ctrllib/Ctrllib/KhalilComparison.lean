/-
Khalil's classical comparison / class-𝒦 / Barbalat layer, stated in Khalil's own
forms (proof rung R3, Lane B — pure wiring).

Khalil, *Nonlinear Systems*, 3rd ed. (2002). Each theorem re-fronts an
already-sealed ctrllib result into the Khalil statement it instantiates; no new
mathematics is introduced here.

  - `comparison_lemma_dini`      — Khalil Lemma 3.4 (Comparison Lemma), linear
                                   majorant instance, upper-right (Dini D⁺) form.
                                   Wires the Mathlib primitive
                                   `le_gronwallBound_of_liminf_deriv_right_le`, the
                                   same engine as `comparison_shift`
                                   (TimeVaryingComparison.lean), but takes the
                                   Dini right-slope inequality directly as
                                   hypothesis rather than deriving it from a
                                   `HasDerivWithinAt` witness — strictly closer to
                                   Khalil's `D⁺v(t) ≤ f(t, v(t))`.
  - `classK_sandwich_stability`  — Khalil Theorem 4.8 uniform-stability estimate
                                   (render 4848–4849), autonomous class-𝒦 sandwich
                                   core. Chains the sealed class-𝒦 toolkit
                                   (ComparisonFunctions.lean).
  - `barbalat_integral`          — Khalil Lemma 8.2 (integral Barbalat). Bridges
                                   the sealed derivative-form `barbalat`
                                   (Barbalat.lean) via Mathlib's FTC-1. Consumes
                                   Mathlib measure theory; does not develop it.

Human derivations (wiki dir the corresponding derivation record (not bundled)):
the corresponding local note, the corresponding local note, the corresponding local note.
-/
import Ctrllib.TimeVaryingComparison
import Ctrllib.ComparisonFunctions
import Ctrllib.Barbalat
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Set Filter Topology MeasureTheory

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E]

/-! ### T4 · Khalil Lemma 3.4 — Comparison Lemma, linear-majorant Dini form -/

/-- **Comparison Lemma** (Khalil 2002, Lemma 3.4), linear-majorant instance in
upper-right-derivative (Dini `D⁺`) form. If `v` is continuous on `[t₀, T]` and its
upper right Dini derivative dominates the linear majorant `f(t, u) = -a·u + c` in
the frequently-below-any-strict-upper-bound sense
`∀ r, -a·v t + c < r → ∃ᶠ z in 𝓝[>] t, slope v t z < r`, then `v` is bounded by the
scalar Grönwall solution of `u̇ = -a·u + c`, `u(t₀) = v t₀`.

This is Khalil's `D⁺v(t) ≤ f(t, v(t))` with the linear `f`, stated directly on the
Dini derivative. It wires the same Mathlib primitive
`le_gronwallBound_of_liminf_deriv_right_le` as `comparison_shift`, but takes the
Dini inequality as the hypothesis rather than obtaining it from a `HasDerivWithinAt`
witness — the form nearer to Khalil's statement. -/
theorem comparison_lemma_dini {v : ℝ → ℝ} {a c t₀ T : ℝ}
    (hvc : ContinuousOn v (Icc t₀ T))
    (hDini : ∀ t ∈ Ico t₀ T, ∀ r, -a * v t + c < r →
      ∃ᶠ z in 𝓝[>] t, slope v t z < r) :
    ∀ t ∈ Icc t₀ T, v t ≤ gronwallBound (v t₀) (-a) c (t - t₀) := by
  intro t ht
  exact le_gronwallBound_of_liminf_deriv_right_le hvc hDini le_rfl
    (fun _ _ => le_rfl) t ht

/-! ### T5 · Khalil Theorem 4.8 — class-𝒦 sandwich uniform-stability estimate -/

/-- **Class-𝒦 sandwich estimate** (Khalil 2002, Theorem 4.8 proof, render
4848–4849), autonomous core. Given a class-𝒦∞ lower bound `α₁` and an upper bound
`α₂` sandwiching `V` (`α₁ ‖z‖ ≤ V z ≤ α₂ ‖z‖`; Khalil takes `α₂ ∈ 𝒦`, but the
estimate itself holds for any `α₂ : ℝ → ℝ`, so no class-𝒦 hypothesis on `α₂` is
taken), and `V` non-increasing along
the trajectory `x` for `t ≥ t₀` (the pulled-back `V̇ ≤ 0`, same status `lasalle`
gives its `hdec`), the state obeys `‖x t‖ ≤ α₁⁻¹(α₂ ‖x t₀‖)`.

Khalil's chain verbatim: `α₁‖x t‖ ≤ V(x t) ≤ V(x t₀) ≤ α₂‖x t₀‖`, then apply the
class-𝒦∞ inverse `classKInv α₁` (monotone, and a genuine left inverse on the ray —
both sealed in ComparisonFunctions.lean) to cancel the left side.

`α₁⁻¹` here is `classKInv`, the class-𝒦 functional inverse (sealed), **not** the
absent Gaussian-quantile `Φ⁻¹`. -/
theorem classK_sandwich_stability {α₁ α₂ : ℝ → ℝ}
    (hα₁ : IsClassKInfinity α₁)
    {V : E → ℝ} {x : ℝ → E} {t₀ : ℝ}
    (hlo : ∀ z, α₁ ‖z‖ ≤ V z) (hhi : ∀ z, V z ≤ α₂ ‖z‖)
    (hmono : ∀ t, t₀ ≤ t → V (x t) ≤ V (x t₀)) :
    ∀ t, t₀ ≤ t → ‖x t‖ ≤ classKInv α₁ (α₂ ‖x t₀‖) := by
  intro t ht
  -- Khalil's sandwich chain: α₁‖x t‖ ≤ V(x t) ≤ V(x t₀) ≤ α₂‖x t₀‖
  have hchain : α₁ ‖x t‖ ≤ α₂ ‖x t₀‖ :=
    (hlo (x t)).trans ((hmono t ht).trans (hhi (x t₀)))
  -- classKInv α₁ is monotone on the ray, and α₁‖x t‖ ≥ 0
  have hKinv : IsClassK (classKInv α₁) := hα₁.classKInv_isClassKInfinity.toIsClassK
  have h0 : (0 : ℝ) ≤ α₁ ‖x t‖ := hα₁.toIsClassK.nonneg (norm_nonneg _)
  have hle : classKInv α₁ (α₁ ‖x t‖) ≤ classKInv α₁ (α₂ ‖x t₀‖) :=
    hKinv.le_of_le h0 hchain
  -- cancel the left side: classKInv α₁ (α₁ ‖x t‖) = ‖x t‖
  have hcancel : classKInv α₁ (α₁ ‖x t‖) = ‖x t‖ :=
    hα₁.classKInv_leftInvOn (mem_Ici.mpr (norm_nonneg _))
  rwa [hcancel] at hle

/-! ### T6 · Khalil Lemma 8.2 — integral form of Barbalat's lemma -/

/-- **Integral Barbalat** (Khalil 2002, Lemma 8.2). If `φ : ℝ → ℝ` is uniformly
continuous and `∫₀ᵗ φ` has a finite limit as `t → ∞`, then `φ t → 0`.

Bridge to the sealed derivative-form `barbalat` (Barbalat.lean, Slotine & Li Lemma
4.2): set `F t = ∫₀ᵗ φ`; uniform continuity gives `φ` continuous, so FTC-1
(`intervalIntegral.integral_hasDerivAt_right`) yields `HasDerivAt F (φ t) t` for
every `t`; `hconv` is `F`'s finite limit and `huc` its derivative's uniform
continuity, whence `barbalat` closes it. This consumes Mathlib's measure-theoretic
FTC (axiom-clean); it does not develop measure theory. -/
theorem barbalat_integral {φ : ℝ → ℝ} (huc : UniformContinuous φ)
    (hconv : ∃ L, Tendsto (fun t => ∫ τ in (0 : ℝ)..t, φ τ) atTop (𝓝 L)) :
    Tendsto φ atTop (𝓝 0) := by
  have hcont : Continuous φ := huc.continuous
  have hderiv : ∀ x, HasDerivAt (fun t => ∫ τ in (0 : ℝ)..t, φ τ) (φ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 x)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcont.continuousAt
  exact barbalat hderiv hconv huc

end Ctrllib

#print axioms Ctrllib.comparison_lemma_dini
#print axioms Ctrllib.classK_sandwich_stability
#print axioms Ctrllib.barbalat_integral
