/-
Gaussian tail-integral lemma — the reachable half of risk obligation A3.

For the standard normal density φ(w) = exp(-w²/2)/√(2π):

      ∫_{q}^{∞} w · φ(w) dw  =  φ(q).

This is the numerator of the Gaussian closed-form CVaR
      CVaR_α = μ + σ · φ(Φ⁻¹(α)) / (1 − α).
Only the tail integral is sealed here. The α-parametrization needs Φ⁻¹ (the probit /
inverse Gaussian CDF), which is ABSENT from Mathlib (no quantile, no probit, no erf; the
generic `cdf` on `gaussianReal` exists but has no inverse) — a DOCUMENTED WALL, never
attempted. See the corresponding local note rows A3,
§7 item 4, and the walls table (§8).

Route: the antiderivative route. Since d/dw[−φ(w)] = w·φ(w) and φ(w) → 0 at +∞, the improper
integral telescopes to −φ(∞) + φ(q) = φ(q). Engine: `integral_Ioi_of_hasDerivAt_of_tendsto'`
(FTC-2 on (a,∞)). The density is stated on Mathlib's `gaussianPDFReal 0 1`; the derivative
algebra runs on the explicit form `stdNormalPdf` and is bridged by the PROVED lemma
`stdNormalPdf_eq` (no assumed bridge).

SymPy pin: the corresponding local note (symbolic identity = 0,
antiderivative identity = 0, φ(∞) = 0, three numeric spot values < 1e-12).
Human derivation: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet).
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped Real

namespace Ctrllib

/-- Explicit standard-normal density `φ(w) = exp(-w²/2) / √(2π)`. Written with the
fully-parenthesized exponent `-(w ^ 2) / 2` so it matches the derivative chain syntactically. -/
noncomputable def stdNormalPdf (w : ℝ) : ℝ := Real.exp (-(w ^ 2) / 2) / Real.sqrt (2 * π)

/-- **Bridge (proved).** The explicit `stdNormalPdf` is Mathlib's `gaussianPDFReal 0 1`. -/
lemma stdNormalPdf_eq (w : ℝ) : stdNormalPdf w = gaussianPDFReal 0 1 w := by
  simp only [stdNormalPdf, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  ring

/-- The derivative of `-φ` is `w·φ(w)` (equivalently φ'(w) = -w·φ(w)). -/
lemma hasDerivAt_neg_stdNormalPdf (w : ℝ) :
    HasDerivAt (fun x => -stdNormalPdf x) (w * stdNormalPdf w) w := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have hinner : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-w) w := by
    have h2 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-(2 * w) / 2) w := h1.neg.div_const 2
    rwa [show -(2 * w) / 2 = -w from by ring] at h2
  have hpdf := (hinner.exp).div_const (Real.sqrt (2 * π))
  have hfinal : HasDerivAt (fun x => -stdNormalPdf x)
      (-(Real.exp (-(w ^ 2) / 2) * -w / Real.sqrt (2 * π))) w := hpdf.neg
  rwa [show -(Real.exp (-(w ^ 2) / 2) * -w / Real.sqrt (2 * π)) = w * stdNormalPdf w from by
    simp only [stdNormalPdf]; ring] at hfinal

/-- `w · φ(w)` is integrable on `(q, ∞)`: it is a constant multiple of the Mathlib
integrand `x · exp(-b x²)` (`integrable_mul_exp_neg_mul_sq`) with `b = 1/2`. -/
lemma integrable_mul_stdNormalPdf_Ioi (q : ℝ) :
    IntegrableOn (fun w => w * stdNormalPdf w) (Ioi q) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hbase := (integrable_mul_exp_neg_mul_sq hb).const_mul (Real.sqrt (2 * π))⁻¹
  have heq : (fun x : ℝ => (Real.sqrt (2 * π))⁻¹ * (x * Real.exp (-(1 / 2) * x ^ 2)))
      = fun x => x * stdNormalPdf x := by
    funext x
    have hexp : Real.exp (-(1 / 2 : ℝ) * x ^ 2) = Real.exp (-(x ^ 2) / 2) := by
      congr 1; ring
    rw [stdNormalPdf, hexp]; ring
  rw [heq] at hbase
  exact hbase.integrableOn

/-- `φ(w) → 0` at `+∞` (hence `-φ(w) → 0`), the vanishing-at-infinity leg of FTC-2. -/
lemma tendsto_neg_stdNormalPdf :
    Tendsto (fun x => -stdNormalPdf x) atTop (𝓝 0) := by
  have hquad : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot := by
    have h : Tendsto (fun x : ℝ => x ^ 2 / (-2)) atTop atBot :=
      (tendsto_pow_atTop (n := 2) (by norm_num)).atTop_div_const_of_neg (by norm_num)
    have heq : (fun x : ℝ => x ^ 2 / (-2)) = fun x : ℝ => -(x ^ 2) / 2 := by
      funext x; ring
    rwa [heq] at h
  have hexp0 : Tendsto (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hquad
  have hpdf0 : Tendsto stdNormalPdf atTop (𝓝 0) := by
    have h := hexp0.div_const (Real.sqrt (2 * π))
    rw [zero_div] at h
    exact h
  simpa using hpdf0.neg

/-- **Gaussian tail-integral lemma.** For the standard normal density,
`∫_{q}^{∞} w · φ(w) dw = φ(q)`. The reachable half of obligation A3; the Φ⁻¹ half is a
documented Mathlib wall (see the module header). -/
theorem integral_Ioi_mul_gaussianPDFReal (q : ℝ) :
    ∫ w in Ioi q, w * gaussianPDFReal 0 1 w = gaussianPDFReal 0 1 q := by
  have key : ∫ w in Ioi q, w * stdNormalPdf w = stdNormalPdf q := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x (_ : x ∈ Ici q) => hasDerivAt_neg_stdNormalPdf x)
      (integrable_mul_stdNormalPdf_Ioi q) tendsto_neg_stdNormalPdf
    simpa using h
  simp_rw [← stdNormalPdf_eq]
  exact key

end Ctrllib

#print axioms Ctrllib.integral_Ioi_mul_gaussianPDFReal
#print axioms Ctrllib.stdNormalPdf_eq
#print axioms Ctrllib.hasDerivAt_neg_stdNormalPdf
#print axioms Ctrllib.integrable_mul_stdNormalPdf_Ioi
#print axioms Ctrllib.tendsto_neg_stdNormalPdf
