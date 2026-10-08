/-
Lyapunov layer, first stones (L2 of the ctrllib stream).

Mathlib has no Lyapunov / ISS / LaSalle layer (verified absent 2026-07-04).
This file starts it minimally: the definitions one theorem needs, nothing more.

The theorem is the exponential comparison lemma (Khalil, *Nonlinear Systems*,
"comparison lemma") that cascaded-systems stability builds on, per the sources:
- panteley2001growth Prop. 1 (eq 14): every UGAS system admits V with V' ≤ -V
  — the a = 1, ε = 0 instance of `LyapunovDecrease` below.
- panteley2001growth Lemma 2 (eq 35): the boundedness proof runs on
  v' ≤ -v + c(r)·‖x₂(t)‖ — here the driving term is majorized by the
  constant ε on the horizon, the ε > 0 instance.
- giordano2019coordinated (framing paper) Prop. IV.1 closes with a
  LaSalle/negative-semidefinite argument (eq 38) + compact-set cascade
  theorems — that invariance layer is future work (L3+), NOT this file.

Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.ODE.Gronwall

open Set Real

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Field-level Lyapunov decrease: the derivative of `V` along the vector
field `f` is at most `-a * V + ε` at every point. `ε = 0` is the strict
decrease of panteley2001growth Prop. 1 (eq 14); `ε > 0` majorizes the cascade
interconnection term of its Lemma 2 (eq 35). -/
def LyapunovDecrease (V : E → ℝ) (f : E → E) (a ε : ℝ) : Prop :=
  ∀ y, fderiv ℝ V y (f y) ≤ -a * V y + ε

/-- Quadratic sandwich `c₁‖y‖² ≤ V y ≤ c₂‖y‖²` — the quadratic instance of
the class-K∞ bounds of panteley2001growth (eq 10); satisfied by the framing
paper's V (giordano2019coordinated eq 37) via the extreme eigenvalues of the
inertia and stiffness matrices. -/
def QuadSandwich (V : E → ℝ) (c₁ c₂ : ℝ) : Prop :=
  ∀ y, c₁ * ‖y‖ ^ 2 ≤ V y ∧ V y ≤ c₂ * ‖y‖ ^ 2

/-- The comparison lemma in Grönwall form: along any solution of `x' = f x`
on `[0, T]`, a differentiable Lyapunov function with
`LyapunovDecrease V f a ε` obeys the Grönwall bound. With `a > 0` this is
exponential decay of `V` toward the ultimate bound `ε / a`. -/
theorem lyapunov_comparison
    {V : E → ℝ} {f : E → E} {a ε : ℝ} {x : ℝ → E} {T : ℝ}
    (hV : Differentiable ℝ V) (hdec : LyapunovDecrease V f a ε)
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (f (x t)) (Ici t) t) :
    ∀ t ∈ Icc 0 T, V (x t) ≤ gronwallBound (V (x 0)) (-a) ε t := by
  intro t ht
  have key := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun s => V (x s))
    (f' := fun s => fderiv ℝ V (x s) (f (x s)))
    (δ := V (x 0)) (K := -a) (ε := ε) (a := 0) (b := T)
    (hV.continuous.comp_continuousOn hxc)
    (fun s hs r hr => by
      have hcomp : HasDerivWithinAt (fun u => V (x u))
          (fderiv ℝ V (x s) (f (x s))) (Ici s) s :=
        HasFDerivAt.comp_hasDerivWithinAt s (hV (x s)).hasFDerivAt (hx s hs)
      exact hcomp.liminf_right_slope_le hr)
    le_rfl
    (fun s _ => hdec (x s))
    t ht
  simpa using key

/-- Strict decrease (`ε = 0`, panteley2001growth Prop. 1 shape): `V` decays
exponentially along solutions. -/
theorem lyapunov_exp_decay
    {V : E → ℝ} {f : E → E} {a : ℝ} {x : ℝ → E} {T : ℝ}
    (hV : Differentiable ℝ V) (hdec : LyapunovDecrease V f a 0)
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (f (x t)) (Ici t) t) :
    ∀ t ∈ Icc 0 T, V (x t) ≤ V (x 0) * exp (-a * t) := by
  intro t ht
  have h := lyapunov_comparison hV hdec hxc hx t ht
  rwa [gronwallBound_ε0] at h

/-- Perturbed decrease (`a ≠ 0`, panteley2001growth Lemma 2 shape, eq 35):
`V` decays exponentially toward the ultimate bound `ε / a`. -/
theorem lyapunov_ultimate_bound
    {V : E → ℝ} {f : E → E} {a ε : ℝ} {x : ℝ → E} {T : ℝ}
    (ha : a ≠ 0)
    (hV : Differentiable ℝ V) (hdec : LyapunovDecrease V f a ε)
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (f (x t)) (Ici t) t) :
    ∀ t ∈ Icc 0 T,
      V (x t) ≤ V (x 0) * exp (-a * t) + ε / a * (1 - exp (-a * t)) := by
  intro t ht
  have h := lyapunov_comparison hV hdec hxc hx t ht
  simp only [gronwallBound, if_neg (neg_ne_zero.mpr ha)] at h
  have hrw : ε / -a * (exp (-a * t) - 1) = ε / a * (1 - exp (-a * t)) := by
    ring
  linarith [h, hrw]

/-- State-level exponential decay: with quadratic sandwich bounds and strict
decrease, the squared state norm decays exponentially (rate `a`, overshoot
`c₂ / c₁` after dividing by `c₁ > 0` — stated division-free). This is the
Lyapunov direct method's exponential-stability conclusion in the quadratic
case. -/
theorem lyapunov_norm_sq_exp_decay
    {V : E → ℝ} {f : E → E} {a c₁ c₂ : ℝ} {x : ℝ → E} {T : ℝ}
    (hV : Differentiable ℝ V) (hsand : QuadSandwich V c₁ c₂)
    (hdec : LyapunovDecrease V f a 0)
    (hxc : ContinuousOn x (Icc 0 T))
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (f (x t)) (Ici t) t) :
    ∀ t ∈ Icc 0 T, c₁ * ‖x t‖ ^ 2 ≤ c₂ * ‖x 0‖ ^ 2 * exp (-a * t) := by
  intro t ht
  calc c₁ * ‖x t‖ ^ 2 ≤ V (x t) := (hsand (x t)).1
    _ ≤ V (x 0) * exp (-a * t) := lyapunov_exp_decay hV hdec hxc hx t ht
    _ ≤ c₂ * ‖x 0‖ ^ 2 * exp (-a * t) :=
        mul_le_mul_of_nonneg_right (hsand (x 0)).2 (exp_pos _).le

end Ctrllib

#print axioms Ctrllib.lyapunov_comparison
#print axioms Ctrllib.lyapunov_exp_decay
#print axioms Ctrllib.lyapunov_ultimate_bound
#print axioms Ctrllib.lyapunov_norm_sq_exp_decay
