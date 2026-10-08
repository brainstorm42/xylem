import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Ctrllib.ForcedImpedance

/-!
Integrated finite-horizon mechanical power bound (atlas contract C1).

The generic theorem integrates a scalar storage derivative bound over `[0, T]`:
if `V' = d`, `d` and the supplied external power `s` are continuous on the
interval, and `d ≤ s`, then `V T - V 0 ≤ ∫ t in 0..T, s t`.  The forced-
impedance instance takes `d = vᵀ f - vᵀ D v` and `s = vᵀ f`, reusing the
existing local derivative theorem.  These are calculus contracts for supplied
trajectories; this module asserts no ODE existence, stability, or physical
model correspondence.
-/
open Matrix
open MeasureTheory
open scoped InnerProductSpace

namespace Ctrllib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Generic scalar storage contract -/

/--
Finite-horizon integration of a differential storage inequality.

The assumptions are a sufficient `C¹`-style contract on the closed interval:
`d` is a continuous derivative witness for `V`, and `s` is continuous external
power.  The interval FTC identifies the integral of `d` with `V T - V 0`,
while interval integral monotonicity uses `d ≤ s` pointwise.  The result is
deliberately independent of how the trajectory was generated.
-/
theorem integrated_storage_le_power
    {V d s : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hV : ContinuousOn V (Set.Icc 0 T))
    (hd : ContinuousOn d (Set.Icc 0 T))
    (hs : ContinuousOn s (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt V (d t) t)
    (hbound : ∀ t ∈ Set.Icc 0 T, d t ≤ s t) :
    V T - V 0 ≤ ∫ t in (0 : ℝ)..T, s t := by
  have hd_int : IntervalIntegrable d volume 0 T := hd.intervalIntegrable_of_Icc hT
  have hs_int : IntervalIntegrable s volume 0 T := hs.intervalIntegrable_of_Icc hT
  have hfund : (∫ t in (0 : ℝ)..T, d t) = V T - V 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hV hderiv hd_int
  have hmono : (∫ t in (0 : ℝ)..T, d t) ≤ ∫ t in (0 : ℝ)..T, s t :=
    intervalIntegral.integral_mono_on hT hd_int hs_int hbound
  rw [hfund] at hmono
  exact hmono

/-! ### Forced-impedance endpoint -/

/-- External mechanical power at the forced-impedance port, `vᵀ f`. -/
noncomputable def forcedImpedanceExternalPower
    (v f : ForcedImpedanceCoord n) : ℝ :=
  ⟪v, f⟫_ℝ

/-- Damping power in the forced-impedance storage, `vᵀ D v`. -/
noncomputable def forcedImpedanceDampingPower
    (D : Matrix n n ℝ) (v : ForcedImpedanceCoord n) : ℝ :=
  ⟪v, toEuclideanCLM (𝕜 := ℝ) D v⟫_ℝ

omit [DecidableEq n] in
private lemma real_inner_eq_dotProduct (x y : ForcedImpedanceCoord n) :
    ⟪x, y⟫_ℝ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/- The trajectory-generated power functions are continuous under continuous
   velocity and force paths.  The fixed matrix action is a continuous linear
   map, so no continuity of an acceleration witness is needed. -/
omit [DecidableEq n] in
private lemma continuousOn_forcedImpedanceExternalPower
    {v f : ℝ → ForcedImpedanceCoord n}
    {T : ℝ} (hv : ContinuousOn v (Set.Icc 0 T))
    (hf : ContinuousOn f (Set.Icc 0 T)) :
    ContinuousOn (fun t ↦ forcedImpedanceExternalPower (v t) (f t)) (Set.Icc 0 T) := by
  exact (hv.inner hf).congr fun t ht ↦ rfl

private lemma continuousOn_forcedImpedanceDampingPower
    (D : Matrix n n ℝ) {v : ℝ → ForcedImpedanceCoord n}
    {T : ℝ} (hv : ContinuousOn v (Set.Icc 0 T)) :
    ContinuousOn (fun t ↦ forcedImpedanceDampingPower D (v t)) (Set.Icc 0 T) := by
  have hD : ContinuousOn (fun _t : ℝ ↦ toEuclideanCLM (𝕜 := ℝ) D)
      (Set.Icc 0 T) := continuousOn_const
  exact (hv.inner (hD.clm_apply hv)).congr fun t ht ↦ rfl

/--
Integrated passivity bound for a forced constant-matrix impedance trajectory.

For `T ≥ 0`, assume a supplied trajectory has derivative witnesses `a` and
satisfies `e' = v` and `M a + D v + K e = f` at every time.  A continuous force
path makes the external port power continuous; the velocity and storage paths
are continuous because the derivative witnesses supply pointwise continuity.
The generic FTC contract then gives

`V(T) - V(0) ≤ ∫₀ᵀ ⟪v(t), f(t)⟫ dt`.

The PSD damping hypothesis is consumed by the existing instantaneous bound.
No trajectory existence, uniqueness, stability, or physical correspondence is
asserted.
-/
theorem forcedImpedance_energy_le_integrated_power
    (M D K : Matrix n n ℝ) (hM : M.IsHermitian) (hK : K.IsHermitian)
    (hD : D.PosSemidef)
    {v e f a : ℝ → ForcedImpedanceCoord n} {T : ℝ}
    (hT : 0 ≤ T)
    (hv : ∀ t ∈ Set.Icc 0 T, HasDerivAt v (a t) t)
    (he : ∀ t ∈ Set.Icc 0 T, HasDerivAt e (v t) t)
    (heq : ∀ t ∈ Set.Icc 0 T, toEuclideanCLM (𝕜 := ℝ) M (a t) +
      toEuclideanCLM (𝕜 := ℝ) D (v t) + toEuclideanCLM (𝕜 := ℝ) K (e t) = f t)
    (hf : ContinuousOn f (Set.Icc 0 T)) :
    forcedImpedanceEnergy M K (v T) (e T) - forcedImpedanceEnergy M K (v 0) (e 0) ≤
      ∫ t in (0 : ℝ)..T, forcedImpedanceExternalPower (v t) (f t) := by
  have hv_cont : ContinuousOn v (Set.Icc 0 T) := fun t ht ↦
    (hv t ht).continuousAt.continuousWithinAt
  have hstorage_cont :
      ContinuousOn (fun t ↦ forcedImpedanceEnergy M K (v t) (e t)) (Set.Icc 0 T) := by
    intro t ht
    have hpath := forcedImpedance_energy_path_hasDerivAt M K hM hK (hv t ht) (he t ht)
    exact hpath.continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun s ↦ forcedImpedanceEnergy M K (v s) (e s))
        (forcedImpedanceExternalPower (v t) (f t) -
          forcedImpedanceDampingPower D (v t)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hlocal := forcedImpedance_energy_hasDerivAt M D K hM hK (hv t ht') (he t ht')
      (heq t ht')
    apply hlocal.congr_deriv
    rw [forcedImpedanceExternalPower, forcedImpedanceDampingPower]
    rw [real_inner_eq_dotProduct, inner_toEuclideanCLM]
  have hderiv_le : ∀ t ∈ Set.Icc 0 T,
      forcedImpedanceExternalPower (v t) (f t) - forcedImpedanceDampingPower D (v t) ≤
        forcedImpedanceExternalPower (v t) (f t) := by
    intro t ht
    have hnonneg := hD.dotProduct_mulVec_nonneg (WithLp.ofLp (v t))
    have hnonneg' : 0 ≤ forcedImpedanceDampingPower D (v t) := by
      rw [forcedImpedanceDampingPower, inner_toEuclideanCLM]
      simpa using hnonneg
    linarith
  have hpower_cont := continuousOn_forcedImpedanceExternalPower hv_cont hf
  have hdamper_cont := continuousOn_forcedImpedanceDampingPower D hv_cont
  have hd_cont : ContinuousOn
      (fun t ↦ forcedImpedanceExternalPower (v t) (f t) -
        forcedImpedanceDampingPower D (v t)) (Set.Icc 0 T) := hpower_cont.sub hdamper_cont
  exact integrated_storage_le_power hT hstorage_cont hd_cont hpower_cont hderiv hderiv_le

end Ctrllib

#print axioms Ctrllib.integrated_storage_le_power
#print axioms Ctrllib.forcedImpedance_energy_le_integrated_power
