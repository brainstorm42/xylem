/-
Time-varying comparison bound (TARGET 2 of the ctrllib stream).

Extends the L2 constant-eps comparison lemma (Lyapunov.lean) to a time-varying
disturbance eps(t), the panteley2001growth Lemma 2 shape (eq 35). Two results ride
on Mathlib's gronwallBound: convergence to zero under a vanishing disturbance
(comparison_tendsto_zero) and no finite escape under a bounded one
(comparison_bounded). The engine is comparison_shift, L2's comparison lemma with a
movable start point.

SymPy pin: the corresponding symbolic check (not bundled).py.
Human derivation:
the corresponding derivation record (not bundled).
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Analysis.Normed.Group.Basic

open Set Filter Topology Real

namespace Ctrllib

variable {v v' ε : ℝ → ℝ} {a c t₀ T : ℝ}

/-- Restartable scalar comparison lemma. If `v` is continuous on `[t₀, T]`,
right-differentiable with derivative `v'` on `[t₀, T)`, and satisfies the
constant-ceiling decrease `v' t ≤ -a·v t + c`, then `v` is bounded by the
Grönwall comparison solution started at `t₀`. This is `Lyapunov.lyapunov_comparison`
stated directly on the scalar `v` and with a movable start point `t₀`. -/
theorem comparison_shift
    (hvc : ContinuousOn v (Icc t₀ T))
    (hv : ∀ t ∈ Ico t₀ T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico t₀ T, v' t ≤ -a * v t + c) :
    ∀ t ∈ Icc t₀ T, v t ≤ gronwallBound (v t₀) (-a) c (t - t₀) := by
  intro t ht
  exact le_gronwallBound_of_liminf_deriv_right_le hvc
    (fun s hs r hr => (hv s hs).liminf_right_slope_le hr)
    le_rfl hbound t ht

/-- Vanishing-disturbance convergence. With decay rate `a > 0`, a nonnegative
`v` obeying `v' t ≤ -a·v t + ε t` and a disturbance `ε t → 0` tends to `0`.
The proof: fix a target `δ`; once `ε` has fallen below the ceiling `c = aδ/2`,
restart Grönwall (via `comparison_shift`) from that time; the resulting bound is
a vanishing transient plus the floor `c/a = δ/2 < δ`. -/
theorem comparison_tendsto_zero
    (ha : 0 < a)
    (hvc : ContinuousOn v (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt v (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * v t + ε t)
    (hnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ v t)
    (heps : Tendsto ε atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro δ hδ
  set c : ℝ := a * δ / 2 with hc
  have hc_pos : 0 < c := by rw [hc]; exact div_pos (mul_pos ha hδ) (by norm_num)
  have hd_nn : (0 : ℝ) ≤ c / a := div_nonneg hc_pos.le ha.le
  have hd_lt : c / a < δ := by
    rw [div_lt_iff₀ ha, hc]; nlinarith [mul_pos ha hδ]
  -- eventually the disturbance sits below the ceiling c
  have hev : ∀ᶠ t in atTop, 0 ≤ t ∧ ε t ≤ c := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), heps.eventually (Iio_mem_nhds hc_pos)]
      with t ht0 htε using ⟨ht0, htε.le⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  have hT₀0 : (0 : ℝ) ≤ T₀ := (hT₀ T₀ le_rfl).1
  -- the transient v T₀ · e^{-a(t-T₀)} vanishes
  have hlin : Tendsto (fun t : ℝ => t - T₀) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-T₀) tendsto_id
  have hg : Tendsto (fun t : ℝ => -a * (t - T₀)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr ha)).mpr hlin
  have hexp : Tendsto (fun t : ℝ => Real.exp (-a * (t - T₀))) atTop (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr hg
  have hw : Tendsto (fun t : ℝ => v T₀ * Real.exp (-a * (t - T₀))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul (v T₀)
  have hwlt : ∀ᶠ t in atTop, v T₀ * Real.exp (-a * (t - T₀)) < δ - c / a :=
    hw.eventually (Iio_mem_nhds (by linarith))
  -- assemble
  filter_upwards [eventually_ge_atTop T₀, hwlt, eventually_ge_atTop (0 : ℝ)]
    with t htT₀ hwt ht0
  have hsub : Icc T₀ t ⊆ Ici (0 : ℝ) := Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hT₀0)
  have hgron : v t ≤ gronwallBound (v T₀) (-a) c (t - T₀) :=
    comparison_shift (hvc.mono hsub)
      (fun s hs => hv s (mem_Ici.mpr (le_trans hT₀0 hs.1)))
      (fun s hs => by
        have hεc : ε s ≤ c := (hT₀ s hs.1).2
        have := hbound s (mem_Ici.mpr (le_trans hT₀0 hs.1))
        linarith)
      t (right_mem_Icc.mpr htT₀)
  have hane : (-a) ≠ 0 := neg_ne_zero.mpr ha.ne'
  simp only [gronwallBound_of_K_ne_0 hane] at hgron
  have hE : (0 : ℝ) < Real.exp (-a * (t - T₀)) := Real.exp_pos _
  have hfloor : c / (-a) * (Real.exp (-a * (t - T₀)) - 1) ≤ c / a := by
    have key : c / (-a) * (Real.exp (-a * (t - T₀)) - 1)
        = c / a - c / a * Real.exp (-a * (t - T₀)) := by rw [div_neg]; ring
    rw [key]; nlinarith [mul_nonneg hd_nn hE.le]
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn t (mem_Ici.mpr ht0))]
  linarith [hgron, hwt, hfloor]

/-- No finite escape under a bounded disturbance. If `ε t ≤ M` (with `M ≥ 0`)
and `v 0 ≥ 0`, then `v t ≤ v 0 + M/a` for every `t ≥ 0`. The constant `M/a` is
the ultimate-bound / noise-floor level -- the time-varying analogue of L2's
`lyapunov_ultimate_bound`. -/
theorem comparison_bounded
    (ha : 0 < a) {M : ℝ} (hM : 0 ≤ M)
    (hvc : ContinuousOn v (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt v (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * v t + ε t)
    (hεM : ∀ t ∈ Ici (0 : ℝ), ε t ≤ M)
    (hv0 : 0 ≤ v 0) :
    ∀ t ∈ Ici (0 : ℝ), v t ≤ v 0 + M / a := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Ici (0 : ℝ) := Icc_subset_Ici_self
  have hgron : v t ≤ gronwallBound (v 0) (-a) M (t - 0) :=
    comparison_shift (hvc.mono hsub)
      (fun s hs => hv s (mem_Ici.mpr hs.1))
      (fun s hs => by
        have := hbound s (mem_Ici.mpr hs.1)
        have hεs := hεM s (mem_Ici.mpr hs.1)
        linarith)
      t (right_mem_Icc.mpr (mem_Ici.mp ht))
  rw [sub_zero] at hgron
  have hane : (-a) ≠ 0 := neg_ne_zero.mpr ha.ne'
  simp only [gronwallBound_of_K_ne_0 hane] at hgron
  have hMa : (0 : ℝ) ≤ M / a := div_nonneg hM ha.le
  have hE : (0 : ℝ) < Real.exp (-a * t) := Real.exp_pos _
  have hE1 : Real.exp (-a * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [mul_nonneg ha.le (mem_Ici.mp ht)]
  have hv0E : v 0 * Real.exp (-a * t) ≤ v 0 := mul_le_of_le_one_right hv0 hE1
  have hfloor : M / (-a) * (Real.exp (-a * t) - 1) ≤ M / a := by
    have key : M / (-a) * (Real.exp (-a * t) - 1)
        = M / a - M / a * Real.exp (-a * t) := by rw [div_neg]; ring
    rw [key]; nlinarith [mul_nonneg hMa hE.le]
  linarith [hgron, hv0E, hfloor]

end Ctrllib

#print axioms Ctrllib.comparison_shift
#print axioms Ctrllib.comparison_tendsto_zero
#print axioms Ctrllib.comparison_bounded
