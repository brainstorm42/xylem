import Ctrllib.TimeVaryingComparison

/-!
Continuous-time eventual floor (atlas obligation C6).

If a scalar storage function satisfies `v' ≤ -a · v + M` with `a > 0` and
`M ≥ 0`, its Grönwall comparison has an exponentially decaying initial
transient and converges to the disturbance floor `M / a`.  This module turns
that finite-horizon comparison into the eventual statement needed by the
atlas.  The theorem keeps the project’s one-sided right-derivative interface;
it does not establish that a physical trajectory realizes these hypotheses.

The initial nonnegativity hypothesis is unnecessary for this conclusion and
is therefore omitted: the transient estimate works for every real `v 0`.
The conventional derivation and the remaining modeling boundary are recorded
in the companion conventional note supplied with this proof.
-/

open Set Filter Topology Real

namespace Ctrllib

variable {v v' : ℝ → ℝ} {a : ℝ}

/-- **Continuous-time eventual floor (atlas C6).**  A continuous scalar
storage `v` on `[0, ∞)` with a right derivative witness satisfying
`v' t ≤ -a * v t + M`, for `a > 0` and `M ≥ 0`, eventually lies within any
positive tolerance above the floor `M / a`.  The conclusion does not require
`0 ≤ v 0`; that assumption is useful for nonnegative-storage interpretations
but is not needed to make the exponentially decaying transient vanish. -/
theorem comparison_eventual_floor
    (ha : 0 < a) {M : ℝ} (hM : 0 ≤ M)
    (hvc : ContinuousOn v (Ici 0))
    (hv : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt v (v' t) (Ici t) t)
    (hbound : ∀ t ∈ Ici (0 : ℝ), v' t ≤ -a * v t + M) :
    ∀ ε > 0, ∃ T ≥ 0, ∀ t ≥ T, v t ≤ M / a + ε := by
  intro ε hε
  have hlin : Tendsto (fun t : ℝ ↦ -a * t) atTop atBot := by
    exact (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr ha)).mpr tendsto_id
  have hexp : Tendsto (fun t : ℝ ↦ Real.exp (-a * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_comp_nhds_zero.mpr hlin
  have htrans : Tendsto (fun t : ℝ ↦ v 0 * Real.exp (-a * t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul (v 0)
  have hev : ∀ᶠ t in atTop, 0 ≤ t ∧ v 0 * Real.exp (-a * t) < ε := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), htrans.eventually (Iio_mem_nhds hε)]
      with t ht0 htransε using ⟨ht0, htransε⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  have hT0 : (0 : ℝ) ≤ T := (hT T le_rfl).1
  refine ⟨T, hT0, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := (hT t ht).1
  have htransε : v 0 * Real.exp (-a * t) < ε := (hT t ht).2
  have hsub : Icc (0 : ℝ) t ⊆ Ici (0 : ℝ) := Icc_subset_Ici_self
  have hgron : v t ≤ gronwallBound (v 0) (-a) M (t - 0) :=
    comparison_shift (hvc.mono hsub)
      (fun s hs => hv s (mem_Ici.mpr hs.1))
      (fun s hs => hbound s (mem_Ici.mpr hs.1))
      t (right_mem_Icc.mpr ht0)
  rw [sub_zero] at hgron
  have hane : (-a) ≠ 0 := neg_ne_zero.mpr ha.ne'
  simp only [gronwallBound_of_K_ne_0 hane] at hgron
  have hE : (0 : ℝ) < Real.exp (-a * t) := Real.exp_pos _
  have hMa : (0 : ℝ) ≤ M / a := div_nonneg hM ha.le
  have hfloor : M / (-a) * (Real.exp (-a * t) - 1) ≤ M / a := by
    have key : M / (-a) * (Real.exp (-a * t) - 1)
        = M / a - M / a * Real.exp (-a * t) := by
      rw [div_neg]
      ring
    rw [key]
    nlinarith [mul_nonneg hMa hE.le]
  linarith [hgron, htransε, hfloor]

end Ctrllib

#print axioms Ctrllib.comparison_eventual_floor
