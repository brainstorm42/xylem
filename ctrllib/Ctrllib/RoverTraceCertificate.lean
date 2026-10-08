import Ctrllib.RoverConcreteCovers

namespace Ctrllib

noncomputable def tracePoint (x y : ℝ) : Point3 :=
  WithLp.toLp 2 (![x, y, 0] : Fin 3 → ℝ)

theorem point2_sq_norm_sub (x y ox oy : ℝ) :
    ‖tracePoint x y - tracePoint ox oy‖ ^ 2 = (x - ox)^2 + (y - oy)^2 := by
  rw [EuclideanSpace.norm_eq]
  simp [tracePoint, Fin.sum_univ_succ, Real.norm_eq_abs]
  rw [Real.sq_sqrt]
  positivity

theorem normalized_time_mem_unit_interval
    {t₀ t₁ t : ℝ} (htime : t₀ < t₁) (ht : t ∈ Set.Icc t₀ t₁) :
    (t - t₀) / (t₁ - t₀) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply div_nonneg <;> linarith [ht.1]
  · apply (div_le_iff₀ (by linarith)).2
    linarith [ht.2]

private lemma quad_min_of_certificate
    {A B C α s : ℝ} (hA : 0 ≤ A) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hcert : (α = 0 ∧ 0 ≤ B) ∨ (α = 1 ∧ A + B ≤ 0) ∨ A * α + B = 0) :
    A * α^2 + 2 * B * α + C ≤ A * s^2 + 2 * B * s + C := by
  rcases hcert with h0 | h1 | hstat
  · rcases h0 with ⟨rfl, hB⟩
    have hi : 0 ≤ A * s + 2 * B := by nlinarith
    have hp := mul_nonneg hs0 hi
    nlinarith
  · rcases h1 with ⟨rfl, hAB⟩
    have hAterm : A * (s - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA (by linarith)
    have hinner : A * (1 + s) + 2 * B ≤ 0 := by nlinarith
    have hfac : 0 ≤ (1 - s) * (-(A * (1 + s) + 2 * B)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hfac]
  · have hsq : 0 ≤ A * (s - α)^2 := mul_nonneg hA (sq_nonneg _)
    have hid : A * s^2 + 2 * B * s + C - (A * α^2 + 2 * B * α + C) = A * (s - α)^2 := by
      have hB : B = - A * α := by linarith
      rw [hB]
      ring
    nlinarith [hsq, hid]

/-- A finite exact certificate for the minimum of squared planar separation.

The three alternatives identify a minimizer at the left endpoint, the right
endpoint, or an interior stationary point. The conclusion lifts the resulting
scalar quadratic bound to two translated planar discs.
-/
theorem planar_segment_disc_trace_certificate
    {x₀ y₀ dx dy ox oy aBody aObs R α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcert :
      (α = 0 ∧ 0 ≤ ((x₀ - ox) * dx + (y₀ - oy) * dy)) ∨
      (α = 1 ∧ (dx^2 + dy^2) + (x₀ - ox) * dx + (y₀ - oy) * dy ≤ 0) ∨
      (dx^2 + dy^2) * α + ((x₀ - ox) * dx + (y₀ - oy) * dy) = 0)
    (hR : 0 < R) (hBody : 0 ≤ aBody) (hObs : 0 ≤ aObs)
    (hαsep :
      (R + aBody + aObs)^2 ≤
        (dx^2 + dy^2) * α^2 +
          2 * ((x₀ - ox) * dx + (y₀ - oy) * dy) * α +
          ((x₀ - ox)^2 + (y₀ - oy)^2)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ x ∈ (fun z ↦ tracePoint (x₀ + s * dx) (y₀ + s * dy) + z) '' planarDisc aBody,
      ∀ y ∈ (fun z ↦ tracePoint ox oy + z) '' planarDisc aObs,
        R ≤ dist x y := by
  intro s hs x hx y hy
  have hcert' :
      (α = 0 ∧ 0 ≤ ((x₀ - ox) * dx + (y₀ - oy) * dy)) ∨
      (α = 1 ∧ (dx^2 + dy^2) + ((x₀ - ox) * dx + (y₀ - oy) * dy) ≤ 0) ∨
      (dx^2 + dy^2) * α + ((x₀ - ox) * dx + (y₀ - oy) * dy) = 0 := by
    simpa [add_assoc] using hcert
  have hquad := quad_min_of_certificate
    (A := dx^2 + dy^2)
    (B := (x₀ - ox) * dx + (y₀ - oy) * dy)
    (C := (x₀ - ox)^2 + (y₀ - oy)^2)
    (α := α) (s := s) (by positivity) hs.1 hs.2 hcert'
  have hq : (R + aBody + aObs)^2 ≤
      ‖tracePoint (x₀ + s * dx) (y₀ + s * dy) - tracePoint ox oy‖ ^ 2 := by
    rw [point2_sq_norm_sub]
    nlinarith [hαsep, hquad]
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hu' : ‖u‖ ≤ aBody := hu.1
  have hv' : ‖v‖ ≤ aObs := hv.1
  have hK : 0 ≤ R + aBody + aObs := by linarith
  have hcentre : R + aBody + aObs ≤
      ‖tracePoint (x₀ + s * dx) (y₀ + s * dy) - tracePoint ox oy‖ := by
    have hn : 0 ≤ ‖tracePoint (x₀ + s * dx) (y₀ + s * dy) - tracePoint ox oy‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖tracePoint (x₀ + s * dx) (y₀ + s * dy) - tracePoint ox oy‖ - (R + aBody + aObs))]
  have htri : ‖tracePoint (x₀ + s * dx) (y₀ + s * dy) - tracePoint ox oy‖ ≤
      dist (tracePoint (x₀ + s * dx) (y₀ + s * dy) + u) (tracePoint ox oy + v) + (‖v‖ + ‖u‖) := by
    rw [dist_eq_norm]
    have hnorm : ‖v - u‖ ≤ ‖v‖ + ‖u‖ := norm_sub_le _ _
    calc
      ‖tracePoint (x₀ + s * dx) (y₀ + s * dy) - tracePoint ox oy‖ =
          ‖((tracePoint (x₀ + s * dx) (y₀ + s * dy) + u) - (tracePoint ox oy + v)) + (v - u)‖ := by congr 1; abel
      _ ≤ ‖(tracePoint (x₀ + s * dx) (y₀ + s * dy) + u) - (tracePoint ox oy + v)‖ + ‖v - u‖ := norm_add_le _ _
      _ ≤ ‖(tracePoint (x₀ + s * dx) (y₀ + s * dy) + u) - (tracePoint ox oy + v)‖ + (‖v‖ + ‖u‖) := by
        have hh := add_le_add hnorm
          (le_refl ‖(tracePoint (x₀ + s * dx) (y₀ + s * dy) + u) - (tracePoint ox oy + v)‖)
        convert hh using 1 <;> ac_rfl
  rw [dist_eq_norm] at *
  nlinarith [hcentre, htri, hu', hv']

end Ctrllib

#print axioms Ctrllib.point2_sq_norm_sub
#print axioms Ctrllib.normalized_time_mem_unit_interval
#print axioms Ctrllib.planar_segment_disc_trace_certificate
