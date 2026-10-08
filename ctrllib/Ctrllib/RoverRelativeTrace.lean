import Ctrllib.RoverTraceCertificate

/-!
Two affine moving discs reduce to the existing exact relative-separation
certificate. Both centres use the same normalized time. The result concerns
the declared continuous affine paths, not arbitrary interpolation of logs.
-/

namespace Ctrllib

/-- Translating both points by the same vector preserves their separation. -/
theorem relative_displacement_dist (a b u v : Point3) :
    dist (a + u) (b + v) = dist ((a - b) + u) v := by
  simp only [dist_eq_norm]
  congr 1
  abel

private theorem tracePoint_sub (x y ox oy : ℝ) :
    tracePoint x y - tracePoint ox oy = tracePoint (x - ox) (y - oy) := by
  ext i
  fin_cases i <;> simp [tracePoint]

/-- An exact quadratic certificate proves whole-body clearance between two
simultaneously moving planar discs over their common affine segment. -/
theorem two_moving_discs_trace_certificate
    {x₁ y₁ dx₁ dy₁ x₂ y₂ dx₂ dy₂ a₁ a₂ R α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcert :
      (α = 0 ∧ 0 ≤ (x₁ - x₂) * (dx₁ - dx₂) + (y₁ - y₂) * (dy₁ - dy₂)) ∨
      (α = 1 ∧ ((dx₁ - dx₂) ^ 2 + (dy₁ - dy₂) ^ 2) +
        (x₁ - x₂) * (dx₁ - dx₂) + (y₁ - y₂) * (dy₁ - dy₂) ≤ 0) ∨
      ((dx₁ - dx₂) ^ 2 + (dy₁ - dy₂) ^ 2) * α +
        ((x₁ - x₂) * (dx₁ - dx₂) + (y₁ - y₂) * (dy₁ - dy₂)) = 0)
    (hR : 0 < R) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hsep : (R + a₁ + a₂) ^ 2 ≤
      ((dx₁ - dx₂) ^ 2 + (dy₁ - dy₂) ^ 2) * α ^ 2 +
      2 * ((x₁ - x₂) * (dx₁ - dx₂) + (y₁ - y₂) * (dy₁ - dy₂)) * α +
      ((x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2)) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ x ∈ (fun z ↦ tracePoint (x₁ + s * dx₁) (y₁ + s * dy₁) + z) '' planarDisc a₁,
      ∀ y ∈ (fun z ↦ tracePoint (x₂ + s * dx₂) (y₂ + s * dy₂) + z) '' planarDisc a₂,
        R ≤ dist x y := by
  have h := planar_segment_disc_trace_certificate
    (x₀ := x₁ - x₂) (y₀ := y₁ - y₂) (dx := dx₁ - dx₂) (dy := dy₁ - dy₂)
    (ox := 0) (oy := 0) hα0 hα1 (by simpa using hcert) hR ha₁ ha₂
    (by simpa using hsep)
  intro s hs x hx y hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [relative_displacement_dist, tracePoint_sub]
  have heqx : x₁ + s * dx₁ - (x₂ + s * dx₂) = x₁ - x₂ + s * (dx₁ - dx₂) := by ring
  have heqy : y₁ + s * dy₁ - (y₂ + s * dy₂) = y₁ - y₂ + s * (dy₁ - dy₂) := by ring
  rw [heqx, heqy]
  have hz : tracePoint 0 0 = 0 := by ext i; fin_cases i <;> simp [tracePoint]
  exact h s hs _ ⟨u, hu, rfl⟩ _ ⟨v, hv, by simp [hz]⟩

end Ctrllib

#print axioms Ctrllib.relative_displacement_dist
#print axioms Ctrllib.two_moving_discs_trace_certificate
