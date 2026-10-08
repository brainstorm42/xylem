import Ctrllib.RoverPoseGeometry
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Concrete planar heading rotations embedded in `Point3`.

The third coordinate is fixed.  This module supplies the geometric part of a
heading interface; a runtime still has to justify how its heading and heading
rate relate to these real parameters.
-/

open Matrix
open scoped BigOperators

namespace Ctrllib

noncomputable def planarRotationMatrix (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = 0 ∧ j = 0 then Real.cos θ else
    if i = 0 ∧ j = 1 then -Real.sin θ else
    if i = 1 ∧ j = 0 then Real.sin θ else
    if i = 1 ∧ j = 1 then Real.cos θ else
    if i = j then 1 else 0

noncomputable def planarRotation (θ : ℝ) : Point3 →L[ℝ] Point3 :=
  (Matrix.toEuclideanCLM : Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point3 →L[ℝ] Point3)
    (planarRotationMatrix θ)

private lemma planarRotation_coord0 (θ : ℝ) (x : Point3) :
    (planarRotation θ x).ofLp 0 = Real.cos θ * x.ofLp 0 - Real.sin θ * x.ofLp 1 := by
  change ((((Matrix.toEuclideanCLM : Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point3 →L[ℝ] Point3)
      (planarRotationMatrix θ)) x).ofLp 0) = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [planarRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private lemma planarRotation_coord1 (θ : ℝ) (x : Point3) :
    (planarRotation θ x).ofLp 1 = Real.sin θ * x.ofLp 0 + Real.cos θ * x.ofLp 1 := by
  change ((((Matrix.toEuclideanCLM : Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point3 →L[ℝ] Point3)
      (planarRotationMatrix θ)) x).ofLp 1) = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [planarRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private lemma planarRotation_coord2 (θ : ℝ) (x : Point3) :
    (planarRotation θ x).ofLp 2 = x.ofLp 2 := by
  change ((((Matrix.toEuclideanCLM : Matrix (Fin 3) (Fin 3) ℝ ≃⋆ₐ[ℝ] Point3 →L[ℝ] Point3)
      (planarRotationMatrix θ)) x).ofLp 2) = _
  rw [Matrix.ofLp_toEuclideanCLM]
  simp [planarRotationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- A planar heading rotation preserves the Euclidean distance between points. -/
theorem planarRotation_isometry (θ : ℝ) (x y : Point3) :
    ‖planarRotation θ x - planarRotation θ y‖ = ‖x - y‖ := by
  have h0 := planarRotation_coord0 θ (x - y)
  have h1 := planarRotation_coord1 θ (x - y)
  have h2 := planarRotation_coord2 θ (x - y)
  have hnorm : ‖planarRotation θ (x - y)‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
    have h1' : (planarRotation θ (x - y)).ofLp (Fin.succ 0) =
        Real.sin θ * (x - y).ofLp 0 + Real.cos θ * (x - y).ofLp 1 := by simpa using h1
    have h2' : (planarRotation θ (x - y)).ofLp ((Fin.succ 0).succ) =
        (x - y).ofLp 2 := by simpa using h2
    rw [h1', h2']
    rw [h0]
    have hx1 : (x - y).ofLp (Fin.succ 0) = (x - y).ofLp 1 := by rfl
    have hx2 : (x - y).ofLp ((Fin.succ 0).succ) = (x - y).ofLp 2 := by rfl
    rw [hx1, hx2]
    ring_nf
    nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [← map_sub]
  nlinarith [norm_nonneg (planarRotation θ (x - y)), norm_nonneg (x - y)]

private lemma planarRotation_diff_coord0 (θ φ : ℝ) (x : Point3) :
    ((planarRotation θ - planarRotation φ) x).ofLp 0 =
      (Real.cos θ - Real.cos φ) * x.ofLp 0 - (Real.sin θ - Real.sin φ) * x.ofLp 1 := by
  change ((planarRotation θ x).ofLp 0 - (planarRotation φ x).ofLp 0) = _
  rw [planarRotation_coord0, planarRotation_coord0]
  ring

private lemma planarRotation_diff_coord1 (θ φ : ℝ) (x : Point3) :
    ((planarRotation θ - planarRotation φ) x).ofLp 1 =
      (Real.sin θ - Real.sin φ) * x.ofLp 0 + (Real.cos θ - Real.cos φ) * x.ofLp 1 := by
  change ((planarRotation θ x).ofLp 1 - (planarRotation φ x).ofLp 1) = _
  rw [planarRotation_coord1, planarRotation_coord1]
  ring

private lemma planarRotation_diff_coord2 (θ φ : ℝ) (x : Point3) :
    ((planarRotation θ - planarRotation φ) x).ofLp 2 = 0 := by
  change ((planarRotation θ x).ofLp 2 - (planarRotation φ x).ofLp 2) = 0
  rw [planarRotation_coord2, planarRotation_coord2]
  ring

private lemma planarRotation_diff_apply_sq_le (θ φ : ℝ) (x : Point3) :
    ‖(planarRotation θ - planarRotation φ) x‖ ^ 2 ≤
      2 * |θ - φ| ^ 2 * ‖x‖ ^ 2 := by
  have hc : |Real.cos θ - Real.cos φ| ≤ |θ - φ| := Real.abs_cos_sub_cos_le _ _
  have hs : |Real.sin θ - Real.sin φ| ≤ |θ - φ| := Real.abs_sin_sub_sin_le _ _
  have hc2 : (Real.cos θ - Real.cos φ) ^ 2 ≤ |θ - φ| ^ 2 :=
    (sq_le_sq).2 (by simpa only [abs_abs] using hc)
  have hs2 : (Real.sin θ - Real.sin φ) ^ 2 ≤ |θ - φ| ^ 2 :=
    (sq_le_sq).2 (by simpa only [abs_abs] using hs)
  have hnorm : ‖(planarRotation θ - planarRotation φ) x‖ ^ 2 =
      ∑ i, ‖((planarRotation θ - planarRotation φ) x).ofLp i‖ ^ 2 :=
    EuclideanSpace.norm_sq_eq _
  rw [hnorm]
  simp only [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  have h0 := planarRotation_diff_coord0 θ φ x
  have h1 := planarRotation_diff_coord1 θ φ x
  have h2 := planarRotation_diff_coord2 θ φ x
  have h1' : ((planarRotation θ - planarRotation φ) x).ofLp (Fin.succ 0) =
      (Real.sin θ - Real.sin φ) * x.ofLp 0 + (Real.cos θ - Real.cos φ) * x.ofLp 1 := by
    simpa using h1
  have h2' : ((planarRotation θ - planarRotation φ) x).ofLp ((Fin.succ 0).succ) = 0 := by
    simpa using h2
  have hx1 : x.ofLp (Fin.succ 0) = x.ofLp 1 := by rfl
  have hx2 : x.ofLp ((Fin.succ 0).succ) = x.ofLp 2 := by rfl
  rw [h0, h1', h2', hx1, hx2]
  have htail : (∑ i : Fin 0, ((planarRotation θ - planarRotation φ) x).ofLp
      i.succ.succ.succ ^ 2) = 0 := by simp
  rw [htail]
  have hp0 : 0 ≤ x.ofLp 0 ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ x.ofLp 1 ^ 2 := sq_nonneg _
  have hcprod : (Real.cos θ - Real.cos φ) ^ 2 * x.ofLp 0 ^ 2 ≤
      |θ - φ| ^ 2 * x.ofLp 0 ^ 2 := mul_le_mul_of_nonneg_right hc2 hp0
  have hcprod' : (Real.cos θ - Real.cos φ) ^ 2 * x.ofLp 1 ^ 2 ≤
      |θ - φ| ^ 2 * x.ofLp 1 ^ 2 := mul_le_mul_of_nonneg_right hc2 hp1
  have hsprod : (Real.sin θ - Real.sin φ) ^ 2 * x.ofLp 0 ^ 2 ≤
      |θ - φ| ^ 2 * x.ofLp 0 ^ 2 := mul_le_mul_of_nonneg_right hs2 hp0
  have hsprod' : (Real.sin θ - Real.sin φ) ^ 2 * x.ofLp 1 ^ 2 ≤
      |θ - φ| ^ 2 * x.ofLp 1 ^ 2 := mul_le_mul_of_nonneg_right hs2 hp1
  have htailx : (∑ i : Fin 0, x.ofLp i.succ.succ.succ ^ 2) = 0 := by simp
  rw [htailx]
  have hz : 0 ≤ 2 * |θ - φ| ^ 2 * x.ofLp 2 ^ 2 := by positivity
  -- Expansion cancels the mixed terms exactly; no coordinate-wise triangle
  -- estimate is used, since that would lose a further factor of two.
  simp only [sq_abs] at hcprod hcprod' hsprod hsprod' hz
  nlinarith only [hcprod, hcprod', hsprod, hsprod', hz]

/- The operator difference bound is conservative by a factor of `sqrt 2`. -/
theorem planarRotation_operator_diff_le (θ φ : ℝ) :
    ‖planarRotation θ - planarRotation φ‖ ≤ Real.sqrt 2 * |θ - φ| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x ↦ ?_)
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsq := planarRotation_diff_apply_sq_le θ φ x
  have hnorm : 0 ≤ ‖x‖ := norm_nonneg _
  have hsquare : (Real.sqrt 2 * |θ - φ| * ‖x‖) ^ 2 =
      2 * |θ - φ| ^ 2 * ‖x‖ ^ 2 := by
    calc
      (Real.sqrt 2 * |θ - φ| * ‖x‖) ^ 2 = (Real.sqrt 2) ^ 2 *
          |θ - φ| ^ 2 * ‖x‖ ^ 2 := by ring
      _ = 2 * |θ - φ| ^ 2 * ‖x‖ ^ 2 := by rw [Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hsquare]
  exact hsq

theorem planarRotation_heading_error_le {θ φ ε : ℝ} (_hε : 0 ≤ ε)
    (hθφ : |θ - φ| ≤ ε) :
    ‖planarRotation θ - planarRotation φ‖ ≤ Real.sqrt 2 * ε := by
  calc
    ‖planarRotation θ - planarRotation φ‖ ≤ Real.sqrt 2 * |θ - φ| :=
      planarRotation_operator_diff_le θ φ
    _ ≤ Real.sqrt 2 * ε := mul_le_mul_of_nonneg_left hθφ (Real.sqrt_nonneg _)

theorem planarRotation_heading_lipschitz_le {θ : ℝ → ℝ} {S : Set ℝ} {ω : ℝ}
    (hθ : ∀ s ∈ S, ∀ u ∈ S, |θ s - θ u| ≤ ω * |s - u|)
    {s u : ℝ} (hs : s ∈ S) (hu : u ∈ S) :
    ‖planarRotation (θ s) - planarRotation (θ u)‖ ≤
      Real.sqrt 2 * ω * |s - u| := by
  calc
    ‖planarRotation (θ s) - planarRotation (θ u)‖ ≤ Real.sqrt 2 * |θ s - θ u| :=
      planarRotation_operator_diff_le _ _
    _ ≤ Real.sqrt 2 * (ω * |s - u|) :=
      mul_le_mul_of_nonneg_left (hθ s hs u hu) (Real.sqrt_nonneg _)
    _ = Real.sqrt 2 * ω * |s - u| := by ring

end Ctrllib

#print axioms Ctrllib.planarRotation_isometry
#print axioms Ctrllib.planarRotation_operator_diff_le
#print axioms Ctrllib.planarRotation_heading_error_le
#print axioms Ctrllib.planarRotation_heading_lipschitz_le
