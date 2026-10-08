/-
Finite-dimensional power balance for a lumped elastic attachment.

The attachment has an absolute lumped coordinate `eta`, a nominal rigid
attachment coordinate `s(q)`, deformation `delta = eta - s(q)`, and relative
velocity `rel = eta' - (s ∘ q)'`.  Its internal force is
`lambda = K *ᵥ delta + D *ᵥ rel`, while the lumped force balance is
`M *ᵥ eta'' = -lambda + f`.  The theorem below keeps the rigid-layer power
identity as an explicit premise.  It therefore proves the local finite
dimensional balance without making an ODE-existence or plant-correspondence
claim.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul

open Matrix
open scoped BigOperators

namespace Ctrllib

variable {r n : Type*} [Fintype r] [Fintype n]

/-- Mechanical storage of an attachment velocity and deformation. -/
noncomputable def attachmentStorage (M K : Matrix r r ℝ)
    (u delta : r → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (u ⬝ᵥ M *ᵥ u) + (1 / 2 : ℝ) * (delta ⬝ᵥ K *ᵥ delta)

/-- Kelvin--Voigt attachment force. -/
def attachmentForce (K D : Matrix r r ℝ) (delta rel : r → ℝ) : r → ℝ :=
  K *ᵥ delta + D *ᵥ rel

private lemma hasDerivAt_dotProduct
    {x y : ℝ → (r → ℝ)} {xd yd : r → ℝ} {t : ℝ}
    (hx : HasDerivAt x xd t) (hy : HasDerivAt y yd t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s)
      (xd ⬝ᵥ y t + x t ⬝ᵥ yd) t := by
  classical
  have hxi : ∀ i : r, HasDerivAt (fun s => x s i) (xd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hx
  have hyi : ∀ i : r, HasDerivAt (fun s => y s i) (yd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hy
  have hsum : HasDerivAt (fun s => ∑ i : r, x s i * y s i)
      (∑ i : r, (xd i * y t i + x t i * yd i)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact (hxi i).mul (hyi i)
  simpa [dotProduct, Finset.sum_add_distrib] using hsum

private lemma hasDerivAt_mulVec
    {m : Type*} {A : Matrix m r ℝ}
    {x : ℝ → (r → ℝ)} {xd : r → ℝ} {t : ℝ}
    (hx : HasDerivAt x xd t) :
    HasDerivAt (fun s => A *ᵥ x s) (A *ᵥ xd) t := by
  classical
  have hxi : ∀ j : r, HasDerivAt (fun s => x s j) (xd j) t := by
    intro j
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj j)).clm_apply hx
  have hcomp : ∀ i : m,
      HasDerivAt (fun s => (A *ᵥ x s) i) ((A *ᵥ xd) i) t := by
    intro i
    change HasDerivAt (fun s => ∑ j : r, A i j * x s j)
      (∑ j : r, A i j * xd j) t
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hxi j).const_mul (A i j)
  have hf : HasFDerivAt (fun s i => (A *ᵥ x s) i)
      (ContinuousLinearMap.pi
        (fun i => ContinuousLinearMap.toSpanSingleton ℝ ((A *ᵥ xd) i))) t :=
    hasFDerivAt_pi.mpr (fun i => (hcomp i).hasFDerivAt)
  simpa using hf.hasDerivAt

/-- Chain rule for a differentiable attachment map.  The derivative map `J` is
evaluated only at the selected point, so it may change with the rigid
configuration. -/
theorem hasDerivAt_attachment_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : E → F} {q : ℝ → E} {J : E →L[ℝ] F}
    {qdot : E} {t : ℝ}
    (hs : HasFDerivAt s J (q t)) (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun τ => s (q τ)) (J qdot) t := by
  change HasDerivAt (s ∘ q) (J qdot) t
  convert (hs.comp t hq.hasFDerivAt).hasDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one]

/-- The force/velocity power at a rectangular port cancels exactly after the
equal-and-opposite transpose force is used. -/
theorem attachment_port_power_cancel
    (J : Matrix r n ℝ) (lambda : r → ℝ) (qdot : n → ℝ) :
    (Jᵀ *ᵥ lambda) ⬝ᵥ qdot = lambda ⬝ᵥ (J *ᵥ qdot) := by
  rw [mulVec_transpose]
  exact (dotProduct_mulVec lambda J qdot).symm

/-- Derivative of the attachment storage before using the force balance. -/
theorem attachmentStorage_hasDerivAt
    (M K : Matrix r r ℝ) (hM : Mᵀ = M) (hK : Kᵀ = K)
    {u delta : ℝ → (r → ℝ)} {up deltap : r → ℝ} {t : ℝ}
    (hu : HasDerivAt u up t) (hdelta : HasDerivAt delta deltap t) :
    HasDerivAt (fun s => attachmentStorage M K (u s) (delta s))
      (u t ⬝ᵥ M *ᵥ up + delta t ⬝ᵥ K *ᵥ deltap) t := by
  have hMu := hasDerivAt_mulVec (A := M) hu
  have hKdelta := hasDerivAt_mulVec (A := K) hdelta
  have hkin := hasDerivAt_dotProduct hu hMu
  have hpot := hasDerivAt_dotProduct hdelta hKdelta
  have hsum := (hkin.const_mul (1 / 2 : ℝ)).add (hpot.const_mul (1 / 2 : ℝ))
  have hMcross : up ⬝ᵥ M *ᵥ u t = u t ⬝ᵥ M *ᵥ up := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]
  have hKcross : deltap ⬝ᵥ K *ᵥ delta t = delta t ⬝ᵥ K *ᵥ deltap := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hK, dotProduct_comm]
  rw [hMcross, hKcross] at hsum
  have hsum' :
      HasDerivAt (fun s => attachmentStorage M K (u s) (delta s))
        (2⁻¹ * (u t ⬝ᵥ M *ᵥ up + u t ⬝ᵥ M *ᵥ up) +
          2⁻¹ * (delta t ⬝ᵥ K *ᵥ deltap + delta t ⬝ᵥ K *ᵥ deltap)) t := by
    simpa [attachmentStorage] using
      hsum.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun s => by simp [Pi.add_apply]))
  convert hsum' using 1
  ring

/-- Deformation derivative for `delta = eta - s(q)`, with the Jacobian
evaluated at the selected configuration. -/
theorem hasDerivAt_attachment_deformation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {eta : ℝ → F} {q : ℝ → E} {s : E → F}
    {u : F} {qdot : E} {J : E →L[ℝ] F} {t : ℝ}
    (heta : HasDerivAt eta u t)
    (hs : HasFDerivAt s J (q t)) (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun τ => eta τ - s (q τ)) (u - J qdot) t := by
  exact heta.sub (hasDerivAt_attachment_map hs hq)

/-- Actual attachment power identity.  The rigid velocity `w` is related to
the absolute lumped velocity `u` and relative velocity `rel` by
`w = u - rel`; this is the only kinematic relation used by the algebra. -/
theorem elasticAttachment_energy_hasDerivAt
    (M K D : Matrix r r ℝ) (hM : Mᵀ = M) (hK : Kᵀ = K)
    {u delta : ℝ → (r → ℝ)} {up rel : r → ℝ} {lambda f w : r → ℝ} {t : ℝ}
    (hu : HasDerivAt u up t) (hdelta : HasDerivAt delta rel t)
    (hdyn : M *ᵥ up = -lambda + f)
    (hlambda : lambda = attachmentForce K D (delta t) rel)
    (hrel : w = u t - rel) :
    HasDerivAt (fun s => attachmentStorage M K (u s) (delta s))
      (u t ⬝ᵥ f - w ⬝ᵥ lambda - rel ⬝ᵥ D *ᵥ rel) t := by
  have hraw := attachmentStorage_hasDerivAt M K hM hK hu hdelta
  have hKforce : K *ᵥ delta t = lambda - D *ᵥ rel := by
    rw [hlambda, attachmentForce, add_sub_cancel_right]
  have hKcross : delta t ⬝ᵥ K *ᵥ rel = rel ⬝ᵥ K *ᵥ delta t := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hK, dotProduct_comm]
  apply hraw.congr_deriv
  rw [hdyn, hKcross, hKforce, hrel]
  simp only [dotProduct_add, dotProduct_sub, sub_dotProduct, dotProduct_neg]
  ring

/-- Summed storage balance with the rigid layer's power identity supplied as a
local derivative premise.  The internal port power cancels exactly. -/
theorem elasticAttachment_total_balance
    (M K D : Matrix r r ℝ) (hM : Mᵀ = M) (hK : Kᵀ = K)
    {u delta : ℝ → (r → ℝ)} {up rel : r → ℝ} {lambda f w : r → ℝ}
    {V0 : ℝ → ℝ} {d0 p0 : ℝ} {t : ℝ}
    (hu : HasDerivAt u up t) (hdelta : HasDerivAt delta rel t)
    (hdyn : M *ᵥ up = -lambda + f)
    (hlambda : lambda = attachmentForce K D (delta t) rel)
    (hrel : w = u t - rel)
    (hRigid : HasDerivAt V0 (w ⬝ᵥ lambda - d0 + p0) t) :
    HasDerivAt (fun s => attachmentStorage M K (u s) (delta s) + V0 s)
      (u t ⬝ᵥ f + p0 - rel ⬝ᵥ D *ᵥ rel - d0) t := by
  have hElastic := elasticAttachment_energy_hasDerivAt M K D hM hK
    hu hdelta hdyn hlambda hrel
  apply (hElastic.add hRigid).congr_deriv
  ring

/-- The summed balance is bounded by the declared external power when the
attachment damping form and rigid dissipation are nonnegative.  This is a
differential power inequality; it does not assert nonnegativity of the rigid
storage or any convergence property of the coupled plant. -/
theorem elasticAttachment_total_balance_le_external
    (M K D : Matrix r r ℝ) (hM : Mᵀ = M) (hK : Kᵀ = K)
    {u delta : ℝ → (r → ℝ)} {up rel : r → ℝ} {lambda f w : r → ℝ}
    {V0 : ℝ → ℝ} {d0 p0 : ℝ} {t : ℝ}
    (hu : HasDerivAt u up t) (hdelta : HasDerivAt delta rel t)
    (hdyn : M *ᵥ up = -lambda + f)
    (hlambda : lambda = attachmentForce K D (delta t) rel)
    (hrel : w = u t - rel)
    (hRigid : HasDerivAt V0 (w ⬝ᵥ lambda - d0 + p0) t)
    (hD : ∀ z : r → ℝ, 0 ≤ z ⬝ᵥ D *ᵥ z) (hd0 : 0 ≤ d0) :
    HasDerivAt (fun s => attachmentStorage M K (u s) (delta s) + V0 s)
      (u t ⬝ᵥ f + p0 - rel ⬝ᵥ D *ᵥ rel - d0) t ∧
      u t ⬝ᵥ f + p0 - rel ⬝ᵥ D *ᵥ rel - d0 ≤ u t ⬝ᵥ f + p0 := by
  refine ⟨elasticAttachment_total_balance M K D hM hK hu hdelta hdyn hlambda hrel
    hRigid, ?_⟩
  have hDrel := hD rel
  linarith

/-- Derivative-form corollary using the matrix-level positive-semidefinite
damping predicate. -/
theorem elasticAttachment_total_deriv_le_external
    (M K D : Matrix r r ℝ) (hM : Mᵀ = M) (hK : Kᵀ = K)
    {u delta : ℝ → (r → ℝ)} {up rel : r → ℝ} {lambda f w : r → ℝ}
    {V0 : ℝ → ℝ} {d0 p0 : ℝ} {t : ℝ}
    (hu : HasDerivAt u up t) (hdelta : HasDerivAt delta rel t)
    (hdyn : M *ᵥ up = -lambda + f)
    (hlambda : lambda = attachmentForce K D (delta t) rel)
    (hrel : w = u t - rel)
    (hRigid : HasDerivAt V0 (w ⬝ᵥ lambda - d0 + p0) t)
    (hD : D.PosSemidef) (hd0 : 0 ≤ d0) :
    deriv (fun s => attachmentStorage M K (u s) (delta s) + V0 s) t
      ≤ u t ⬝ᵥ f + p0 := by
  have hDq : ∀ z : r → ℝ, 0 ≤ z ⬝ᵥ D *ᵥ z := by
    intro z
    simpa using hD.dotProduct_mulVec_nonneg z
  have h := elasticAttachment_total_balance_le_external M K D hM hK
    hu hdelta hdyn hlambda hrel hRigid hDq hd0
  rw [h.1.deriv]
  exact h.2

/-- Nonnegativity of the attachment storage under positive semidefinite mass and
stiffness matrices. -/
theorem attachmentStorage_nonneg
    (M K : Matrix r r ℝ) (hM : M.PosSemidef) (hK : K.PosSemidef)
    (u delta : r → ℝ) : 0 ≤ attachmentStorage M K u delta := by
  have hMu := hM.dotProduct_mulVec_nonneg u
  have hKdelta := hK.dotProduct_mulVec_nonneg delta
  simpa [attachmentStorage] using
    add_nonneg (mul_nonneg (by norm_num) hMu) (mul_nonneg (by norm_num) hKdelta)

end Ctrllib

#print axioms Ctrllib.hasDerivAt_attachment_map
#print axioms Ctrllib.hasDerivAt_attachment_deformation
#print axioms Ctrllib.attachment_port_power_cancel
#print axioms Ctrllib.attachmentStorage_hasDerivAt
#print axioms Ctrllib.elasticAttachment_energy_hasDerivAt
#print axioms Ctrllib.elasticAttachment_total_balance
#print axioms Ctrllib.elasticAttachment_total_balance_le_external
#print axioms Ctrllib.elasticAttachment_total_deriv_le_external
#print axioms Ctrllib.attachmentStorage_nonneg
