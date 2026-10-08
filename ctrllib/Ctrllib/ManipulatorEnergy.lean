/-
Local mechanical energy identity for a generic finite-dimensional manipulator.

At the selected time, the joint equations are

    M a + C v + g + D v = tau + Jᵀ f.

Here `M` is the instantaneous inertia, `C` the Coriolis matrix, `g` the
conservative potential gradient, `D` the joint damping matrix, and `J` may be
rectangular.  The path-level inertia may vary with time.  The only metric
identity used by the storage derivative is that `Ṁ - 2 C` is skew-symmetric.

This module proves a local calculus identity for supplied derivative witnesses.
It makes no ODE existence, robot-specific, controller, stability, or parameter
claim.  A configuration-dependent inertia `M(q(t))` can be connected to the
path-level hypothesis through `hasDerivAt_inertia_of_configuration`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Ctrllib.Passivity

open Matrix
open scoped BigOperators

namespace Ctrllib

variable {n r : Type*} [Fintype n] [Fintype r]

/- The finite-dimensional mechanical storage.  The final argument is the
   scalar value of the conservative potential at the selected configuration. -/
noncomputable def manipulatorEnergy (M : Matrix n n ℝ) (v : n → ℝ) (potential : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (v ⬝ᵥ M *ᵥ v) + potential

private lemma hasDerivAt_dotProduct
    {x y : ℝ → (n → ℝ)} {xd yd : n → ℝ} {t : ℝ}
    (hx : HasDerivAt x xd t) (hy : HasDerivAt y yd t) :
    HasDerivAt (fun s => x s ⬝ᵥ y s)
      (xd ⬝ᵥ y t + x t ⬝ᵥ yd) t := by
  classical
  have hxi : ∀ i : n, HasDerivAt (fun s => x s i) (xd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hx
  have hyi : ∀ i : n, HasDerivAt (fun s => y s i) (yd i) t := by
    intro i
    simpa using (hasDerivAt_const t (ContinuousLinearMap.proj i)).clm_apply hy
  have hsum : HasDerivAt (fun s => ∑ i : n, x s i * y s i)
      (∑ i : n, (xd i * y t i + x t i * yd i)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    exact (hxi i).mul (hyi i)
  simpa [dotProduct, Finset.sum_add_distrib] using hsum

private lemma hasDerivAt_matrix_mulVec
    {A : ℝ → Matrix n n ℝ} {x : ℝ → (n → ℝ)}
    {Ad : Matrix n n ℝ} {xd : n → ℝ} {t : ℝ}
    (hA : HasDerivAt A Ad t) (hx : HasDerivAt x xd t) :
    HasDerivAt (fun s => A s *ᵥ x s)
      (Ad *ᵥ x t + A t *ᵥ xd) t := by
  classical
  have hAi : ∀ i : n, HasDerivAt (fun s => A s i) (Ad i) t := by
    intro i
    have h := (hasDerivAt_const t
      (ContinuousLinearMap.proj i : (Matrix n n ℝ) →L[ℝ] (n → ℝ))).clm_apply hA
    have hfun :
        (fun s =>
            (ContinuousLinearMap.proj i : (Matrix n n ℝ) →L[ℝ] (n → ℝ)) (A s)) =
          (fun s => A s i) := by
      funext s
      rfl
    rw [hfun] at h
    have hderiv :
        ((0 : (Matrix n n ℝ) →L[ℝ] (n → ℝ)) (A t) +
          (ContinuousLinearMap.proj i : (Matrix n n ℝ) →L[ℝ] (n → ℝ)) Ad) = Ad i := by
      change (0 : n → ℝ) + Ad i = Ad i
      simp
    exact h.congr_deriv hderiv
  have hAij : ∀ i j : n, HasDerivAt (fun s => A s i j) (Ad i j) t := by
    intro i j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ)).clm_apply (hAi i)
  have hxi : ∀ j : n, HasDerivAt (fun s => x s j) (xd j) t := by
    intro j
    simpa [ContinuousLinearMap.proj_apply] using
      (hasDerivAt_const t
        (ContinuousLinearMap.proj j : (n → ℝ) →L[ℝ] ℝ)).clm_apply hx
  apply hasDerivAt_pi.mpr
  intro i
  have hsum : HasDerivAt (fun s => ∑ j : n, A s i j * x s j)
      (∑ j : n, (Ad i j * x t j + A t i j * xd j)) t := by
    apply HasDerivAt.fun_sum
    intro j hj
    exact (hAij i j).mul (hxi j)
  simpa [Matrix.mulVec, dotProduct, Pi.add_apply, Finset.sum_add_distrib] using hsum

/-- Chain rule for a configuration-dependent inertia path `M(q(t))`.

The derivative `DM` is a continuous linear map from configuration space to
matrix space.  This theorem records the exact path-level derivative needed by
the energy theorem; it does not assert that a particular robot has this map. -/
theorem hasDerivAt_inertia_of_configuration
    {Q P : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {I : Q → P} {q : ℝ → Q}
    {DM : Q →L[ℝ] P} {qdot : Q} {t : ℝ}
    (hI : HasFDerivAt I DM (q t)) (hq : HasDerivAt q qdot t) :
    HasDerivAt (fun s => I (q s)) (DM qdot) t := by
  change HasDerivAt (I ∘ q) (DM qdot) t
  convert (hI.comp t hq.hasFDerivAt).hasDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one]

/- A path derivative for the variable-inertia kinetic energy plus a scalar
   potential.  The Frechet derivative witness `L` is identified with the
   gradient vector by `hVgrad`. -/
theorem manipulatorEnergy_path_hasDerivAt
    (M : ℝ → Matrix n n ℝ) (V : (n → ℝ) → ℝ)
    (Mdot : Matrix n n ℝ) (L : (n → ℝ) →L[ℝ] ℝ) (grad : n → ℝ)
    {q v : ℝ → (n → ℝ)} {a : n → ℝ} {t : ℝ}
    (hMdot : HasDerivAt M Mdot t)
    (hMsymm : (M t)ᵀ = M t)
    (hv : HasDerivAt v a t)
    (hq : HasDerivAt q (v t) t)
    (hV : HasFDerivAt V L (q t))
    (hVgrad : ∀ z : n → ℝ, L z = grad ⬝ᵥ z) :
    HasDerivAt (fun s => manipulatorEnergy (M s) (v s) (V (q s)))
      (v t ⬝ᵥ M t *ᵥ a +
        (1 / 2 : ℝ) * (v t ⬝ᵥ Mdot *ᵥ v t) +
        grad ⬝ᵥ v t) t := by
  have hMv := hasDerivAt_matrix_mulVec hMdot hv
  have hkin := hasDerivAt_dotProduct hv hMv
  have hpot0 := (hV.comp t hq.hasFDerivAt).hasDerivAt
  have hpot1 := hpot0.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => rfl))
  have hpotDeriv :
      ((L ∘SL ContinuousLinearMap.toSpanSingleton ℝ (v t)) 1) =
        grad ⬝ᵥ v t := by
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using hVgrad (v t)
  have hpot := hpot1.congr_deriv hpotDeriv
  have hsum :
      HasDerivAt
        (fun s => manipulatorEnergy (M s) (v s) (V (q s)))
        ((1 / 2 : ℝ) *
            (a ⬝ᵥ M t *ᵥ v t +
              v t ⬝ᵥ (Mdot *ᵥ v t + M t *ᵥ a)) +
          grad ⬝ᵥ v t) t := by
    have hsum0 := (hkin.const_mul (1 / 2 : ℝ)).add hpot
    apply hsum0.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s => by
      simp [manipulatorEnergy, Pi.add_apply])
  have hMcross : a ⬝ᵥ M t *ᵥ v t = v t ⬝ᵥ M t *ᵥ a := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hMsymm, dotProduct_comm]
  apply hsum.congr_deriv
  rw [hMcross, dotProduct_add]
  ring

/-- The skew residual turns the variable-inertia quadratic term into the
   Coriolis power term: `½ vᵀ Ṁ v = vᵀ C v`. -/
theorem manipulator_kinetic_skew_identity
    (Mdot C : Matrix n n ℝ) (v : n → ℝ)
    (hskew : (Mdot - 2 • C)ᵀ = -(Mdot - 2 • C)) :
    (1 / 2 : ℝ) * (v ⬝ᵥ Mdot *ᵥ v) = v ⬝ᵥ C *ᵥ v := by
  have hzero := dotProduct_mulVec_self_of_skew hskew v
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul] at hzero
  norm_num at hzero
  linarith

/-- Power identity derived directly by taking the joint-velocity dot product
   of the displayed manipulator dynamics.  The task port is rectangular; its
   transpose pairing is reduced by `mulVec_transpose`, with no inverse or rank
   assumption on `J`. -/
theorem manipulator_power_identity
    (M C D : Matrix n n ℝ) (J : Matrix r n ℝ)
    (a v g tau : n → ℝ) (f : r → ℝ)
    (hdyn : M *ᵥ a + C *ᵥ v + g + D *ᵥ v = tau + Jᵀ *ᵥ f) :
    v ⬝ᵥ M *ᵥ a + v ⬝ᵥ C *ᵥ v + v ⬝ᵥ g =
      v ⬝ᵥ tau + (J *ᵥ v) ⬝ᵥ f - v ⬝ᵥ D *ᵥ v := by
  have hinner := congrArg (fun z : n → ℝ => v ⬝ᵥ z) hdyn
  rw [dotProduct_add, dotProduct_add, dotProduct_add, dotProduct_add] at hinner
  have hport : v ⬝ᵥ Jᵀ *ᵥ f = (J *ᵥ v) ⬝ᵥ f := by
    rw [mulVec_transpose, dotProduct_comm v (f ᵥ* J), ← dotProduct_mulVec]
    exact dotProduct_comm _ _
  rw [hport] at hinner
  linarith

/- The complete local derivative, now using the displayed dynamics rather than
   a supplied rigid-layer power premise. -/
theorem manipulatorEnergy_hasDerivAt
    (M : ℝ → Matrix n n ℝ) (C D : Matrix n n ℝ) (V : (n → ℝ) → ℝ)
    (J : Matrix r n ℝ) (Mdot : Matrix n n ℝ)
    (L : (n → ℝ) →L[ℝ] ℝ) (grad : n → ℝ)
    {q v : ℝ → (n → ℝ)} {a g tau : n → ℝ} {f : r → ℝ} {t : ℝ}
    (hMdot : HasDerivAt M Mdot t)
    (hMsymm : (M t)ᵀ = M t)
    (hv : HasDerivAt v a t)
    (hq : HasDerivAt q (v t) t)
    (hV : HasFDerivAt V L (q t))
    (hVgrad : ∀ z : n → ℝ, L z = grad ⬝ᵥ z)
    (hskew : (Mdot - 2 • C)ᵀ = -(Mdot - 2 • C))
    (hgrad : grad = g)
    (hdyn : M t *ᵥ a + C *ᵥ v t + g + D *ᵥ v t = tau + Jᵀ *ᵥ f) :
    HasDerivAt (fun s => manipulatorEnergy (M s) (v s) (V (q s)))
      (v t ⬝ᵥ tau + (J *ᵥ v t) ⬝ᵥ f - v t ⬝ᵥ D *ᵥ v t) t := by
  have hpath := manipulatorEnergy_path_hasDerivAt M V Mdot L grad
    hMdot hMsymm hv hq hV hVgrad
  have hkin := manipulator_kinetic_skew_identity Mdot C (v t) hskew
  have hpower := manipulator_power_identity (M t) C D J a (v t) g tau f hdyn
  apply hpath.congr_deriv
  rw [hkin, hgrad, dotProduct_comm g (v t)]
  exact hpower

/-- The derivative is bounded by external joint and task-port power under PSD
   joint damping. -/
theorem manipulatorEnergy_deriv_le_power
    (M : ℝ → Matrix n n ℝ) (C D : Matrix n n ℝ) (V : (n → ℝ) → ℝ)
    (J : Matrix r n ℝ) (Mdot : Matrix n n ℝ)
    (L : (n → ℝ) →L[ℝ] ℝ) (grad : n → ℝ)
    {q v : ℝ → (n → ℝ)} {a g tau : n → ℝ} {f : r → ℝ} {t : ℝ}
    (hMdot : HasDerivAt M Mdot t)
    (hMsymm : (M t)ᵀ = M t)
    (hv : HasDerivAt v a t)
    (hq : HasDerivAt q (v t) t)
    (hV : HasFDerivAt V L (q t))
    (hVgrad : ∀ z : n → ℝ, L z = grad ⬝ᵥ z)
    (hskew : (Mdot - 2 • C)ᵀ = -(Mdot - 2 • C))
    (hgrad : grad = g)
    (hdyn : M t *ᵥ a + C *ᵥ v t + g + D *ᵥ v t = tau + Jᵀ *ᵥ f)
    (hD : D.PosSemidef) :
    deriv (fun s => manipulatorEnergy (M s) (v s) (V (q s))) t ≤
      v t ⬝ᵥ tau + (J *ᵥ v t) ⬝ᵥ f := by
  have hderiv := manipulatorEnergy_hasDerivAt M C D V J Mdot L grad
    hMdot hMsymm hv hq hV hVgrad hskew hgrad hdyn
  rw [hderiv.deriv]
  have hDnonneg := hD.dotProduct_mulVec_nonneg (v t)
  have hDnonneg' : 0 ≤ v t ⬝ᵥ D *ᵥ v t := by
    simpa using hDnonneg
  linarith

/-- Storage nonnegativity requires PSD inertia and an explicit lower bound on
   the potential at the selected configuration. -/
theorem manipulatorEnergy_nonneg
    (M : Matrix n n ℝ) (v : n → ℝ) (potential : ℝ)
    (hM : M.PosSemidef) (hPotential : 0 ≤ potential) :
    0 ≤ manipulatorEnergy M v potential := by
  have hMnonneg := hM.dotProduct_mulVec_nonneg v
  simpa [manipulatorEnergy] using
    add_nonneg (mul_nonneg (by norm_num) hMnonneg) hPotential

end Ctrllib

#print axioms Ctrllib.manipulatorEnergy
#print axioms Ctrllib.hasDerivAt_inertia_of_configuration
#print axioms Ctrllib.manipulatorEnergy_path_hasDerivAt
#print axioms Ctrllib.manipulator_kinetic_skew_identity
#print axioms Ctrllib.manipulator_power_identity
#print axioms Ctrllib.manipulatorEnergy_hasDerivAt
#print axioms Ctrllib.manipulatorEnergy_deriv_le_power
#print axioms Ctrllib.manipulatorEnergy_nonneg
