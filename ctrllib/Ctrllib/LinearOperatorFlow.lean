/-
The global flow of a bounded real linear operator, constructed from its
operator exponential. This extracts the reusable construction behind the
existing point-mass flow without changing that public interface.
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Exponential
import Ctrllib.LaSalle

set_option maxSynthPendingDepth 3

namespace Ctrllib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem mem_ball_endomorphism (B : E →L[ℝ] E) :
    B ∈ Metric.eball (0 : E →L[ℝ] E)
      (NormedSpace.expSeries ℝ (E →L[ℝ] E)).radius :=
  (NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _

private theorem endomorphism_exp_continuous :
    Continuous fun B : E →L[ℝ] E => NormedSpace.exp B := by
  rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : E →L[ℝ] E),
    ← NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)]
  exact NormedSpace.continuousOn_exp

/-- The global real-time flow `exp(t A) z`. No sign or stability premise is
needed for its existence. -/
noncomputable def linearOperatorFlow (A : E →L[ℝ] E) : Flow ℝ E where
  toFun t z := NormedSpace.exp (t • A) z
  cont' := by
    have h : Continuous fun p : ℝ × E => NormedSpace.exp (p.1 • A) :=
      endomorphism_exp_continuous.comp (continuous_fst.smul continuous_const)
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E)).continuous.comp
      (h.prodMk continuous_snd)
  map_add' s t z := by
    have hcomm : Commute (s • A) (t • A) :=
      ((Commute.refl A).smul_left s).smul_right t
    change NormedSpace.exp ((s + t) • A) z = _
    rw [add_smul, NormedSpace.exp_add_of_commute_of_mem_ball hcomm
      (mem_ball_endomorphism _) (mem_ball_endomorphism _),
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  map_zero' z := by
    change NormedSpace.exp ((0 : ℝ) • A) z = z
    rw [zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply]

/-- The exponential flow solves the linear differential equation `z' = A z`. -/
theorem linearOperatorFlow_hasDerivAt (A : E →L[ℝ] E) (z : E) (t : ℝ) :
    HasDerivAt (fun s => linearOperatorFlow A s z)
      (A (linearOperatorFlow A t z)) t := by
  have h := (ContinuousLinearMap.apply ℝ E z).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  simp only [ContinuousLinearMap.apply_apply] at h
  rwa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at h

/-- The concrete flow discharges the library's solution interface. -/
theorem linearOperatorFlow_isSolutionTo (A : E →L[ℝ] E) :
    IsSolutionTo (linearOperatorFlow A) A :=
  linearOperatorFlow_hasDerivAt A

end Ctrllib

#print axioms Ctrllib.linearOperatorFlow
#print axioms Ctrllib.linearOperatorFlow_hasDerivAt
#print axioms Ctrllib.linearOperatorFlow_isSolutionTo
