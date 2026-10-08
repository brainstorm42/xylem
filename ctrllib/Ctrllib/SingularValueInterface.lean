import Ctrllib.SigmaMinDet
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Matrix Module Function WithLp LinearMap

namespace Ctrllib

/-! ## Square Euclidean smallest-singular-value interface -/

/-- The last of the `n` Euclidean singular values of an `n × n` real matrix.
The explicit positivity hypothesis on `n` is carried by the theorems using this
definition; at `n = 0` the index convention is intentionally not interpreted. -/
noncomputable def sigmaMinSquareEuclid {n : ℕ}
    (J : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (Matrix.toEuclideanLin J).singularValues (n - 1)

/-- The generic square convention specializes definitionally to the registered
six-dimensional `sigmaMinEuclid`. -/
theorem sigmaMinSquareEuclid_fin6_eq (J : Matrix (Fin 6) (Fin 6) ℝ) :
    sigmaMinSquareEuclid J = sigmaMinEuclid J := by
  rfl

/-- For a nonempty square Euclidean matrix, the last singular value is positive
exactly when the matrix is nonsingular.  This is the dimension-generic version
of `sigmaMinEuclid_pos_iff_det_ne_zero`. -/
theorem sigmaMinSquareEuclid_pos_iff_det_ne_zero {n : ℕ} (hn : 0 < n)
    (J : Matrix (Fin n) (Fin n) ℝ) :
    0 < sigmaMinSquareEuclid J ↔ J.det ≠ 0 := by
  rw [sigmaMinSquareEuclid]
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hlast : n - 1 < n := Nat.sub_lt hn (by norm_num)
  have hinj : 0 < (Matrix.toEuclideanLin J).singularValues (n - 1)
      ↔ Function.Injective (Matrix.toEuclideanLin J) := by
    rw [injective_iff_forall_lt_finrank_singularValues_pos, hfr]
    constructor
    · intro h i hi
      exact lt_of_lt_of_le h
        ((Matrix.toEuclideanLin J).singularValues_antitone
          (Nat.le_sub_one_of_lt hi))
    · intro h
      exact h (n - 1) hlast
  rw [hinj, injective_iff_map_eq_zero]
  rw [ne_eq, ← exists_mulVec_eq_zero_iff (M := J)]
  constructor
  · intro h
    rintro ⟨v, hv, hJv⟩
    apply hv
    have h0 : Matrix.toEuclideanLin J (toLp _ v) = 0 := by
      rw [toLpLin_apply]
      simp [hJv]
    simpa using h (toLp _ v) h0
  · intro h a ha
    by_contra hane
    exact h ⟨ofLp a, by simpa using hane,
      by rw [toLpLin_apply] at ha; simpa using ha⟩

/-- Nonzero uniform scaling preserves the square singularity decision.  This
does not claim a numerical scaling law for the singular value. -/
theorem sigmaMinSquareEuclid_smul_pos_iff {n : ℕ} (hn : 0 < n)
    (c : ℝ) (hc : c ≠ 0) (J : Matrix (Fin n) (Fin n) ℝ) :
    0 < sigmaMinSquareEuclid (c • J) ↔ 0 < sigmaMinSquareEuclid J := by
  rw [sigmaMinSquareEuclid_pos_iff_det_ne_zero hn,
    sigmaMinSquareEuclid_pos_iff_det_ne_zero hn, Matrix.det_smul]
  simp [hc]

/-- Nonzero uniform scaling preserves the matrix-vector kernel. -/
theorem smul_mulVec_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n]
    (c : ℝ) (hc : c ≠ 0) (J : Matrix m n ℝ) (x : n → ℝ) :
    (c • J) *ᵥ x = 0 ↔ J *ᵥ x = 0 := by
  simp [Matrix.smul_mulVec, hc]

/-! ## Coordinated-transform lower-gain comparison -/

/-- `s` is a Euclidean lower gain bound for `M`.  This predicate avoids
pretending that Mathlib already packages the variational characterization of a
matrix singular value. -/
def IsEuclideanLowerGainBound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n]
    (M : Matrix m n ℝ) (s : ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ n,
    s * ‖x‖ ≤ ‖Matrix.toEuclideanLin M x‖

/-- A least Euclidean gain is a lower bound that dominates every other lower
bound.  The definition is deliberately independent of any robot model. -/
def IsLeastEuclideanGain {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n]
    (M : Matrix m n ℝ) (s : ℝ) : Prop :=
  IsEuclideanLowerGainBound M s ∧
    ∀ t, IsEuclideanLowerGainBound M t → t ≤ s

/-- The exact witness interface needed to compare a larger coordinated map
`Gamma` with a task map `J`: every task input has a coordinated preimage whose
norm is no smaller and whose output norm is exactly the task output norm.

The registered block construction still has to discharge this interface from
its concrete frame convention.  Keeping that obligation explicit prevents an
unproved block-cancellation argument from entering the theorem. -/
structure EuclideanGainComparison
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q]
    (Gamma : Matrix m n ℝ) (J : Matrix p q ℝ) where
  embed : EuclideanSpace ℝ q → EuclideanSpace ℝ n
  norm_le : ∀ y, ‖y‖ ≤ ‖embed y‖
  action_norm_eq : ∀ y,
    ‖Matrix.toEuclideanLin Gamma (embed y)‖ = ‖Matrix.toEuclideanLin J y‖

/-- A nonnegative lower gain bound transfers from `Gamma` to `J` whenever the
registered comparison witness has been supplied. -/
theorem lowerGainBound_of_comparison
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q]
    {Gamma : Matrix m n ℝ} {J : Matrix p q ℝ}
    (comparison : EuclideanGainComparison Gamma J)
    {s : ℝ} (hs : 0 ≤ s)
    (hGamma : IsEuclideanLowerGainBound Gamma s) :
    IsEuclideanLowerGainBound J s := by
  intro y
  calc
    s * ‖y‖ ≤ s * ‖comparison.embed y‖ :=
      mul_le_mul_of_nonneg_left (comparison.norm_le y) hs
    _ ≤ ‖Matrix.toEuclideanLin Gamma (comparison.embed y)‖ := hGamma _
    _ = ‖Matrix.toEuclideanLin J y‖ := comparison.action_norm_eq y

/-- Consequently, whenever both reported values have been connected to the
variational least-gain interface, the coordinated value cannot exceed the task
block value. -/
theorem leastGain_le_of_comparison
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    [DecidableEq n] [DecidableEq q]
    {Gamma : Matrix m n ℝ} {J : Matrix p q ℝ}
    (comparison : EuclideanGainComparison Gamma J)
    {sΓ sJ : ℝ} (hsΓ : 0 ≤ sΓ)
    (hΓ : IsLeastEuclideanGain Gamma sΓ)
    (hJ : IsLeastEuclideanGain J sJ) :
    sΓ ≤ sJ :=
  hJ.2 sΓ (lowerGainBound_of_comparison comparison hsΓ hΓ.1)

/-! ## Six-by-seven row-rank and null-direction interface -/

/-- The sixth (zero-indexed position five) singular value of a `6 × 7` map. -/
noncomputable def sigmaSixEuclid (J : Matrix (Fin 6) (Fin 7) ℝ) : ℝ :=
  (Matrix.toEuclideanLin J).singularValues 5

/-- Positivity of `sigmaSixEuclid` is exactly full row rank. -/
theorem sigmaSixEuclid_pos_iff_finrank_range_eq_six
    (J : Matrix (Fin 6) (Fin 7) ℝ) :
    0 < sigmaSixEuclid J ↔
      finrank ℝ (Matrix.toEuclideanLin J).range = 6 := by
  rw [sigmaSixEuclid, LinearMap.singularValues_pos_iff_lt_finrank_range]
  have hrange : finrank ℝ (Matrix.toEuclideanLin J).range ≤ 6 := by
    calc
      finrank ℝ (Matrix.toEuclideanLin J).range
          ≤ finrank ℝ (EuclideanSpace ℝ (Fin 6)) := Submodule.finrank_le _
      _ = 6 := finrank_euclideanSpace_fin
  omega

/-- Full sixth-singular-value authority leaves exactly one algebraic null
degree of freedom in a `6 × 7` task map. -/
theorem sigmaSixEuclid_pos_implies_finrank_ker_eq_one
    (J : Matrix (Fin 6) (Fin 7) ℝ) (hσ : 0 < sigmaSixEuclid J) :
    finrank ℝ (Matrix.toEuclideanLin J).ker = 1 := by
  have hrange : finrank ℝ (Matrix.toEuclideanLin J).range = 6 :=
    (sigmaSixEuclid_pos_iff_finrank_range_eq_six J).mp hσ
  have hrn := (Matrix.toEuclideanLin J).finrank_range_add_finrank_ker
  rw [finrank_euclideanSpace_fin, hrange] at hrn
  omega

/-- Positive sixth singular value guarantees that a nonzero null direction
exists.  The theorem is pointwise: it does not choose that direction
continuously as the matrix varies. -/
theorem sigmaSixEuclid_pos_implies_exists_nonzero_kernel
    (J : Matrix (Fin 6) (Fin 7) ℝ) (hσ : 0 < sigmaSixEuclid J) :
    ∃ k : EuclideanSpace ℝ (Fin 7),
      Matrix.toEuclideanLin J k = 0 ∧ k ≠ 0 := by
  have hdim : finrank ℝ (Matrix.toEuclideanLin J).ker = 1 :=
    sigmaSixEuclid_pos_implies_finrank_ker_eq_one J hσ
  have hne : (Matrix.toEuclideanLin J).ker ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨k, hkmem, hk⟩ :=
    (Submodule.ne_bot_iff (Matrix.toEuclideanLin J).ker).mp hne
  exact ⟨k, hkmem, hk⟩

/-- A concrete nonzero kernel vector spans the entire null line once
`sigmaSixEuclid` is positive. -/
theorem sigmaSixEuclid_kernel_spanned_by
    (J : Matrix (Fin 6) (Fin 7) ℝ) (hσ : 0 < sigmaSixEuclid J)
    (k : EuclideanSpace ℝ (Fin 7))
    (hk0 : Matrix.toEuclideanLin J k = 0) (hk : k ≠ 0) :
    ∀ x : EuclideanSpace ℝ (Fin 7), Matrix.toEuclideanLin J x = 0 →
      ∃ c : ℝ, c • k = x := by
  have hdim : finrank ℝ (Matrix.toEuclideanLin J).ker = 1 :=
    sigmaSixEuclid_pos_implies_finrank_ker_eq_one J hσ
  let k' : (Matrix.toEuclideanLin J).ker := ⟨k, hk0⟩
  have hk' : k' ≠ 0 := by
    intro h
    apply hk
    exact Subtype.ext_iff.mp h
  intro x hx
  let x' : (Matrix.toEuclideanLin J).ker := ⟨x, hx⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hk' x'
  exact ⟨c, congrArg Subtype.val hc⟩

/-- Uniform nonzero scaling preserves the full-row-rank decision for a `6 × 7`
map.  As above, this is a zero-set statement, not a numerical scaling formula. -/
theorem sigmaSixEuclid_smul_pos_iff (c : ℝ) (hc : c ≠ 0)
    (J : Matrix (Fin 6) (Fin 7) ℝ) :
    0 < sigmaSixEuclid (c • J) ↔ 0 < sigmaSixEuclid J := by
  rw [sigmaSixEuclid_pos_iff_finrank_range_eq_six,
    sigmaSixEuclid_pos_iff_finrank_range_eq_six]
  have hker : (Matrix.toEuclideanLin (c • J)).ker =
      (Matrix.toEuclideanLin J).ker := by
    ext x
    simp only [LinearMap.mem_ker]
    rw [toLpLin_apply, toLpLin_apply]
    simp only [WithLp.toLp_eq_zero]
    exact smul_mulVec_eq_zero_iff c hc J (WithLp.ofLp x)
  have hA := (Matrix.toEuclideanLin (c • J)).finrank_range_add_finrank_ker
  have hJ := (Matrix.toEuclideanLin J).finrank_range_add_finrank_ker
  rw [hker] at hA
  omega

end Ctrllib

#print axioms Ctrllib.sigmaMinSquareEuclid_pos_iff_det_ne_zero
#print axioms Ctrllib.sigmaMinSquareEuclid_smul_pos_iff
#print axioms Ctrllib.smul_mulVec_eq_zero_iff
#print axioms Ctrllib.lowerGainBound_of_comparison
#print axioms Ctrllib.leastGain_le_of_comparison
#print axioms Ctrllib.sigmaSixEuclid_pos_iff_finrank_range_eq_six
#print axioms Ctrllib.sigmaSixEuclid_pos_implies_finrank_ker_eq_one
#print axioms Ctrllib.sigmaSixEuclid_pos_implies_exists_nonzero_kernel
#print axioms Ctrllib.sigmaSixEuclid_kernel_spanned_by
#print axioms Ctrllib.sigmaSixEuclid_smul_pos_iff
