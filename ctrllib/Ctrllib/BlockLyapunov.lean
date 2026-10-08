/-
Block Lyapunov admissibility (TARGET 20 of the ctrllib stream) — the
*candidate-admissibility* leg the thesis states without proof.

The framing paper's storage function (giordano2019coordinated eq 37;
the source model note §4.6 eq 4.15) is the sum of two quadratic forms

    V(v, x) = ½ vᵀ M v + ½ xᵀ K x ,     M ≻ 0 , K ≻ 0

with `M = M̆` the reduced inertia and `K = K̆` the block-diagonal stiffness.
For `V` to be a valid Lyapunov candidate it must be **positive-definite**
(`V ≥ 0`, and `V = 0` only at the origin) and **radially unbounded / coercive**
(a positive constant `c₁` with `c₁(‖v‖² + ‖x‖²) ≤ V`, so `V → ∞` with the
state). This file seals exactly that, as a *direct instance of the Rayleigh
sandwich* (Ctrllib.Rayleigh, TARGET 4) applied to each block and summed —
no `fromBlocks` single-matrix detour, because eq 4.15 is literally the sum.

The quantity `v ⬝ᵥ v + x ⬝ᵥ x` IS the squared Euclidean norm of the stacked
state `(v, x)`; it is written transparently so no `WithLp`/product-norm
bookkeeping is needed (see the ).

SymPy/numeric pin: the corresponding symbolic check (not bundled).py (4000 random SPD 9×9
blocks + the symbolic min/max collapse identity).
Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.Matrix.PosDef
import Ctrllib.Rayleigh

open Matrix

-- The eigenvalue machinery (`IsHermitian.eigenvalues`, `PosDef.eigenvalues_pos`)
-- needs `DecidableEq` in the *proofs*; it does not surface in the statements, so
-- silence the in-type linter rather than drop a genuinely-used instance.
set_option linter.unusedDecidableInType false

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  {M : Matrix n n ℝ} {K : Matrix m m ℝ}

/-- The block Lyapunov value `V(v,x) = ½ vᵀ M v + ½ xᵀ K x`
(giordano2019coordinated eq 37; the source model note eq 4.15). -/
noncomputable def blockLyap (M : Matrix n n ℝ) (K : Matrix m m ℝ) (v : n → ℝ) (x : m → ℝ) : ℝ :=
  (1 / 2) * (v ⬝ᵥ M *ᵥ v) + (1 / 2) * (x ⬝ᵥ K *ᵥ x)

/-- A real vector's self dot product is nonnegative: `0 ≤ v ⬝ᵥ v` (`= ‖v‖²`). -/
private lemma dp_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **Additive lower bound.** Per-block Rayleigh lower bounds, summed. -/
private lemma blockLyap_lower (hM : M.IsHermitian) (hK : K.IsHermitian)
    {aM aK : ℝ} (hM1 : ∀ i, aM ≤ hM.eigenvalues i) (hK1 : ∀ i, aK ≤ hK.eigenvalues i)
    (v : n → ℝ) (x : m → ℝ) :
    (1 / 2) * (aM * (v ⬝ᵥ v)) + (1 / 2) * (aK * (x ⬝ᵥ x)) ≤ blockLyap M K v x := by
  have hv := le_dotProduct_mulVec hM hM1 v
  have hx := le_dotProduct_mulVec hK hK1 x
  simp only [blockLyap]
  linarith

/-- **Additive upper bound.** Per-block Rayleigh upper bounds, summed. -/
private lemma blockLyap_upper (hM : M.IsHermitian) (hK : K.IsHermitian)
    {bM bK : ℝ} (hM2 : ∀ i, hM.eigenvalues i ≤ bM) (hK2 : ∀ i, hK.eigenvalues i ≤ bK)
    (v : n → ℝ) (x : m → ℝ) :
    blockLyap M K v x ≤ (1 / 2) * (bM * (v ⬝ᵥ v)) + (1 / 2) * (bK * (x ⬝ᵥ x)) := by
  have hv := dotProduct_mulVec_le hM hM2 v
  have hx := dotProduct_mulVec_le hK hK2 x
  simp only [blockLyap]
  linarith

/-- **Block Rayleigh sandwich.** With uniform eigenvalue bounds `aM ≤ λᵢ(M) ≤ bM`
and `aK ≤ λᵢ(K) ≤ bK`, the block Lyapunov value is trapped between the two
weighted squared norms. The engine underneath admissibility. -/
theorem blockLyap_sandwich (hM : M.IsHermitian) (hK : K.IsHermitian)
    {aM bM aK bK : ℝ}
    (hM1 : ∀ i, aM ≤ hM.eigenvalues i) (hM2 : ∀ i, hM.eigenvalues i ≤ bM)
    (hK1 : ∀ i, aK ≤ hK.eigenvalues i) (hK2 : ∀ i, hK.eigenvalues i ≤ bK)
    (v : n → ℝ) (x : m → ℝ) :
    (1 / 2) * (aM * (v ⬝ᵥ v)) + (1 / 2) * (aK * (x ⬝ᵥ x)) ≤ blockLyap M K v x
      ∧ blockLyap M K v x ≤ (1 / 2) * (bM * (v ⬝ᵥ v)) + (1 / 2) * (bK * (x ⬝ᵥ x)) :=
  ⟨blockLyap_lower hM hK hM1 hK1 v x, blockLyap_upper hM hK hM2 hK2 v x⟩

/-- **Coercivity / radial unboundedness.** For `M, K` positive-definite there is a
strictly positive `c₁` with `c₁(v ⬝ᵥ v + x ⬝ᵥ x) ≤ V(v,x)`; since `v ⬝ᵥ v + x ⬝ᵥ x`
is the squared norm of the stacked state, `V → ∞` as the state grows. The
constant is `½ min(λ_min M, λ_min K)`. -/
theorem blockLyap_coercive [Nonempty n] [Nonempty m]
    (hM : M.PosDef) (hK : K.PosDef) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (v : n → ℝ) (x : m → ℝ),
      c₁ * (v ⬝ᵥ v + x ⬝ᵥ x) ≤ blockLyap M K v x := by
  set aM := Finset.univ.inf' Finset.univ_nonempty hM.isHermitian.eigenvalues with haM_def
  set aK := Finset.univ.inf' Finset.univ_nonempty hK.isHermitian.eigenvalues with haK_def
  have hMinf : ∀ i, aM ≤ hM.isHermitian.eigenvalues i :=
    fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hKinf : ∀ i, aK ≤ hK.isHermitian.eigenvalues i :=
    fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have haM : 0 < aM := by
    rw [haM_def, Finset.lt_inf'_iff]
    exact fun i _ => hM.eigenvalues_pos i
  have haK : 0 < aK := by
    rw [haK_def, Finset.lt_inf'_iff]
    exact fun i _ => hK.eigenvalues_pos i
  refine ⟨(1 / 2) * min aM aK, by have := lt_min haM haK; linarith, ?_⟩
  intro v x
  have lower := blockLyap_lower hM.isHermitian hK.isHermitian hMinf hKinf v x
  have hp := dp_self_nonneg v
  have hq := dp_self_nonneg x
  have h1 : min aM aK * (v ⬝ᵥ v) ≤ aM * (v ⬝ᵥ v) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hp
  have h2 : min aM aK * (x ⬝ᵥ x) ≤ aK * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) hq
  nlinarith [lower, h1, h2]

/-- **Nonnegativity** — `V ≥ 0` everywhere (the weak half of positive-definiteness). -/
theorem blockLyap_nonneg [Nonempty n] [Nonempty m]
    (hM : M.PosDef) (hK : K.PosDef) (v : n → ℝ) (x : m → ℝ) :
    0 ≤ blockLyap M K v x := by
  obtain ⟨c₁, hc₁, hbound⟩ := blockLyap_coercive hM hK
  have hp := dp_self_nonneg v
  have hq := dp_self_nonneg x
  have : 0 ≤ c₁ * (v ⬝ᵥ v + x ⬝ᵥ x) := mul_nonneg hc₁.le (by linarith)
  linarith [hbound v x]

/-- **Positive-definiteness.** `V(v,x) = 0` exactly at the origin `v = 0 ∧ x = 0`;
with `blockLyap_nonneg` this is the Lyapunov positive-definite property
(`V(0)=0`, `V > 0` off the origin). -/
theorem blockLyap_eq_zero_iff [Nonempty n] [Nonempty m]
    (hM : M.PosDef) (hK : K.PosDef) (v : n → ℝ) (x : m → ℝ) :
    blockLyap M K v x = 0 ↔ v = 0 ∧ x = 0 := by
  constructor
  · intro h
    obtain ⟨c₁, hc₁, hbound⟩ := blockLyap_coercive hM hK
    have hb := hbound v x
    rw [h] at hb
    have hp := dp_self_nonneg v
    have hq := dp_self_nonneg x
    have hsum : v ⬝ᵥ v + x ⬝ᵥ x ≤ 0 := by
      by_contra hcon
      exact absurd hb (not_le.mpr (mul_pos hc₁ (not_le.mp hcon)))
    have hpz : v ⬝ᵥ v = 0 := by linarith
    have hqz : x ⬝ᵥ x = 0 := by linarith
    exact ⟨dotProduct_self_eq_zero.mp hpz, dotProduct_self_eq_zero.mp hqz⟩
  · rintro ⟨rfl, rfl⟩
    simp [blockLyap]

end Ctrllib

#print axioms Ctrllib.blockLyap_sandwich
#print axioms Ctrllib.blockLyap_coercive
#print axioms Ctrllib.blockLyap_nonneg
#print axioms Ctrllib.blockLyap_eq_zero_iff
