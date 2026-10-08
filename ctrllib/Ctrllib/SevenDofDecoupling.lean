/-
Arc 7 — P1: the augmented inertia decouples the self-motion coordinate (ctrllib).

Ground: the corresponding local note §4b–c ("Proved above"; the HARD HALF
of proof obligation P1). Companion to the sealed `SevenDof.lean` (P3 passivity, P4
null-space damping), which this imports and extends. SymPy/NumPy-pinned BEFORE formalizing:
the corresponding local note (10/10), each test citing the
doc section it checks.

The augmented transformation is SQUARE: `Γ_a = [Γ; z_aᵀ] ∈ ℝ^{13×13}`, invertible on the
singularity-free region Ω, with `z_aᵀ = k̂ᵀM / (k̂ᵀM k̂)` the inertia-weighted (dynamically
consistent, Khatib) covector. The transformed inertia is the congruence `M̂ = Γ_a⁻ᵀ M Γ_a⁻¹`
(kinetic energy is invariant under a change of velocity coordinates). §4b–c: `M̂` is
BLOCK-DIAGONAL — the self-motion coordinate `v_n` decouples from the 12 task coordinates.

This module works over the abstract congruence data `(G, P, M)` with `P` the two-sided
inverse of `G = Γ_a` (`P = Γ_a⁻¹`, its right-inverse property `G*P = 1` is all that is used
below), `M` symmetric, and the self-motion index `j` fixing the appended coordinate. Writing
`eₙ := Pi.single j 1` and `k̂ := P *ᵥ eₙ` (the last inverse column, `c₁₃`), the construction
fact is `hrow : denom • (Gᵀ *ᵥ eₙ) = M *ᵥ k̂` — "row j of `G`, scaled by `denom`, is `M k̂`",
i.e. `z_aᵀ = k̂ᵀM/denom` (test_M_maps_khat_to_za_symbolic, the §4b algebraic bridge). Here
`denom = k̂ᵀM k̂ = m̂_n` (`selfmotion_inertia_eq_denom`). No `Matrix.inv` machinery is used —
the invertibility of `Γ_a` on Ω enters only as the abstract `G*P = 1`, exactly the ring-level
discipline of the sealed passivity theorems (`inv_deriv_eq` takes its inverse as a hypothesis).

Results (all INTERFACE-FREE — the hypotheses are the definitional givens of a congruence
transform + the construction of `z_a`, not un-formalized analysis facts):
  * `gamma_a_khat_eq`            — `Γ_a k̂ = eₙ` (test: c₁₃ = k̂; `Γ k̂ = 0` ∧ `z_aᵀk̂ = 1`).
  * `mhat_symm`                  — `M̂` is symmetric (congruence of a symmetric matrix).
  * `mhat_selfmotion_column`     — `M̂ *ᵥ eₙ = denom • eₙ`: the task←self coupling column
                                   vanishes and the diagonal entry is `denom` (§4c, P1 hard half).
  * `mhat_selfmotion_row`        — `eₙ ᵥ* M̂ = denom • eₙ`: the self←task coupling row vanishes.
  * `task_M_orthogonal`          — every task velocity is `M`-orthogonal to the self-motion:
                                   `eₙ ⬝ᵥ (G *ᵥ c) = 0 → k̂ ⬝ᵥ (M *ᵥ c) = 0` (§4b).
  * `selfmotion_inertia_eq_denom`— `k̂ᵀM k̂ = denom` (the scalar self-motion inertia `m̂_n`).
  * `selfmotion_inertia_pos` (ℝ)— `0 < k̂ᵀM k̂` for `M` positive definite (`m̂_n > 0`, §4c).

Honest boundary (from the derivation doc §6, P1 row: "Remaining: relate the task block to
the old M̆"): the residual §4c BOOKKEEPING — identifying the 12×12 task block `M̂_task` with
the nonredundant `M̆` — is NOT proved here; the doc itself lists it as remaining. What is
sealed is the block-diagonal STRUCTURE (the self-motion row/column decouple), which is the
hard half the doc marks "Proved above".

Human derivation: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet) · pin `the corresponding private check`
-/
import Ctrllib.SevenDof
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace Ctrllib

-- `DecidableEq n` is used in the proofs (identity matrix / `Pi.single`) but does not surface
-- in every statement; silence the in-type linter, same pattern as `PassivityTransport`.
set_option linter.unusedDecidableInType false

section Decoupling

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]
variable {M G P : Matrix n n R} {khat : n → R} {denom : R} {j : n}

/-- **`Γ_a k̂ = eₙ`** (test_gamma_a_khat_is_last_basis / c₁₃ = k̂). With `k̂ = P *ᵥ eₙ` the last
column of the inverse and `P` a right inverse of `G = Γ_a`, applying `G` returns the basis
vector: `Γ k̂ = 0` and `z_aᵀ k̂ = 1` packed into `Γ_a k̂ = eₙ`. -/
theorem gamma_a_khat_eq (hGP : G * P = 1) (hkhat : khat = P *ᵥ Pi.single j 1) :
    G *ᵥ khat = Pi.single j (1 : R) := by
  rw [hkhat, mulVec_mulVec, hGP, one_mulVec]

omit [DecidableEq n] in
/-- **`M̂` is symmetric.** The congruence `M̂ = Pᵀ M P` of a symmetric `M` (`Mᵀ = M`) is again
symmetric — the fact that lets the vanishing self-motion column give the vanishing row too. -/
theorem mhat_symm (hMsymm : Mᵀ = M) : (Pᵀ * M * P)ᵀ = Pᵀ * M * P := by
  rw [transpose_mul, transpose_mul, transpose_transpose, hMsymm, mul_assoc]

/-- **P1 hard half — the self-motion column of `M̂` decouples** (§4c, test_block_diagonal_
inertia_numeric). `M̂ *ᵥ eₙ = denom • eₙ`: the task←self coupling block (entries `i ≤ 12`,
column 13) vanishes and the diagonal self-motion inertia is `denom = m̂_n`. Route (the doc's
forward argument): `M̂ eₙ = Pᵀ M (P eₙ) = Pᵀ M k̂ = denom · Pᵀ(Gᵀ eₙ) = denom · (G P)ᵀ eₙ
= denom · eₙ`, using `hrow` and `G P = 1`. Symmetry is not needed here. -/
theorem mhat_selfmotion_column (hGP : G * P = 1) (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    (Pᵀ * M * P) *ᵥ Pi.single j 1 = denom • Pi.single j (1 : R) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← hkhat, ← hrow, mulVec_smul, mulVec_mulVec,
    ← transpose_mul, hGP, transpose_one, one_mulVec]

/-- **The self-motion row of `M̂` decouples.** `eₙ ᵥ* M̂ = denom • eₙ`: the self←task coupling
block (row 13, columns `i ≤ 12`) vanishes. Immediate from the column result and `mhat_symm`
(`eₙ ᵥ* M̂ = M̂ᵀ *ᵥ eₙ = M̂ *ᵥ eₙ`). -/
theorem mhat_selfmotion_row (hGP : G * P = 1) (hMsymm : Mᵀ = M)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    Pi.single j (1 : R) ᵥ* (Pᵀ * M * P) = denom • Pi.single j (1 : R) := by
  rw [← mulVec_transpose, mhat_symm hMsymm]
  exact mhat_selfmotion_column hGP hkhat hrow

/-- **Every task velocity is `M`-orthogonal to the self-motion** (§4b, test_M_orthogonality_
numeric). This is what turns the tautological `z_aᵀ c_i = 0` (row 13 of `Γ_a Γ_a⁻¹ = E`) into
the physical statement: if `c` reads zero under the appended covector — `eₙ ⬝ᵥ (G c) = 0`,
i.e. `z_aᵀ c = 0` — then `k̂ᵀ M c = 0`. Uses `hrow` and symmetry of `M`. -/
theorem task_M_orthogonal (hMsymm : Mᵀ = M)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat)
    (c : n → R) (hc : Pi.single j (1 : R) ⬝ᵥ (G *ᵥ c) = 0) :
    khat ⬝ᵥ (M *ᵥ c) = 0 := by
  have h1 : khat ⬝ᵥ (M *ᵥ c) = (M *ᵥ khat) ⬝ᵥ c := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hMsymm]
  rw [h1, ← hrow, smul_dotProduct, mulVec_transpose, ← dotProduct_mulVec, hc, smul_zero]

/-- **The scalar self-motion inertia is `denom`.** `m̂_n = k̂ᵀ M k̂ = denom` — the `(13,13)`
entry of the block-diagonal `M̂`, twice the kinetic energy of the self-motion at unit
amplitude. Pins the abstract scale in `hrow` to the physical quantity, via `z_aᵀ k̂ = 1`. -/
theorem selfmotion_inertia_eq_denom (hGP : G * P = 1) (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    khat ⬝ᵥ (M *ᵥ khat) = denom := by
  calc khat ⬝ᵥ (M *ᵥ khat)
      = khat ⬝ᵥ (denom • (Gᵀ *ᵥ Pi.single j 1)) := by rw [← hrow]
    _ = denom • (khat ⬝ᵥ (Gᵀ *ᵥ Pi.single j 1)) := by rw [dotProduct_smul]
    _ = denom • ((Gᵀ *ᵥ Pi.single j 1) ⬝ᵥ khat) := by rw [dotProduct_comm]
    _ = denom • (Pi.single j (1 : R) ⬝ᵥ (G *ᵥ khat)) := by
          rw [mulVec_transpose, ← dotProduct_mulVec]
    _ = denom • (Pi.single j (1 : R) ⬝ᵥ Pi.single j 1) := by rw [gamma_a_khat_eq hGP hkhat]
    _ = denom := by rw [single_dotProduct, Pi.single_eq_same, mul_one, smul_eq_mul, mul_one]

end Decoupling

section RealPositive

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {M G P : Matrix n n ℝ} {khat : n → ℝ} {j : n}

/-- **`m̂_n > 0`** (§4c, test_za_denominator_positive_numeric). The scalar self-motion inertia
`k̂ᵀ M k̂` is strictly positive: `M` positive definite and `k̂ ≠ 0` (from `Γ_a k̂ = eₙ ≠ 0`), so
`z_a` is well posed and `M̂`'s self-motion block is nondegenerate. -/
theorem selfmotion_inertia_pos (hpd : M.PosDef) (hGP : G * P = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1) :
    0 < khat ⬝ᵥ (M *ᵥ khat) := by
  have hk0 : khat ≠ 0 := by
    intro h
    have hg : G *ᵥ khat = Pi.single j (1 : ℝ) := gamma_a_khat_eq hGP hkhat
    rw [h, mulVec_zero] at hg
    have hj := congrFun hg j
    rw [Pi.zero_apply, Pi.single_eq_same] at hj
    exact one_ne_zero hj.symm
  simpa using hpd.dotProduct_mulVec_pos hk0

end RealPositive

end Ctrllib

#print axioms Ctrllib.gamma_a_khat_eq
#print axioms Ctrllib.mhat_symm
#print axioms Ctrllib.mhat_selfmotion_column
#print axioms Ctrllib.mhat_selfmotion_row
#print axioms Ctrllib.task_M_orthogonal
#print axioms Ctrllib.selfmotion_inertia_eq_denom
#print axioms Ctrllib.selfmotion_inertia_pos
