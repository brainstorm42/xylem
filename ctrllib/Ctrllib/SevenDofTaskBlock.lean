/-
Arc 7 — the §4c task-block identification: `M̂_task` IS the operational-space inertia
(ctrllib).

Ground: the corresponding local note §4c/§6, the P1 row's own residual —
"Remaining: relate the task block to the old M̆". `SevenDofDecoupling.lean:38-42` flags
exactly this item as NOT proved there ("the residual §4c BOOKKEEPING — identifying the
12×12 task block `M̂_task` with the nonredundant `M̆`"). This module closes it. Nothing in
`SevenDof.lean` or `SevenDofDecoupling.lean` is restated or re-proved; both are imported
and used as sealed.

SETTING (unchanged from `SevenDofDecoupling`). `G = Γ_a = [Γ; z_aᵀ]` is the SQUARE augmented
transformation, `P = Γ_a⁻¹` entering only as the ring-level `G * P = 1`, `M` the symmetric
joint inertia, `j` the appended self-motion index, `k̂ = P *ᵥ eₙ`, and
`hrow : denom • (Gᵀ *ᵥ eₙ) = M *ᵥ k̂` the construction of `z_aᵀ = k̂ᵀM/denom`. The transformed
inertia is the congruence `M̂ = Pᵀ M P`. Index-generic throughout: `n` is an arbitrary
`Fintype`, the ring an arbitrary `CommRing`; nothing is specialised to 13 or to ℝ except the
final positive-definite convenience corollary. The TASK indices are `{i : n // i ≠ j}` — the
complement of the one self-motion coordinate — so "12×12" is never hardcoded.

  * `taskBlock j X`  — the submatrix of `X` on the task indices (`M̂_task` when `X = M̂`).
  * `taskRows j G`   — the task ROWS of `Γ_a`, i.e. the wide task Jacobian `Γ` itself
                       (12×13 in the concrete arm). `taskRows j G * Minv * (taskRows j G)ᵀ`
                       is therefore literally `Γ M⁻¹ Γᵀ`, the operational-space INVERSE
                       inertia `Λ⁻¹` (Khatib).

THE IDENTIFICATION AND ITS ROUTE. `M̂ = Pᵀ M P` and `G Minv Gᵀ` are two-sided inverses of
each other — one line of ring algebra from `G * P = 1` and `M * Minv = 1`
(`mhat_mul_operational`). `SevenDofDecoupling`'s sealed block-diagonality
(`mhat_selfmotion_column` / `mhat_selfmotion_row`) says the `j`-column and `j`-row of `M̂`
vanish off the diagonal, so the matrix product SURVIVES restriction to the task indices:
the cross term dropped by the restriction is exactly `M̂ a j · (G Minv Gᵀ) j b`, and its
first factor is zero. Hence

    M̂_task * (Γ M⁻¹ Γᵀ) = 1    and    (Γ M⁻¹ Γᵀ) * M̂_task = 1,

i.e. `M̂_task = (Γ M⁻¹ Γᵀ)⁻¹ = Λ`. That is the identification: the task block of the
augmented, decoupled inertia is the operational-space inertia given by the SAME formula the
nonredundant derivation gives for `M̆` — evaluated on the redundant arm's own `Γ` and `M`.
`mhat_task_eq_mbreve` states it in the doc's own words: ANY `M̆` inverting the same
operational inverse-inertia equals `M̂_task`; `mhat_task_eq_nonredundant_congruence`
discharges that hypothesis for the nonredundant congruence `M̆ = Γ̆⁻ᵀ M̆_joint Γ̆⁻¹`.

Results:
  * `taskBlock_one`, `taskBlock_transpose`, `taskBlock_mul_of_col_zero`,
    `taskBlock_mul_of_row_zero`, `taskBlock_gramian` — the block bookkeeping, stated for
    arbitrary matrices (no 7-DOF content).
  * `mhat_mul_operational`, `operational_mul_mhat` — the full-size two-sided inverse pair.
  * `mhat_task_mul_operational`, `operational_mul_mhat_task` — the same, restricted to the
    task block; this is where the sealed decoupling is consumed.
  * `mhat_task_eq_inv_operational` — `M̂_task = (Γ M⁻¹ Γᵀ)⁻¹` (§4c headline).
  * `mhat_task_eq_mbreve` — the identification in the doc's phrasing.
  * `mhat_task_eq_nonredundant_congruence` — the "old M̆" formula meets that hypothesis.
  * `mhat_task_symm` — `M̂_task` is symmetric.
  * `mhat_task_eq_inv_operational_of_posDef` (ℝ) — the `Minv` hypothesis discharged from
    positive definiteness of `M`, so nothing is assumed of the physical arm beyond `M ≻ 0`.

  The PASSIVITY counterpart (§5 restricted; hypotheses exactly those of the sealed
  `SevenDof.augmented_passivity_skew`, no new interface row):
  * `taskBlock_neg`, `taskBlock_skew` — the task block of a skew matrix is skew.
  * `mhat_task_passivity_skew` — `(M̂̇ − 2Ĉ)_task` is skew.
  * `mhat_task_passivity_identity` (ℝ) — its velocity quadratic form vanishes (eq 23, task).

  The DEFINITENESS layer (ℝ; hypotheses `M ≻ 0` and `G * P = 1` only):
  * `mulVec_injective_of_mul_eq_one` — invertibility of `Γ_a`, read as injectivity of `P *ᵥ ·`.
  * `mhat_task_posDef` — `M̂_task ≻ 0`.
  * `operational_posDef` — `Γ M⁻¹ Γᵀ ≻ 0`, hence `Λ = (Γ M⁻¹ Γᵀ)⁻¹` is a bona fide inertia.

TAKEN TOGETHER (the Part III transfer statement). The task block of the redundant arm is a
positive-definite inertia that IS the operational-space inertia, carrying a skew passivity
residual — exactly the three properties the sealed six-DOF chain consumes of `M̆`. Note what
the passivity half does NOT claim: `Ĉ` is not block-diagonal (`SevenDof.lean:30-33`), and the
cross-Coriolis terms coupling self-motion to the task block genuinely exist. The RESIDUAL's
restriction is skew regardless — antisymmetry is inherited by every principal submatrix,
which is why this costs one line rather than a decoupling argument.

HYPOTHESIS DISCIPLINE. One hypothesis is new relative to `SevenDofDecoupling`:
`hMinv : M * Minv = 1`, the joint inertia's invertibility with a NAMED inverse. It is not an
un-formalized analysis fact — `mhat_task_eq_inv_operational_of_posDef` discharges it from
`M.PosDef` over ℝ, which is the standing physical assumption on an inertia matrix (the same
`PosDef` hypothesis `selfmotion_inertia_pos` already uses). `P * G = 1` and `Minv * M = 1`
are DERIVED from their one-sided partners by `Matrix.mul_eq_one_comm`, so the interface is
one equation per invertible object, exactly the sealed module's discipline. No analytic fact
is assumed and no interface row is opened.

Human derivation: wiki dir the corresponding derivation record (not bundled)
(no the corresponding local note page filed yet) · sealed companions: Ctrllib/SevenDof.lean,
Ctrllib/SevenDofDecoupling.lean.
-/
import Ctrllib.SevenDofDecoupling

open Matrix

namespace Ctrllib

set_option linter.unusedDecidableInType false

section TaskBlock

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]
variable {M Minv G P : Matrix n n R} {khat : n → R} {denom : R} {j : n}

/-! ### The task indices and the block bookkeeping -/

/-- The **task indices**: every generalized coordinate except the appended self-motion one.
In the concrete 13-dimensional augmentation this is the 12-element index set of
`(ω_b, ν_e⁺)`; nothing here depends on the count. -/
abbrev TaskIdx {n : Type*} (j : n) := {i : n // i ≠ j}

/-- The **task block** of a full-size matrix: its submatrix on the task indices. `M̂_task` is
`taskBlock j M̂`. -/
def taskBlock (j : n) (X : Matrix n n R) : Matrix (TaskIdx j) (TaskIdx j) R :=
  X.submatrix (fun a => a.val) (fun b => b.val)

/-- The **task rows** of a full-size matrix. Applied to `G = Γ_a = [Γ; z_aᵀ]` this is the
task Jacobian `Γ` itself — the wide (12×13) map, recovered from the square augmentation by
deleting the appended row. -/
def taskRows (j : n) (X : Matrix n n R) : Matrix (TaskIdx j) n R :=
  X.submatrix (fun a => a.val) id

omit [Fintype n] [DecidableEq n] [CommRing R] in
theorem taskBlock_apply (j : n) (X : Matrix n n R) (a b : TaskIdx j) :
    taskBlock j X a b = X a.val b.val := rfl

omit [Fintype n] [DecidableEq n] [CommRing R] in
theorem taskRows_apply (j : n) (X : Matrix n n R) (a : TaskIdx j) (c : n) :
    taskRows j X a c = X a.val c := rfl

omit [Fintype n] in
/-- The task block of the identity is the identity. -/
theorem taskBlock_one (j : n) : taskBlock j (1 : Matrix n n R) = 1 := by
  ext a b
  by_cases h : a = b
  · subst h; simp [taskBlock_apply, Matrix.one_apply_eq]
  · have hv : a.val ≠ b.val := fun hval => h (Subtype.ext hval)
    simp [taskBlock_apply, Matrix.one_apply_ne hv, Matrix.one_apply_ne h]

omit [Fintype n] [DecidableEq n] [CommRing R] in
/-- Restriction to the task block commutes with transposition. -/
theorem taskBlock_transpose (j : n) (X : Matrix n n R) :
    (taskBlock j X)ᵀ = taskBlock j Xᵀ := rfl

omit [Fintype n] [DecidableEq n] in
/-- Restriction to the task block commutes with negation. -/
theorem taskBlock_neg (j : n) (X : Matrix n n R) :
    taskBlock j (-X) = -(taskBlock j X) := rfl

omit [Fintype n] [DecidableEq n] in
/-- **The task block of a skew matrix is skew.** Restriction to a COMMON index set on both
sides commutes with transposition (`taskBlock_transpose`, definitional) and with negation, so
antisymmetry is inherited by every principal submatrix. No hypothesis on `j`, no 7-DOF
content: this is the one-line bookkeeping that carries the passivity residual into the task
coordinates. -/
theorem taskBlock_skew {X : Matrix n n R} (j : n) (hX : Xᵀ = -X) :
    (taskBlock j X)ᵀ = -(taskBlock j X) := by
  rw [taskBlock_transpose, hX, taskBlock_neg]

/-- **The task block of a product splits, if the left factor's self-motion COLUMN vanishes.**
Restricting `X * Y` to the task indices drops the single cross term `X a j * Y j b`; the
hypothesis kills it. This is the bookkeeping step that makes the §4c identification a
restriction rather than a Schur complement. -/
theorem taskBlock_mul_of_col_zero {X Y : Matrix n n R} {j : n}
    (hX : ∀ a, a ≠ j → X a j = 0) :
    taskBlock j (X * Y) = taskBlock j X * taskBlock j Y := by
  ext a b
  rw [taskBlock_apply, Matrix.mul_apply, Matrix.mul_apply]
  have hsplit : ∑ c : n, X a.val c * Y c b.val
      = (∑ c ∈ Finset.univ.erase j, X a.val c * Y c b.val) + X a.val j * Y j b.val :=
    (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)).symm
  rw [hsplit, hX a.val a.property, zero_mul, add_zero]
  refine Finset.sum_subtype _ (fun x => ?_) _
  simp [Finset.mem_erase]

/-- **The task block of a product splits, if the right factor's self-motion ROW vanishes.**
The mirror of `taskBlock_mul_of_col_zero`; the dropped cross term is the same
`X a j * Y j b`, killed from the other side. -/
theorem taskBlock_mul_of_row_zero {X Y : Matrix n n R} {j : n}
    (hY : ∀ b, b ≠ j → Y j b = 0) :
    taskBlock j (X * Y) = taskBlock j X * taskBlock j Y := by
  ext a b
  rw [taskBlock_apply, Matrix.mul_apply, Matrix.mul_apply]
  have hsplit : ∑ c : n, X a.val c * Y c b.val
      = (∑ c ∈ Finset.univ.erase j, X a.val c * Y c b.val) + X a.val j * Y j b.val :=
    (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)).symm
  rw [hsplit, hY b.val b.property, mul_zero, add_zero]
  refine Finset.sum_subtype _ (fun x => ?_) _
  simp [Finset.mem_erase]

omit [DecidableEq n] in
/-- **The task block of the augmented Gramian is the operational-space inverse inertia.**
`(Γ_a M⁻¹ Γ_aᵀ)_task = Γ M⁻¹ Γᵀ`: restricting the full-size Gramian to the task indices is
the same as building it from the task Jacobian in the first place. No hypothesis — the
appended row of `Γ_a` simply never enters a task-indexed entry. -/
theorem taskBlock_gramian (j : n) (X Y : Matrix n n R) :
    taskBlock j (X * Y * Xᵀ) = taskRows j X * Y * (taskRows j X)ᵀ := by
  ext a b
  simp [taskBlock_apply, taskRows_apply, Matrix.mul_apply, Matrix.transpose_apply]

/-! ### The full-size inverse pair -/

/-- **`M̂` and `Γ_a M⁻¹ Γ_aᵀ` are inverse to each other.** `(Pᵀ M P)(G Minv Gᵀ) = 1`:
kinetic energy is invariant under the change of velocity coordinates, so the transformed
inertia inverts the transformed inverse inertia. Pure ring algebra from `G * P = 1` (whose
partner `P * G = 1` is derived, not assumed) and `M * Minv = 1`. -/
theorem mhat_mul_operational (hGP : G * P = 1) (hMinv : M * Minv = 1) :
    (Pᵀ * M * P) * (G * Minv * Gᵀ) = 1 := by
  have hPG : P * G = 1 := _root_.mul_eq_one_comm.mp hGP
  have h1 : (Pᵀ * M * P) * (G * Minv * Gᵀ) = Pᵀ * M * (P * G) * (Minv * Gᵀ) := by
    noncomm_ring
  rw [h1, hPG, mul_one]
  have h2 : Pᵀ * M * (Minv * Gᵀ) = Pᵀ * (M * Minv) * Gᵀ := by noncomm_ring
  rw [h2, hMinv, mul_one, ← Matrix.transpose_mul, hGP, Matrix.transpose_one]

/-- The other side of `mhat_mul_operational`, by `mul_eq_one_comm` (square matrices over a
commutative ring form a Dedekind-finite monoid, so one-sided inverses are two-sided). -/
theorem operational_mul_mhat (hGP : G * P = 1) (hMinv : M * Minv = 1) :
    (G * Minv * Gᵀ) * (Pᵀ * M * P) = 1 :=
  _root_.mul_eq_one_comm.mp (mhat_mul_operational hGP hMinv)

/-! ### The sealed decoupling, read entrywise -/

/-- The self-motion COLUMN of `M̂` vanishes off the diagonal — the entrywise reading of the
sealed `mhat_selfmotion_column`. -/
theorem mhat_entry_col_zero (hGP : G * P = 1) (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    ∀ a, a ≠ j → (Pᵀ * M * P) a j = 0 := by
  intro a ha
  have h := congrFun (mhat_selfmotion_column hGP hkhat hrow) a
  simpa [Matrix.mulVec_single, Pi.single_apply, ha] using h

/-- The self-motion ROW of `M̂` vanishes off the diagonal. Immediate from the column reading
and the sealed `mhat_symm`. -/
theorem mhat_entry_row_zero (hMsymm : Mᵀ = M) (hGP : G * P = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    ∀ b, b ≠ j → (Pᵀ * M * P) j b = 0 := by
  intro b hb
  have hs : (Pᵀ * M * P) j b = (Pᵀ * M * P) b j := by
    conv_lhs => rw [← mhat_symm (P := P) hMsymm]
    rfl
  rw [hs]
  exact mhat_entry_col_zero hGP hkhat hrow b hb

/-! ### §4c — the task-block identification -/

/-- **`M̂_task * (Γ M⁻¹ Γᵀ) = 1`.** The full-size inverse relation survives restriction to the
task indices, because the sealed block-diagonality kills the only cross term the restriction
would drop. -/
theorem mhat_task_mul_operational (hGP : G * P = 1) (hMinv : M * Minv = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    taskBlock j (Pᵀ * M * P) * (taskRows j G * Minv * (taskRows j G)ᵀ) = 1 := by
  rw [← taskBlock_gramian,
    ← taskBlock_mul_of_col_zero (Y := G * Minv * Gᵀ) (mhat_entry_col_zero hGP hkhat hrow),
    mhat_mul_operational hGP hMinv, taskBlock_one]

/-- **`(Γ M⁻¹ Γᵀ) * M̂_task = 1`.** The mirror, consuming the sealed self-motion ROW instead
of the column. Together with `mhat_task_mul_operational` this makes `M̂_task` a two-sided
inverse, so the identification below needs no determinant or rank argument. -/
theorem operational_mul_mhat_task (hMsymm : Mᵀ = M) (hGP : G * P = 1) (hMinv : M * Minv = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    (taskRows j G * Minv * (taskRows j G)ᵀ) * taskBlock j (Pᵀ * M * P) = 1 := by
  rw [← taskBlock_gramian,
    ← taskBlock_mul_of_row_zero (X := G * Minv * Gᵀ)
        (mhat_entry_row_zero hMsymm hGP hkhat hrow),
    operational_mul_mhat hGP hMinv, taskBlock_one]

/-- **§4c headline — the task block IS the operational-space inertia.**
`M̂_task = (Γ M⁻¹ Γᵀ)⁻¹ = Λ` (Khatib). This is the residual bookkeeping the derivation doc
lists as remaining under P1: the 12×12 task block of the augmented, decoupled inertia is
given by the SAME operational-space formula the nonredundant derivation gives for `M̆`,
evaluated on the redundant arm's own task Jacobian `Γ` and joint inertia `M`. -/
theorem mhat_task_eq_inv_operational (hGP : G * P = 1) (hMinv : M * Minv = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    taskBlock j (Pᵀ * M * P) = (taskRows j G * Minv * (taskRows j G)ᵀ)⁻¹ :=
  (Matrix.inv_eq_left_inv (mhat_task_mul_operational hGP hMinv hkhat hrow)).symm

/-- **The identification in the doc's own phrasing: `M̂_task = M̆`.** Any matrix `M̆` that
inverts the operational inverse-inertia `Γ M⁻¹ Γᵀ` — which is exactly how the nonredundant
derivation characterises the old task inertia — equals the task block. Stated without
`Matrix.inv` so it composes with whatever form `M̆` is presented in. -/
theorem mhat_task_eq_mbreve (hMsymm : Mᵀ = M) (hGP : G * P = 1) (hMinv : M * Minv = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat)
    {Mbreve : Matrix (TaskIdx j) (TaskIdx j) R}
    (hbreve : Mbreve * (taskRows j G * Minv * (taskRows j G)ᵀ) = 1) :
    taskBlock j (Pᵀ * M * P) = Mbreve := by
  calc taskBlock j (Pᵀ * M * P)
      = 1 * taskBlock j (Pᵀ * M * P) := (one_mul _).symm
    _ = Mbreve * (taskRows j G * Minv * (taskRows j G)ᵀ) * taskBlock j (Pᵀ * M * P) := by
          rw [hbreve]
    _ = Mbreve * ((taskRows j G * Minv * (taskRows j G)ᵀ) * taskBlock j (Pᵀ * M * P)) :=
          mul_assoc _ _ _
    _ = Mbreve * 1 := by
          rw [operational_mul_mhat_task hMsymm hGP hMinv hkhat hrow]
    _ = Mbreve := mul_one _

/-- **The nonredundant congruence meets the hypothesis of `mhat_task_eq_mbreve`.** The old
`M̆ = Γ̆⁻ᵀ M̆_joint Γ̆⁻¹` — the nonredundant derivation's task inertia, built from a SQUARE
task transformation `Γ̆` — inverts its own operational inverse-inertia `Γ̆ M̆_joint⁻¹ Γ̆ᵀ`, by
the very same one-line algebra as `mhat_mul_operational`. So whenever the two formulations
describe the same task-space inverse inertia (`hoper` — that is what "the same task" MEANS,
not an un-formalized analytic fact), the redundant task block IS the old `M̆`. -/
theorem mhat_task_eq_nonredundant_congruence (hMsymm : Mᵀ = M) (hGP : G * P = 1)
    (hMinv : M * Minv = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat)
    {Gb Pb Mb Mbinv : Matrix (TaskIdx j) (TaskIdx j) R}
    (hGPb : Gb * Pb = 1) (hMinvb : Mb * Mbinv = 1)
    (hoper : Gb * Mbinv * Gbᵀ = taskRows j G * Minv * (taskRows j G)ᵀ) :
    taskBlock j (Pᵀ * M * P) = Pbᵀ * Mb * Pb := by
  refine mhat_task_eq_mbreve hMsymm hGP hMinv hkhat hrow ?_
  rw [← hoper]
  exact mhat_mul_operational hGPb hMinvb

omit [DecidableEq n] in
/-- **`M̂_task` is symmetric** — the task block of the symmetric congruence `M̂`. Restriction
to a common index set commutes with transposition, so this is the sealed `mhat_symm` read on
the block. -/
theorem mhat_task_symm (hMsymm : Mᵀ = M) :
    (taskBlock j (Pᵀ * M * P))ᵀ = taskBlock j (Pᵀ * M * P) := by
  rw [taskBlock_transpose, mhat_symm hMsymm]

/-! ### §5 restricted — passivity of the task block -/

/-- **The task block of the augmented passivity residual is skew.** The sealed
`SevenDof.augmented_passivity_skew` says `M̂̇ − 2Ĉ` is antisymmetric for the SQUARE
augmentation; restricting to the task indices preserves that (`taskBlock_skew`). So the
12×12 task subsystem of the redundant arm carries a skew `Ṁ̂_task − 2Ĉ_task` in exactly the
form the sealed six-DOF passivity chain consumes.

This is the counterpart of `mhat_task_eq_inv_operational`: that theorem identifies the task
block of the INERTIA with the operational-space inertia, this one restricts the CORIOLIS
side. Note what it does NOT claim — `Ĉ` is not block-diagonal (`SevenDof.lean:30-33`: the
cross-Coriolis terms coupling self-motion to the task block genuinely exist), and nothing
here says otherwise. The restriction of the residual is skew regardless, because
antisymmetry is a property of principal submatrices, not of a block decomposition.

Hypotheses are exactly those of the sealed theorem: `hMsymm` and `hid`. No new interface
row. -/
theorem mhat_task_passivity_skew {C Ginv Gdot Ginvdot : Matrix n n R} (j : n)
    (hMsymm : Mᵀ = M) (hid : Ginvdot = -(Ginv * Gdot * Ginv)) :
    (taskBlock j ((Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot))))ᵀ
      = -(taskBlock j ((Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot)))) :=
  taskBlock_skew j (augmented_passivity_skew hMsymm hid)

end TaskBlock

section RealPositive

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {M G P : Matrix n n ℝ} {khat : n → ℝ} {denom : ℝ} {j : n}

/-- **§4c over ℝ, with the inverse hypothesis discharged.** For a positive-definite joint
inertia `M` — the standing physical assumption, the same one `selfmotion_inertia_pos` uses —
`M⁻¹` exists, so the identification needs no named invertibility input at all:
`M̂_task = (Γ M⁻¹ Γᵀ)⁻¹`. -/
theorem mhat_task_eq_inv_operational_of_posDef (hpd : M.PosDef) (hGP : G * P = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    taskBlock j (Pᵀ * M * P) = (taskRows j G * M⁻¹ * (taskRows j G)ᵀ)⁻¹ :=
  mhat_task_eq_inv_operational hGP
    (Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hpd.isUnit)) hkhat hrow

/-- The augmentation's invertibility, read as injectivity of `P *ᵥ ·`. From `G * P = 1`:
if `P *ᵥ x = P *ᵥ y` then applying `G` returns `x = y`. This is the only place the
invertibility of `Γ_a` on the singularity-free region Ω is used below. -/
theorem mulVec_injective_of_mul_eq_one (hGP : G * P = 1) :
    Function.Injective P.mulVec := by
  intro x y hxy
  have h : G *ᵥ (P *ᵥ x) = G *ᵥ (P *ᵥ y) := by rw [hxy]
  rwa [mulVec_mulVec, mulVec_mulVec, hGP, one_mulVec, one_mulVec] at h

/-- **`M̂_task ≻ 0`.** The task block of the augmented inertia is positive definite whenever
the joint inertia is. Two steps, both standard: the full congruence `M̂ = Pᵀ M P` is positive
definite because `P *ᵥ ·` is injective (`Matrix.PosDef.conjTranspose_mul_mul_same`, with
`Pᴴ = Pᵀ` over ℝ), and a principal submatrix of a positive-definite matrix is positive
definite (`Matrix.PosDef.submatrix` at the injective index map `Subtype.val`).

Hypothesis discipline: `M.PosDef` and `G * P = 1`, nothing else. In particular NO separate
full-row-rank hypothesis on the task Jacobian `Γ` — invertibility of the augmentation
`Γ_a = [Γ; z_aᵀ]` already supplies it, which is why `operational_posDef` below can drop
straight out. `mhat_task_symm` gave symmetry; this is the definiteness that the sealed
Rayleigh/sandwich analysis stones actually consume. -/
theorem mhat_task_posDef (hpd : M.PosDef) (hGP : G * P = 1) :
    (taskBlock j (Pᵀ * M * P)).PosDef := by
  have hcong : (Pᵀ * M * P).PosDef := by
    have h := hpd.conjTranspose_mul_mul_same (B := P) (mulVec_injective_of_mul_eq_one hGP)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact hcong.submatrix (e := fun a : TaskIdx j => a.val) Subtype.val_injective

/-- **`Γ M⁻¹ Γᵀ ≻ 0`** — the operational-space inverse inertia `Λ⁻¹` is positive definite.
Corollary of `mhat_task_posDef` through the sealed two-sided inverse pair: the task block and
`Γ M⁻¹ Γᵀ` invert each other (`operational_mul_mhat_task`), so `Γ M⁻¹ Γᵀ = M̂_task⁻¹`, and the
inverse of a positive-definite matrix is positive definite (`Matrix.PosDef.inv`).

Physically: the redundant arm's operational-space inertia `Λ = (Γ M⁻¹ Γᵀ)⁻¹` is a bona fide
inertia — bounded above and below on the singularity-free region — assuming nothing about the
arm beyond `M ≻ 0`. That is the quantitative input the task-space Lyapunov sandwich needs. -/
theorem operational_posDef (hpd : M.PosDef) (hGP : G * P = 1)
    (hkhat : khat = P *ᵥ Pi.single j 1)
    (hrow : denom • (Gᵀ *ᵥ Pi.single j 1) = M *ᵥ khat) :
    (taskRows j G * M⁻¹ * (taskRows j G)ᵀ).PosDef := by
  have hMsymm : Mᵀ = M := by
    have h := hpd.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hMinv : M * M⁻¹ = 1 :=
    Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hpd.isUnit)
  have hleft : (taskBlock j (Pᵀ * M * P))⁻¹ = taskRows j G * M⁻¹ * (taskRows j G)ᵀ :=
    Matrix.inv_eq_left_inv (operational_mul_mhat_task hMsymm hGP hMinv hkhat hrow)
  rw [← hleft]
  exact (mhat_task_posDef hpd hGP).inv

/-- **Giordano eq 23 restricted to the task block.** For every task velocity `w` the quadratic
form of the restricted passivity residual vanishes: the 12-dimensional task subsystem of the
redundant arm is workless in the same sense the full augmentation is. The sealed
`dotProduct_mulVec_self_of_skew` reads the skewness of `mhat_task_passivity_skew` as the
energy-balance identity. Hypotheses unchanged from the sealed
`SevenDof.augmented_passivity_identity`: `hMsymm` and `hid`. -/
theorem mhat_task_passivity_identity {C Ginv Gdot Ginvdot : Matrix n n ℝ} (j : n)
    (hMsymm : Mᵀ = M) (hid : Ginvdot = -(Ginv * Gdot * Ginv)) (w : TaskIdx j → ℝ) :
    w ⬝ᵥ (taskBlock j ((Ginvdotᵀ * M * Ginv + Ginvᵀ * (C + Cᵀ) * Ginv + Ginvᵀ * M * Ginvdot)
        - 2 • (Ginvᵀ * (C * Ginv + M * Ginvdot)))) *ᵥ w = 0 :=
  dotProduct_mulVec_self_of_skew (mhat_task_passivity_skew j hMsymm hid) w

end RealPositive

end Ctrllib

#print axioms Ctrllib.taskBlock_one
#print axioms Ctrllib.taskBlock_transpose
#print axioms Ctrllib.taskBlock_mul_of_col_zero
#print axioms Ctrllib.taskBlock_mul_of_row_zero
#print axioms Ctrllib.taskBlock_gramian
#print axioms Ctrllib.mhat_mul_operational
#print axioms Ctrllib.operational_mul_mhat
#print axioms Ctrllib.mhat_entry_col_zero
#print axioms Ctrllib.mhat_entry_row_zero
#print axioms Ctrllib.mhat_task_mul_operational
#print axioms Ctrllib.operational_mul_mhat_task
#print axioms Ctrllib.mhat_task_eq_inv_operational
#print axioms Ctrllib.mhat_task_eq_mbreve
#print axioms Ctrllib.mhat_task_eq_nonredundant_congruence
#print axioms Ctrllib.mhat_task_symm
#print axioms Ctrllib.mhat_task_eq_inv_operational_of_posDef
#print axioms Ctrllib.taskBlock_neg
#print axioms Ctrllib.taskBlock_skew
#print axioms Ctrllib.mhat_task_passivity_skew
#print axioms Ctrllib.mhat_task_passivity_identity
#print axioms Ctrllib.mulVec_injective_of_mul_eq_one
#print axioms Ctrllib.mhat_task_posDef
#print axioms Ctrllib.operational_posDef
