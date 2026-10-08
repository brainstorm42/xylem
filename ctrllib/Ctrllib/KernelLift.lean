/-
Kernel lift — the arm null direction raised to a coordinated null direction (M1, formal side).

WHAT THIS PROVES. The seven-joint packet
(the corresponding derivation record (not bundled))
states in (H3) that a nonzero `n(q) ∈ ℝ⁷` with `J₇⊕(q) n(q) = 0` (eq. (6)) has a
"corresponding" coordinated null direction `k(q) ∈ ℝ¹³` with `Γ(q) k(q) = 0` (eq. (7)). The word
"corresponding" is the whole content of that step, and the 2026-08-27 professor review flagged it
(finding M1). This module replaces the word with an explicit map and proves both directions.

THE LIFT. With the packet's block form (eq. (3)), rows split `(3, 3, 6)` and columns split
`(3, 3, 7)`,

    Γ = [ R   A   B   ]       B = R B̄   (Giordano 2019 RA-L eq. (19): B = R_cb J̄_v)
        [ 0   I₃  0   ]
        [ 0   G   J₇⊕ ]

solving `Γ ξ = 0` row by row forces `ω_b = 0` (row 2), `J₇⊕ q̇ = 0` (row 3), and
`R v_b + R B̄ q̇ = 0`, i.e. `v_b = −B̄ q̇` (row 1, using only that `R` has a left inverse). So

    k = L(q) n = [ −B̄ n ; 0₃ ; n ] ∈ ℝ¹³,      L(q) = [ −B̄ ; 0₃ₓ₇ ; I₇ ].

Physically: the arm moves at joint rate `n`, the base does not rotate, and the base translates
exactly fast enough to hold the system centre of mass fixed. That is `kernelLift` below.

  * `coordinated_annihilates_kernelLift` — `Γ L n = 0`. Uses only the block form and eq. (6);
    no inverse, no rank condition, no positivity.
  * `kernelLift_ne_zero` — `n ≠ 0 → L n ≠ 0`, so eq. (7)'s nonzero clause is derived, not assumed.
  * `eq_kernelLift_of_mem_kernel` — the converse: every `x` with `Γ x = 0` satisfies
    `J₇⊕ (x∘inr∘inr) = 0` and `x = L (x∘inr∘inr)`. `L` is therefore a bijection
    `ker J₇⊕ → ker Γ`, so `dim ker Γ = dim ker J₇⊕` and the packet's separate "corresponding
    `k(q)`" clause in (H3) can be dropped. This is the only place a left inverse of the rotation
    block appears.
  * `coordinated_annihilates_kernelLift_of_inv` — the same annihilation for the packet's own
    unfactored top-right block `[A ∣ B]`, given a right inverse of the rotation block.
  * `coordinated_annihilates_kernelLift_projector`, `inertiaDenominator_kernelLift_pos`,
    `coordinated_annihilates_inertiaProjector_kernelLift` — instantiations of the registered
    `NullspaceMotion` projector and inertia machinery at `k := kernelLift`.
  * `exists_nonzero_coordinated_kernel_of_sigmaSixEuclid_pos` — the σ₆ bridge.

WHICH PACKET HYPOTHESES THIS DISCHARGES. (H3)'s eq. (7) clause — existence of a nonzero
coordinated null direction attached to `n` — and the kernel-dimension bookkeeping of §3. It does
NOT discharge (H3)'s augmentation-invertibility clause, which §5 still needs for `z_aᵀk = 1`, nor
any of (H1), (H2), (H4).

HONEST BOUNDARY. Nothing physical is proved here. Every result is an algebraic implication about
matrices with the stated block shape. In particular:

  * the block form must BE the physical `Γ` — frames, task point, coordinate ordering, units and
    scaling are (H4)'s obligation and are not formalized;
  * `B̄` must BE the registered centre-of-mass Jacobian `J̄_v`; the factorization `B = R B̄` is
    imported from Giordano 2019 eq. (19) as a modelling input, not derived here;
  * the "base translates to keep the CoM fixed" reading of `v_b = −B̄ n` is commentary on that
    identification, not a theorem.

Index types stay generic (`l ⊕ (m ⊕ n)` rows, `l ⊕ (m ⊕ n')` columns), matching `DetGamma.lean`
and `GammaInvertible.lean`. No `Fin 13` is introduced anywhere: the projector and inertia
machinery of `NullspaceMotion.lean` is generic over the index type and instantiates directly.
Only the final `sigmaSixEuclid` bridge is `Fin`-typed, because `SingularValueInterface.lean`
produces its kernel vector in `EuclideanSpace ℝ (Fin 7)`.

Plan: the corresponding derivation record (not bundled) (Lane E).
-/
import Ctrllib.NullspaceMotion
import Ctrllib.SingularValueInterface
import Mathlib.Data.Matrix.ColumnRowPartitioned

/- The nested `Sum` index type `l ⊕ (m ⊕ n')` pushes instance search past Lean's default pending
depth of 1. The lakefile sets `maxSynthPendingDepth = 3` for `lake build`, but a single-file check
via `lake env lean` does not read `[leanOptions]`; pinning it here makes the file elaborate
identically under both routes. Precedent: `PointMassComFlow.lean`. -/
set_option maxSynthPendingDepth 3

/- The block index types carry `Fintype`/`DecidableEq` instances that several statements need only
in their proofs (matrix products, the identity block) and not in their types. Same pattern, and
same reason, as `SevenDofDecoupling.lean`. -/
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Matrix Module Function WithLp

namespace Ctrllib

section Ring

/-- The lift of an arm null direction `nv` to the coordinated velocity space:
`k = [ −B̄ nv ; 0 ; nv ]`. The base does not rotate, and its translational rate `−B̄ nv` is the
one that holds the centre of mass fixed once `B̄` is the registered centre-of-mass Jacobian.
The middle index type `m` (the base angular block) is explicit because the remaining arguments
do not determine it. -/
def kernelLift {R : Type*} [CommRing R] {l n' : Type*} [Fintype n']
    (m : Type*) (Bbar : Matrix l n' R) (nv : n' → R) : l ⊕ (m ⊕ n') → R :=
  Sum.elim (-(Bbar *ᵥ nv)) (Sum.elim 0 nv)

/-- **The lift is injective on nonzero directions.** The last block of `kernelLift` is `nv`
itself, so a nonzero arm direction gives a nonzero coordinated direction. This derives the
"nonzero" clause of packet eq. (7) instead of assuming it. -/
theorem kernelLift_ne_zero {R : Type*} [CommRing R] {l n' : Type*} [Fintype n']
    (m : Type*) (Bbar : Matrix l n' R) (nv : n' → R) (hnv : nv ≠ 0) :
    kernelLift m Bbar nv ≠ 0 := by
  intro h
  apply hnv
  funext i
  simpa [kernelLift] using congrFun h (Sum.inr (Sum.inr i))

variable {R : Type*} [CommRing R]
variable {l m n n' : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype n'] [DecidableEq m]

/-- The coordinated transform in the packet's block form (eq. (3)), with the top-right block
factored as `[A ∣ R B̄]` following Giordano 2019 eq. (19) (`B = R_cb J̄_v`). Rows split
`l ⊕ (m ⊕ n)`, columns split `l ⊕ (m ⊕ n')`; the thesis instance is `(3, 3, 6) × (3, 3, 7)`. -/
def coordinatedMap (Rot : Matrix l l R) (A : Matrix l m R) (Bbar : Matrix l n' R)
    (G : Matrix n m R) (J : Matrix n n' R) : Matrix (l ⊕ (m ⊕ n)) (l ⊕ (m ⊕ n')) R :=
  fromBlocks Rot (fromCols A (Rot * Bbar)) 0 (fromBlocks 1 0 G J)

omit [Fintype n] in
/-- **The lift lands in the coordinated kernel** (packet eq. (6) ⟹ eq. (7)). Only the arm
kernel hypothesis `hJ` is used: no invertibility, no rank condition, no positivity. -/
theorem coordinated_annihilates_kernelLift
    (Rot : Matrix l l R) (A : Matrix l m R) (Bbar : Matrix l n' R)
    (G : Matrix n m R) (J : Matrix n n' R) (nv : n' → R) (hJ : J *ᵥ nv = 0) :
    coordinatedMap Rot A Bbar G J *ᵥ kernelLift m Bbar nv = 0 := by
  ext i
  rcases i with i | i | i <;>
    simp [coordinatedMap, kernelLift, fromBlocks_mulVec, mulVec_neg, ← mulVec_mulVec, hJ]

omit [Fintype n] in
/-- **Exhaustiveness: every coordinated null direction is a lift** (the (H3) upgrade). If `Rot`
has a left inverse and `Γ x = 0`, then the arm block of `x` is an arm null direction and `x` is
its lift. Together with `coordinated_annihilates_kernelLift` and `kernelLift_ne_zero` this makes
`kernelLift` a bijection `ker J → ker Γ`, so `dim ker Γ = dim ker J` is derived and the packet's
separate "corresponding `k(q)`" clause is redundant. This is the only statement in the module
that uses a one-sided inverse of the rotation block. -/
theorem eq_kernelLift_of_mem_kernel [DecidableEq l]
    (Rot RotInv : Matrix l l R) (hRot : RotInv * Rot = 1)
    (A : Matrix l m R) (Bbar : Matrix l n' R)
    (G : Matrix n m R) (J : Matrix n n' R)
    (x : l ⊕ (m ⊕ n') → R) (hx : coordinatedMap Rot A Bbar G J *ᵥ x = 0) :
    J *ᵥ (x ∘ Sum.inr ∘ Sum.inr) = 0 ∧ x = kernelLift m Bbar (x ∘ Sum.inr ∘ Sum.inr) := by
  obtain ⟨u, w, nv, rfl⟩ : ∃ u w nv, x = Sum.elim u (Sum.elim w nv) :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr ∘ Sum.inl, x ∘ Sum.inr ∘ Sum.inr, by
      funext j; rcases j with j | j | j <;> rfl⟩
  change J *ᵥ nv = 0 ∧ _ = kernelLift m Bbar nv
  rw [coordinatedMap, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    fromCols_mulVec_sumElim, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at hx
  have hmid : w = 0 := by
    funext i
    simpa using congrFun hx (Sum.inr (Sum.inl i))
  have hlow : J *ᵥ nv = 0 := by
    funext i
    simpa [hmid] using congrFun hx (Sum.inr (Sum.inr i))
  have htop : Rot *ᵥ (u + Bbar *ᵥ nv) = 0 := by
    funext i
    simpa [hmid, mulVec_add, ← mulVec_mulVec] using congrFun hx (Sum.inl i)
  have hcancel : u + Bbar *ᵥ nv = 0 := by
    have h := congrArg (fun y => RotInv *ᵥ y) htop
    simpa [mulVec_mulVec, hRot, one_mulVec] using h
  refine ⟨hlow, ?_⟩
  rw [kernelLift, eq_neg_of_add_eq_zero_left hcancel, hmid]

omit [Fintype n] in
/-- **Unfactored variant.** The packet writes the top-right block as `[A ∣ B]` without naming
`B̄`. Given a right inverse of the rotation block, `B̄ := RotInv * B` recovers the factored form,
so the lift annihilates the packet's own matrix. -/
theorem coordinated_annihilates_kernelLift_of_inv [DecidableEq l]
    (Rot RotInv : Matrix l l R) (hRot : Rot * RotInv = 1)
    (A : Matrix l m R) (B : Matrix l n' R)
    (G : Matrix n m R) (J : Matrix n n' R) (nv : n' → R) (hJ : J *ᵥ nv = 0) :
    fromBlocks Rot (fromCols A B) 0 (fromBlocks (1 : Matrix m m R) 0 G J) *ᵥ
      kernelLift m (RotInv * B) nv = 0 := by
  have hB : Rot * (RotInv * B) = B := by rw [← Matrix.mul_assoc, hRot, Matrix.one_mul]
  have h := coordinated_annihilates_kernelLift Rot A (RotInv * B) G J nv hJ
  rwa [coordinatedMap, hB] at h

omit [Fintype n] in
/-- **The coordinated map annihilates the rank-one projector onto the lifted kernel line.**
Instantiation of `task_annihilates_rankOneProjector` (`NullspaceMotion`) at `k := kernelLift`. -/
theorem coordinated_annihilates_kernelLift_projector
    (Rot : Matrix l l R) (A : Matrix l m R) (Bbar : Matrix l n' R)
    (G : Matrix n m R) (J : Matrix n n' R) (nv : n' → R) (hJ : J *ᵥ nv = 0)
    (z : l ⊕ (m ⊕ n') → R) :
    coordinatedMap Rot A Bbar G J * rankOneProjector (kernelLift m Bbar nv) z = 0 :=
  task_annihilates_rankOneProjector _ _ z
    (coordinated_annihilates_kernelLift Rot A Bbar G J nv hJ)

end Ring

section RealInertia

variable {l m n n' : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype n'] [DecidableEq m]

omit [DecidableEq m] in
/-- **The self-motion inertia along the lifted direction is positive.** Instantiation of
`inertiaDenominator_pos` (`NullspaceMotion`): a positive-definite generalized inertia and a
nonzero arm null direction give a strictly positive `kᵀ M k`, so the inertia-weighted covector
of packet §5 is well defined along the lift. -/
theorem inertiaDenominator_kernelLift_pos
    (M : Matrix (l ⊕ (m ⊕ n')) (l ⊕ (m ⊕ n')) ℝ) (Bbar : Matrix l n' ℝ) (nv : n' → ℝ)
    (hM : M.PosDef) (hnv : nv ≠ 0) :
    0 < inertiaDenominator M (kernelLift m Bbar nv) :=
  inertiaDenominator_pos hM (kernelLift_ne_zero m Bbar nv hnv)

omit [Fintype n] in
/-- **The coordinated map annihilates the inertia-weighted projector onto the lifted line.**
Instantiation of `task_annihilates_inertiaProjector` (`NullspaceMotion`): the dynamically
consistent null-space projector built from the lift injects no coordinated task motion. -/
theorem coordinated_annihilates_inertiaProjector_kernelLift
    (Rot : Matrix l l ℝ) (A : Matrix l m ℝ) (Bbar : Matrix l n' ℝ)
    (G : Matrix n m ℝ) (J : Matrix n n' ℝ)
    (M : Matrix (l ⊕ (m ⊕ n')) (l ⊕ (m ⊕ n')) ℝ) (nv : n' → ℝ) (hJ : J *ᵥ nv = 0) :
    coordinatedMap Rot A Bbar G J * inertiaProjector M (kernelLift m Bbar nv) = 0 :=
  task_annihilates_inertiaProjector _ M _
    (coordinated_annihilates_kernelLift Rot A Bbar G J nv hJ)

end RealInertia

section SigmaBridge

variable {l m : Type*} [Fintype l] [Fintype m] [DecidableEq m]

/-- **σ₆ bridge.** Full row rank of the six-by-seven circumcentroidal task map — packet (H1)'s
`σ₆(J₇⊕) > 0` — yields a nonzero arm null direction, and the lift carries it to a nonzero
coordinated null direction. This is the single statement joining `SingularValueInterface`'s
`EuclideanSpace ℝ (Fin 7)` kernel to the plain function type the projector machinery consumes;
that transfer is `WithLp` bookkeeping only. The conclusion is pointwise in the configuration: it
does not choose the direction continuously along a trajectory. -/
theorem exists_nonzero_coordinated_kernel_of_sigmaSixEuclid_pos
    (Rot : Matrix l l ℝ) (A : Matrix l m ℝ) (Bbar : Matrix l (Fin 7) ℝ)
    (G : Matrix (Fin 6) m ℝ) (J : Matrix (Fin 6) (Fin 7) ℝ) (hσ : 0 < sigmaSixEuclid J) :
    ∃ nv : Fin 7 → ℝ, nv ≠ 0 ∧ J *ᵥ nv = 0 ∧
      coordinatedMap Rot A Bbar G J *ᵥ kernelLift m Bbar nv = 0 ∧
      kernelLift m Bbar nv ≠ 0 := by
  obtain ⟨k, hk0, hk⟩ := sigmaSixEuclid_pos_implies_exists_nonzero_kernel J hσ
  rw [toLpLin_apply] at hk0
  have hJk : J *ᵥ ofLp k = 0 := by simpa using hk0
  have hkne : ofLp k ≠ (0 : Fin 7 → ℝ) := by simpa using hk
  exact ⟨ofLp k, hkne, hJk,
    coordinated_annihilates_kernelLift Rot A Bbar G J _ hJk,
    kernelLift_ne_zero m Bbar _ hkne⟩

end SigmaBridge

end Ctrllib

#print axioms Ctrllib.coordinated_annihilates_kernelLift
#print axioms Ctrllib.kernelLift_ne_zero
#print axioms Ctrllib.eq_kernelLift_of_mem_kernel
#print axioms Ctrllib.coordinated_annihilates_kernelLift_of_inv
#print axioms Ctrllib.coordinated_annihilates_kernelLift_projector
#print axioms Ctrllib.inertiaDenominator_kernelLift_pos
#print axioms Ctrllib.coordinated_annihilates_inertiaProjector_kernelLift
#print axioms Ctrllib.exists_nonzero_coordinated_kernel_of_sigmaSixEuclid_pos
