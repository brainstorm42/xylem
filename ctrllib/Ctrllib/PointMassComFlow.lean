/-
Point-mass CoM flow realization, invariant energy sublevels, and convergence
(the corresponding point-mass flow note).

SYSTEM (the corresponding flow note §P4.1; human proof
the corresponding local note): the autonomous linear loop

    m v' + d v + k x = 0 ,   x' = v ,   m, d, k > 0 ,

on the state `z = (v, x) : PointMassState := H × H`, `H := EuclideanSpace ℝ
(Fin 3)`. The closed-loop field is

    f(v, x) = ( -(d/m) v - (k/m) x ,  v ) ,

and the mechanical energy is `V(v, x) = (m/2) ‖v‖² + (k/2) ‖x‖²`.

THE NEW CONTENT (`IsSolutionTo` discharged, not assumed). `Ctrllib.LaSalle`'s
own comment names the standing wall: "How such a flow arises on the region of
interest (Picard–Lindelöf, completeness on Ω) deliberately stays on the
applier's side", and the corresponding local note's `IsSolutionTo` row records that
"Mathlib v4.31.0 has no ODE→Flow bridge" for the general nonlinear case. This
module does not build that general bridge. It builds the flow BY HAND for
this one linear field, from the pinned Mathlib operator-exponential calculus
(`Mathlib.Analysis.SpecialFunctions.Exponential`'s `hasDerivAt_exp_smul_const'`
and `Mathlib.Analysis.Normed.Algebra.Exponential`'s `exp_add_of_commute` /
`exp_zero`), exactly the matrix-exponential construction the human proof uses
(`Φ(t, z₀) := e^{tA} z₀`, eq (7) there). No ODE existence theorem
(Picard–Lindelöf, Peano, or otherwise) is invoked or needed: for a linear
field the solution formula is written down directly and its flow identities
are algebraic consequences of the exponential's own defining properties.

REUSE. The point-mass field and energy are exactly `Ctrllib.ComLaSalle`'s
`comField`/`comEnergy` specialized to the SCALAR operators `M = m • id`,
`D = d • id`, `K = k • id`, `Minv = m⁻¹ • id` on `H`
(`pointMassField_eq_comField`, `pointMassEnergy_eq_comEnergy` below). Once the
flow is built, `pointMass_tendsto_zero` is the sealed `Ctrllib.com_attractive`
applied at this scalar instantiation — no new LaSalle argument is re-derived;
only the six operator hypotheses (`hMsa/hKsa/hMinv/hDnn/hDdef/hKdef`) are
discharged for `m • id`/`d • id`/`k • id`, mirroring `ComLaSalleMatrix`'s
discharge for concrete SPD matrices (here even simpler: isotropic scalar
operators).

Human derivation:
the corresponding derivation record (not bundled)
Task packet:
the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Exponential
import Ctrllib.ComLaSalle

/- Instance search for `Module ℝ (PointMassState →L[ℝ] PointMassState)` and the
`SMulCommClass` fact behind `Commute.smul_left` needs a pending-synthesis depth
above Lean's default of 1. The lakefile already sets `maxSynthPendingDepth = 3`
for `lake build`, but a single-file check via `lake env lean` does not read
`[leanOptions]`; without this line such a run reports a spurious
`SMulCommClass` failure at `pointMassFlow` and prints `sorryAx` for every
dependent declaration. Setting it here makes the file elaborate identically
under both routes. -/
set_option maxSynthPendingDepth 3

open Set Filter Topology
open scoped InnerProductSpace

namespace Ctrllib

/-- The 3D Euclidean coordinate space carrying velocity and position. -/
abbrev PointMassCoord := EuclideanSpace ℝ (Fin 3)

/-- The stacked point-mass state `(v, x)`. -/
abbrev PointMassState := PointMassCoord × PointMassCoord

section Definitions

variable (m d k : ℝ)

/-- The point-mass closed-loop field `f(v, x) = (-(d/m) v - (k/m) x, v)`
(packet eq for `f_{m,d,k}`; human proof eq (2)). -/
noncomputable def pointMassField : PointMassState → PointMassState :=
  fun z => (-(d / m) • z.1 - (k / m) • z.2, z.1)

/-- The mechanical energy `V(v, x) = (m/2) ‖v‖² + (k/2) ‖x‖²`
(packet's `V`; human proof eq (10)). -/
noncomputable def pointMassEnergy : PointMassState → ℝ :=
  fun z => (m / 2) * ‖z.1‖ ^ 2 + (k / 2) * ‖z.2‖ ^ 2

/-- `pointMassField` as a continuous linear map: the block operator
`A (v, x) = (-(d/m) v - (k/m) x, v)`. This is the matrix `A` of human-proof
eq (5), packaged so the Mathlib operator exponential applies to it. -/
noncomputable def pointMassCLM : PointMassState →L[ℝ] PointMassState :=
  ((-(d / m)) • ContinuousLinearMap.fst ℝ PointMassCoord PointMassCoord +
      (-(k / m)) • ContinuousLinearMap.snd ℝ PointMassCoord PointMassCoord).prod
    (ContinuousLinearMap.fst ℝ PointMassCoord PointMassCoord)

@[simp]
theorem pointMassCLM_apply (z : PointMassState) :
    pointMassCLM m d k z = pointMassField m d k z := by
  simp [pointMassCLM, pointMassField, sub_eq_add_neg]

end Definitions

section Flow

variable (m d k : ℝ)

/-- `PointMassState →L[ℝ] PointMassState` has `expSeries` radius `⊤`, so every
element is trivially in the convergence ball. This is the fact that lets the
CharZero-generic exponential lemmas (`𝕂 := ℝ`, no need for the `ℚ`-specialized
unconditional corollaries, which would additionally demand a
`NormedAlgebra ℚ` instance this non-division-ring endomorphism algebra does
not have) apply unconditionally here. -/
private theorem mem_ball_pointMassCLM (x : PointMassState →L[ℝ] PointMassState) :
    x ∈ Metric.eball (0 : PointMassState →L[ℝ] PointMassState)
      (NormedSpace.expSeries ℝ (PointMassState →L[ℝ] PointMassState)).radius :=
  (NormedSpace.expSeries_radius_eq_top ℝ (PointMassState →L[ℝ] PointMassState)).symm ▸
    edist_lt_top _ _

private theorem pointMassCLM_exp_continuous :
    Continuous fun x : PointMassState →L[ℝ] PointMassState => NormedSpace.exp x := by
  rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 : PointMassState →L[ℝ] PointMassState),
    ← NormedSpace.expSeries_radius_eq_top ℝ (PointMassState →L[ℝ] PointMassState)]
  exact NormedSpace.continuousOn_exp

-- `hm` is carried only to match the pinned interface signature; the
-- construction below is well-defined (if not physically meaningful) for any
-- `m`.
set_option linter.unusedVariables false in
/-- **T1 — global realization.** The point-mass flow `Φ(t, z) := exp(t • A) z`
(human proof eq (7)), built directly from the operator exponential — no
ODE→Flow bridge, no Picard–Lindelöf. Continuity, the group law, and
`Φ(0, ·) = id` are algebraic consequences of `NormedSpace.exp`'s own
continuity, additivity on commuting elements, and value at zero. -/
noncomputable def pointMassFlow (hm : 0 < m) : Flow ℝ PointMassState where
  toFun t z := (NormedSpace.exp (t • pointMassCLM m d k)) z
  cont' := by
    have h1 : Continuous fun p : ℝ × PointMassState => p.1 • pointMassCLM m d k :=
      continuous_fst.smul continuous_const
    have h2 : Continuous fun p : ℝ × PointMassState =>
        NormedSpace.exp (p.1 • pointMassCLM m d k) :=
      pointMassCLM_exp_continuous.comp h1
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ)
      (E := PointMassState) (F := PointMassState)).continuous.comp
      (h2.prodMk continuous_snd)
  map_add' t₁ t₂ z := by
    have hcomm : Commute (t₁ • pointMassCLM m d k) (t₂ • pointMassCLM m d k) :=
      ((Commute.refl (pointMassCLM m d k)).smul_left t₁).smul_right t₂
    change NormedSpace.exp ((t₁ + t₂) • pointMassCLM m d k) z = _
    rw [add_smul, NormedSpace.exp_add_of_commute_of_mem_ball hcomm
        (mem_ball_pointMassCLM _) (mem_ball_pointMassCLM _),
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  map_zero' z := by
    change NormedSpace.exp ((0 : ℝ) • pointMassCLM m d k) z = z
    rw [zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_apply]

/-- The flow really does solve the field: `d/dt Φ(t, z) = A (Φ(t, z))`
(human-proof eq (9)), read off `NormedSpace.hasDerivAt_exp_smul_const'`
(the pinned derivative of `u ↦ exp(u • x)` in a non-commutative Banach
algebra) post-composed with the evaluation map at `z`. -/
theorem pointMassFlow_hasDerivAt (hm : 0 < m) (z : PointMassState) (t : ℝ) :
    HasDerivAt (fun s => pointMassFlow m d k hm s z)
      (pointMassCLM m d k ((pointMassFlow m d k hm) t z)) t := by
  have hderiv : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • pointMassCLM m d k))
      (pointMassCLM m d k * NormedSpace.exp (t • pointMassCLM m d k)) t :=
    hasDerivAt_exp_smul_const' (pointMassCLM m d k) t
  have hcomp := (ContinuousLinearMap.apply ℝ PointMassState z).hasFDerivAt.comp_hasDerivAt
    t hderiv
  simp only [ContinuousLinearMap.apply_apply] at hcomp
  rwa [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at hcomp

end Flow

section Interfaces

-- `hd`/`hk` are carried only to match the pinned interface signature; the
-- ODE identity itself is algebraic and does not need positivity of `d` or
-- `k`.
set_option linter.unusedVariables false in
/-- **T1 (interface form) — the flow solves the field.** -/
theorem pointMass_isSolutionTo (m d k : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    IsSolutionTo (pointMassFlow m d k hm) (pointMassField m d k) := by
  intro z t
  simpa only [pointMassCLM_apply] using pointMassFlow_hasDerivAt m d k hm z t

end Interfaces

section Coercivity

variable (m k : ℝ)

/-- `PointMassState` has the sup product norm, so `‖z‖² ≤ ‖z.1‖² + ‖z.2‖²`
(the same bookkeeping `BlockPrecompact.blockLyap_norm_coercive` uses). -/
private theorem pointMassState_norm_sq_le (z : PointMassState) :
    ‖z‖ ^ 2 ≤ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  rw [Prod.norm_def]
  rcases le_total ‖z.1‖ ‖z.2‖ with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg ‖z.1‖]
  · rw [max_eq_left h]; nlinarith [sq_nonneg ‖z.2‖]

/-- **Coercivity of the point-mass energy.** `(min m k / 2) ‖z‖² ≤ V z`. -/
theorem pointMassEnergy_coercive (hm : 0 < m) (hk : 0 < k) (z : PointMassState) :
    min m k / 2 * ‖z‖ ^ 2 ≤ pointMassEnergy m k z := by
  have hmin : min m k * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤ m * ‖z.1‖ ^ 2 + k * ‖z.2‖ ^ 2 := by
    have h1 : min m k ≤ m := min_le_left m k
    have h2 : min m k ≤ k := min_le_right m k
    nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
  have h3 := pointMassState_norm_sq_le z
  have hminpos : 0 < min m k := lt_min hm hk
  unfold pointMassEnergy
  nlinarith [mul_le_mul_of_nonneg_left h3 hminpos.le]

/-- **T2, first half — invariant energy sublevels are compact.** Closed
(continuity of `V`) and bounded (coercivity), hence compact by Heine–Borel in
the finite-dimensional, hence proper, state space. -/
theorem pointMass_sublevel_isCompact (hm : 0 < m) (hk : 0 < k) (R : ℝ) :
    IsCompact {z : PointMassState | pointMassEnergy m k z ≤ R} := by
  have hcont : Continuous (pointMassEnergy m k) := by
    unfold pointMassEnergy
    fun_prop
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
  have hc₁ : 0 < min m k / 2 := by positivity
  apply (Metric.isBounded_closedBall
    (x := (0 : PointMassState)) (r := R / (min m k / 2) + 1)).subset
  rintro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : min m k / 2 * ‖z‖ ^ 2 ≤ R := (pointMassEnergy_coercive m k hm hk z).trans hz
  have h2 : ‖z‖ ^ 2 ≤ R / (min m k / 2) := by rw [le_div_iff₀ hc₁]; linarith
  nlinarith [sq_nonneg (‖z‖ - 1), sq_nonneg ‖z‖, norm_nonneg z, h2]

end Coercivity

section ScalarOperators

variable (m d k : ℝ)

/-- The scalar inertia operator `M = m • id`. -/
noncomputable def pmM : PointMassCoord →L[ℝ] PointMassCoord := m • ContinuousLinearMap.id ℝ _

/-- The scalar damping operator `D = d • id`. -/
noncomputable def pmD : PointMassCoord →L[ℝ] PointMassCoord := d • ContinuousLinearMap.id ℝ _

/-- The scalar stiffness operator `K = k • id`. -/
noncomputable def pmK : PointMassCoord →L[ℝ] PointMassCoord := k • ContinuousLinearMap.id ℝ _

/-- The scalar inertia inverse `Minv = m⁻¹ • id`. -/
noncomputable def pmMinv : PointMassCoord →L[ℝ] PointMassCoord :=
  m⁻¹ • ContinuousLinearMap.id ℝ _

theorem pointMassField_eq_comField (z : PointMassState) :
    pointMassField m d k z = comField (pmD d) (pmK k) (pmMinv m) z := by
  simp only [pointMassField, comField, pmD, pmK, pmMinv, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, smul_add, div_eq_mul_inv, Prod.mk.injEq, and_true]
  module

theorem pointMassEnergy_eq_comEnergy (z : PointMassState) :
    pointMassEnergy m k z = comEnergy (pmM m) (pmK k) z := by
  simp only [pointMassEnergy, comEnergy, pmM, pmK, smul_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

variable {m d k}

theorem pmM_selfAdjoint (a b : PointMassCoord) : ⟪pmM m a, b⟫_ℝ = ⟪a, pmM m b⟫_ℝ := by
  simp [pmM, real_inner_smul_left, real_inner_smul_right]

theorem pmK_selfAdjoint (a b : PointMassCoord) : ⟪pmK k a, b⟫_ℝ = ⟪a, pmK k b⟫_ℝ := by
  simp [pmK, real_inner_smul_left, real_inner_smul_right]

theorem pmM_inv (hm : 0 < m) (w : PointMassCoord) : pmM m (pmMinv m w) = w := by
  simp only [pmM, pmMinv, smul_apply, ContinuousLinearMap.id_apply, smul_smul]
  rw [mul_inv_cancel₀ hm.ne', one_smul]

theorem pmD_nonneg (hd : 0 < d) (v : PointMassCoord) : 0 ≤ ⟪v, pmD d v⟫_ℝ := by
  simp only [pmD, smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  positivity

theorem pmD_def (hd : 0 < d) (v : PointMassCoord) : ⟪v, pmD d v⟫_ℝ = 0 → v = 0 := by
  simp only [pmD, smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  intro h
  have : ‖v‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hd.ne'
    · exact h0
  have hv0 : ‖v‖ = 0 := by nlinarith [sq_nonneg ‖v‖, norm_nonneg v]
  exact norm_eq_zero.mp hv0

theorem pmK_def (hk : 0 < k) (x : PointMassCoord) : pmK k x = 0 → x = 0 := by
  simp only [pmK, smul_apply, ContinuousLinearMap.id_apply]
  intro h
  rcases smul_eq_zero.mp h with h0 | h0
  · exact absurd h0 hk.ne'
  · exact h0

end ScalarOperators

section Invariance

variable (m d k : ℝ)

/-- Local helper: energy is nonincreasing forward in time along any solution
of a field with `fderiv V [f] ≤ 0` everywhere (the flow-level integration
Ctrllib.LaSalle's own `lasalle` proof performs internally). -/
private theorem energy_antitone_of_decrease {V : PointMassState → ℝ}
    {f : PointMassState → PointMassState}
    {ϕ : Flow ℝ PointMassState} (hϕ : IsSolutionTo ϕ f) (hV : Differentiable ℝ V)
    (hdec : ∀ y, fderiv ℝ V y (f y) ≤ 0) (z : PointMassState) :
    Antitone (fun t : ℝ => V (ϕ t z)) := by
  have hg_diff : Differentiable ℝ fun t : ℝ => V (ϕ t z) := fun t =>
    (hϕ.hasDerivAt_comp hV z t).differentiableAt
  have hg_deriv : ∀ t : ℝ, deriv (fun t : ℝ => V (ϕ t z)) t ≤ 0 := fun t => by
    rw [(hϕ.hasDerivAt_comp hV z t).deriv]
    exact hdec _
  exact antitone_of_deriv_nonpos hg_diff hg_deriv

/-- The point-mass flow, viewed as solving the scalar-operator `comField`. -/
private theorem pointMass_isSolutionTo_comField (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) :
    IsSolutionTo (pointMassFlow m d k hm) (comField (pmD d) (pmK k) (pmMinv m)) := by
  intro z t
  have h := pointMass_isSolutionTo m d k hm hd hk z t
  rwa [pointMassField_eq_comField] at h

/-- **T2, second half — the energy sublevels are forward invariant.** -/
theorem pointMass_sublevel_forwardInvariant (hm : 0 < m) (hd : 0 < d) (hk : 0 < k) (R : ℝ) :
    ∀ z, pointMassEnergy m k z ≤ R → ∀ t : ℝ, 0 ≤ t →
      pointMassEnergy m k (pointMassFlow m d k hm t z) ≤ R := by
  intro z hz t ht
  have hϕfield := pointMass_isSolutionTo_comField m d k hm hd hk
  have hdec := com_decrease (M := pmM m) (D := pmD d) (K := pmK k) (Minv := pmMinv m)
    pmM_selfAdjoint pmK_selfAdjoint (pmM_inv hm) (pmD_nonneg hd)
  have hanti := energy_antitone_of_decrease hϕfield comEnergy_differentiable hdec z
  have h0 : (fun t : ℝ => comEnergy (pmM m) (pmK k) ((pointMassFlow m d k hm) t z)) 0
      = comEnergy (pmM m) (pmK k) z := by
    simp [(pointMassFlow m d k hm).map_zero_apply]
  have hstep : comEnergy (pmM m) (pmK k) ((pointMassFlow m d k hm) t z) ≤
      comEnergy (pmM m) (pmK k) z := h0 ▸ hanti ht
  rw [pointMassEnergy_eq_comEnergy]
  calc comEnergy (pmM m) (pmK k) ((pointMassFlow m d k hm) t z)
      ≤ comEnergy (pmM m) (pmK k) z := hstep
    _ = pointMassEnergy m k z := (pointMassEnergy_eq_comEnergy m k z).symm
    _ ≤ R := hz

/-- **T3 — global asymptotic convergence.** Assembles the sealed
`Ctrllib.com_attractive`: forward precompactness comes from coercivity plus
the forward decrease just proved, and the scalar operator hypotheses are
`pmM_selfAdjoint` / `pmK_selfAdjoint` / `pmM_inv` / `pmD_nonneg` / `pmD_def` /
`pmK_def`. No new LaSalle argument is written here. -/
theorem pointMass_tendsto_zero (m d k : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k)
    (z₀ : PointMassState) :
    Tendsto (fun t : ℝ => pointMassFlow m d k hm t z₀) atTop (𝓝 0) := by
  have hϕfield := pointMass_isSolutionTo_comField m d k hm hd hk
  have hdec := com_decrease (M := pmM m) (D := pmD d) (K := pmK k) (Minv := pmMinv m)
    pmM_selfAdjoint pmK_selfAdjoint (pmM_inv hm) (pmD_nonneg hd)
  have hcpt : ForwardPrecompact (pointMassFlow m d k hm) z₀ := by
    apply forwardPrecompact_of_coercive (V := comEnergy (pmM m) (pmK k))
      (pointMassFlow m d k hm) z₀ (c₁ := min m k / 2) (by positivity)
    · intro y
      rw [← pointMassEnergy_eq_comEnergy]
      exact pointMassEnergy_coercive m k hm hk y
    · intro t ht
      have hanti := energy_antitone_of_decrease hϕfield comEnergy_differentiable hdec z₀
      have h0 : (fun t : ℝ => comEnergy (pmM m) (pmK k) ((pointMassFlow m d k hm) t z₀)) 0
          = comEnergy (pmM m) (pmK k) z₀ := by
        simp [(pointMassFlow m d k hm).map_zero_apply]
      exact h0 ▸ hanti ht
  exact com_attractive (pointMassFlow m d k hm) hϕfield
    pmM_selfAdjoint pmK_selfAdjoint (pmM_inv hm) (pmD_nonneg hd) (pmD_def hd) (pmK_def hk) z₀ hcpt

end Invariance

end Ctrllib

#print axioms Ctrllib.pointMassCLM_apply
#print axioms Ctrllib.pointMassFlow_hasDerivAt
#print axioms Ctrllib.pointMass_isSolutionTo
#print axioms Ctrllib.pointMass_sublevel_isCompact
#print axioms Ctrllib.pointMass_sublevel_forwardInvariant
#print axioms Ctrllib.pointMass_tendsto_zero
