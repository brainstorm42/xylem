/-
CoM tracking loop — global asymptotic stability via the sealed LaSalle engine
(TARGET 1 of the ctrllib stream, difficulty M, the rung's headline).

SYSTEM (the source model note §4.3 line 402 / eq 4.9; Giordano 2019 RA-L eq 34a — the
homogeneous damped second-order CoM-error loop):

    M x'' + D x' + K x = 0 ,   M, D, K symmetric positive definite.

Written as a first-order field on the state `z = (v, x)` with `v = x'`:

    f(v, x) = ( -M⁻¹(D v + K x) ,  v ) .

The storage function is the mechanical energy

    V(v, x) = ½ ⟪v, M v⟫ + ½ ⟪x, K x⟫ .

WHAT IS PROVEN OUTRIGHT (real content, non-vacuous):
  `com_dissipation` — the energy-dissipation identity `DV(z)[f z] = -⟪v, D v⟫`.
    The `K` cross terms cancel by symmetry of `K`; the `M⁻¹` cancels against
    the `M` in `∇V` (SymPy-pinned, the corresponding symbolic check (not bundled).py).
  `com_decrease` — `DV(z)[f z] ≤ 0` (negative semidefinite: `D ⪰ 0`).
  `com_collapse` — the LaSalle collapse: on ANY invariant set where `DV[f] = 0`
    the state is the origin. This is the headline — the largest invariant set in
    `{v = 0}` is `{0}`, proved with the invariance of the ω-limit set (not just
    the zero-set containment `propIV1_tendsto` consumes): `v ≡ 0` along the orbit
    ⇒ `v̇ ≡ 0` ⇒ `M⁻¹ K x = 0` ⇒ `K x = 0` ⇒ `x = 0` (`K` injective).
  `com_attractive` — the assembly: every precompact orbit converges to the origin,
    `ϕ t z₀ → 0`. Wires the sealed L3 `lasalle` and the L4a reduction engine
    `tendsto_infDist_of_omegaLimit_subset` through the collapse.

VALUE. `com_attractive` discharges cascade step 1 of Prop IV.1 (Corollary 12 condition
"y = 0 is a GAS equilibrium of ẏ = g(y)") at the attractivity level: the autonomous
Hurwitz CoM-error driver, previously supplied as a hypothesis. What is proved is
convergence of every forward-precompact trajectory, not ε–δ stability (for the
genuine notion see `KhalilStability.AsympStable`). Fully explicit linear field, so the
LaSalle collapse is proved outright rather than interfaced (contrast
`propIV1_tendsto`'s `hzero`).

INTERFACES (named, not `sorry` — the L3/L4a precedent):
  * `IsSolutionTo ϕ f` — the flow solving the ODE (existence/Picard–Lindelöf
    stays applier-side, exactly as in LaSalle.lean).
  * `hcpt` — `ForwardPrecompact ϕ z₀`, precompactness of the FORWARD orbit
    only (the forward-only refactor of the SAME named hypothesis `lasalle` and
    `propIV1_tendsto` carry). Coercivity of `V` (the sealed
    `Ctrllib.blockLyap_coercive`, `forwardPrecompact_of_coercive`) supplies it;
    two-sided precompactness is no longer required (see the wiki page
    the corresponding local note §5).
  * The operator hypotheses `hMsa/hKsa` (symmetry), `hMinv` (M invertible),
    `hDnn/hDdef` (D ⪰ 0, definite), `hKdef` (K injective) ARE positive-definite
    symmetry; for concrete symmetric-PosDef matrices they are discharged by the
    sealed `Ctrllib.le_dotProduct_mulVec` / `PosDef.isUnit` (Rayleigh,
    StiffnessResidual). See the .

SymPy pin: the corresponding symbolic check (not bundled).py.
Human derivation: the corresponding derivation record (not bundled)
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Ctrllib.LaSalle
import Ctrllib.Reduction

open Set Filter Topology omegaLimit
open scoped InnerProductSpace

namespace Ctrllib

section CoM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (M D K Minv : H →L[ℝ] H)

/-- The state space of the second-order loop: velocity `×` position. -/
abbrev ComState (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] := H × H

/-- The closed-loop field `f(v, x) = (-M⁻¹(D v + K x), v)` (eq 34a, first-order
form). `Minv` is the given inverse of `M`. -/
def comField (z : ComState H) : ComState H := (-(Minv (D z.1 + K z.2)), z.1)

/-- The mechanical energy `V(v, x) = ½⟪v, M v⟫ + ½⟪x, K x⟫` (eq 37 / 4.15
specialized to the CoM block). -/
noncomputable def comEnergy (z : ComState H) : ℝ :=
  (1 / 2 : ℝ) * ⟪z.1, M z.1⟫_ℝ + (1 / 2 : ℝ) * ⟪z.2, K z.2⟫_ℝ

variable {M D K Minv}

/-- `V` is differentiable everywhere (quadratic form of continuous operators). -/
theorem comEnergy_differentiable : Differentiable ℝ (comEnergy M K) := by
  intro z
  have h1 : DifferentiableAt ℝ (fun w : ComState H => ⟪w.1, M w.1⟫_ℝ) z :=
    differentiableAt_fst.inner ℝ (M.differentiableAt.comp z differentiableAt_fst)
  have h2 : DifferentiableAt ℝ (fun w : ComState H => ⟪w.2, K w.2⟫_ℝ) z :=
    differentiableAt_snd.inner ℝ (K.differentiableAt.comp z differentiableAt_snd)
  exact (h1.const_mul _).add (h2.const_mul _)

/-- **Energy-dissipation identity.** `DV(z)[f z] = -⟪v, D v⟫`. The `M⁻¹` cancels
against the `M` in `∇V`, and the `K` cross terms cancel by symmetry of `K`
(SymPy-pinned). Needs `M`, `K` symmetric and `M ∘ M⁻¹ = id`. -/
theorem com_dissipation
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w) (z : ComState H) :
    fderiv ℝ (comEnergy M K) z (comField D K Minv z) = -⟪z.1, D z.1⟫_ℝ := by
  have hMf : DifferentiableAt ℝ (fun w : ComState H => M w.1) z :=
    M.differentiableAt.comp z differentiableAt_fst
  have hKf : DifferentiableAt ℝ (fun w : ComState H => K w.2) z :=
    K.differentiableAt.comp z differentiableAt_snd
  have hi1 : DifferentiableAt ℝ (fun w : ComState H => ⟪w.1, M w.1⟫_ℝ) z :=
    differentiableAt_fst.inner ℝ hMf
  have hi2 : DifferentiableAt ℝ (fun w : ComState H => ⟪w.2, K w.2⟫_ℝ) z :=
    differentiableAt_snd.inner ℝ hKf
  -- linearity of fderiv: split the two half-blocks
  rw [show comEnergy M K =
      (fun w : ComState H => (1 / 2 : ℝ) * ⟪w.1, M w.1⟫_ℝ)
        + (fun w : ComState H => (1 / 2 : ℝ) * ⟪w.2, K w.2⟫_ℝ) from rfl]
  rw [fderiv_add (hi1.const_mul _) (hi2.const_mul _), add_apply,
    fderiv_const_mul hi1, fderiv_const_mul hi2, smul_apply,
    smul_apply, smul_eq_mul, smul_eq_mul,
    fderiv_inner_apply ℝ differentiableAt_fst hMf (comField D K Minv z),
    fderiv_inner_apply ℝ differentiableAt_snd hKf (comField D K Minv z)]
  -- reduce the four sub-fderivs applied to `f z`
  have d_fst : fderiv ℝ (Prod.fst : ComState H → H) z = ContinuousLinearMap.fst ℝ H H :=
    hasFDerivAt_fst.fderiv
  have d_snd : fderiv ℝ (Prod.snd : ComState H → H) z = ContinuousLinearMap.snd ℝ H H :=
    hasFDerivAt_snd.fderiv
  have d_Mf : fderiv ℝ (fun w : ComState H => M w.1) z
      = M.comp (ContinuousLinearMap.fst ℝ H H) :=
    (M.hasFDerivAt.comp z hasFDerivAt_fst).fderiv
  have d_Kf : fderiv ℝ (fun w : ComState H => K w.2) z
      = K.comp (ContinuousLinearMap.snd ℝ H H) :=
    (K.hasFDerivAt.comp z hasFDerivAt_snd).fderiv
  rw [d_fst, d_snd, d_Mf, d_Kf]
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  -- the four inner terms, each reduced with M/K symmetry and M∘M⁻¹ = id
  have e1 : ⟪z.1, M (comField D K Minv z).1⟫_ℝ
      = -(⟪z.1, D z.1⟫_ℝ + ⟪z.1, K z.2⟫_ℝ) := by
    change ⟪z.1, M (-(Minv (D z.1 + K z.2)))⟫_ℝ = _
    rw [map_neg, hMinv, inner_neg_right, inner_add_right]
  have e2 : ⟪(comField D K Minv z).1, M z.1⟫_ℝ
      = -(⟪z.1, D z.1⟫_ℝ + ⟪z.1, K z.2⟫_ℝ) := by
    change ⟪-(Minv (D z.1 + K z.2)), M z.1⟫_ℝ = _
    rw [inner_neg_left, real_inner_comm (M z.1) (Minv _), hMsa z.1 (Minv _), hMinv,
      inner_add_right]
  have e3 : ⟪z.2, K (comField D K Minv z).2⟫_ℝ = ⟪z.1, K z.2⟫_ℝ := by
    change ⟪z.2, K z.1⟫_ℝ = _
    rw [← hKsa z.2 z.1, real_inner_comm]
  have e4 : ⟪(comField D K Minv z).2, K z.2⟫_ℝ = ⟪z.1, K z.2⟫_ℝ := rfl
  rw [e1, e2, e3, e4]
  ring

/-- **Weak decrease.** `DV(z)[f z] ≤ 0` — negative semidefinite (`D ⪰ 0`). -/
theorem com_decrease
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ) (z : ComState H) :
    fderiv ℝ (comEnergy M K) z (comField D K Minv z) ≤ 0 := by
  rw [com_dissipation hMsa hKsa hMinv z]
  exact neg_nonpos.mpr (hDnn z.1)

/-- **The LaSalle collapse (headline).** On any set `S` invariant under the flow,
on which `DV[f] = 0`, the state is the origin: `S ⊆ {0}`. Uses the flow's
invariance to run `v ≡ 0 ⇒ v̇ ≡ 0 ⇒ K x = 0 ⇒ x = 0`. -/
theorem com_collapse (ϕ : Flow ℝ (ComState H))
    (hϕ : IsSolutionTo ϕ (comField D K Minv))
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hDdef : ∀ v : H, ⟪v, D v⟫_ℝ = 0 → v = 0)
    (hKdef : ∀ x : H, K x = 0 → x = 0)
    {S : Set (ComState H)} (hinv : IsInvariant ϕ.toFun S)
    (hvanish : ∀ y ∈ S, fderiv ℝ (comEnergy M K) y (comField D K Minv y) = 0) :
    S ⊆ {0} := by
  -- velocity component vanishes on all of S
  have hv0 : ∀ w ∈ S, (w : ComState H).1 = 0 := by
    intro w hw
    have h := hvanish w hw
    rw [com_dissipation hMsa hKsa hMinv w] at h
    exact hDdef _ (by linarith [h])
  -- Minv is injective (M is its left inverse)
  have hMinj : Function.Injective Minv := by
    intro a b hab
    have := congrArg M hab
    rwa [hMinv, hMinv] at this
  intro y hy
  rw [Set.mem_singleton_iff]
  have hy1 : y.1 = 0 := hv0 y hy
  -- (f y).1 = 0 by derivative uniqueness on the constant-zero velocity
  have hbase : HasDerivAt (fun s : ℝ => ϕ s y) (comField D K Minv y) 0 := by
    have h := hϕ y 0
    rwa [ϕ.map_zero_apply] at h
  have hproj : HasDerivAt (fun s : ℝ => (ϕ s y).1) (comField D K Minv y).1 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (ContinuousLinearMap.fst ℝ H H).hasFDerivAt hbase
    simpa only [ContinuousLinearMap.coe_fst', Function.comp_def] using h
  have hconst : (fun s : ℝ => (ϕ s y).1) = fun _ => (0 : H) := by
    funext s
    exact hv0 _ (hinv s hy)
  have hzero : HasDerivAt (fun s : ℝ => (ϕ s y).1) 0 0 := by
    rw [hconst]; exact hasDerivAt_const 0 0
  have hfy1 : (comField D K Minv y).1 = 0 := hproj.unique hzero
  -- unpack: (f y).1 = -(Minv (K y.2)) since y.1 = 0
  have hval : (comField D K Minv y).1 = -(Minv (K y.2)) := by
    change -(Minv (D y.1 + K y.2)) = _
    rw [hy1, map_zero, zero_add]
  rw [hval, neg_eq_zero] at hfy1
  have hKy : K y.2 = 0 := hMinj (by rw [hfy1, map_zero])
  have hy2 : y.2 = 0 := hKdef _ hKy
  exact Prod.ext hy1 hy2

/-- **Attractivity of the CoM loop (the deliverable).** For a flow solving the
closed-loop field, every forward-precompact trajectory converges to the origin:
`ϕ t z₀ → 0`. This is attractivity of forward-precompact trajectories, not ε–δ
stability (see `KhalilStability.AsympStable` for the genuine notion; formerly
named `com_gas`). Assembles the sealed `lasalle` (L3) and
`tendsto_infDist_of_omegaLimit_subset` (L4a) through `com_collapse`. -/
theorem com_attractive (ϕ : Flow ℝ (ComState H))
    (hϕ : IsSolutionTo ϕ (comField D K Minv))
    (hMsa : ∀ a b : H, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hKsa : ∀ a b : H, ⟪K a, b⟫_ℝ = ⟪a, K b⟫_ℝ)
    (hMinv : ∀ w : H, M (Minv w) = w)
    (hDnn : ∀ v : H, 0 ≤ ⟪v, D v⟫_ℝ)
    (hDdef : ∀ v : H, ⟪v, D v⟫_ℝ = 0 → v = 0)
    (hKdef : ∀ x : H, K x = 0 → x = 0)
    (z₀ : ComState H)
    (hcpt : ForwardPrecompact ϕ z₀) :
    Tendsto (fun t : ℝ => ϕ t z₀) atTop (𝓝 0) := by
  have hlas := lasalle ϕ hϕ comEnergy_differentiable
    (com_decrease hMsa hKsa hMinv hDnn) z₀ hcpt
  have hsub : ω⁺ ϕ.toFun {z₀} ⊆ ({0} : Set (ComState H)) :=
    com_collapse ϕ hϕ hMsa hKsa hMinv hDdef hKdef hlas.2.1 hlas.2.2.2
  have htend := tendsto_infDist_of_omegaLimit_subset ϕ z₀ hcpt hsub
  simp only [Metric.infDist_singleton] at htend
  rw [tendsto_iff_dist_tendsto_zero]
  exact htend

@[deprecated com_attractive (since := "2026-08-15")]
alias com_gas := com_attractive

end CoM

end Ctrllib

#print axioms Ctrllib.com_dissipation
#print axioms Ctrllib.com_decrease
#print axioms Ctrllib.com_collapse
#print axioms Ctrllib.com_attractive
