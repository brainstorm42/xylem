/-
König decomposition — the algebraic core of P2 (ctrllib).

Ground: the spatial numeric pin in the associated proof evidence record (`the corresponding private check`)
(Pinocchio 3.8 + CasADi AD; 3-D free-flying base + n-link spatial revolute chain, n = 1,2,3,6,7;
run 2026-08-28, all checks PASS to 1e-13, exit 0; receipt
the corresponding local note). Its planar predecessor `the corresponding local note`
(SymPy, verdict GO 2026-07-12, memo the corresponding local note) remains as a stepping
stone only. The pin establishes, n-generically, four properties of the augmented dynamics
written in whole-body–CoM coordinates:
  (K) König split      T = ½ m_t‖v_c‖² + T_int,  with ∂T_int/∂v_c = 0;
  (D) inertial decoupling  M = diag(m_t E, M_shape), CoM↔shape off-diagonal ≡ 0;
  (C) the CoM position is cyclic (M is translation-invariant);
  (R) the Christoffel/Coriolis rows for the CoM coordinates vanish.

This module formalizes the ALGEBRAIC HEART that (K),(D),(C) all rest on: König's second
theorem for a finite family of point masses. Everything above follows from the single
identity `∑ mᵢ sᵢ = 0` about the CoM (`hbal` here, with `sᵢ - d = wᵢ` the body velocity
relative to the CoM). Writing each body velocity as `v_c + wᵢ` (inertial CoM velocity plus
a relative field with `∑ mᵢ wᵢ = 0`):

  * `com_cross_term_zero`     — the CoM velocity does not couple to any relative-velocity
                                field: `∑ mᵢ ⟪v_c, wᵢ⟫ = 0`. This is (C)/(D)'s core (the
                                off-diagonal CoM↔shape inertia block is identically zero)
                                and (R)'s translation-invariance driver.
  * `koenig_inertia_bilinear` — the POLARIZED König split, i.e. property (D) in full:
        ∑ mᵢ ⟪v_c + wᵢ, v_c' + wᵢ'⟫ = (∑ mᵢ) ⟪v_c, v_c'⟫ + ∑ mᵢ ⟪wᵢ, wᵢ'⟫,
      exhibiting the block structure — the CoM–CoM block carries the constant coefficient
      `m_t = ∑ mᵢ` (so the CoM inertia block is `m_t · id`), and BOTH CoM↔shape coupling
      blocks `⟪v_c, wᵢ'⟫`, `⟪wᵢ, v_c'⟫` drop out.
  * `koenig_kinetic_split`    — König's second theorem, the norm form (diagonal case):
        ∑ mᵢ‖v_c + wᵢ‖² = (∑ mᵢ)‖v_c‖² + ∑ mᵢ‖wᵢ‖².
  * `koenig_energy_split`     — property (K) as the physicist writes it:
        T = ½ m_t‖v_c‖² + T_int,  T_int = ½ ∑ mᵢ‖wᵢ‖²  (visibly free of v_c).

Scope / honest boundary. This is the coordinate-free algebra over an arbitrary real inner
product space `E`, with masses arbitrary reals (positivity is not needed for the split).
It is the form the thesis uses. The Lagrangian/Christoffel layer — property (R) as the
literal statement that the Coriolis rows `c_{c i j}` vanish — is a statement about
derivatives of a configuration-dependent mass matrix and is left to the pin
(`the corresponding private check`, symbolic Christoffel) and the wiki's human proof; here it is present
only through its algebraic causes (D)+(C), which (D)+(C) ⟹ (R) discharges by the Christoffel
formula. See the interfaces note in the P2 return.

Published anchors:
  * König's second theorem: D. Cline, *Variational Principles in Classical Mechanics*, 2nd
    ed., 2018, §2.10 eq. (2.10.4)  T = ∑ ½ mᵢ vᵢ′² + ½ M V²  ("Samuel König's second
    theorem").
  * Giordano 2019 RA-L (the corresponding local note),
    transform Γ eq. (19) line 204; eq. (21) line 218; cancellation sentence line 221;
    eq. (22a) line 224; frame 𝒞 non-rotating by definition, line 53. The CoM
    row `m v̇_c = f_c` is Coriolis-free precisely because the CoM inertia block is the
    constant `m_t E` and decouples — exactly `koenig_inertia_bilinear` here.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped InnerProductSpace BigOperators

namespace Ctrllib

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {s : Finset ι} {m : ι → ℝ} {w w' : ι → E}

/-- **CoM cross-term vanishes** (properties (C)/(D) core). If the mass-weighted relative
velocities balance about the CoM, `∑ mᵢ • wᵢ = 0`, then the CoM velocity `v_c` is inertially
orthogonal to the whole family: `∑ mᵢ ⟪v_c, wᵢ⟫ = 0`. This is the identity that zeroes the
CoM↔shape off-diagonal inertia block and makes the CoM coordinate cyclic. Pin (D)/(C). -/
theorem com_cross_term_zero (hbal : ∑ i ∈ s, m i • w i = 0) (vc : E) :
    ∑ i ∈ s, m i * ⟪vc, w i⟫_ℝ = 0 := by
  calc ∑ i ∈ s, m i * ⟪vc, w i⟫_ℝ
      = ∑ i ∈ s, ⟪vc, m i • w i⟫_ℝ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [real_inner_smul_right]
    _ = ⟪vc, ∑ i ∈ s, m i • w i⟫_ℝ := (inner_sum _ _ _).symm
    _ = ⟪vc, (0 : E)⟫_ℝ := by rw [hbal]
    _ = 0 := inner_zero_right _

/-- **König's second theorem, polarized** — property (D), the inertial block-diagonalization.
With both relative-velocity fields balanced about the CoM (`∑ mᵢ • wᵢ = 0`,
`∑ mᵢ • wᵢ' = 0`), the mass-weighted inner product of the two body-velocity fields
`v_c + wᵢ`, `v_c' + wᵢ'` splits with NO cross terms:

    ∑ mᵢ ⟪v_c + wᵢ, v_c' + wᵢ'⟫ = (∑ mᵢ) ⟪v_c, v_c'⟫ + ∑ mᵢ ⟪wᵢ, wᵢ'⟫.

The CoM–CoM block carries the constant total mass `m_t = ∑ mᵢ` (the CoM inertia block is
`m_t · id`); both CoM↔shape coupling blocks vanish by `com_cross_term_zero`. This is exactly
Giordano eq. (21)'s constant, decoupled CoM block. Pin (D). -/
theorem koenig_inertia_bilinear
    (hbal : ∑ i ∈ s, m i • w i = 0) (hbal' : ∑ i ∈ s, m i • w' i = 0) (vc vc' : E) :
    ∑ i ∈ s, m i * ⟪vc + w i, vc' + w' i⟫_ℝ
      = (∑ i ∈ s, m i) * ⟪vc, vc'⟫_ℝ + ∑ i ∈ s, m i * ⟪w i, w' i⟫_ℝ := by
  have h3 : ∑ i ∈ s, m i * ⟪w i, vc'⟫_ℝ = 0 := by
    calc ∑ i ∈ s, m i * ⟪w i, vc'⟫_ℝ
        = ∑ i ∈ s, m i * ⟪vc', w i⟫_ℝ := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [real_inner_comm]
      _ = 0 := com_cross_term_zero hbal vc'
  have key : ∑ i ∈ s, m i * ⟪vc + w i, vc' + w' i⟫_ℝ
      = (∑ i ∈ s, m i * ⟪vc, vc'⟫_ℝ) + (∑ i ∈ s, m i * ⟪vc, w' i⟫_ℝ)
        + (∑ i ∈ s, m i * ⟪w i, vc'⟫_ℝ) + (∑ i ∈ s, m i * ⟪w i, w' i⟫_ℝ) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [inner_add_left, inner_add_right]
    ring
  rw [key, com_cross_term_zero hbal' vc, h3, Finset.sum_mul]
  abel

/-- **König's second theorem, norm form** — the diagonal case of `koenig_inertia_bilinear`.
For a relative-velocity field balanced about the CoM (`∑ mᵢ • wᵢ = 0`), the total quadratic
form splits cleanly:

    ∑ mᵢ‖v_c + wᵢ‖² = (∑ mᵢ)‖v_c‖² + ∑ mᵢ‖wᵢ‖².

The `∑ mᵢ‖wᵢ‖²` term carries no `v_c`, so it is the internal (shape) energy. Pin (K). -/
theorem koenig_kinetic_split (hbal : ∑ i ∈ s, m i • w i = 0) (vc : E) :
    ∑ i ∈ s, m i * ‖vc + w i‖ ^ 2
      = (∑ i ∈ s, m i) * ‖vc‖ ^ 2 + ∑ i ∈ s, m i * ‖w i‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq]
  exact koenig_inertia_bilinear hbal hbal vc vc

/-- **König split of the kinetic energy** — property (K) as stated physically. The total
kinetic energy `T = ½ ∑ mᵢ‖v_c + wᵢ‖²` decomposes as the CoM (translational) energy plus an
internal energy manifestly independent of the CoM velocity `v_c`:

    T = ½ m_t‖v_c‖² + T_int,   T_int = ½ ∑ mᵢ‖wᵢ‖²,   m_t = ∑ mᵢ.

Immediate from `koenig_kinetic_split`. Pin (K). -/
theorem koenig_energy_split (hbal : ∑ i ∈ s, m i • w i = 0) (vc : E) :
    (1 / 2) * ∑ i ∈ s, m i * ‖vc + w i‖ ^ 2
      = (1 / 2) * (∑ i ∈ s, m i) * ‖vc‖ ^ 2 + (1 / 2) * ∑ i ∈ s, m i * ‖w i‖ ^ 2 := by
  rw [koenig_kinetic_split hbal]; ring

end Ctrllib

#print axioms Ctrllib.com_cross_term_zero
#print axioms Ctrllib.koenig_inertia_bilinear
#print axioms Ctrllib.koenig_kinetic_split
#print axioms Ctrllib.koenig_energy_split
