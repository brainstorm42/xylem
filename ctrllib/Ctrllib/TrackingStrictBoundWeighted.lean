/-
Weighted (M̆, K̆-metric) restatement of the PD+ domination step (the corresponding design note,
follow-up to TrackingStrictBound). Motivation, from the "Application layer" update
of the corresponding local note: `TrackingStrictBound.strict_rate_dominated`
states its bounds relative to the STACKED EUCLIDEAN quadratic forms E = e⬝e,
X = x̃⬝x̃. For the implemented UR3 model and nominal gains, the sampled constants
give m₁ = 9.1e−4 against m₂ = 132 — i.e. M̆'s Euclidean-coordinate conditioning
(≈1.4e5) enters every constant of the certificate — and NO admissible α exists for
the implemented residual. The report's diagnosis: "a metric weighted by M̆ and K̆
(the storage's own norm) is needed, not the identity."

THE STEP. `TrackingCrossTerm.cross_term_rate_identity` (F = 0) gives the exact rate
of W = V_e + α gᵀM̆e; `TrackingStrictBound.strict_rate_dominated` dominates that rate
under NAMED pointwise bounds stated against E, X. This module proves the SAME
implication with every bound restated against the storage's own weighted quadratic
forms

    E_M := e ⬝ᵥ (M *ᵥ e),   X_K := x ⬝ᵥ (K *ᵥ x),

so a constant such as d₁ (damping floor) is a ratio relative to the M̆-metric energy
rather than to raw Euclidean length — the route the deliverable names as "the only
listed route to an admissible κ" for the implemented residual.

CAVEAT: not literally every bound is reweighted. `hgg` (γ₁² X_K ≤ g⬝ᵥg) keeps the
EUCLIDEAN dot product on the stiffness force g = J_x̃ᵀK̆x̃, because the rate identity's
cross terms pair against g itself rather than a weighted form of it; and since M is
only PSD (not PD), E_M can vanish at some e ≠ 0, so the weighted conclusion alone
carries no coercivity in e by itself.

BUILDING BLOCK (searched first; Mathlib has no ready-made weighted Cauchy–Schwarz
for `Matrix.PosSemidef` dot products — see `Mathlib/LinearAlgebra/Matrix/PosDef.lean`,
which supplies only `dotProduct_mulVec_nonneg`, and
`Mathlib/LinearAlgebra/BilinearForm/Properties.lean`, whose `IsPosSemidef` has no
Cauchy–Schwarz corollary either). `weighted_young_cross` is proved by hand, by the
SAME discriminant trick as `TrackingStrictBound.young_cross` lifted from scalars to
the M̆-quadratic form: `0 ≤ (1/(2λ)) (λu − v) ⬝ᵥ M *ᵥ (λu − v)` expands (via M
symmetric) to the Young bound directly — no case split, unlike the sqrt-form
Cauchy–Schwarz `|u⬝ᵥMv| ≤ √(u⬝ᵥMu)√(v⬝ᵥMv)`, which needs a degenerate-radius case
split this module does not need: every downstream use here (`strict_rate_dominated`
itself, and every cross-term bound in its weighted mirror) already consumes cross
terms through the Young form, never through the bare square-root Cauchy–Schwarz
statement, so only the Young form is proved.

WHAT IS PROVEN:
  `weighted_young_cross`         — u⬝ᵥMv ≤ (λ/2)(u⬝ᵥMu) + (1/(2λ))(v⬝ᵥMv) for M
                                    symmetric PSD, λ > 0, any u, v.
  `weighted_residual_bound`      — corollary at λ = ρ: if r⬝ᵥKr ≤ ρ²(x⬝ᵥKx) (r is
                                    small relative to x in the K̆-metric) then
                                    x⬝ᵥKr ≤ ρ (x⬝ᵥKx) — the weighted form of the
                                    kinematics-residual hypothesis `hr`.
  `strict_rate_dominated_weighted` — the domination step of
                                    `TrackingStrictBound.strict_rate_dominated`,
                                    every bound restated against E_M, X_K instead of
                                    E, X; same κ formula (`quad_form_dominates` is
                                    generic in `s, t` and is reused unchanged).

PINNED (the corresponding project check (not bundled).py):
  (A) weighted Young, numeric + the symbolic quadratic expansion; (B) the residual
  corollary; (C) the weighted dominated rate on random data satisfying the weighted
  bounds.

INTERFACE BOUNDARY (honest, unchanged from `TrackingStrictBound`). The constants
d₁, γ₁, κr, c₁..c₅ are still hypotheses at one instant; what supplies them
uniformly on a forward-invariant set is still the application layer (Rayleigh
bounds, σ_min(J_x̃) > 0, Coriolis growth, `‖r‖ ≤ 3‖x̃‖‖v̆_d‖`). What THIS module
changes is only the metric the constants are measured against — it does not by
itself supply admissible numeric constants; that evaluation is the next
application-layer step (`the corresponding private check`'s Euclidean run is the one
that failed and motivated this restatement).
-/
import Ctrllib.TrackingStrictBound

open Matrix

namespace Ctrllib

variable {n m : Type*} [Fintype n] [Fintype m]

section WeightedYoung

variable {M : Matrix n n ℝ}

/-- A symmetric matrix's `mulVec`-dot-product is commutative: `u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u`.
Same route as `TrackingDissipation.stiffness_cross_symm`, specialised to one matrix. -/
private lemma dotProduct_mulVec_symm (hM : Mᵀ = M) (u v : n → ℝ) :
    u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u := by
  rw [dotProduct_mulVec u M v, ← mulVec_transpose, hM, dotProduct_comm]

/-- **Weighted Young's inequality.** For `M` symmetric and positive semidefinite
(`hMpsd` as the pointwise nonnegativity of its quadratic form, the house convention
of `Rayleigh.lean`/`TrackingStrictBound.lean`), any `u, v` and `λ > 0`:
`u ⬝ᵥ M *ᵥ v ≤ (λ/2)(u ⬝ᵥ M *ᵥ u) + (1/(2λ))(v ⬝ᵥ M *ᵥ v)`. Generalises
`TrackingStrictBound.young_cross` from scalars to the `M`-weighted quadratic form:
the same `0 ≤ (1/(2λ))(λu − v)ᵀM(λu − v)` expansion, now over vectors. -/
theorem weighted_young_cross (hM : Mᵀ = M) (hMpsd : ∀ z : n → ℝ, 0 ≤ z ⬝ᵥ M *ᵥ z)
    {lam : ℝ} (hlam : 0 < lam) (u v : n → ℝ) :
    u ⬝ᵥ M *ᵥ v ≤ lam / 2 * (u ⬝ᵥ M *ᵥ u) + 1 / (2 * lam) * (v ⬝ᵥ M *ᵥ v) := by
  have hw := hMpsd (lam • u - v)
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul] at hw
  rw [dotProduct_mulVec_symm hM v u] at hw
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have heq : lam / 2 * (u ⬝ᵥ M *ᵥ u) + 1 / (2 * lam) * (v ⬝ᵥ M *ᵥ v) - u ⬝ᵥ M *ᵥ v
      = (lam * (lam * (u ⬝ᵥ M *ᵥ u) - u ⬝ᵥ M *ᵥ v)
          - (lam * (u ⬝ᵥ M *ᵥ v) - v ⬝ᵥ M *ᵥ v)) / (2 * lam) := by
    field_simp
    ring
  have hnn : 0 ≤ (lam * (lam * (u ⬝ᵥ M *ᵥ u) - u ⬝ᵥ M *ᵥ v)
      - (lam * (u ⬝ᵥ M *ᵥ v) - v ⬝ᵥ M *ᵥ v)) / (2 * lam) :=
    div_nonneg hw (by positivity)
  linarith [heq, hnn]

/-- **Weighted kinematics-residual corollary.** If the residual `r` is small relative
to `x` in the `K`-metric (`r ⬝ᵥ K *ᵥ r ≤ ρ² (x ⬝ᵥ K *ᵥ x)`), then
`x ⬝ᵥ K *ᵥ r ≤ ρ (x ⬝ᵥ K *ᵥ x)` — the weighted form of the `hr` hypothesis of
`strict_rate_dominated`, obtained from `weighted_young_cross` at `λ = ρ`. -/
theorem weighted_residual_bound {K : Matrix m m ℝ} (hK : Kᵀ = K)
    (hKpsd : ∀ z : m → ℝ, 0 ≤ z ⬝ᵥ K *ᵥ z) {ρ : ℝ} (hρ : 0 < ρ) {x r : m → ℝ}
    (hr : r ⬝ᵥ K *ᵥ r ≤ ρ ^ 2 * (x ⬝ᵥ K *ᵥ x)) :
    x ⬝ᵥ K *ᵥ r ≤ ρ * (x ⬝ᵥ K *ᵥ x) := by
  have hy := weighted_young_cross hK hKpsd hρ x r
  have hstep : 1 / (2 * ρ) * (r ⬝ᵥ K *ᵥ r) ≤ 1 / (2 * ρ) * (ρ ^ 2 * (x ⬝ᵥ K *ᵥ x)) :=
    mul_le_mul_of_nonneg_left hr (by positivity)
  have hrw : 1 / (2 * ρ) * (ρ ^ 2 * (x ⬝ᵥ K *ᵥ x)) = ρ / 2 * (x ⬝ᵥ K *ᵥ x) := by
    field_simp
  linarith [hy, hstep, hrw]

end WeightedYoung

section DominatedWeighted

variable {M Mdot C D : Matrix n n ℝ} {K : Matrix m m ℝ} {J Jdot : Matrix m n ℝ}
variable {e edot : n → ℝ} {x xdot r : m → ℝ}

/-- **The weighted dominated rate.** The domination step of
`TrackingStrictBound.strict_rate_dominated`, with every named bound restated against
the storage's own weighted quadratic forms `E_M := e ⬝ᵥ M *ᵥ e`,
`X_K := x ⬝ᵥ K *ᵥ x` instead of the stacked Euclidean `E = e ⬝ᵥ e`, `X = x ⬝ᵥ x`.
Under `M`, `K` symmetric PSD (`hMpsd`, `hKpsd`) and the same rate hypotheses (`hK`,
`hM`, `hdyn`, `hkin`, `F = 0`) with the pointwise bounds now weighted,
`Ẇ ≤ −κ(E_M + X_K)` with the SAME `κ = min(A − Cλ/2, B − C/(2λ))` formula as the
Euclidean statement (`quad_form_dominates` does not care what `s, t` denote). -/
theorem strict_rate_dominated_weighted
    (hMpsd : ∀ z : n → ℝ, 0 ≤ z ⬝ᵥ M *ᵥ z) (hKpsd : ∀ z : m → ℝ, 0 ≤ z ⬝ᵥ K *ᵥ z)
    (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x))
    (hkin : xdot = J *ᵥ e + r)
    {d₁ γ₁ κr c₁ c₂ c₃ c₄ c₅ α lam : ℝ} (hα : 0 ≤ α) (hlam : 0 < lam)
    (hcs : 0 ≤ c₂ + c₃ + c₄ + c₅)
    (hD : d₁ * (e ⬝ᵥ M *ᵥ e) ≤ e ⬝ᵥ D *ᵥ e)
    (hr : x ⬝ᵥ K *ᵥ r ≤ κr * (x ⬝ᵥ K *ᵥ x))
    (hgg : γ₁ ^ 2 * (x ⬝ᵥ K *ᵥ x) ≤ stiffForce J K x ⬝ᵥ stiffForce J K x)
    (hgd : (Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) ⬝ᵥ M *ᵥ e
      ≤ c₁ * (e ⬝ᵥ M *ᵥ e)
        + c₂ * (Real.sqrt (e ⬝ᵥ M *ᵥ e) * Real.sqrt (x ⬝ᵥ K *ᵥ x)))
    (hgM : stiffForce J K x ⬝ᵥ Mdot *ᵥ e
      ≤ c₃ * (Real.sqrt (e ⬝ᵥ M *ᵥ e) * Real.sqrt (x ⬝ᵥ K *ᵥ x)))
    (hgC : -(stiffForce J K x ⬝ᵥ C *ᵥ e)
      ≤ c₄ * (Real.sqrt (e ⬝ᵥ M *ᵥ e) * Real.sqrt (x ⬝ᵥ K *ᵥ x)))
    (hgD : -(stiffForce J K x ⬝ᵥ D *ᵥ e)
      ≤ c₅ * (Real.sqrt (e ⬝ᵥ M *ᵥ e) * Real.sqrt (x ⬝ᵥ K *ᵥ x))) :
    strictRate M Mdot K J Jdot α e edot x xdot
      ≤ -(min ((d₁ - α * c₁) - α * (c₂ + c₃ + c₄ + c₅) * lam / 2)
              ((α * γ₁ ^ 2 - κr) - α * (c₂ + c₃ + c₄ + c₅) / (2 * lam)))
          * (e ⬝ᵥ M *ᵥ e + x ⬝ᵥ K *ᵥ x) := by
  have hdyn' : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x) - (0 : n → ℝ) := by
    rw [sub_zero]; exact hdyn
  rw [cross_term_rate_identity hK hM hdyn' hkin]
  simp only [dotProduct_zero, sub_zero]
  set g := stiffForce J K x with hg
  set gd := Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot) with hgd_def
  set s := Real.sqrt (e ⬝ᵥ M *ᵥ e) with hs
  set t := Real.sqrt (x ⬝ᵥ K *ᵥ x) with ht
  have hE : s ^ 2 = e ⬝ᵥ M *ᵥ e := Real.sq_sqrt (hMpsd e)
  have hX : t ^ 2 = x ⬝ᵥ K *ᵥ x := Real.sq_sqrt (hKpsd x)
  have hbr : α * (gd ⬝ᵥ M *ᵥ e + g ⬝ᵥ Mdot *ᵥ e - g ⬝ᵥ C *ᵥ e - g ⬝ᵥ D *ᵥ e - g ⬝ᵥ g)
      ≤ α * (c₁ * (e ⬝ᵥ M *ᵥ e) + (c₂ + c₃ + c₄ + c₅) * (s * t) - γ₁ ^ 2 * (x ⬝ᵥ K *ᵥ x)) := by
    apply mul_le_mul_of_nonneg_left _ hα
    linarith [hgd, hgM, hgC, hgD, hgg]
  have hq := quad_form_dominates (A := d₁ - α * c₁) (B := α * γ₁ ^ 2 - κr)
    (C := α * (c₂ + c₃ + c₄ + c₅)) (lam := lam) (s := s) (t := t)
    (mul_nonneg hα hcs) hlam
  rw [hE, hX] at hq
  nlinarith [hbr, hq, hD, hr]

end DominatedWeighted

end Ctrllib

#print axioms Ctrllib.weighted_young_cross
#print axioms Ctrllib.weighted_residual_bound
#print axioms Ctrllib.strict_rate_dominated_weighted
