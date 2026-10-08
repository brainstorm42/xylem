/-
PD+ local domination step (the corresponding design note, follow-up to TrackingCrossTerm) — the
strict-Lyapunov inequalities for the augmented tracking storage
W = V_e + α gᵀ M̆ e (g = J_x̃ᵀ K̆ x̃), stated under NAMED pointwise bounds.

THE STEP. TrackingCrossTerm seals the exact rate identity of W along the `velocity_ff`
loop (the source model note eq 4.12, scientific configuration) with the moving-reference
kinematics residual r (eq 4.1c). A convergence theorem needs two more facts:
(1) W is bounded below by a positive multiple of ‖e‖² + ‖x̃‖² (coercive), and
(2) Ẇ ≤ −κ(‖e‖² + ‖x̃‖²) for some κ > 0. Both follow from the identity plus bounds on
the individual terms; this module proves exactly that implication, with every bound a
hypothesis. Writing E = ‖e‖², X = ‖x̃‖², s = √E, t = √X:

  bounds:  d₁E ≤ eᵀD̆e,  x̃ᵀK̆r ≤ κ_r X,  γ₁²X ≤ ‖g‖²,  ġᵀM̆e ≤ c₁E + c₂st,
           gᵀṀ̆e ≤ c₃st,  −gᵀC̆e ≤ c₄st,  −gᵀD̆e ≤ c₅st            (F = 0)
  hence    Ẇ ≤ −(d₁ − αc₁)E − (αγ₁² − κ_r)X + α(c₂+c₃+c₄+c₅)st,
  and with A := d₁ − αc₁, B := αγ₁² − κ_r, C := α(c₂+…+c₅), any λ > 0 with
  Cλ/2 < A and C/(2λ) < B gives Ẇ ≤ −κ(E + X), κ = min(A − Cλ/2, B − C/(2λ)) > 0
  (Young's inequality; λ = √(A/B) recovers the sharp C² < 4AB).

WHAT IS PROVEN:
  `young_cross`             — C·s·t ≤ (Cλ/2)s² + (C/(2λ))t²  for C ≥ 0, λ > 0.
  `quad_form_dominates`     — A s² + B t² − C s t ≥ min(A − Cλ/2, B − C/(2λ))·(s² + t²).
  `strict_rate_dominated`   — the sealed rate ≤ −κ(E + X) under the bounds above.
  `strict_rate_dominated_exact_twist` — the r = 0 (exact relative twist) specialization:
                              κ_r drops out of B = αγ₁² entirely, so only A > 0 and
                              C² < 4AB bind on the design constants — the citable
                              controller-design reading of the r = 0 remark above.
  `strict_storage_lower`    — W ≥ (min(m₁,k₁)/2 − αc₆/2)(E + X) when m₁E ≤ eᵀM̆e,
                              k₁X ≤ x̃ᵀK̆x̃, |gᵀM̆e| ≤ c₆st.
  `strict_storage_upper`    — W ≤ (max(m₂,k₂)/2 + αc₆/2)(E + X) when eᵀM̆e ≤ m₂E,
                              x̃ᵀK̆x̃ ≤ k₂X, |gᵀM̆e| ≤ c₆st (mirror of the lower bound).
  `strict_storage_sandwich` — the two packaged: c_lo(E+X) ≤ W ≤ c_hi(E+X).
  `forced_rate_sqrt_comparison` — scalar adapter: given the forced rate bound
                              Ẇ ≤ −κ(E+X) + f√E + (αγ₂f+ρ)√X and a storage sandwich
                              c_lo(E+X) ≤ W ≤ c_hi(E+X), derive
                              Ẇ ≤ −(κ/c_hi)W + c'(f+ρ)√W, c' = (1+αγ₂)/√c_lo — the
                              shape `TimeVaryingComparison` consumes once an applier
                              supplies the flow-level derivative of √W (see the note
                              at the theorem).

PINNED (the corresponding project check (not bundled).py):
  (A) Young/quadratic-form lemma; (B) dominated rate on random data satisfying the
  bounds; (C) the storage lower bound.
PINNED (the corresponding private check):
  (D) the storage upper bound / sandwich; (E) the forced √W comparison inequality on
  random samples; (F) the exact-twist (κ_r = 0) corollary.

INTERFACE BOUNDARY (honest). The constants d₁, γ₁, κ_r, c₁..c₆ are hypotheses at one
instant. What supplies them uniformly on a forward-invariant set — Rayleigh bounds
for D̆, M̆, K̆ (Rayleigh.lean), σ_min(J_x̃) > 0 on Ω with η ≠ 0 (TrackingErrorJacobian),
Coriolis growth ‖C̆‖ ≤ c(‖e‖ + ‖v̆_d‖), ‖J̇_x̃‖ bounded, ‖r‖ ≤ 3‖x̃‖‖v̆_d‖ (sheet 4.1c),
and the flow realisation — is the remaining application layer. Note the structural
requirement B > 0: αγ₁² > κ_r, i.e. the kinematics-residual term (∝ ‖v̆_d‖) must be
smaller than the strict term the cross term buys; for the exact relative twist
(r = 0) it is automatic.
-/
import Ctrllib.TrackingCrossTerm

open Matrix

namespace Ctrllib

/-- Young's inequality in the form used for the cross term: `C s t ≤ (Cλ/2) s² + (C/(2λ)) t²`. -/
theorem young_cross {C lam s t : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    C * s * t ≤ C * lam / 2 * s ^ 2 + C / (2 * lam) * t ^ 2 := by
  have hkey : 0 ≤ C / (2 * lam) * (lam * s - t) ^ 2 := by positivity
  have hexp : C / (2 * lam) * (lam * s - t) ^ 2
      = C * lam / 2 * s ^ 2 - C * s * t + C / (2 * lam) * t ^ 2 := by
    field_simp
    ring
  linarith

/-- **Quadratic-form domination.** For `A, B > 0`-type margins after Young,
`A s² + B t² − C s t ≥ min(A − Cλ/2, B − C/(2λ)) (s² + t²)`. -/
theorem quad_form_dominates {A B C lam s t : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    min (A - C * lam / 2) (B - C / (2 * lam)) * (s ^ 2 + t ^ 2)
      ≤ A * s ^ 2 + B * t ^ 2 - C * s * t := by
  have hy := young_cross (s := s) (t := t) hC hlam
  have h1 : min (A - C * lam / 2) (B - C / (2 * lam)) * s ^ 2 ≤ (A - C * lam / 2) * s ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg s)
  have h2 : min (A - C * lam / 2) (B - C / (2 * lam)) * t ^ 2 ≤ (B - C / (2 * lam)) * t ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg t)
  nlinarith [h1, h2, hy]

variable {n m : Type*} [Fintype n] [Fintype m]

/-- `0 ≤ v ⬝ᵥ v`. -/
theorem dotProduct_self_nonneg' (v : n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

section Dominated

variable {M Mdot C D : Matrix n n ℝ} {K : Matrix m m ℝ} {J Jdot : Matrix m n ℝ}
variable {e edot : n → ℝ} {x xdot r : m → ℝ}

/-- **The dominated rate.** Under the named pointwise bounds (F = 0), the sealed rate of
`W = V_e + α gᵀ M e` satisfies `Ẇ ≤ −κ (‖e‖² + ‖x‖²)` with the explicit
`κ = min(A − Cλ/2, B − C/(2λ))`, `A = d₁ − αc₁`, `B = αγ₁² − κ_r`, `C = α(c₂+c₃+c₄+c₅)`. -/
theorem strict_rate_dominated (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x))
    (hkin : xdot = J *ᵥ e + r)
    {d₁ γ₁ κr c₁ c₂ c₃ c₄ c₅ α lam : ℝ} (hα : 0 ≤ α) (hlam : 0 < lam)
    (hcs : 0 ≤ c₂ + c₃ + c₄ + c₅)
    (hD : d₁ * (e ⬝ᵥ e) ≤ e ⬝ᵥ D *ᵥ e)
    (hr : x ⬝ᵥ K *ᵥ r ≤ κr * (x ⬝ᵥ x))
    (hgg : γ₁ ^ 2 * (x ⬝ᵥ x) ≤ stiffForce J K x ⬝ᵥ stiffForce J K x)
    (hgd : (Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) ⬝ᵥ M *ᵥ e
      ≤ c₁ * (e ⬝ᵥ e) + c₂ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgM : stiffForce J K x ⬝ᵥ Mdot *ᵥ e ≤ c₃ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgC : -(stiffForce J K x ⬝ᵥ C *ᵥ e) ≤ c₄ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgD : -(stiffForce J K x ⬝ᵥ D *ᵥ e) ≤ c₅ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x))) :
    strictRate M Mdot K J Jdot α e edot x xdot
      ≤ -(min ((d₁ - α * c₁) - α * (c₂ + c₃ + c₄ + c₅) * lam / 2)
              ((α * γ₁ ^ 2 - κr) - α * (c₂ + c₃ + c₄ + c₅) / (2 * lam)))
          * (e ⬝ᵥ e + x ⬝ᵥ x) := by
  -- the sealed identity with F = 0
  have hdyn' : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x) - (0 : n → ℝ) := by
    rw [sub_zero]; exact hdyn
  rw [cross_term_rate_identity hK hM hdyn' hkin]
  simp only [dotProduct_zero, sub_zero]
  -- names
  set g := stiffForce J K x with hg
  set gd := Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot) with hgd_def
  set s := Real.sqrt (e ⬝ᵥ e) with hs
  set t := Real.sqrt (x ⬝ᵥ x) with ht
  have hE : s ^ 2 = e ⬝ᵥ e := Real.sq_sqrt (dotProduct_self_nonneg' e)
  have hX : t ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dotProduct_self_nonneg' x)
  -- the α-bracket bound
  have hbr : α * (gd ⬝ᵥ M *ᵥ e + g ⬝ᵥ Mdot *ᵥ e - g ⬝ᵥ C *ᵥ e - g ⬝ᵥ D *ᵥ e - g ⬝ᵥ g)
      ≤ α * (c₁ * (e ⬝ᵥ e) + (c₂ + c₃ + c₄ + c₅) * (s * t) - γ₁ ^ 2 * (x ⬝ᵥ x)) := by
    apply mul_le_mul_of_nonneg_left _ hα
    linarith [hgd, hgM, hgC, hgD, hgg]
  -- quadratic-form domination with A, B, C
  have hq := quad_form_dominates (A := d₁ - α * c₁) (B := α * γ₁ ^ 2 - κr)
    (C := α * (c₂ + c₃ + c₄ + c₅)) (lam := lam) (s := s) (t := t)
    (mul_nonneg hα hcs) hlam
  rw [hE, hX] at hq
  nlinarith [hbr, hq, hD, hr]

/-- **The dominated rate with forcing.** Same bounds, but the CoM coupling `F` is kept
(`−eᵀF ≤ f‖e‖`, `−gᵀF ≤ γ₂ f ‖x‖` with `f = ‖F‖`) and the kinematics term may carry a
non-vanishing part (`xᵀ K r ≤ κ_r ‖x‖² + ρ ‖x‖`, e.g. a regularization residual). Then
`Ẇ ≤ −κ(‖e‖² + ‖x‖²) + f‖e‖ + (α γ₂ f + ρ)‖x‖` — the input shape of the comparison /
cascade engines (`TimeVaryingComparison`, `Cascade`): a strict decay plus a forcing
that is linear in the state norm. -/
theorem strict_rate_dominated_forced (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    {F : n → ℝ}
    (hdyn : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x) - F)
    (hkin : xdot = J *ᵥ e + r)
    {d₁ γ₁ γ₂ κr ρ f c₁ c₂ c₃ c₄ c₅ α lam : ℝ} (hα : 0 ≤ α) (hlam : 0 < lam)
    (hcs : 0 ≤ c₂ + c₃ + c₄ + c₅)
    (hD : d₁ * (e ⬝ᵥ e) ≤ e ⬝ᵥ D *ᵥ e)
    (hr : x ⬝ᵥ K *ᵥ r ≤ κr * (x ⬝ᵥ x) + ρ * Real.sqrt (x ⬝ᵥ x))
    (hgg : γ₁ ^ 2 * (x ⬝ᵥ x) ≤ stiffForce J K x ⬝ᵥ stiffForce J K x)
    (hgd : (Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) ⬝ᵥ M *ᵥ e
      ≤ c₁ * (e ⬝ᵥ e) + c₂ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgM : stiffForce J K x ⬝ᵥ Mdot *ᵥ e ≤ c₃ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgC : -(stiffForce J K x ⬝ᵥ C *ᵥ e) ≤ c₄ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgD : -(stiffForce J K x ⬝ᵥ D *ᵥ e) ≤ c₅ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hFe : -(e ⬝ᵥ F) ≤ f * Real.sqrt (e ⬝ᵥ e))
    (hFg : -(stiffForce J K x ⬝ᵥ F) ≤ γ₂ * f * Real.sqrt (x ⬝ᵥ x)) :
    strictRate M Mdot K J Jdot α e edot x xdot
      ≤ -(min ((d₁ - α * c₁) - α * (c₂ + c₃ + c₄ + c₅) * lam / 2)
              ((α * γ₁ ^ 2 - κr) - α * (c₂ + c₃ + c₄ + c₅) / (2 * lam)))
          * (e ⬝ᵥ e + x ⬝ᵥ x)
        + f * Real.sqrt (e ⬝ᵥ e) + (α * γ₂ * f + ρ) * Real.sqrt (x ⬝ᵥ x) := by
  rw [cross_term_rate_identity hK hM hdyn hkin]
  set g := stiffForce J K x with hg
  set gd := Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot) with hgd_def
  set s := Real.sqrt (e ⬝ᵥ e) with hs
  set t := Real.sqrt (x ⬝ᵥ x) with ht
  have hE : s ^ 2 = e ⬝ᵥ e := Real.sq_sqrt (dotProduct_self_nonneg' e)
  have hX : t ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dotProduct_self_nonneg' x)
  have hbr : α * (gd ⬝ᵥ M *ᵥ e + g ⬝ᵥ Mdot *ᵥ e - g ⬝ᵥ C *ᵥ e - g ⬝ᵥ D *ᵥ e - g ⬝ᵥ g - g ⬝ᵥ F)
      ≤ α * (c₁ * (e ⬝ᵥ e) + (c₂ + c₃ + c₄ + c₅) * (s * t) - γ₁ ^ 2 * (x ⬝ᵥ x)
              + γ₂ * f * t) := by
    apply mul_le_mul_of_nonneg_left _ hα
    linarith [hgd, hgM, hgC, hgD, hgg, hFg]
  have hq := quad_form_dominates (A := d₁ - α * c₁) (B := α * γ₁ ^ 2 - κr)
    (C := α * (c₂ + c₃ + c₄ + c₅)) (lam := lam) (s := s) (t := t)
    (mul_nonneg hα hcs) hlam
  rw [hE, hX] at hq
  nlinarith [hbr, hq, hD, hr, hFe]

/-- **The exact-relative-twist specialization.** `strict_rate_dominated` with `r = 0`
(no kinematics residual): `κ_r` drops out of `B = αγ₁² − κ_r` entirely, leaving
`B = αγ₁²`, so the structural requirement `αγ₁² > κ_r` reduces to `α > 0` (with
`γ₁ ≠ 0`) — only `A = d₁ − αc₁ > 0` and `C² < 4AB` bind. This is the citable
controller-design reading of the module header's r = 0 remark. -/
theorem strict_rate_dominated_exact_twist (hK : Kᵀ = K) (hM : Mdot = C + Cᵀ)
    (hdyn : M *ᵥ edot = -(C *ᵥ e) - D *ᵥ e - Jᵀ *ᵥ (K *ᵥ x))
    (hkin : xdot = J *ᵥ e)
    {d₁ γ₁ c₁ c₂ c₃ c₄ c₅ α lam : ℝ} (hα : 0 ≤ α) (hlam : 0 < lam)
    (hcs : 0 ≤ c₂ + c₃ + c₄ + c₅)
    (hD : d₁ * (e ⬝ᵥ e) ≤ e ⬝ᵥ D *ᵥ e)
    (hgg : γ₁ ^ 2 * (x ⬝ᵥ x) ≤ stiffForce J K x ⬝ᵥ stiffForce J K x)
    (hgd : (Jdotᵀ *ᵥ (K *ᵥ x) + Jᵀ *ᵥ (K *ᵥ xdot)) ⬝ᵥ M *ᵥ e
      ≤ c₁ * (e ⬝ᵥ e) + c₂ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgM : stiffForce J K x ⬝ᵥ Mdot *ᵥ e ≤ c₃ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgC : -(stiffForce J K x ⬝ᵥ C *ᵥ e) ≤ c₄ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x)))
    (hgD : -(stiffForce J K x ⬝ᵥ D *ᵥ e) ≤ c₅ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x))) :
    strictRate M Mdot K J Jdot α e edot x xdot
      ≤ -(min ((d₁ - α * c₁) - α * (c₂ + c₃ + c₄ + c₅) * lam / 2)
              (α * γ₁ ^ 2 - α * (c₂ + c₃ + c₄ + c₅) / (2 * lam)))
          * (e ⬝ᵥ e + x ⬝ᵥ x) := by
  have hkin' : xdot = J *ᵥ e + (0 : m → ℝ) := by simp [hkin]
  have hr0 : x ⬝ᵥ K *ᵥ (0 : m → ℝ) ≤ (0 : ℝ) * (x ⬝ᵥ x) := by simp
  simpa using
    strict_rate_dominated hK hM hdyn hkin' hα hlam hcs hD hr0 hgg hgd hgM hgC hgD

end Dominated

section Storage

variable {M : Matrix n n ℝ} {K : Matrix m m ℝ} {J : Matrix m n ℝ} {e : n → ℝ} {x : m → ℝ}

/-- The augmented storage `W = ½eᵀMe + ½xᵀKx + α gᵀ M e`. -/
noncomputable def strictStorage (M : Matrix n n ℝ) (K : Matrix m m ℝ) (J : Matrix m n ℝ)
    (α : ℝ) (e : n → ℝ) (x : m → ℝ) : ℝ :=
  blockLyap M K e x + α * (stiffForce J K x ⬝ᵥ M *ᵥ e)

/-- **Lower bound of the augmented storage.** With Rayleigh lower bounds `m₁`, `k₁` and a
cross-term bound `|gᵀ M e| ≤ c₆ ‖e‖‖x‖`, `W ≥ (min(m₁,k₁)/2 − αc₆/2)(‖e‖² + ‖x‖²)`. -/
theorem strict_storage_lower {m₁ k₁ c₆ α : ℝ} (hα : 0 ≤ α) (hc₆ : 0 ≤ c₆)
    (hM : m₁ * (e ⬝ᵥ e) ≤ e ⬝ᵥ M *ᵥ e) (hK : k₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ K *ᵥ x)
    (hg : |stiffForce J K x ⬝ᵥ M *ᵥ e| ≤ c₆ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x))) :
    (min m₁ k₁ / 2 - α * c₆ / 2) * (e ⬝ᵥ e + x ⬝ᵥ x) ≤ strictStorage M K J α e x := by
  unfold strictStorage blockLyap
  set s := Real.sqrt (e ⬝ᵥ e) with hs
  set t := Real.sqrt (x ⬝ᵥ x) with ht
  have hE : s ^ 2 = e ⬝ᵥ e := Real.sq_sqrt (dotProduct_self_nonneg' e)
  have hX : t ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dotProduct_self_nonneg' x)
  have hst : 2 * (s * t) ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (s - t)]
  have hlow : -(c₆ * (s * t)) ≤ stiffForce J K x ⬝ᵥ M *ᵥ e := by
    have := (abs_le.mp hg).1
    linarith
  have hcross : -(α * c₆ * (s * t)) ≤ α * (stiffForce J K x ⬝ᵥ M *ᵥ e) := by
    have := mul_le_mul_of_nonneg_left hlow hα
    linarith
  have h1 : min m₁ k₁ * (e ⬝ᵥ e) ≤ m₁ * (e ⬝ᵥ e) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (dotProduct_self_nonneg' e)
  have h2 : min m₁ k₁ * (x ⬝ᵥ x) ≤ k₁ * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (dotProduct_self_nonneg' x)
  have hαc : 0 ≤ α * c₆ := mul_nonneg hα hc₆
  have hst' : α * c₆ * (s * t) ≤ α * c₆ / 2 * (e ⬝ᵥ e + x ⬝ᵥ x) := by
    rw [← hE, ← hX]
    nlinarith [hst, hαc]
  nlinarith [h1, h2, hcross, hst', hM, hK]

/-- **Upper bound of the augmented storage.** Mirror of `strict_storage_lower`: with
Rayleigh upper bounds `m₂`, `k₂` and the same cross-term bound `|gᵀ M e| ≤ c₆ ‖e‖‖x‖`,
`W ≤ (max(m₂,k₂)/2 + αc₆/2)(‖e‖² + ‖x̃‖²)`. -/
theorem strict_storage_upper {m₂ k₂ c₆ α : ℝ} (hα : 0 ≤ α) (hc₆ : 0 ≤ c₆)
    (hM : e ⬝ᵥ M *ᵥ e ≤ m₂ * (e ⬝ᵥ e)) (hK : x ⬝ᵥ K *ᵥ x ≤ k₂ * (x ⬝ᵥ x))
    (hg : |stiffForce J K x ⬝ᵥ M *ᵥ e| ≤ c₆ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x))) :
    strictStorage M K J α e x ≤ (max m₂ k₂ / 2 + α * c₆ / 2) * (e ⬝ᵥ e + x ⬝ᵥ x) := by
  unfold strictStorage blockLyap
  set s := Real.sqrt (e ⬝ᵥ e) with hs
  set t := Real.sqrt (x ⬝ᵥ x) with ht
  have hE : s ^ 2 = e ⬝ᵥ e := Real.sq_sqrt (dotProduct_self_nonneg' e)
  have hX : t ^ 2 = x ⬝ᵥ x := Real.sq_sqrt (dotProduct_self_nonneg' x)
  have hst : 2 * (s * t) ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (s - t)]
  have hupp : stiffForce J K x ⬝ᵥ M *ᵥ e ≤ c₆ * (s * t) := by
    have := (abs_le.mp hg).2
    linarith
  have hcross : α * (stiffForce J K x ⬝ᵥ M *ᵥ e) ≤ α * c₆ * (s * t) := by
    have := mul_le_mul_of_nonneg_left hupp hα
    linarith
  have h1 : m₂ * (e ⬝ᵥ e) ≤ max m₂ k₂ * (e ⬝ᵥ e) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (dotProduct_self_nonneg' e)
  have h2 : k₂ * (x ⬝ᵥ x) ≤ max m₂ k₂ * (x ⬝ᵥ x) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (dotProduct_self_nonneg' x)
  have hαc : 0 ≤ α * c₆ := mul_nonneg hα hc₆
  have hst' : α * c₆ * (s * t) ≤ α * c₆ / 2 * (e ⬝ᵥ e + x ⬝ᵥ x) := by
    rw [← hE, ← hX]
    nlinarith [hst, hαc]
  nlinarith [h1, h2, hcross, hst', hM, hK]

/-- **The storage sandwich.** `strict_storage_lower` and `strict_storage_upper`
packaged: `c_lo(‖e‖² + ‖x̃‖²) ≤ W ≤ c_hi(‖e‖² + ‖x̃‖²)`, `c_lo = min(m₁,k₁)/2 − αc₆/2`,
`c_hi = max(m₂,k₂)/2 + αc₆/2`. Closes the report's asserted-but-unbricked `c_hi` half
(the corresponding local note, "forced lemma" update). -/
theorem strict_storage_sandwich {m₁ m₂ k₁ k₂ c₆ α : ℝ} (hα : 0 ≤ α) (hc₆ : 0 ≤ c₆)
    (hM1 : m₁ * (e ⬝ᵥ e) ≤ e ⬝ᵥ M *ᵥ e) (hM2 : e ⬝ᵥ M *ᵥ e ≤ m₂ * (e ⬝ᵥ e))
    (hK1 : k₁ * (x ⬝ᵥ x) ≤ x ⬝ᵥ K *ᵥ x) (hK2 : x ⬝ᵥ K *ᵥ x ≤ k₂ * (x ⬝ᵥ x))
    (hg : |stiffForce J K x ⬝ᵥ M *ᵥ e| ≤ c₆ * (Real.sqrt (e ⬝ᵥ e) * Real.sqrt (x ⬝ᵥ x))) :
    (min m₁ k₁ / 2 - α * c₆ / 2) * (e ⬝ᵥ e + x ⬝ᵥ x) ≤ strictStorage M K J α e x
      ∧ strictStorage M K J α e x ≤ (max m₂ k₂ / 2 + α * c₆ / 2) * (e ⬝ᵥ e + x ⬝ᵥ x) :=
  ⟨strict_storage_lower hα hc₆ hM1 hK1 hg, strict_storage_upper hα hc₆ hM2 hK2 hg⟩

end Storage

section Comparison

/-- **Scalar-level adapter into the comparison engines.** Given the forced rate bound
(`strict_rate_dominated_forced`'s conclusion, `E = e⬝e`, `X = x̃⬝x̃`)
`Ẇ ≤ −κ(E+X) + f√E + (αγ₂f+ρ)√X` and a storage sandwich `c_lo(E+X) ≤ W ≤ c_hi(E+X)`
(`strict_storage_sandwich`), derive `Ẇ ≤ −(κ/c_hi)W + c'(f+ρ)√W` with
`c' = (1+αγ₂)/√c_lo` — the report's asserted intermediate step
(the corresponding local note, "forced lemma" update).

This is a PURELY ALGEBRAIC, pointwise inequality: it needs no positivity of `W`
(the sandwich already forces `0 ≤ W`, and `E, X ≤ W/c_lo` holds whether or not
`W = 0`). The companion step the report also states — the comparison form on
`u := √W`, `u' ≤ −(κ/(2c_hi))u + (c'/2)(f+ρ)`, ready for
`TimeVaryingComparison.comparison_tendsto_zero` / `comparison_bounded` — needs the
chain rule for `√` along an actual flow (`HasDerivWithinAt.sqrt`, which does need
`W t ≠ 0`) applied to a REALIZED trajectory `t ↦ (e t, x̃ t)` with `Ẇ` the genuine time
derivative of `strictStorage`. TrackingStrictBound and TrackingCrossTerm never
establish that flow realisation (see both modules' INTERFACE BOUNDARY notes, item
"(iv) flow realisation" / "the flow realises the displayed rate"); supplying it here
would mean inventing that bridge, not reusing sealed machinery. So `forced_rate_tendsto_zero`
/ `forced_rate_ultimate_bound` corollaries are NOT added: they do not compose with
the sealed comparison engines without that missing application-layer hypothesis. This
theorem is the honest stopping point — the differential inequality, application-ready
once a caller supplies the flow-level `HasDerivWithinAt` bridge. -/
theorem forced_rate_sqrt_comparison {E X W Wdot f ρ α γ₂ κ c_lo c_hi : ℝ}
    (hE : 0 ≤ E) (hX : 0 ≤ X) (hf : 0 ≤ f) (hρ : 0 ≤ ρ) (hα : 0 ≤ α) (hγ₂ : 0 ≤ γ₂)
    (hκ : 0 ≤ κ) (hclo : 0 < c_lo) (hchi : 0 < c_hi)
    (hlo : c_lo * (E + X) ≤ W) (hhi : W ≤ c_hi * (E + X))
    (hrate : Wdot ≤ -κ * (E + X) + f * Real.sqrt E + (α * γ₂ * f + ρ) * Real.sqrt X) :
    Wdot ≤ -(κ / c_hi) * W + (1 + α * γ₂) / Real.sqrt c_lo * (f + ρ) * Real.sqrt W := by
  have hclne : c_lo ≠ 0 := hclo.ne'
  -- E, X dominated by W / c_lo
  have hEdiv : E ≤ W / c_lo := by
    rw [le_div_iff₀ hclo]
    nlinarith [hlo, mul_nonneg hclo.le hX]
  have hXdiv : X ≤ W / c_lo := by
    rw [le_div_iff₀ hclo]
    nlinarith [hlo, mul_nonneg hclo.le hE]
  -- sqrt bounds
  have hsw : Real.sqrt E ≤ Real.sqrt W / Real.sqrt c_lo := by
    have h1 : Real.sqrt E ≤ Real.sqrt (W / c_lo) := Real.sqrt_le_sqrt hEdiv
    rwa [Real.sqrt_div' W hclo.le] at h1
  have htw : Real.sqrt X ≤ Real.sqrt W / Real.sqrt c_lo := by
    have h1 : Real.sqrt X ≤ Real.sqrt (W / c_lo) := Real.sqrt_le_sqrt hXdiv
    rwa [Real.sqrt_div' W hclo.le] at h1
  -- E + X versus W / c_hi
  have hEXhi : W / c_hi ≤ E + X := by
    rw [div_le_iff₀ hchi]
    nlinarith [hhi]
  -- term A: the −κ(E+X) part
  have hA : -κ * (E + X) ≤ -(κ / c_hi) * W := by
    have h2 : κ * (W / c_hi) ≤ κ * (E + X) := mul_le_mul_of_nonneg_left hEXhi hκ
    have heq : κ * (W / c_hi) = (κ / c_hi) * W := by ring
    linarith [h2, heq]
  -- term B: the forcing part
  have hfs : f * Real.sqrt E ≤ f * (Real.sqrt W / Real.sqrt c_lo) :=
    mul_le_mul_of_nonneg_left hsw hf
  have hcoef_nonneg : 0 ≤ α * γ₂ * f + ρ := by positivity
  have hgt : (α * γ₂ * f + ρ) * Real.sqrt X ≤ (α * γ₂ * f + ρ) * (Real.sqrt W / Real.sqrt c_lo) :=
    mul_le_mul_of_nonneg_left htw hcoef_nonneg
  have hsum : f * Real.sqrt E + (α * γ₂ * f + ρ) * Real.sqrt X
      ≤ (1 + α * γ₂) * (f + ρ) * (Real.sqrt W / Real.sqrt c_lo) := by
    have hquot_nonneg : 0 ≤ Real.sqrt W / Real.sqrt c_lo :=
      div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hρnn : 0 ≤ α * γ₂ * ρ := by positivity
    have hcoef_le : f + α * γ₂ * f + ρ ≤ (1 + α * γ₂) * (f + ρ) := by nlinarith [hρnn]
    have hstep : (f + α * γ₂ * f + ρ) * (Real.sqrt W / Real.sqrt c_lo)
        ≤ (1 + α * γ₂) * (f + ρ) * (Real.sqrt W / Real.sqrt c_lo) :=
      mul_le_mul_of_nonneg_right hcoef_le hquot_nonneg
    have heq2 : (f + α * γ₂ * f + ρ) * (Real.sqrt W / Real.sqrt c_lo)
        = f * (Real.sqrt W / Real.sqrt c_lo) + (α * γ₂ * f + ρ) * (Real.sqrt W / Real.sqrt c_lo) := by
      ring
    linarith [hfs, hgt, hstep, heq2]
  calc Wdot ≤ -κ * (E + X) + f * Real.sqrt E + (α * γ₂ * f + ρ) * Real.sqrt X := hrate
    _ ≤ -(κ / c_hi) * W + (1 + α * γ₂) * (f + ρ) * (Real.sqrt W / Real.sqrt c_lo) := by
        linarith [hA, hsum]
    _ = -(κ / c_hi) * W + (1 + α * γ₂) / Real.sqrt c_lo * (f + ρ) * Real.sqrt W := by ring

end Comparison

end Ctrllib

#print axioms Ctrllib.young_cross
#print axioms Ctrllib.quad_form_dominates
#print axioms Ctrllib.strict_rate_dominated
#print axioms Ctrllib.strict_rate_dominated_forced
#print axioms Ctrllib.strict_rate_dominated_exact_twist
#print axioms Ctrllib.strict_storage_lower
#print axioms Ctrllib.strict_storage_upper
#print axioms Ctrllib.strict_storage_sandwich
#print axioms Ctrllib.forced_rate_sqrt_comparison
