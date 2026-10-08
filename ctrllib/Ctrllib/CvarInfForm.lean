/-
SAA (sample-average / discrete) CVaR inf-form — risk obligations A1 + A5
(and B3 by reuse). Seals the Rockafellar–Uryasev auxiliary-function form of
Conditional Value-at-Risk for a FINITE equal-weight sample, the case a
scenario-based risk-aware planner actually produces.

For samples `Z : Fin q → ℝ` and confidence level `α ∈ [0,1)`, the SAA objective is

    cvarObj α Z τ = τ + (1 / (q (1-α))) · Σ_k (Z k − τ)⁺        (posPart via `max · 0`)

(Rockafellar–Uryasev 2000 eq. 9 `F̃_β`; RU-2002 Thm 16, equal weights `p_k = 1/q`,
`α` = confidence level, `τ` = auxiliary variable — this file uses the RU-2002
naming, see the corresponding local note). CVaR is DEFINED
by the inf-form (`cvarSAA α Z := ⨅ τ, cvarObj α Z τ`, RU-2000 Thm 1 / RU-2002 Thm 10).

ROUTE (recorded loudly, per the house provenance rule): DEFINITION-FIRST, the
sanctioned honest fallback. We do NOT re-derive `cvarSAA` from a from-scratch
sorted-tail-average CVaR (that needs order statistics / a sort — deferred; it is
covered numerically by the SymPy pin `the corresponding private check`). We seal, from the
inf-form definition:

  T1 `cvarObj_convexOn` — the objective is convex in τ (piecewise-linear convex),
     RU-2000 Thm 1 convexity, the property that makes the LP reduction valid.
  T2 `cvarObj_min_at_sample` — the min over τ ∈ ℝ is ATTAINED at a sample point
     `Z k`. This is the piecewise-linear-minimizer characterization: the
     breakpoints of the objective are exactly the samples, so the global min is
     one of them (RU-2002 Prop. 8: the argmin lower endpoint is `z_{k_α}` = VaR).
  T3 `cvarSAA_eq_obj_sample` — hence `cvarSAA α Z = cvarObj α Z (Z k)` for that
     sample: the inf is attained (the RU-2002 Prop. 8 closed-form SHAPE — the CVaR
     equals the objective at the VaR breakpoint).

ATOM-SAFETY (obligation A5, the visibility-flip case). Every theorem is stated
for an ARBITRARY `Z : Fin q → ℝ`, with NO distinctness / no-tie hypothesis. So a
probability mass sitting exactly at the VaR quantile (the A5 flip, where the loss
distribution has an atom) is handled by construction: the inf-form never forms the
ambiguous conditional expectation that the naive tail averages (RU-2002 CVaR⁻/CVaR⁺)
do. The SymPy pin exhibits the numeric disagreement on the atom case
`Z = [1,2,3,3,10]`, `α = 3/5`: inf-form = 13/2 (= RU-2002 Prop. 8), naive CVaR⁻ =
16/3, CVaR⁺ = 10 — the inf-form "splits the atom", the naive averages do not.

COHERENCE (obligation A2). The A2 section at the foot of this file proves the four Artzner
axioms for `cvarSAA` — monotonicity, translation equivariance, positive homogeneity, and
subadditivity. Together with the kernel-checked VaR counterexample in
`Ctrllib/VaRSubadditivity.lean` (`var_not_subadditive`), which builds in the same library,
the design decision "use CVaR, not VaR" is now a pair of theorems rather than a citation.

PROVENANCE — resolved against the live tree.
* Human derivation page: wiki dir the corresponding derivation record (not bundled)
  — no the corresponding local note page filed yet.
* SymPy pin `the corresponding private check` — ARCHIVED, NOT mirrored into the live proof evidence record.
  The old citation
  `the corresponding local note` was a dead relative path; the file lives at
  the corresponding archived source (not bundled)
  the corresponding local note
* Numeric pin for the A2 bundle: `pins/the corresponding private check` in this repository
  (filed here because the house proof-evidence directory is read-only to the authoring agent;
  the chair should mirror it).
-/
import Mathlib

open scoped BigOperators

namespace Ctrllib

variable {q : ℕ}

/-- The SAA (sample-average) CVaR objective of Rockafellar–Uryasev, equal weights
`p_k = 1/q`. `(Z k − τ)⁺` is written `max (Z k − τ) 0`. `α` = confidence level,
`τ` = auxiliary minimization variable (RU-2002 naming). -/
noncomputable def cvarObj (α : ℝ) (Z : Fin q → ℝ) (τ : ℝ) : ℝ :=
  τ + (1 / ((q : ℝ) * (1 - α))) * ∑ k, max (Z k - τ) 0

/-- Sample-average-approximation CVaR, DEFINED by the Rockafellar–Uryasev inf-form
(RU-2000 Thm 1 / RU-2002 Thm 10). Attainment at a sample and the closed-form value
are the sealed theorems below. -/
noncomputable def cvarSAA (α : ℝ) (Z : Fin q → ℝ) : ℝ := ⨅ τ : ℝ, cvarObj α Z τ

/-- **T1 — convexity of the SAA objective** (`cvarObj_convexOn`). Each summand
`τ ↦ max (Z k − τ) 0` is a max of an affine function and a constant, hence convex;
a nonnegative-weighted sum of convex functions plus the identity is convex. This is
the RU-2000 Thm 1 convexity that licenses the LP reduction. -/
theorem cvarObj_convexOn (α : ℝ) (Z : Fin q → ℝ) (hq : 0 < q) (hα : α < 1) :
    ConvexOn ℝ Set.univ (cvarObj α Z) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1a : (0 : ℝ) < 1 - α := by linarith
  have hden : (0 : ℝ) < (q : ℝ) * (1 - α) := mul_pos hq' h1a
  have hc : (0 : ℝ) ≤ 1 / ((q : ℝ) * (1 - α)) := le_of_lt (div_pos one_pos hden)
  -- each summand is convex
  have hterm : ∀ k : Fin q, ConvexOn ℝ Set.univ (fun τ : ℝ => max (Z k - τ) 0) := by
    intro k
    have h1 : ConvexOn ℝ Set.univ (fun τ : ℝ => Z k - τ) :=
      (convexOn_const (Z k) convex_univ).sub (concaveOn_id convex_univ)
    exact h1.sup (convexOn_const 0 convex_univ)
  -- the finite sum of convex functions is convex
  have hsum : ConvexOn ℝ Set.univ (fun τ : ℝ => ∑ k, max (Z k - τ) 0) := by
    have h := Finset.sum_induction (s := Finset.univ)
      (fun (k : Fin q) (τ : ℝ) => max (Z k - τ) 0)
      (ConvexOn ℝ Set.univ) (fun _ _ ha hb => ha.add hb)
      (convexOn_const 0 convex_univ) (fun k _ => hterm k)
    have heq : (∑ k : Fin q, fun τ : ℝ => max (Z k - τ) 0)
             = fun τ : ℝ => ∑ k, max (Z k - τ) 0 := by
      funext τ; simp only [Finset.sum_apply]
    rwa [heq] at h
  -- scale by the nonnegative weight and add the identity
  have hscaled : ConvexOn ℝ Set.univ
      (fun τ : ℝ => (1 / ((q : ℝ) * (1 - α))) * ∑ k, max (Z k - τ) 0) := by
    have h := hsum.smul hc
    simp only [smul_eq_mul] at h
    exact h
  have hfinal : ConvexOn ℝ Set.univ
      (fun τ : ℝ => τ + (1 / ((q : ℝ) * (1 - α))) * ∑ k, max (Z k - τ) 0) :=
    (convexOn_id convex_univ).add hscaled
  exact hfinal

/-- The signed objective difference between a "separating" sample value `w` and any
`τ`. `w` separates the samples at/below `τ` from those strictly above (`hlo`/`hhi`).
Then the difference is exactly `(w − τ)(1 − (1/(q(1-α)))·|{k : τ < Z k}|)`. This is
the affine-between-breakpoints fact — the slope of the piecewise-linear objective on
the segment reaching `w` — with NO tie/atom hypothesis. -/
private lemma cvarObj_diff_sep (α : ℝ) (Z : Fin q → ℝ) {w τ : ℝ}
    (hlo : ∀ k, Z k ≤ τ → Z k ≤ w) (hhi : ∀ k, τ < Z k → w ≤ Z k) :
    cvarObj α Z w - cvarObj α Z τ
      = (w - τ) * (1 - (1 / ((q : ℝ) * (1 - α)))
          * ((Finset.univ.filter (fun k => τ < Z k)).card : ℝ)) := by
  have hkey : (∑ k, max (Z k - w) 0) - (∑ k, max (Z k - τ) 0)
      = ((Finset.univ.filter (fun k => τ < Z k)).card : ℝ) * (τ - w) := by
    rw [← Finset.sum_sub_distrib,
        ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => τ < Z k)
            (fun k => max (Z k - w) 0 - max (Z k - τ) 0)]
    have hP : (∑ k ∈ Finset.univ.filter (fun k => τ < Z k),
                (max (Z k - w) 0 - max (Z k - τ) 0))
            = ∑ _k ∈ Finset.univ.filter (fun k => τ < Z k), (τ - w) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hτk : τ < Z k := (Finset.mem_filter.mp hk).2
      have hwk : w ≤ Z k := hhi k hτk
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ Z k - w),
          max_eq_left (by linarith : (0 : ℝ) ≤ Z k - τ)]; ring
    have hnP : (∑ k ∈ Finset.univ.filter (fun k => ¬ τ < Z k),
                (max (Z k - w) 0 - max (Z k - τ) 0)) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      have hτk : Z k ≤ τ := not_lt.mp (Finset.mem_filter.mp hk).2
      have hwk : Z k ≤ w := hlo k hτk
      rw [max_eq_right (by linarith : Z k - w ≤ (0 : ℝ)),
          max_eq_right (by linarith : Z k - τ ≤ (0 : ℝ))]; ring
    rw [hP, hnP, add_zero, Finset.sum_const, nsmul_eq_mul]
  have expand : cvarObj α Z w - cvarObj α Z τ
      = (w - τ) + (1 / ((q : ℝ) * (1 - α)))
          * ((∑ k, max (Z k - w) 0) - (∑ k, max (Z k - τ) 0)) := by
    simp only [cvarObj]; ring
  rw [expand, hkey]; ring

/-- **T2 — the inf-form minimizer is a sample point** (`cvarObj_min_at_sample`).
There is a sample `Z k` at which the objective is globally minimal over all `τ ∈ ℝ`.
The objective is piecewise-linear with breakpoints exactly at the samples, so its
global minimum is attained at one of them (RU-2002 Prop. 8: the argmin lower
endpoint is `z_{k_α}` = VaR). Atom-safe: no distinctness hypothesis on `Z`. -/
theorem cvarObj_min_at_sample (α : ℝ) (Z : Fin q → ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, ∀ τ, cvarObj α Z (Z k) ≤ cvarObj α Z τ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1a : (0 : ℝ) < 1 - α := by linarith
  have hden : (0 : ℝ) < (q : ℝ) * (1 - α) := mul_pos hq' h1a
  have hc₀ : (0 : ℝ) < 1 / ((q : ℝ) * (1 - α)) := div_pos one_pos hden
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  -- per-point: every τ is dominated by SOME sample
  have key : ∀ τ, ∃ k, cvarObj α Z (Z k) ≤ cvarObj α Z τ := by
    intro τ
    by_cases hcase : 1 ≤ (1 / ((q : ℝ) * (1 - α)))
        * ((Finset.univ.filter (fun k => τ < Z k)).card : ℝ)
    · -- right slope ≤ 0: descend up to the smallest sample strictly above τ
      have hPne : (Finset.univ.filter (fun k => τ < Z k)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro hempty
        rw [hempty, Finset.card_empty, Nat.cast_zero, mul_zero] at hcase
        linarith
      obtain ⟨k, hkP, hkmin⟩ :=
        Finset.exists_min_image (Finset.univ.filter (fun k => τ < Z k)) Z hPne
      have hτk : τ < Z k := (Finset.mem_filter.mp hkP).2
      refine ⟨k, ?_⟩
      have hlo : ∀ j, Z j ≤ τ → Z j ≤ Z k := fun j hj => by linarith
      have hhi : ∀ j, τ < Z j → Z k ≤ Z j := fun j hj =>
        hkmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hdiff := cvarObj_diff_sep α Z hlo hhi
      nlinarith [hdiff, hτk, hcase]
    · -- right slope > 0: descend down to the largest sample at/below τ
      rw [not_le] at hcase
      have hAne : (Finset.univ.filter (fun k => Z k ≤ τ)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro hempty
        have hfull : (Finset.univ.filter (fun k => τ < Z k)) = Finset.univ := by
          apply Finset.eq_univ_of_forall; intro k
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ k, ?_⟩
          by_contra hnk
          have hk : k ∈ Finset.univ.filter (fun k => Z k ≤ τ) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ k, not_lt.mp hnk⟩
          rw [hempty] at hk; exact absurd hk (Finset.notMem_empty k)
        have hcardq : ((Finset.univ.filter (fun k => τ < Z k)).card : ℝ) = (q : ℝ) := by
          rw [hfull, Finset.card_univ, Fintype.card_fin]
        have hbig : (1 : ℝ)
            ≤ (1 / ((q : ℝ) * (1 - α)))
                * ((Finset.univ.filter (fun k => τ < Z k)).card : ℝ) := by
          rw [hcardq, div_mul_eq_mul_div, one_mul, one_le_div hden]
          nlinarith [mul_nonneg (le_of_lt hq') hα0]
        linarith
      obtain ⟨k, hkA, hkmax⟩ :=
        Finset.exists_max_image (Finset.univ.filter (fun k => Z k ≤ τ)) Z hAne
      have hkτ : Z k ≤ τ := (Finset.mem_filter.mp hkA).2
      refine ⟨k, ?_⟩
      have hlo : ∀ j, Z j ≤ τ → Z j ≤ Z k := fun j hj =>
        hkmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
      have hhi : ∀ j, τ < Z j → Z k ≤ Z j := fun j hj => by linarith
      have hdiff := cvarObj_diff_sep α Z hlo hhi
      nlinarith [hdiff, hkτ, hcase]
  -- finite argmin over the samples, then dominate any τ through `key`
  obtain ⟨k₀, -, hk₀⟩ :=
    Finset.exists_min_image Finset.univ (fun k => cvarObj α Z (Z k)) Finset.univ_nonempty
  refine ⟨k₀, fun τ => ?_⟩
  obtain ⟨k, hk⟩ := key τ
  exact le_trans (hk₀ k (Finset.mem_univ k)) hk

/-- **T3 — the inf-form is attained at a sample** (`cvarSAA_eq_obj_sample`). The
defined CVaR `cvarSAA α Z = ⨅ τ, cvarObj α Z τ` equals the objective evaluated at a
sample `Z k` — the RU-2002 Prop. 8 closed-form shape (`CVaR = cvarObj(VaR)`). -/
theorem cvarSAA_eq_obj_sample (α : ℝ) (Z : Fin q → ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    ∃ k, cvarSAA α Z = cvarObj α Z (Z k) := by
  obtain ⟨k, hk⟩ := cvarObj_min_at_sample α Z hq hα0 hα
  refine ⟨k, ?_⟩
  have hbdd : BddBelow (Set.range (cvarObj α Z)) :=
    ⟨cvarObj α Z (Z k), by rintro _ ⟨τ, rfl⟩; exact hk τ⟩
  exact le_antisymm (ciInf_le hbdd (Z k)) (le_ciInf (fun τ => hk τ))

/-! ### A2 — the Artzner coherence bundle for `cvarSAA`

`VaRSubadditivity.lean` seals the NEGATIVE half of obligation A2 by kernel `decide`: VaR
violates Artzner's Axiom S on the two-bond example (`var_not_subadditive`). The positive
half — that `cvarSAA` satisfies all four coherence axioms — was previously asserted from the
literature rather than proved here. This section closes it, so the design decision "use CVaR,
not VaR" is a theorem in the same repository as its counterexample.

  A2.1 `cvarSAA_mono`             — monotonicity (Artzner Axiom M).
  A2.2 `cvarSAA_translation`      — translation equivariance (Axiom T).
  A2.3 `cvarSAA_posHomogeneous`   — positive homogeneity (Axiom PH).
  A2.4 `cvarSAA_subadditive`      — subadditivity (Axiom S) — the one VaR fails.

`cvarSAA_const` (the risk of a certain loss is that loss) is proved en route; it is the
normalization the `λ = 0` branch of positive homogeneity degenerates to.

Every proof runs on the inf-form and needs no new machinery: attainment (T2) supplies the
`BddBelow` witness both infimum comparisons need, and the pointwise inequalities are
elementary facts about `max · 0`. All four are stated for an ARBITRARY sample, so they are
atom-safe by construction like T1–T3.
-/

/-- The SAA objective is bounded below over all `τ`, because T2 says its minimum is ATTAINED
at a sample. This is the witness every `ciInf_le` in this section needs. -/
theorem cvarObj_bddBelow (α : ℝ) (Z : Fin q → ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    BddBelow (Set.range (cvarObj α Z)) := by
  obtain ⟨k, hk⟩ := cvarObj_min_at_sample α Z hq hα0 hα
  exact ⟨cvarObj α Z (Z k), by rintro _ ⟨τ, rfl⟩; exact hk τ⟩

/-- The infimum is below the objective at every `τ` — `ciInf_le` packaged with its witness. -/
theorem cvarSAA_le_obj (α : ℝ) (Z : Fin q → ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) (τ : ℝ) :
    cvarSAA α Z ≤ cvarObj α Z τ :=
  ciInf_le (cvarObj_bddBelow α Z hq hα0 hα) τ

/-- The SAA objective is monotone in the loss sample, pointwise in `τ`. Each summand
`max (Z k − τ) 0` is monotone in `Z k` and the weight `1/(q(1−α))` is nonnegative. -/
theorem cvarObj_mono (α : ℝ) {Z Z' : Fin q → ℝ} (hq : 0 < q) (hα : α < 1)
    (hZ : ∀ k, Z k ≤ Z' k) (τ : ℝ) :
    cvarObj α Z τ ≤ cvarObj α Z' τ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1a : (0 : ℝ) < 1 - α := by linarith
  have hden : (0 : ℝ) < (q : ℝ) * (1 - α) := mul_pos hq' h1a
  have hc : (0 : ℝ) ≤ 1 / ((q : ℝ) * (1 - α)) := le_of_lt (div_pos one_pos hden)
  have hsum : (∑ k, max (Z k - τ) 0) ≤ ∑ k, max (Z' k - τ) 0 :=
    Finset.sum_le_sum fun k _ => max_le_max (by linarith [hZ k]) le_rfl
  have hscaled := mul_le_mul_of_nonneg_left hsum hc
  simp only [cvarObj]
  linarith

/-- **A2.1 — monotonicity** (`cvarSAA_mono`, Artzner Axiom M). A pointwise larger loss sample
has a larger sampled CVaR. The infimum comparison needs the objective bounded below, which is
exactly the sealed attainment T2.

(Previously proved in `CvarMarginWrapper.lean` as the E1 composition tool E1.4, where that
file's own header disclaimed the coherence reading. It belongs on the engine; downstream uses
are unchanged because `CvarMarginWrapper` imports this module.) -/
theorem cvarSAA_mono (α : ℝ) {Z Z' : Fin q → ℝ}
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) (hZ : ∀ k, Z k ≤ Z' k) :
    cvarSAA α Z ≤ cvarSAA α Z' := by
  have hstep : ∀ τ, cvarSAA α Z ≤ cvarObj α Z' τ := fun τ =>
    le_trans (cvarSAA_le_obj α Z hq hα0 hα τ) (cvarObj_mono α hq hα hZ τ)
  exact le_ciInf hstep

/-- **Normalization** (`cvarSAA_const`). The sampled CVaR of a certain loss `c` is `c`: the
objective is `τ + (1/(1−α))·(c − τ)⁺`, which equals `c` at `τ = c` and is `≥ c` everywhere
(left of `c` because `1/(1−α) ≥ 1`, right of `c` because the positive part vanishes). -/
theorem cvarSAA_const (α : ℝ) (c : ℝ) (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    cvarSAA α (fun _ : Fin q => c) = c := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1a : (0 : ℝ) < 1 - α := by linarith
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq'
  have hane : (1 : ℝ) - α ≠ 0 := ne_of_gt h1a
  have hobj : ∀ τ : ℝ, cvarObj α (fun _ : Fin q => c) τ = τ + (1 / (1 - α)) * max (c - τ) 0 := by
    intro τ
    simp only [cvarObj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hs : (1 : ℝ) ≤ 1 / (1 - α) := (one_le_div h1a).mpr (by linarith)
  have hlb : ∀ τ, c ≤ cvarObj α (fun _ : Fin q => c) τ := by
    intro τ
    rw [hobj]
    rcases le_or_gt τ c with h | h
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ c - τ)]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / (1 - α) - 1)
        (by linarith : (0 : ℝ) ≤ c - τ)]
    · rw [max_eq_right (by linarith : c - τ ≤ (0 : ℝ))]
      linarith
  have hat : cvarObj α (fun _ : Fin q => c) c = c := by rw [hobj]; simp
  have hbdd : BddBelow (Set.range (cvarObj α (fun _ : Fin q => c))) :=
    ⟨c, by rintro _ ⟨τ, rfl⟩; exact hlb τ⟩
  have hle : cvarSAA α (fun _ : Fin q => c) ≤ c := le_trans (ciInf_le hbdd c) (le_of_eq hat)
  have hge : c ≤ cvarSAA α (fun _ : Fin q => c) := le_ciInf hlb
  linarith

/-- Shifting every sample by `c` shifts the objective's argument by `c` and its value by `c`.
This is the reindexing that makes translation equivariance a bijection of the `τ`-line. -/
private lemma cvarObj_translate (α : ℝ) (Z : Fin q → ℝ) (c σ : ℝ) :
    cvarObj α (fun k => Z k + c) σ = cvarObj α Z (σ - c) + c := by
  simp only [cvarObj]
  have hmax : ∀ k : Fin q, max (Z k + c - σ) 0 = max (Z k - (σ - c)) 0 := by
    intro k; congr 1; ring
  simp only [hmax]
  ring

/-- **A2.2 — translation equivariance** (`cvarSAA_translation`, Artzner Axiom T). Adding a
deterministic `c` to every scenario's loss raises the sampled CVaR by exactly `c`. The map
`τ ↦ τ + c` is a bijection of the auxiliary line carrying one objective onto the other plus
`c`, so the two infima differ by `c`. -/
theorem cvarSAA_translation (α : ℝ) (Z : Fin q → ℝ) (c : ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    cvarSAA α (fun k => Z k + c) = cvarSAA α Z + c := by
  refine le_antisymm ?_ ?_
  · have h : ∀ τ : ℝ, cvarSAA α (fun k => Z k + c) - c ≤ cvarObj α Z τ := by
      intro τ
      have hle : cvarSAA α (fun k => Z k + c) ≤ cvarObj α (fun k => Z k + c) (τ + c) :=
        cvarSAA_le_obj α (fun k => Z k + c) hq hα0 hα (τ + c)
      rw [cvarObj_translate α Z c (τ + c), add_sub_cancel_right] at hle
      linarith
    have hle2 : cvarSAA α (fun k => Z k + c) - c ≤ cvarSAA α Z := le_ciInf h
    linarith
  · have h : ∀ σ : ℝ, cvarSAA α Z + c ≤ cvarObj α (fun k => Z k + c) σ := by
      intro σ
      rw [cvarObj_translate α Z c σ]
      have hle : cvarSAA α Z ≤ cvarObj α Z (σ - c) := cvarSAA_le_obj α Z hq hα0 hα (σ - c)
      linarith
    exact le_ciInf h

/-- Scaling every sample by `λ ≥ 0` scales the objective, provided the auxiliary variable is
scaled with it: `(λ a)⁺ = λ a⁺`, so the whole objective is homogeneous along `τ ↦ λ τ`. -/
private lemma cvarObj_smul (α : ℝ) (Z : Fin q → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (τ : ℝ) :
    cvarObj α (fun k => lam * Z k) (lam * τ) = lam * cvarObj α Z τ := by
  have hmax : ∀ k : Fin q, max (lam * Z k - lam * τ) 0 = lam * max (Z k - τ) 0 := by
    intro k
    rcases le_total (Z k - τ) 0 with h | h
    · rw [max_eq_right h, mul_zero,
        max_eq_right (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hlam h] :
          lam * Z k - lam * τ ≤ (0 : ℝ))]
    · rw [max_eq_left h, ← mul_sub]
      exact max_eq_left (mul_nonneg hlam h)
  simp only [cvarObj, hmax, ← Finset.mul_sum]
  ring

/-- **A2.3 — positive homogeneity** (`cvarSAA_posHomogeneous`, Artzner Axiom PH). Scaling
every scenario's loss by `λ ≥ 0` scales the sampled CVaR by `λ`. For `λ > 0` the map
`τ ↦ λ τ` is a bijection of the auxiliary line and the objective is homogeneous along it; the
`λ = 0` branch degenerates to the certain loss `0` and is `cvarSAA_const`. -/
theorem cvarSAA_posHomogeneous (α : ℝ) (Z : Fin q → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    cvarSAA α (fun k => lam * Z k) = lam * cvarSAA α Z := by
  rcases eq_or_lt_of_le hlam with hz | hpos
  · rw [← hz]
    simp only [zero_mul]
    exact cvarSAA_const α 0 hq hα0 hα
  · have hlne : lam ≠ 0 := ne_of_gt hpos
    refine le_antisymm ?_ ?_
    · have h : ∀ τ : ℝ, cvarSAA α (fun k => lam * Z k) / lam ≤ cvarObj α Z τ := by
        intro τ
        have hle : cvarSAA α (fun k => lam * Z k) ≤ cvarObj α (fun k => lam * Z k) (lam * τ) :=
          cvarSAA_le_obj α (fun k => lam * Z k) hq hα0 hα (lam * τ)
        rw [cvarObj_smul α Z hlam τ] at hle
        rw [div_le_iff₀ hpos]
        linarith
      have hle2 : cvarSAA α (fun k => lam * Z k) / lam ≤ cvarSAA α Z := le_ciInf h
      rw [div_le_iff₀ hpos] at hle2
      linarith
    · have h : ∀ σ : ℝ, lam * cvarSAA α Z ≤ cvarObj α (fun k => lam * Z k) σ := by
        intro σ
        have hσ : σ = lam * (σ / lam) := by field_simp
        rw [hσ, cvarObj_smul α Z hlam (σ / lam)]
        have hle : cvarSAA α Z ≤ cvarObj α Z (σ / lam) :=
          cvarSAA_le_obj α Z hq hα0 hα (σ / lam)
        exact mul_le_mul_of_nonneg_left hle hlam
      exact le_ciInf h

/-- The pointwise engine of subadditivity: `(a + b)⁺ ≤ a⁺ + b⁺` summand by summand, so the
objective of the summed sample at the summed auxiliary variable is below the sum of the two
objectives. Everything else is an infimum over the diagonal dominating the infimum over the
product. -/
private lemma cvarObj_subadd (α : ℝ) (Z Z' : Fin q → ℝ) (hq : 0 < q) (hα : α < 1) (τ τ' : ℝ) :
    cvarObj α (fun k => Z k + Z' k) (τ + τ') ≤ cvarObj α Z τ + cvarObj α Z' τ' := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1a : (0 : ℝ) < 1 - α := by linarith
  have hden : (0 : ℝ) < (q : ℝ) * (1 - α) := mul_pos hq' h1a
  have hc : (0 : ℝ) ≤ 1 / ((q : ℝ) * (1 - α)) := le_of_lt (div_pos one_pos hden)
  have hsum : (∑ k, max (Z k + Z' k - (τ + τ')) 0)
      ≤ (∑ k, max (Z k - τ) 0) + (∑ k, max (Z' k - τ') 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have ha := le_max_left (Z k - τ) 0
    have ha0 := le_max_right (Z k - τ) 0
    have hb := le_max_left (Z' k - τ') 0
    have hb0 := le_max_right (Z' k - τ') 0
    exact max_le (by linarith) (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hsum hc
  simp only [cvarObj]
  linarith

/-- **A2.4 — subadditivity** (`cvarSAA_subadditive`, Artzner Axiom S). The sampled CVaR of a
sum of losses is at most the sum of their sampled CVaRs — diversification never increases
risk. This is the axiom `VaRSubadditivity.var_not_subadditive` shows VaR violates, and the
two compile in the same build, so the contrast is machine-checked rather than cited.

The inf-form makes it short: `cvarObj α (Z+Z') (τ+τ') ≤ cvarObj α Z τ + cvarObj α Z' τ'`
pointwise, and the infimum over the DIAGONAL `{(τ, τ)}` is dominated by the infimum over the
full product, which factors. Attainment (T2) supplies the `BddBelow` witness. -/
theorem cvarSAA_subadditive (α : ℝ) (Z Z' : Fin q → ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) :
    cvarSAA α (fun k => Z k + Z' k) ≤ cvarSAA α Z + cvarSAA α Z' := by
  have step : ∀ τ τ' : ℝ,
      cvarSAA α (fun k => Z k + Z' k) ≤ cvarObj α Z τ + cvarObj α Z' τ' := by
    intro τ τ'
    exact le_trans (cvarSAA_le_obj α (fun k => Z k + Z' k) hq hα0 hα (τ + τ'))
      (cvarObj_subadd α Z Z' hq hα τ τ')
  have h1 : ∀ τ' : ℝ, cvarSAA α (fun k => Z k + Z' k) - cvarObj α Z' τ' ≤ cvarSAA α Z := by
    intro τ'
    exact le_ciInf (fun τ => by linarith [step τ τ'])
  have h2 : cvarSAA α (fun k => Z k + Z' k) - cvarSAA α Z ≤ cvarSAA α Z' :=
    le_ciInf (fun τ' => by linarith [h1 τ'])
  linarith

end Ctrllib

#print axioms Ctrllib.cvarObj_convexOn
#print axioms Ctrllib.cvarObj_min_at_sample
#print axioms Ctrllib.cvarSAA_eq_obj_sample
#print axioms Ctrllib.cvarObj_bddBelow
#print axioms Ctrllib.cvarSAA_le_obj
#print axioms Ctrllib.cvarObj_mono
#print axioms Ctrllib.cvarSAA_mono
#print axioms Ctrllib.cvarSAA_const
#print axioms Ctrllib.cvarSAA_translation
#print axioms Ctrllib.cvarSAA_posHomogeneous
#print axioms Ctrllib.cvarSAA_subadditive
