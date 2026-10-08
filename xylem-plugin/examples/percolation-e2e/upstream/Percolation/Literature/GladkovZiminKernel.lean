import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Percolation.Literature.DecisionTreeWeighted
import Percolation.Util.Linter

/-!
# The Gladkov–Zimin two-copy kernel inequality (Harris–Kleitman-type inequalities for product measures)

Written in the finitary weighted-cube language of `DecisionTreeWeighted.lean`
(`wtW D p S = ∏_{i ∈ D} (p_i if i ∈ S else 1 - p_i)`, configurations are `Finset ι`, `S ⊆ D` enforced by summing over
`D.powerset`; no measure theory).

## Source

Primary: N. Gladkov, *Inequalities for connectivity events in Bernoulli percolation*, Ph.D. thesis, UCLA (2025),
Chapter 5 ("On Harris–Kleitman type inequalities", based on a manuscript with A. Zimin), Theorem 5.2.1 (p. 98),
Corollary 5.2.2 (p. 99), Theorem 5.2.3 (p. 100) [cite: Gladkov2025Thesis, Thm. 5.2.1 (p. 98), Cor. 5.2.2 (p. 99), Thm. 5.2.3 (p. 100)];
= N. Gladkov, A. Zimin, *On Harris–Kleitman type inequalities*, manuscript, September 2024, Theorems 2.1, 2.2, 2.3
[cite: GladkovZimin2024HK, Thms. 2.1–2.3]. Quoted from the thesis:

> **Theorem 5.2.1.** Let `μ` be a probability product measure on `2^[n]`. Let `g(x, y)` be a function on
> `2^[n] × 2^[n]` such that for any `x ⪯ y`, `z ⪯ t` one has `g(x, z) + g(y, t) ≤ g(x, t) + g(y, z)`. (5.1)
> Then `E_{μ×μ} g(x, y) ≥ E_μ g(x, x)`. (5.2)

> **Corollary 5.2.2.** Let `f₁` and `f₂` be nondecreasing functions on `H_n`, then `f₁` and `f₂` correlate nonnegatively
> with respect to `μ`.

> **Theorem 5.2.3.** Let `P` be a poset of size `m` and `H_n` be split into subsets `S_p` indexed by `p ∈ P` such that if
> `x ∈ S_a` and `y ∈ S_b` are such that `x ⪯ y`, then `a ≤_P b`. Let `A` be an `m × m` matrix satisfying the condition
> `A_{a,c} + A_{b,d} ≤ A_{a,d} + A_{b,c}`, (5.3) whenever `a <_P b` and `c <_P d`. Then for any probability product
> measure `μ` we have `Σ_{a,b ∈ P} A_{a,b} μ(S_a) μ(S_b) ≥ Σ_{a ∈ P} A_{a,a} μ(S_a)`. (5.4)

The manuscript's Theorem 2.1 adds: "Moreover, if the sign in (1) is reversed, the sign in (2) reverses as well."

## What is proved here

The REVERSED-SIGN form, i.e. Theorem 5.2.1 applied to `−g` (hypothesis and conclusion are linear in `g`), which is the
orientation containing Harris–Kleitman: call `g` **cross-supermodular** if `g x t + g y z ≤ g x z + g y t` whenever
`x ⊆ y` and `z ⊆ t` (for `g(x, y) = f₁(x) f₂(y)` with `f₁, f₂` increasing this is `(f₁ y − f₁ x)(f₂ t − f₂ z) ≥ 0`).
Then the two-copy average is at most the diagonal average:

* `ED D p φ = Σ_{S ⊆ D} wtW D p S · φ S` — expectation of `φ` under the weighted cube (with `ED_empty`, `ED_insert`
  (one-coordinate decomposition), `ED_add`, `ED_mul_left`, `ED_mono`);
* **`ED_ED_le_ED_diag`** — Theorem 5.2.1 (reversed-sign form): for cross-supermodular `g` and `p ∈ [0,1]^ι`,
  `ED D p (fun S => ED D p (fun T => g S T)) ≤ ED D p (fun S => g S S)`;
* `sum_sum_wtW_le_sum_wtW_diag` — the same with the sums written out;
* **`kernel_sum_sum_le_sum_of_monotone`** — Theorem 5.2.3 along a monotone labelling `π` of configurations by a
  preorder, for a kernel `A` with `A a d + A b c ≤ A a c + A b d` whenever `a ≤ b`, `c ≤ d`;
* `classMass D p π a = Σ_{S ⊆ D, π S = a} wtW D p S` and **`kernel_classMass_le`** — Theorem 5.2.3 as printed, on the
  vector of class masses: `Σ_{a,b ∈ t} A a b · m_a m_b ≤ Σ_{a ∈ t} A a a · m_a` for any finite `t` containing the labels.

## Proof (the induction of the source on `n`, mirrored on `D`)

Induction on the finite coordinate set `D` (`Finset.induction_on`). For `D = ∅` both sides are `g ∅ ∅`. For
`D = insert e D'`, the one-coordinate decomposition `ED_{insert e D'} φ = (1 - p_e) ED_{D'} φ + p_e ED_{D'} (φ ∘ insert e)`
splits the two-copy average into four pieces with weights `(1-p_e)², (1-p_e)p_e, p_e(1-p_e), p_e²` and the diagonal
average into two; the kernel condition with `x = S ⊆ y = insert e S`, `z = T ⊆ t = insert e T` bounds the two mixed
pieces by the two pure ones, and the induction hypothesis (for `g` and for `g (insert e ·) (insert e ·)`) finishes:
`(1-p)² X₀₀ + p(1-p)(X₀₁ + X₁₀) + p² X₁₁ ≤ (1-p) X₀₀ + p X₁₁ ≤ (1-p) Y₀ + p Y₁`.

Not here: the completely-positive realizability test (thesis Thm. 5.4.2 = manuscript Thm. 4.3), conditional posets,
and the manuscript's higher-degree §5.
-/

noncomputable section

namespace Percolation.Literature

namespace DecisionTree

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ### Expectation under the weighted cube -/

/-- The expectation of `φ` under the weighted cube on the coordinates `D`:
`ED D p φ = Σ_{S ⊆ D} wtW D p S · φ S`. [cite: Gladkov2025Thesis, §5.2 (p. 98), E_μ] (= [cite: GladkovZimin2024HK, §2]) -/
def ED (D : Finset ι) (p : ι → ℝ) (φ : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ D.powerset, wtW D p S * φ S

/-- On no coordinates the expectation is evaluation at the empty configuration. [folklore] -/
theorem ED_empty (p : ι → ℝ) (φ : Finset ι → ℝ) : ED ∅ p φ = φ ∅ := by
  simp [ED, wtW]

/-- Weight of a configuration avoiding the new coordinate `e`: factor `1 - p_e`. [folklore] -/
theorem wtW_insert_of_notMem {D : Finset ι} {e : ι} (p : ι → ℝ) (he : e ∉ D) {S : Finset ι}
    (heS : e ∉ S) : wtW (insert e D) p S = (1 - p e) * wtW D p S := by
  unfold wtW
  rw [Finset.prod_insert he, if_neg heS]

/-- Weight of a configuration containing the new coordinate `e`: factor `p_e`. [folklore] -/
theorem wtW_insert_insert {D : Finset ι} {e : ι} (p : ι → ℝ) (he : e ∉ D) (S : Finset ι) :
    wtW (insert e D) p (insert e S) = p e * wtW D p S := by
  unfold wtW
  rw [Finset.prod_insert he, if_pos (Finset.mem_insert_self e S)]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hie : i ≠ e := fun h => he (h ▸ hi)
  simp only [Finset.mem_insert, hie, false_or]

/-- **One-coordinate decomposition of the expectation**:
`ED_{insert e D} φ = (1 - p_e) · ED_D φ + p_e · ED_D (φ ∘ insert e)`. [folklore] -/
theorem ED_insert {D : Finset ι} {e : ι} (p : ι → ℝ) (he : e ∉ D) (φ : Finset ι → ℝ) :
    ED (insert e D) p φ =
      (1 - p e) * ED D p φ + p e * ED D p (fun S => φ (insert e S)) := by
  unfold ED
  rw [Finset.sum_powerset_insert he, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun S hS => ?_
    have heS : e ∉ S := fun h => he (Finset.mem_powerset.1 hS h)
    rw [wtW_insert_of_notMem p he heS, mul_assoc]
  · refine Finset.sum_congr rfl fun S _ => ?_
    rw [wtW_insert_insert p he S, mul_assoc]

/-- Additivity of the expectation. [folklore] -/
theorem ED_add (D : Finset ι) (p : ι → ℝ) (φ ψ : Finset ι → ℝ) :
    ED D p (fun S => φ S + ψ S) = ED D p φ + ED D p ψ := by
  unfold ED
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- Homogeneity of the expectation. [folklore] -/
theorem ED_mul_left (D : Finset ι) (p : ι → ℝ) (c : ℝ) (φ : Finset ι → ℝ) :
    ED D p (fun S => c * φ S) = c * ED D p φ := by
  unfold ED
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- Monotonicity of the expectation for weights in `[0, 1]`. [folklore] -/
theorem ED_mono (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {φ ψ : Finset ι → ℝ} (h : ∀ S, S ⊆ D → φ S ≤ ψ S) : ED D p φ ≤ ED D p ψ := by
  unfold ED
  exact Finset.sum_le_sum fun S hS =>
    mul_le_mul_of_nonneg_left (h S (Finset.mem_powerset.1 hS)) (wtW_nonneg D hp0 hp1 S)

/-! ### Theorem 2.1: the two-copy kernel inequality -/

/-- **Gladkov–Zimin two-copy kernel inequality (Gladkov 2025, Thm. 5.2.1 = Gladkov–Zimin Thm. 2.1), cross-supermodular (reversed-sign) form.** Let
`p ∈ [0,1]^ι` and let `g` satisfy `g x t + g y z ≤ g x z + g y t` whenever `x ⊆ y` and `z ⊆ t`.
Then the average of `g` over two INDEPENDENT copies of the weighted cube on `D` is at most its
average over the diagonal: `E_{μ×μ} g(S, T) ≤ E_μ g(S, S)`.  (Thm. 5.2.1 is printed with the opposite inequalities (5.1) ⟹ (5.2); this is Thm. 5.2.1 applied to `−g` — the manuscript: "if the sign in (1) is reversed, the sign in (2) reverses as well".)
[cite: Gladkov2025Thesis, Thm. 5.2.1 (p. 98), applied to −g] (= [cite: GladkovZimin2024HK, Thm. 2.1]) -/
theorem ED_ED_le_ED_diag (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∀ g : Finset ι → Finset ι → ℝ,
      (∀ ⦃x y z t : Finset ι⦄, x ⊆ y → z ⊆ t → g x t + g y z ≤ g x z + g y t) →
        ED D p (fun S => ED D p (fun T => g S T)) ≤ ED D p (fun S => g S S) := by
  induction D using Finset.induction_on with
  | empty =>
    intro g _
    simp only [ED_empty, le_refl]
  | @insert e D' he ih =>
    intro g hg
    -- the four sections of `g` along the coordinate `e`
    set q : ℝ := p e with hq
    have hq0 : 0 ≤ q := hp0 e
    have hq1 : 0 ≤ 1 - q := sub_nonneg.2 (hp1 e)
    set X00 : ℝ := ED D' p (fun S => ED D' p (fun T => g S T)) with hX00
    set X01 : ℝ := ED D' p (fun S => ED D' p (fun T => g S (insert e T))) with hX01
    set X10 : ℝ := ED D' p (fun S => ED D' p (fun T => g (insert e S) T)) with hX10
    set X11 : ℝ := ED D' p (fun S => ED D' p (fun T => g (insert e S) (insert e T))) with hX11
    set Y0 : ℝ := ED D' p (fun S => g S S) with hY0
    set Y1 : ℝ := ED D' p (fun S => g (insert e S) (insert e S)) with hY1
    -- left-hand side, decomposed
    have hL : ED (insert e D') p (fun S => ED (insert e D') p (fun T => g S T)) =
        (1 - q) * ((1 - q) * X00 + q * X01) + q * ((1 - q) * X10 + q * X11) := by
      rw [ED_insert p he]
      have h1 : (fun S => ED (insert e D') p (fun T => g S T)) =
          fun S => (1 - q) * ED D' p (fun T => g S T) + q * ED D' p (fun T => g S (insert e T)) := by
        funext S; rw [ED_insert p he]
      have h2 : (fun S => ED (insert e D') p (fun T => g (insert e S) T)) =
          fun S => (1 - q) * ED D' p (fun T => g (insert e S) T) +
            q * ED D' p (fun T => g (insert e S) (insert e T)) := by
        funext S; rw [ED_insert p he]
      rw [h1, h2, ED_add, ED_add, ED_mul_left, ED_mul_left, ED_mul_left, ED_mul_left]
    -- right-hand side, decomposed
    have hR : ED (insert e D') p (fun S => g S S) = (1 - q) * Y0 + q * Y1 := by
      rw [ED_insert p he]
    -- the kernel condition: mixed sections are dominated by the pure ones
    have hK : X01 + X10 ≤ X00 + X11 := by
      rw [hX01, hX10, hX00, hX11, ← ED_add, ← ED_add]
      refine ED_mono D' hp0 hp1 fun S _ => ?_
      rw [← ED_add, ← ED_add]
      refine ED_mono D' hp0 hp1 fun T _ => ?_
      -- `x = S ⊆ y = insert e S`, `z = T ⊆ t = insert e T`
      exact hg (Finset.subset_insert e S) (Finset.subset_insert e T)
    -- induction hypotheses for `g` and for its upper section
    have hI0 : X00 ≤ Y0 := ih g hg
    have hI1 : X11 ≤ Y1 := by
      refine ih (fun S T => g (insert e S) (insert e T)) ?_
      intro x y z t hxy hzt
      exact hg (Finset.insert_subset_insert e hxy) (Finset.insert_subset_insert e hzt)
    rw [hL, hR]
    have h1 : (1 - q) * q * (X01 + X10) ≤ (1 - q) * q * (X00 + X11) :=
      mul_le_mul_of_nonneg_left hK (mul_nonneg hq1 hq0)
    have h2 : (1 - q) * X00 ≤ (1 - q) * Y0 := mul_le_mul_of_nonneg_left hI0 hq1
    have h3 : q * X11 ≤ q * Y1 := mul_le_mul_of_nonneg_left hI1 hq0
    nlinarith [h1, h2, h3]

/-- **The two-copy kernel inequality with the sums written out**: for cross-supermodular `g` and `p ∈ [0,1]^ι`,
`Σ_{S ⊆ D} Σ_{T ⊆ D} wtW S · wtW T · g S T ≤ Σ_{S ⊆ D} wtW S · g S S`.
[cite: Gladkov2025Thesis, Thm. 5.2.1 (p. 98), applied to −g] (= [cite: GladkovZimin2024HK, Thm. 2.1]) -/
theorem sum_sum_wtW_le_sum_wtW_diag (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) (g : Finset ι → Finset ι → ℝ)
    (hg : ∀ ⦃x y z t : Finset ι⦄, x ⊆ y → z ⊆ t → g x t + g y z ≤ g x z + g y t) :
    ∑ S ∈ D.powerset, ∑ T ∈ D.powerset, wtW D p S * wtW D p T * g S T ≤
      ∑ S ∈ D.powerset, wtW D p S * g S S := by
  have h := ED_ED_le_ED_diag D hp0 hp1 g hg
  unfold ED at h
  have hrw : ∀ S ∈ D.powerset,
      wtW D p S * ∑ T ∈ D.powerset, wtW D p T * g S T =
        ∑ T ∈ D.powerset, wtW D p S * wtW D p T * g S T := by
    intro S _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [Finset.sum_congr rfl hrw] at h
  exact h

/-! ### Theorem 2.3: the poset (matrix) form -/

/-- **Gladkov–Zimin, poset form (Gladkov 2025, Thm. 5.2.3 = Gladkov–Zimin Thm. 2.3), along a monotone labelling.** Let `π` map
configurations to a preorder, monotonically along `⊆`, and let the kernel `A` satisfy
`A a d + A b c ≤ A a c + A b d` whenever `a ≤ b` and `c ≤ d` (condition (5.3) of the thesis, (3) of the manuscript, with its
sign matched to the Harris orientation; it suffices on comparable pairs).  Then
`Σ_{S,T ⊆ D} wtW S · wtW T · A (π S) (π T) ≤ Σ_{S ⊆ D} wtW S · A (π S) (π S)`.
[cite: Gladkov2025Thesis, Thm. 5.2.3 (p. 100), eqs. (5.3)–(5.4)] (= [cite: GladkovZimin2024HK, Thm. 2.3]) -/
theorem kernel_sum_sum_le_sum_of_monotone (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) {κ : Type*} [Preorder κ] (π : Finset ι → κ)
    (hπ : ∀ ⦃x y : Finset ι⦄, x ⊆ y → π x ≤ π y) (A : κ → κ → ℝ)
    (hA : ∀ ⦃a b c d : κ⦄, a ≤ b → c ≤ d → A a d + A b c ≤ A a c + A b d) :
    ∑ S ∈ D.powerset, ∑ T ∈ D.powerset, wtW D p S * wtW D p T * A (π S) (π T) ≤
      ∑ S ∈ D.powerset, wtW D p S * A (π S) (π S) :=
  sum_sum_wtW_le_sum_wtW_diag D hp0 hp1 (fun S T => A (π S) (π T))
    fun _ _ _ _ hxy hzt => hA (hπ hxy) (hπ hzt)

/-- The mass of the class `π = a` under the weighted cube: `m_a = Σ_{S ⊆ D, π S = a} wtW D p S`
(the source's `μ(S_a)`). [cite: Gladkov2025Thesis, Thm. 5.2.3 (p. 100)] (= [cite: GladkovZimin2024HK, Def. 1.3 / Thm. 2.3]) -/
def classMass (D : Finset ι) (p : ι → ℝ) {κ : Type*} [DecidableEq κ] (π : Finset ι → κ) (a : κ) : ℝ :=
  ∑ S ∈ D.powerset with π S = a, wtW D p S

/-- A weighted sum of a function of the label is the sum over labels against the class masses.
[folklore] -/
theorem sum_wtW_mul_comp_eq_sum_classMass (D : Finset ι) (p : ι → ℝ) {κ : Type*} [DecidableEq κ]
    (π : Finset ι → κ) (t : Finset κ) (ht : ∀ S ∈ D.powerset, π S ∈ t) (φ : κ → ℝ) :
    ∑ S ∈ D.powerset, wtW D p S * φ (π S) = ∑ a ∈ t, φ a * classMass D p π a := by
  unfold classMass
  rw [← Finset.sum_fiberwise_of_maps_to ht]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_filter.1 hS).2, mul_comm]

/-- **Gladkov–Zimin, poset form as printed (Gladkov 2025, Thm. 5.2.3, eq. (5.4); class masses).** With `m_a` the class masses of a
labelling `π` that is monotone along `⊆` into a preorder, and a kernel `A` with
`A a d + A b c ≤ A a c + A b d` for `a ≤ b`, `c ≤ d`:
`Σ_{a,b ∈ t} A a b · m_a m_b ≤ Σ_{a ∈ t} A a a · m_a` for every finite `t` containing all labels of
configurations `S ⊆ D`.  (Harris–Kleitman is `A a b = f₁ a f₂ b`; Gladkov's strong Harris–Kleitman
and the three-point Aas–Gladkov row are the kernels of the matrix `M₃` of Gladkov 2025, Thm. 5.3.2 = manuscript (6).)
[cite: Gladkov2025Thesis, Thm. 5.2.3 (p. 100), eqs. (5.3)–(5.4)] (= [cite: GladkovZimin2024HK, Thm. 2.3]) -/
theorem kernel_classMass_le (D : Finset ι) {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {κ : Type*} [Preorder κ] [DecidableEq κ] (π : Finset ι → κ)
    (hπ : ∀ ⦃x y : Finset ι⦄, x ⊆ y → π x ≤ π y) (t : Finset κ) (ht : ∀ S ∈ D.powerset, π S ∈ t)
    (A : κ → κ → ℝ) (hA : ∀ ⦃a b c d : κ⦄, a ≤ b → c ≤ d → A a d + A b c ≤ A a c + A b d) :
    ∑ a ∈ t, ∑ b ∈ t, A a b * (classMass D p π a * classMass D p π b) ≤
      ∑ a ∈ t, A a a * classMass D p π a := by
  have h := kernel_sum_sum_le_sum_of_monotone D hp0 hp1 π hπ A hA
  -- rewrite the diagonal side
  rw [sum_wtW_mul_comp_eq_sum_classMass D p π t ht (fun a => A a a)] at h
  -- rewrite the two-copy side, inner sum first
  have hinner : ∀ S ∈ D.powerset,
      ∑ T ∈ D.powerset, wtW D p S * wtW D p T * A (π S) (π T) =
        wtW D p S * ∑ b ∈ t, A (π S) b * classMass D p π b := by
    intro S _
    rw [← sum_wtW_mul_comp_eq_sum_classMass D p π t ht (fun b => A (π S) b), Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => by ring
  rw [Finset.sum_congr rfl hinner,
    sum_wtW_mul_comp_eq_sum_classMass D p π t ht (fun a => ∑ b ∈ t, A a b * classMass D p π b)] at h
  calc ∑ a ∈ t, ∑ b ∈ t, A a b * (classMass D p π a * classMass D p π b)
      = ∑ a ∈ t, (∑ b ∈ t, A a b * classMass D p π b) * classMass D p π a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ ≤ ∑ a ∈ t, A a a * classMass D p π a := h

end DecisionTree

end Percolation.Literature

end
