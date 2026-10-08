import Percolation.Literature.BernoulliPercolation
import Percolation.Literature.BoxCrossing
import Percolation.Literature.Crossings
import Percolation.Util.Linter

/-!
# Russo–Seymour–Welsh theory for bond percolation on `ℤ²`: the box-crossing lower bound reduced to its printed intermediate steps

This file decomposes the box-crossing property
`Percolation.Literature.rsw_half` (Grimmett, *Percolation*, 2nd ed. (1999), §11.7; Bollobás–Riordan,
*Percolation* (2006), Ch. 3, eq. (3)) into the named intermediate results of the printed proofs,
proves the elementary ones, and proves the assembly step.

Conventions. `crossingProb p m n = P_p(LR([0, m] × [0, n]))` (`Crossings.lean`) is the
probability of an open left-right crossing of the lattice rectangle with `(m + 1) × (n + 1)`
sites, all edges of the rectangle allowed. This is *exactly* Bollobás–Riordan's `h_p(m + 1, n + 1)`
(Ch. 3, p. 2 of the chapter: "a `k` by `ℓ` rectangle" has `k ℓ` sites, `H(R)` = open path in `R`
from the left side to the right side). Grimmett's `LR(kl, l)` (§11.7) uses the box
`[-l, (2k-1)l] × [-l, l]` and forbids boundary edges; we therefore vendor the intermediate
statements in the Bollobás–Riordan form and cite Grimmett's numbered counterparts alongside.

Contents.
* Proved: open crossing events are monotone in the ambient set (`openConnIn_mono`,
  `openCrossing_mono`); `LR(m, n)` is increasing in the height `n` (`lrCrossing_mono_right`) and,
  on lattice configurations, decreasing in the width `m` (`lrCrossing_anti_left`, via the discrete
  intermediate value property `exists_openConnIn_column`); hence `crossingProb p m n` is
  antitone in `m` and monotone in `n` (`crossingProb_anti_left`, `crossingProb_mono_right`;
  Bollobás–Riordan Ch. 3, "`h(m, 2n+1) ≥ h(m, 2n)`"). Also `p ^ m ≤ crossingProb p m n`
  (bottom row open, `pow_le_crossingProb`).
* Statements from print (`def … : Prop`, each proved in this file or its companion files as `…_holds`):
  `crossingProb_add_crossingProb_symm` (Bollobás–Riordan Ch. 3, Cor. 3(i): duality
  `h_p(k, ℓ-1) + h_{1-p}(ℓ, k-1) = 1`), `crossingProb_glue` (Ch. 3, eq. (2) before Cor. 3(iii) is
  substituted; Grimmett (11.76)–(11.77): gluing two horizontal crossings through a vertical
  crossing of the common square, by Harris–FKG), `BollobasRiordan2006_cor5`
  (Ch. 3, Lemma 4 and Cor. 5: `h(3n, 2n) ≥ 2⁻⁷`, the RSW step proper), and `rsw_lowerBound`
  (Ch. 3, eq. (3): `h(kn, n) ≥ h_k > 0`).
* Proved reductions: `half_le_crossingProb_self` (Cor. 3(iii) from `crossingProb_half_succ_self`),
  `rsw_lowerBound_of_glue` (eq. (3) from Cor. 5, eq. (2), Cor. 3(ii) and monotonicity, with the
  explicit constant `h_k = 2^{-24k}`), and the assembly
  `rsw_half_of_lowerBound : rsw_lowerBound → crossingProb_add_crossingProb_symm → rsw_half`.

-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ### Monotonicity of crossing events -/

section General

variable {V : Type*}

/-- `{x ↔ y in S}` is monotone in `S`. (Grimmett 1999, §1.6.) [folklore] -/
theorem openConnIn_mono {S S' : Set V} (h : S ⊆ S') (x y : V) :
    (openConnIn S x y : Set (BondConfig V)) ⊆ openConnIn S' x y := by
  rintro ω ⟨hx, hy, hr⟩
  exact ⟨h hx, h hy, hr.map (SimpleGraph.induceHomOfLE (G := openGraph ω) h).toHom⟩

/-- Open crossing events are monotone in the ambient set and in the two target sets.
(Grimmett 1999, §11.3.) [folklore] -/
theorem openCrossing_mono {S S' A A' B B' : Set V} (hS : S ⊆ S') (hA : A ⊆ A') (hB : B ⊆ B') :
    (openCrossing S A B : Set (BondConfig V)) ⊆ openCrossing S' A' B' := by
  rintro ω ⟨x, hx, y, hy, hω⟩
  exact ⟨x, hA hx, y, hB hy, openConnIn_mono hS x y hω⟩

/-- `P_p` is carried by lattice configurations `ω ⊆ E(G)` (Mathlib's
`setBernoulli_ae_subset`). (Grimmett 1999, §1.3.) [folklore] -/
theorem ae_subset_edgeSet [Countable V] (G : SimpleGraph V) (p : unitInterval) :
    ∀ᵐ ω ∂bondPercolation G p, ω ⊆ G.edgeSet :=
  setBernoulli_ae_subset

end General

/-- Rectangles are monotone in both dimensions. [folklore] -/
theorem rectangle_mono {m m' n n' : ℕ} (hm : m ≤ m') (hn : n ≤ n') :
    rectangle m n ⊆ rectangle m' n' := by
  intro x hx
  rw [mem_rectangle_iff] at hx ⊢
  omega

/-- `LR(m, n) ⊆ LR(m, n')` for `n ≤ n'`: a left-right crossing of `[0, m] × [0, n]` is one of the
taller rectangle `[0, m] × [0, n']`. (Bollobás–Riordan 2006, Ch. 3, "`h(m, 2n+1) ≥ h(m, 2n)`".) [cite: BollobasRiordanPercolation2006, Ch. 3, after eq. (2)] -/
theorem lrCrossing_mono_right (m : ℕ) {n n' : ℕ} (h : n ≤ n') :
    lrCrossing m n ⊆ lrCrossing m n' := by
  refine openCrossing_mono ?_ ?_ ?_
  · exact_mod_cast rectangle_mono le_rfl h
  · intro x hx
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter] at hx ⊢
    exact ⟨rectangle_mono le_rfl h hx.1, hx.2⟩
  · intro x hx
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter] at hx ⊢
    exact ⟨rectangle_mono le_rfl h hx.1, hx.2⟩

/-- Neighbours in `ℤ^d` differ by at most one in every coordinate. [folklore] -/
theorem zdGraph_adj_apply_le {d : ℕ} {x y : LatticeModels.Site d} (h : (LatticeModels.zdGraph d).Adj x y) (i : Fin d) :
    y i ≤ x i + 1 ∧ x i ≤ y i + 1 := by
  rw [LatticeModels.zdGraph_adj_iff] at h
  obtain ⟨j, rfl | rfl⟩ := h
  · rcases eq_or_ne i j with rfl | hij
    · simp only [Pi.add_apply, Pi.single_eq_same]; omega
    · simp [hij]
  · rcases eq_or_ne i j with rfl | hij
    · simp only [Pi.add_apply, Pi.single_eq_same]; omega
    · simp [hij]

/-- Discrete intermediate value property of lattice paths: for a lattice configuration `ω`, an
open path inside `S` from `x` with `x₀ ≤ a` to `y` with `a ≤ y₀` contains an initial segment
inside `S ∩ {z₀ ≤ a}` ending on the column `{z₀ = a}` (the first visit to that column).
(Kesten 1982, §2.2; used implicitly in Bollobás–Riordan 2006, Ch. 3.) [folklore] -/
theorem exists_openConnIn_column {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet)
    {S : Set (LatticeModels.Site 2)} {x y : LatticeModels.Site 2} (a : ℤ) (hx : x 0 ≤ a) (hy : a ≤ y 0)
    (h : ω ∈ openConnIn S x y) :
    ∃ z, z 0 = a ∧ ω ∈ openConnIn (S ∩ {z | z 0 ≤ a}) x z := by
  obtain ⟨hxS, hyS, ⟨p⟩⟩ := h
  suffices H : ∀ (u v : S) (p : ((openGraph ω).induce S).Walk u v), (u : LatticeModels.Site 2) 0 ≤ a →
      a ≤ (v : LatticeModels.Site 2) 0 → ∃ z, z 0 = a ∧ ω ∈ openConnIn (S ∩ {z | z 0 ≤ a}) u z from
    H ⟨x, hxS⟩ ⟨y, hyS⟩ p hx hy
  intro u v p
  induction p with
  | nil =>
    intro hu hv
    rename_i u
    exact ⟨u, le_antisymm hu hv, ⟨u.2, hu⟩, ⟨u.2, hu⟩, SimpleGraph.Reachable.refl _⟩
  | cons hadj p ih =>
    intro hu hv
    rename_i u w v'
    rcases hu.eq_or_lt with hua | hua
    · exact ⟨u, hua, ⟨u.2, hu⟩, ⟨u.2, hu⟩, SimpleGraph.Reachable.refl _⟩
    · have hadj' : (openGraph ω).Adj u w := hadj
      have hw : (w : LatticeModels.Site 2) 0 ≤ a := by
        have hzd : (LatticeModels.zdGraph 2).Adj (u : LatticeModels.Site 2) (w : LatticeModels.Site 2) :=
          hω ((openGraph_adj _ _ _).1 hadj').1
        have := (zdGraph_adj_apply_le hzd 0).1
        omega
      obtain ⟨z, hz, huS, hzS, hr⟩ := ih hw hv
      refine ⟨z, hz, ⟨u.2, hu⟩, hzS, ?_⟩
      refine SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable ?_) hr
      simpa [SimpleGraph.induce_adj] using hadj'

/-- `LR(m', n) ⊆ LR(m, n)` for `m ≤ m'` on lattice configurations: an open left-right crossing of
`[0, m'] × [0, n]`, stopped at its first visit to the column `{x₀ = m}`, is a left-right crossing
of `[0, m] × [0, n]`. (The hypothesis `ω ⊆ E(ℤ²)` is needed because `openGraph ω` treats every
pair in `ω` as an edge; it holds `P_p`-a.s., see `ae_subset_edgeSet`.)
(Bollobás–Riordan 2006, Ch. 3, proof of eq. (3).) [cite: BollobasRiordanPercolation2006, Ch. 3, proof of eq. (3)] -/
theorem lrCrossing_anti_left {m m' : ℕ} (h : m ≤ m') (n : ℕ) {ω : BondConfig (LatticeModels.Site 2)}
    (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) (hc : ω ∈ lrCrossing m' n) : ω ∈ lrCrossing m n := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hc
  simp only [Finset.mem_coe, leftSide, rightSide, Finset.mem_filter, mem_rectangle_iff] at hx hy
  obtain ⟨z, hz, hr⟩ := exists_openConnIn_column hω (m : ℤ) (by rw [hx.2]; positivity)
    (by rw [hy.2]; exact_mod_cast h) hxy
  have hsub : (↑(rectangle m' n) ∩ {z : LatticeModels.Site 2 | z 0 ≤ (m : ℤ)}) ⊆
      (↑(rectangle m n) : Set (LatticeModels.Site 2)) := by
    intro w hw
    simp only [Set.mem_inter_iff, Finset.mem_coe, mem_rectangle_iff, Set.mem_setOf_eq] at hw ⊢
    omega
  have hr' := openConnIn_mono hsub x z hr
  refine ⟨x, ?_, z, ?_, hr'⟩
  · simp only [Finset.mem_coe, leftSide, Finset.mem_filter, mem_rectangle_iff]
    exact ⟨by omega, hx.2⟩
  · obtain ⟨-, hzr, -⟩ := hr'
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter] at hzr ⊢
    exact ⟨hzr, hz⟩

/-- The crossing probability `P_p(LR([0, m] × [0, n]))` is non-increasing in the width `m`
(`h_p(m, n)` is decreasing in `m`). (Bollobás–Riordan 2006, Ch. 3, proof of eq. (3).) [cite: BollobasRiordanPercolation2006, Ch. 3, proof of eq. (3)] -/
theorem crossingProb_anti_left (p : unitInterval) {m m' : ℕ} (h : m ≤ m') (n : ℕ) :
    crossingProb p m' n ≤ crossingProb p m n := by
  unfold crossingProb
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ae_subset_edgeSet (LatticeModels.zdGraph 2) p] with ω hω hc
  exact lrCrossing_anti_left h n hω hc

/-- The crossing probability `P_p(LR([0, m] × [0, n]))` is non-decreasing in the height `n`
("`h(m, 2n+1) ≥ h(m, 2n)`"). (Bollobás–Riordan 2006, Ch. 3, after eq. (2).) [cite: BollobasRiordanPercolation2006, Ch. 3, after eq. (2)] -/
theorem crossingProb_mono_right (p : unitInterval) (m : ℕ) {n n' : ℕ} (h : n ≤ n') :
    crossingProb p m n ≤ crossingProb p m n' :=
  measureReal_mono (lrCrossing_mono_right m h)

/-! ### A trivial lower bound: the bottom row -/

/-- The point `(i, j)` of `ℤ²`. [folklore] -/
abbrev pt (i j : ℤ) : LatticeModels.Site 2 := ![i, j]

/-- `(i + 1, j) = (i, j) + e₀`. [folklore] -/
theorem pt_succ_eq (i j : ℤ) : pt (i + 1) j = pt i j + Pi.single 0 1 := by
  ext k; fin_cases k <;> simp [pt]

/-- The `m` horizontal edges `{(i, 0), (i + 1, 0)}`, `0 ≤ i < m`, of the bottom row of
`[0, m] × [0, n]`. [folklore] -/
def bottomRowEdges (m : ℕ) : Finset (Sym2 (LatticeModels.Site 2)) :=
  (Finset.range m).image fun i : ℕ => s(pt i 0, pt (i + 1) 0)

/-- Bottom-row edges are lattice edges. [folklore] -/
theorem bottomRowEdges_subset_edgeSet (m : ℕ) :
    (↑(bottomRowEdges m) : Set (Sym2 (LatticeModels.Site 2))) ⊆ (LatticeModels.zdGraph 2).edgeSet := by
  intro e he
  simp only [bottomRowEdges, Finset.coe_image, Set.mem_image] at he
  obtain ⟨i, -, rfl⟩ := he
  rw [SimpleGraph.mem_edgeSet, LatticeModels.zdGraph_adj_iff]
  exact ⟨0, Or.inl (by exact_mod_cast pt_succ_eq i 0)⟩

/-- If the whole bottom row is open there is a left-right crossing. [folklore] -/
theorem mem_lrCrossing_of_bottomRowEdges_subset {m n : ℕ} {ω : BondConfig (LatticeModels.Site 2)}
    (h : (↑(bottomRowEdges m) : Set (Sym2 (LatticeModels.Site 2))) ⊆ ω) : ω ∈ lrCrossing m n := by
  have hmem : ∀ k : ℕ, k ≤ m → pt k 0 ∈ (↑(rectangle m n) : Set (LatticeModels.Site 2)) := by
    intro k hk
    simp only [Finset.mem_coe, mem_rectangle_iff, pt, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    omega
  have hreach : ∀ k : ℕ, ∀ hk : k ≤ m,
      ((openGraph ω).induce (↑(rectangle m n) : Set (LatticeModels.Site 2))).Reachable
        ⟨pt 0 0, by exact_mod_cast hmem 0 (Nat.zero_le m)⟩ ⟨pt k 0, hmem k hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      intro hk
      refine (ih (Nat.le_of_succ_le hk)).trans (SimpleGraph.Adj.reachable ?_)
      rw [SimpleGraph.induce_adj, openGraph_adj]
      refine ⟨h ?_, ?_⟩
      · simp only [bottomRowEdges, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
        exact ⟨k, Nat.lt_of_succ_le hk, by push_cast; rfl⟩
      · intro heq
        have := congr_fun heq 0
        simp [pt] at this
  refine ⟨pt 0 0, ?_, pt m 0, ?_, hmem 0 (Nat.zero_le m), hmem m le_rfl, hreach m le_rfl⟩
  · simp [leftSide, pt, mem_rectangle_iff]
  · simp [rightSide, pt, mem_rectangle_iff]

/-- `p ^ m ≤ P_p(LR([0, m] × [0, n]))`: the `m` edges of the bottom row are all open with
probability `p ^ m` (in particular `h_p(k, 1) = p^{k-1}`). (Bollobás–Riordan 2006, Ch. 3, §3.4,
"if the rectangle has an open horizontal crossing, so do both squares" style bounds; elementary.) [folklore] -/
theorem pow_le_crossingProb (p : unitInterval) (m n : ℕ) :
    (p : ℝ) ^ m ≤ crossingProb p m n := by
  have hcard : (bottomRowEdges m).card ≤ m := by
    simpa [bottomRowEdges] using (Finset.card_image_le (s := Finset.range m)
      (f := fun i : ℕ => s(pt i 0, pt (i + 1) 0)))
  calc (p : ℝ) ^ m ≤ (p : ℝ) ^ (bottomRowEdges m).card :=
        pow_le_pow_of_le_one p.2.1 p.2.2 hcard
    _ = (bondPercolation (LatticeModels.zdGraph 2) p).real
          {ω | (↑(bottomRowEdges m) : Set (Sym2 (LatticeModels.Site 2))) ⊆ ω} :=
        (Percolation.Literature.bondPercolation_real_setOf_subset _ p _
          (bottomRowEdges_subset_edgeSet m)).symm
    _ ≤ crossingProb p m n :=
        measureReal_mono (fun ω hω => mem_lrCrossing_of_bottomRowEdges_subset hω)

/-- `crossingProb` is a probability: it lies in `[0, 1]`. [folklore] -/
theorem crossingProb_mem_Icc (p : unitInterval) (m n : ℕ) : crossingProb p m n ∈ Set.Icc 0 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

/-- `1 - 1/2 = 1/2` in the unit interval: `p = 1/2` is self-dual. [folklore] -/
@[simp] theorem symm_half : unitInterval.symm half = half := by
  ext; simp [half]; norm_num

end

end Percolation.Literature

namespace Percolation.Literature

open MeasureTheory LatticeModels

noncomputable section

/-! ### Named intermediate results of the printed proofs -/

/-- **Duality of crossing probabilities** (Bollobás–Riordan, *Percolation* (2006), Ch. 3,
Corollary 3(i); Grimmett 1999, §11.2 and Lemma 11.21). If `R` is a `k` by `ℓ - 1` rectangle and
`R'` a `k - 1` by `ℓ` rectangle of `ℤ²`, then `P_p(H(R)) + P_{1-p}(V(R')) = 1`. In the
conventions of `crossingProb` (`crossingProb p m n = h_p(m + 1, n + 1)`, and a vertical crossing
of an `a` by `b` rectangle has the probability of a horizontal crossing of the transposed `b` by
`a` rectangle), with `k = m + 2`, `ℓ = n + 2`:
`crossingProb p (m + 1) n + crossingProb (1 - p) (n + 1) m = 1`. Consequence of the duality
lemma `Percolation.Literature.lrCrossing_xor_dualTBCrossing`, of `Percolation.Literature.bondPercolation_map_dualConfig`
and of the invariance of `P_p` under the symmetries of `ℤ²`. [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 3(i)] -/
def crossingProb_add_crossingProb_symm : Prop :=
  ∀ (p : unitInterval) (m n : ℕ),
    crossingProb p (m + 1) n + crossingProb (unitInterval.symm p) (n + 1) m = 1

/-- **Gluing horizontal crossings** (Bollobás–Riordan, *Percolation* (2006), Ch. 3, eq. (2) with
Figure 7 at `p = 1/2`, and §3.4, eq. (12) with Figure 11 for general `p`, in the form Harris's
Lemma gives before `h(N, N) ≥ 1/2` is substituted; Grimmett 1999, Lemma 11.75,
(11.76)–(11.77) is the same argument in Grimmett's conventions). If an `M₁` by `N` rectangle and
an `M₂` by `N` rectangle of `ℤ²` intersect in an `N` by `N` square, both rectangles have open
horizontal crossings and the square has an open vertical crossing, then the union (an
`M₁ + M₂ - N` by `N` rectangle) has an open horizontal crossing; "noting that the probability that
an `N` by `N` square has an open vertical crossing is just `h_p(N, N)`, from Harris's Lemma"
`h_p(M₁ + M₂ - N, N) ≥ h_p(M₁, N) h_p(M₂, N) h_p(N, N)` for `M₁, M₂ ≥ N`. In `crossingProb`
indices (`Mᵢ = mᵢ + 1`, `N = n + 1`): [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (2) and eq. (12)] [cite: GrimmettPercolation1999, Lemma 11.75] -/
def crossingProb_glue : Prop :=
  ∀ (p : unitInterval) (m₁ m₂ n : ℕ), n ≤ m₁ → n ≤ m₂ →
    crossingProb p m₁ n * crossingProb p m₂ n * crossingProb p n n ≤
      crossingProb p (m₁ + m₂ - n) n

/-- **The Russo–Seymour–Welsh step** (Bollobás–Riordan, *Percolation* (2006), Ch. 3, Lemma 4 and
Corollary 5; cf. Grimmett 1999, Lemma 11.73). For all `n ≥ 1`, `h(3n, 2n) ≥ 2⁻⁷` at `p = 1/2`:
the `3n` by `2n` rectangle of `ℤ²` has an open horizontal crossing with probability at least
`2⁻⁷`. In `crossingProb` indices, with `n = j + 1`: `crossingProb ½ (3j + 2) (2j + 1) ≥ 2⁻⁷`. [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 5] -/
def BollobasRiordan2006_cor5 : Prop :=
  ∀ j : ℕ, (2 : ℝ)⁻¹ ^ 7 ≤ crossingProb half (3 * j + 2) (2 * j + 1)

/-- **RSW lower bound for long rectangles** (Bollobás–Riordan, *Percolation* (2006), Ch. 3,
eq. (3); Grimmett 1999, §11.7, (11.72) for the annulus form). For every `k ≥ 2` there is
`h_k > 0` such that `h(kn, n) ≥ h_k` for all `n ≥ 1` at `p = 1/2`: the `kn` by `n` rectangle is
crossed horizontally with probability bounded below uniformly in `n`. In `crossingProb` indices
`h(kn, n) = crossingProb ½ (kn - 1) (n - 1)` (no truncation occurs since `kn ≥ 2`, `n ≥ 1`). [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (3)] [cite: GrimmettPercolation1999, §11.7 (11.72)] -/
def rsw_lowerBound : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c ≤ crossingProb half (k * n - 1) (n - 1)

/-! ### Reductions -/

/-- Bollobás–Riordan 2006, Ch. 3, Corollary 3(iii): `h(n, n) ≥ 1/2` at `p = 1/2`, from
Corollary 3(ii) (`crossingProb_half_succ_self`: `h(n + 1, n) = 1/2`) and monotonicity in the
width. [cite: BollobasRiordanPercolation2006, Ch. 3, Corollary 3(iii)] -/
theorem half_le_crossingProb_self (hself : crossingProb_half_succ_self) (n : ℕ) :
    1 / 2 ≤ crossingProb half n n :=
  (hself n).symm.le.trans (crossingProb_anti_left half (Nat.le_succ n) n)

/-- Bollobás–Riordan 2006, Ch. 3, "`h(kn, 2n) ≥ 2^{17-8k}` for all `k ≥ 3`": iterating the gluing
inequality from `h(3n, 2n) ≥ 2⁻⁷`. In `crossingProb` indices with `n = j + 1`, `k = t + 3`:
`crossingProb ½ (3j + 2 + t (j + 1)) (2j + 1) ≥ 2^{-(7 + 8t)}`. [cite: BollobasRiordanPercolation2006, Ch. 3, after eq. (2)] -/
theorem crossingProb_long_le (hcor5 : BollobasRiordan2006_cor5) (hglue : crossingProb_glue)
    (hself : crossingProb_half_succ_self) (j t : ℕ) :
    (2 : ℝ)⁻¹ ^ (7 + 8 * t) ≤ crossingProb half (3 * j + 2 + t * (j + 1)) (2 * j + 1) := by
  induction t with
  | zero => simpa using hcor5 j
  | succ t ih =>
    have hw : 3 * j + 2 + (t + 1) * (j + 1) =
        (3 * j + 2 + t * (j + 1)) + (3 * j + 2) - (2 * j + 1) := by
      have : (t + 1) * (j + 1) = t * (j + 1) + (j + 1) := by ring
      omega
    have hg := hglue half (3 * j + 2 + t * (j + 1)) (3 * j + 2) (2 * j + 1) (by omega) (by omega)
    rw [← hw] at hg
    refine le_trans ?_ hg
    have hB := hcor5 j
    have hC := half_le_crossingProb_self hself (2 * j + 1)
    have h0 : ∀ a b : ℕ, (0 : ℝ) ≤ crossingProb half a b := fun a b => (crossingProb_mem_Icc _ _ _).1
    calc (2 : ℝ)⁻¹ ^ (7 + 8 * (t + 1)) = 2⁻¹ ^ (7 + 8 * t) * 2⁻¹ ^ 7 * (1 / 2) := by ring
      _ ≤ crossingProb half (3 * j + 2 + t * (j + 1)) (2 * j + 1) *
            crossingProb half (3 * j + 2) (2 * j + 1) *
            crossingProb half (2 * j + 1) (2 * j + 1) :=
        mul_le_mul (mul_le_mul ih hB (by positivity) (h0 _ _)) hC (by norm_num)
          (mul_nonneg (h0 _ _) (h0 _ _))

/-- **Bollobás–Riordan 2006, Ch. 3, eq. (3)** from Corollary 5, the gluing inequality (2),
Corollary 3(ii) and monotonicity, with the explicit constant `h_k = 2^{-24k}`: even heights
`n = 2(j+1)` use `h(2k(j+1), 2(j+1)) ≥ 2^{17-16k}`; odd heights `n = 2j + 3` use
`h(kn, n) ≥ h(3k(j+1), 2(j+1)) ≥ 2^{17-24k}`; height `1` uses `h(k, 1) = 2^{1-k}`. [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (3)] -/
theorem rsw_lowerBound_of_glue (hcor5 : BollobasRiordan2006_cor5) (hglue : crossingProb_glue)
    (hself : crossingProb_half_succ_self) : rsw_lowerBound := by
  intro k hk
  refine ⟨2⁻¹ ^ (24 * k), by positivity, fun n hn => ?_⟩
  have hhalf : ((half : unitInterval) : ℝ) = 2⁻¹ := by simp
  have hpow : ∀ {a b : ℕ}, b ≤ a → ((2 : ℝ)⁻¹ ^ a ≤ 2⁻¹ ^ b) := fun h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- height index `n = 2j`, i.e. `2j + 1` rows: B–R height `2j + 1` (odd), or `j = 0`.
    rcases j with _ | j
    · -- one row: `h(k, 1) = 2^{1-k}`
      calc (2 : ℝ)⁻¹ ^ (24 * k) ≤ 2⁻¹ ^ (k * (0 + 0 + 1) - 1) := hpow (by omega)
        _ ≤ _ := by rw [← hhalf]; exact pow_le_crossingProb half _ _
    · -- `2(j+1) + 1 = 2j + 3` rows: compare with `3k(j+1)` by `2(j+1)`.
      have hle : k * (j + 1 + (j + 1) + 1) - 1 ≤ 3 * j + 2 + (3 * k - 3) * (j + 1) := by
        have h3 : (3 * k - 3) * (j + 1) = 3 * k * (j + 1) - 3 * (j + 1) := by
          rw [Nat.sub_mul]
        have : k * (j + 1 + (j + 1) + 1) ≤ 3 * k * (j + 1) := by nlinarith
        omega
      calc (2 : ℝ)⁻¹ ^ (24 * k) ≤ 2⁻¹ ^ (7 + 8 * (3 * k - 3)) := hpow (by omega)
        _ ≤ crossingProb half (3 * j + 2 + (3 * k - 3) * (j + 1)) (2 * j + 1) :=
          crossingProb_long_le hcor5 hglue hself j (3 * k - 3)
        _ ≤ crossingProb half (k * (j + 1 + (j + 1) + 1) - 1) (2 * j + 1) :=
          crossingProb_anti_left half hle _
        _ ≤ crossingProb half (k * (j + 1 + (j + 1) + 1) - 1) (j + 1 + (j + 1)) :=
          crossingProb_mono_right half _ (by omega)
  · -- height index `n = 2j + 1`, i.e. `2(j+1)` rows: `h(2k(j+1), 2(j+1)) ≥ 2^{17-16k}`.
    have heq : k * (2 * j + 1 + 1) - 1 = 3 * j + 2 + (2 * k - 3) * (j + 1) := by
      have h3 : (2 * k - 3) * (j + 1) = 2 * k * (j + 1) - 3 * (j + 1) := by rw [Nat.sub_mul]
      have : k * (2 * j + 1 + 1) = 2 * k * (j + 1) := by ring
      have : 3 * (j + 1) ≤ 2 * k * (j + 1) := by nlinarith
      omega
    calc (2 : ℝ)⁻¹ ^ (24 * k) ≤ 2⁻¹ ^ (7 + 8 * (2 * k - 3)) := hpow (by omega)
      _ ≤ crossingProb half (3 * j + 2 + (2 * k - 3) * (j + 1)) (2 * j + 1) :=
        crossingProb_long_le hcor5 hglue hself j (2 * k - 3)
      _ = crossingProb half (k * (2 * j + 1 + 1) - 1) (2 * j + 1) := by rw [heq]

/-! ### Conclusion: `rsw_half` from the RSW lower bound and duality -/

/-- **Conclusion of `rsw_half`** (Bollobás–Riordan 2006, Ch. 3, eq. (3) with Corollary 3(i);
Grimmett 1999, §11.7). Given the RSW lower bound `h(kn, n) ≥ h_k` (`rsw_lowerBound`) and the
duality `h_{1/2}(k, ℓ - 1) + h_{1/2}(ℓ, k - 1) = 1` (`crossingProb_add_crossingProb_symm`), the
crossing probability of `[0, ⌊ρ n⌋] × [0, n]` at `p = 1/2` lies in `[c, 1 - c]` for some
`c = c(ρ) > 0` and all `n` with `⌊ρ n⌋ ≥ 1`: the lower bound by monotonicity in the width with
`k = ⌈ρ⌉ + 2`, the upper bound by duality and the lower bound for the transposed dual rectangle
with `k = ⌈2/ρ⌉ + 2`. [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (3) and Corollary 3(i)] [cite: GrimmettPercolation1999, §11.7] -/
theorem rsw_half_of_lowerBound (hlow : rsw_lowerBound)
    (hdual : crossingProb_add_crossingProb_symm) : rsw_half := by
  intro ρ hρ
  set K₁ := ⌈ρ⌉₊ with hK₁
  set K₂ := ⌈2 / ρ⌉₊ with hK₂
  obtain ⟨c₁, hc₁, h₁⟩ := hlow (K₁ + 2) (by omega)
  obtain ⟨c₂, hc₂, h₂⟩ := hlow (K₂ + 2) (by omega)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun n hm => ?_⟩
  set m := ⌊ρ * n⌋₊ with hm_def
  have hρn : 0 ≤ ρ * n := by positivity
  have hm_le : (m : ℝ) ≤ ρ * n := Nat.floor_le hρn
  have hm_lt : ρ * n < m + 1 := Nat.lt_floor_add_one _
  -- lower bound
  have hlowm : c₁ ≤ crossingProb half m n := by
    have hb := h₁ (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hb
    refine hb.trans (crossingProb_anti_left half ?_ n)
    have hmK : m ≤ K₁ * n := by
      have : (m : ℝ) ≤ K₁ * n := hm_le.trans (by
        gcongr
        exact Nat.le_ceil ρ)
      exact_mod_cast this
    have : (K₁ + 2) * (n + 1) = K₁ * n + (K₁ + 2 * n + 2) := by ring
    omega
  -- upper bound via duality
  have hupm : c₂ ≤ crossingProb half (n + 1) (m - 1) := by
    have hb := h₂ m hm
    refine hb.trans (crossingProb_anti_left half ?_ (m - 1))
    have hnK : n < K₂ * m := by
      have h1 : (n : ℝ) < (m + 1) / ρ := by
        rw [lt_div_iff₀ hρ]; linarith
      have h2 : ((m : ℝ) + 1) / ρ ≤ K₂ * m := by
        calc ((m : ℝ) + 1) / ρ ≤ (2 * m) / ρ := by
              gcongr
              have : (1 : ℝ) ≤ m := by exact_mod_cast hm
              linarith
          _ = (2 / ρ) * m := by ring
          _ ≤ K₂ * m := by
              gcongr
              exact Nat.le_ceil _
      exact_mod_cast h1.trans_le h2
    have : (K₂ + 2) * m = K₂ * m + 2 * m := by ring
    omega
  have hdual' : crossingProb half m n = 1 - crossingProb half (n + 1) (m - 1) := by
    have h := hdual half (m - 1) n
    rw [symm_half, Nat.sub_add_cancel hm] at h
    linarith
  constructor
  · exact (min_le_left _ _).trans hlowm
  · rw [hdual']
    have := min_le_right c₁ c₂
    linarith

end

end Percolation.Literature
