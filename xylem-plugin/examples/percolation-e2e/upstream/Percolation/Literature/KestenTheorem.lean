import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Percolation.Literature.BernoulliPercolation
import Percolation.Literature.Connectivity
import Percolation.Literature.Crossings
import Percolation.Literature.LatticeSymmetry
import Percolation.Literature.PercolationProofs
import Percolation.Literature.RSW
import Percolation.Literature.SiteConnectionTools
import Percolation.Util.Linter

/-!
# Kesten's theorem `p_c(ℤ², bond) = 1/2`: the proof DAG of `kesten_criticalProb_Z2`

This file decomposes the statement
`Percolation.Literature.kesten_criticalProb_Z2 : criticalProb (zdGraph 2) 0 = 1 / 2`
(`BernoulliPercolation.lean`; Kesten, *Comm. Math. Phys.* **74** (1980) 41–59, Thm. 1) into the
named intermediate results of the printed proofs, and proves the reduction steps, so that the
proof `kesten_criticalProb_Z2_holds` can be assembled bottom-up.

## The printed proofs

* Kesten 1980, §1–2. `p_H = sup {p | θ(p) = 0}` ((1.2)); Harris' bound `p_H ≥ 1/2` ((1.4));
  Thm. 1: `p_H = 1/2`; Thm. 2, (1.5): `p > 1/2 ⟹ θ(p) > 0`, (1.6): `p ≤ 1/2 ⟹ θ(p) = 0`.
  Kesten's own approach to `p_H ≤ 1/2` goes through the Seymour–Welsh/Russo identities
  `p_T + p_H = 1`, `p_T = p_S` ((2.9)–(2.10)) and the sponge-crossing estimate (2.11).
* Bollobás–Riordan, *Percolation* (2006), Ch. 3 (the conventions of `RSW.lean`): Thm. 6
  (Harris: `θ(1/2) = 0`), Lemma 8 (sharp threshold: for `p > 1/2` and integer `ρ > 1`,
  `h_p(ρ n, n) ≥ 1 - n^{-γ}` for `n ≥ n₀(p, ρ)`, via Friedgut–Kalai and the Margulis–Russo
  formula), Lemma 9 (its qualitative form `h_p(3n, n) → 1`), Thm. 10 (`p > 1/2 ⟹ P_p(E_∞) = 1`,
  from Lemma 8 by crossing the rectangles `2^k n × 2^{k+1} n` the long way and a union bound),
  and "Together, Theorems 6 and 10 show that `p_H(ℤ²) = 1/2`" (Ch. 3, after Thm. 10).

We follow the Bollobás–Riordan architecture (the RSW layer is in `RSW.lean`
and the zero–one law `Percolation.Literature.Grimmett1999_prob_exists_percolatesAt` in `Connectivity.lean`).

## Contents

* Statements (theorems in print, recorded as `def … : Prop`):
  `Kesten1980_theta_pos` (Kesten 1980, Thm. 2 (1.5): `θ(p) > 0` for `p > 1/2`),
  `BollobasRiordan2006_ch3_lemma8` (sharp-threshold lower bound for long crossings),
  `BollobasRiordan2006_ch3_lemma9` (`h_p(3n, n) → 1` for `p > 1/2`),
  `BollobasRiordan2006_ch3_thm10` (`P_p(∃` infinite open cluster`) = 1` for `p > 1/2`).

## Dependency DAG of `kesten_criticalProb_Z2_holds`

`kesten_criticalProb_Z2` ⇐ (`harris_theta_half`, `theta_mono`, `Kesten1980_theta_pos`);
`theta_mono` ⇐ `map_configOfLabels` + measurability of `percolatesAt` (`Literature/Basic.lean`);
`Kesten1980_theta_pos` ⇐ `BollobasRiordan2006_ch3_thm10` + `Grimmett1999_prob_exists_percolatesAt`;
`BollobasRiordan2006_ch3_thm10` ⇐ `BollobasRiordan2006_ch3_lemma8` + "a long-way crossing of
`R_k` meets a long-way crossing of `R_{k+1}`" (discrete planar topology) + rotation invariance
of `P_p` + union bound; `BollobasRiordan2006_ch3_lemma8` ⇐ `rsw_lowerBound` (`RSW.lean`) +
Friedgut–Kalai (B–R Ch. 2, Thm. 12) + Margulis–Russo (`russo_formula_sum`) + B–R Ch. 3, Lemma 7
with `harris_theta_half`; `harris_theta_half` ⇐ `rsw_half` + `harris_fkg` + duality
(`Crossings.lean`).

Conventions: `crossingProb p m n = P_p(LR([0, m] × [0, n])) = h_p(m + 1, n + 1)` (`RSW.lean`),
so B–R's `h_p(ρ n, n)` is `crossingProb p (ρ n - 1) (n - 1)` for `n ≥ 1`.

## Second approach to `p_c ≤ 1/2`: sharpness and self-duality (Grimmett 1999, Thm. (11.11))

Grimmett, *Percolation*, 2nd ed. (1999), §11.3, Thm. (11.11) "second proof" (p. 294) derives
Kesten's upper bound from two inputs that this library records as statements of their own:
the sharpness of the phase transition (`Percolation.Literature.perc_sharpness`: Menshikov 1986 /
Aizenman–Barsky 1987 = Grimmett Thms. (5.4), (6.1); Duminil-Copin–Tassion 2016, Thm. 1.1(1))
and the self-duality lemma (11.21) (`Percolation.Literature.crossingProb_half_succ_self`:
`P_{1/2}(LR([0, n + 1] × [0, n])) = 1/2`). Verbatim: "Suppose now that `p_c > 1/2`. It follows
that the value `p = 1/2` belongs to the subcritical phase ... there exists `α > 0` such that
`P_{1/2}(0 ↔ ∂B(n)) ≤ e^{-α n}` for all `n` ... In this case
`P_{1/2}(A_n) ≤ Σ_{k=0}^{n} P_{1/2}((0, k) ↔ L_n) ≤ (n + 1) e^{-α n} → 0` as `n → ∞`, in
contradiction of the fact that `P_{1/2}(A_n) = 1/2` for all `n`. It follows that `p_c ≤ 1/2`."
The section `SharpnessReduction` below proves this reduction in full:
`exists_mem_innerBoundary_openConnIn` (first exit of an open path from a finite set),
`exists_leftSide_shiftedOneArm` (`A_n ⊆ ⋃_{k ≤ n} {(0, k) ↔ ∂((0, k) + B(n))}`),
`crossingProb_succ_le` (the union bound, with translation invariance from
`real_openCrossing_shift` of `LatticeSymmetry.lean`), `criticalProb_Z2_le_half_of_sharpness`,
and the assemblies `Kesten1980_theta_pos_of_sharpness` and `kesten_criticalProb_Z2_of_sharpness`
(`harris_theta_half → perc_sharpness → crossingProb_half_succ_self → kesten_criticalProb_Z2`;
the monotonicity of `θ` is the proved `theta_mono_holds` of `PercolationProofs.lean`).
Inputs of this approach: `harris_theta_half` (Harris 1960; Grimmett Thm. (11.12)) and
`perc_sharpness` (Grimmett Thms. (5.4) + (6.1); the DAG of `SharpnessDCT.lean`);
`crossingProb_half_succ_self` is proved in `RSWProofs.lean`
(`crossingProb_half_succ_self_holds`, from the planar duality lemma of `PlanarDuality.lean`).
-/

namespace Percolation.Literature

open MeasureTheory Filter Topology LatticeModels

noncomputable section

/-! ### Named intermediate results -/

/-- **Kesten 1980, Theorem 2, (1.5)** (Kesten, *Comm. Math. Phys.* 74 (1980) 41, Thm. 2:
"`p > 1/2` implies `θ(p) > 0`"; Bollobás–Riordan, *Percolation* (2006), Ch. 3, Thm. 10 with
"`P_p(E_∞) > 0` implies `θ(p) > 0`"). For bond percolation on the square lattice `ℤ²`, the
percolation probability at the origin is positive for every `p > 1/2`. [cite: KestenCMP1980, Thm. 2 (1.5)] [cite: BollobasRiordanPercolation2006, Ch. 3, Thm. 10] -/
def Kesten1980_theta_pos : Prop :=
  ∀ (p : unitInterval), 1 / 2 < (p : ℝ) → 0 < theta (zdGraph 2) (0 : Site 2) p

/-- **Bollobás–Riordan 2006, Ch. 3, Lemma 8** (sharp-threshold lower bound for long crossings;
proof via the Friedgut–Kalai influence bound, Ch. 2 Thm. 12, the Margulis–Russo formula, Ch. 2
Lemma 9, the RSW bound (3) and Lemma 7). "Let `p > 1/2` and an integer `ρ > 1` be fixed. There
are constants `γ = γ(p) > 0` and `n₀ = n₀(p, ρ)` such that `h_p(ρ n, n) ≥ 1 - n^{-γ}` for all
`n ≥ n₀`." Here `h_p(ρ n, n) = crossingProb p (ρ n - 1) (n - 1)` (a `ρ n` by `n` rectangle has
`ρ n × n` sites); we take `n₀ ≥ 1`. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 8] -/
def BollobasRiordan2006_ch3_lemma8 : Prop :=
  ∀ (p : unitInterval), 1 / 2 < (p : ℝ) → ∃ γ : ℝ, 0 < γ ∧ ∀ ρ : ℕ, 1 < ρ →
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      1 - (n : ℝ) ^ (-γ) ≤ crossingProb p (ρ * n - 1) (n - 1)

/-- **Bollobás–Riordan 2006, Ch. 3, Lemma 9** (qualitative sharp threshold). "Let `p > 1/2` be
fixed. If `R_n` is a `3n` by `n` rectangle in `ℤ²`, then `P_p(H(R_n)) → 1` as `n → ∞`." In
`crossingProb` indices `P_p(H(R_n)) = crossingProb p (3n - 1) (n - 1)`. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 9] -/
def BollobasRiordan2006_ch3_lemma9 : Prop :=
  ∀ (p : unitInterval), 1 / 2 < (p : ℝ) →
    Tendsto (fun n : ℕ => crossingProb p (3 * n - 1) (n - 1)) atTop (𝓝 1)

/-- **Bollobás–Riordan 2006, Ch. 3, Theorem 10** ("For bond percolation in `ℤ²`, if `p > 1/2`
then `P_p(E_∞) = 1`", `E_∞` = there is an infinite open cluster; proof from Lemma 8: the
rectangles `R_k` of sides `2^k n`, `2^{k+1} n`, longer side vertical for even `k`, are all
crossed the long way with probability `≥ 1 - Σ_k (2^k n)^{-γ} > 0`, two consecutive long-way
crossings meet, and `P_p(E_∞) > 0 ⟹ P_p(E_∞) = 1` by the zero–one law). Kesten 1980 obtains
the same conclusion from Thm. 2 (1.5). [cite: BollobasRiordanPercolation2006, Ch. 3, Thm. 10] [cite: KestenCMP1980, Thm. 2 (1.5)] -/
def BollobasRiordan2006_ch3_thm10 : Prop :=
  ∀ (p : unitInterval), 1 / 2 < (p : ℝ) →
    (bondPercolation (zdGraph 2) p).real {ω | ∃ x : Site 2, ω ∈ percolatesAt x} = 1

/-! ### Reductions -/

/-- Lemma 9 from Lemma 8 (Bollobás–Riordan 2006, Ch. 3: "the following much weaker form of
Lemma 8"): with `ρ = 3`, `1 - n^{-γ} ≤ h_p(3n, n) ≤ 1` and `n^{-γ} → 0`. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 9] -/
theorem BollobasRiordan2006_ch3_lemma9_of_lemma8 (h8 : BollobasRiordan2006_ch3_lemma8) :
    BollobasRiordan2006_ch3_lemma9 := by
  intro p hp
  obtain ⟨γ, hγ, hρ⟩ := h8 p hp
  obtain ⟨n₀, hn₀, hn⟩ := hρ 3 (by norm_num)
  have hlow : Tendsto (fun n : ℕ => 1 - (n : ℝ) ^ (-γ)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-γ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => measureReal_le_one)
  filter_upwards [eventually_ge_atTop n₀] with n hn' using hn n hn'

/-- **Harris' lower bound `p_c(ℤ²) ≥ 1/2`** (Harris, *Proc. Camb. Phil. Soc.* 56 (1960) 13;
Kesten 1980, (1.4); Bollobás–Riordan 2006, Ch. 3, Thm. 6 and the definition of `p_H`): from
`θ(1/2) = 0` (`harris_theta_half`) and the monotonicity of `θ` (`Percolation.Literature.theta_mono`),
`θ(p) = 0` for all `p ≤ 1/2`, so every `p` with `θ(p) > 0` satisfies `p ≥ 1/2` and
`p_c = inf ({p | θ(p) > 0} ∪ {1}) ≥ 1/2`. [cite: HarrisPCPS1960, main theorem] [cite: KestenCMP1980, (1.4)] -/
theorem half_le_criticalProb_Z2 (hH : harris_theta_half) (hm : theta_mono (V := Site 2)) :
    (1 / 2 : ℝ) ≤ criticalProb (zdGraph 2) 0 := by
  refine le_csInf ⟨1, Or.inr rfl⟩ ?_
  rintro q (⟨hq01, hθ⟩ | hq1)
  · by_contra hlt
    rw [not_le] at hlt
    have hle : (⟨q, hq01⟩ : unitInterval) ≤ half := by
      change q ≤ (1 / 2 : ℝ)
      exact hlt.le
    have := hm (zdGraph 2) (0 : Site 2) hle
    have hH' : theta (zdGraph 2) (0 : Site 2) half = 0 := hH
    rw [hH'] at this
    exact absurd this (not_le.2 hθ)
  · rw [Set.mem_singleton_iff] at hq1
    rw [hq1]; norm_num

/-! ### Second approach: `p_c ≤ 1/2` from sharpness and self-duality
(Grimmett 1999, Thm. (11.11), second proof, p. 294) -/

section SharpnessReduction

/-! #### First exit of an open path from a finite set -/

section FirstExit

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

/-- **First-exit lemma, open-bond form** (an instance of
`Percolation.Literature.exists_innerBoundary_reachable_of_walk` for the subgraph `openGraph ω ≤ G`):
for a lattice configuration `ω ⊆ E(G)`, if a vertex `x ∈ Λ` is joined by an open path to a
vertex `y ∉ Λ`, then `x` is joined by an open path *inside* `Λ` to a vertex of the inner vertex
boundary `∂ⁱⁿΛ`. (Grimmett 1999, Thm. (11.11), second proof, p. 294, in the form
"`(0, k) ↔ L_n` implies `(0, k) ↔ ∂B(n, (0, k))`".) [folklore] -/
theorem exists_mem_innerBoundary_openConnIn {ω : BondConfig V} (hω : ω ⊆ G.edgeSet)
    (Λ : Finset V) {x y : V} (hx : x ∈ Λ) (hy : y ∉ Λ) (h : (openGraph ω).Reachable x y) :
    ∃ z ∈ innerBoundary G Λ, ω ∈ openConnIn (↑Λ : Set V) x z := by
  have hle : openGraph ω ≤ G := fun a b hab => hω ((openGraph_adj _ _ _).1 hab).1
  obtain ⟨w⟩ := h
  obtain ⟨z, hz, hxΛ, hzΛ, hr⟩ := exists_innerBoundary_reachable_of_walk hle Λ w hx hy
  exact ⟨z, hz, hxΛ, hzΛ, hr⟩

end FirstExit

/-! #### The one-arm event and its translates as open crossing events -/

/-- The one-arm event `{0 ↔ ∂B(n)}` (`siteToBoundary`) is the open crossing event inside `B(n)`
from `{0}` to the inner vertex boundary of `B(n)`. [folklore] -/
theorem siteToBoundary_eq_openCrossing (d n : ℕ) :
    siteToBoundary d n =
      openCrossing (↑(box d n) : Set (Site d)) {0} ↑(innerBoundary (zdGraph d) (box d n)) := by
  ext ω
  simp [siteToBoundary, openCrossing]

/-- The inner vertex boundary of subsets of `ℤ^d` is translation covariant:
`∂ⁱⁿ(Λ + v) = ∂ⁱⁿΛ + v`. [folklore] -/
theorem innerBoundary_image_add_right {d : ℕ} (v : Site d) (Λ : Finset (Site d)) :
    innerBoundary (zdGraph d) (Λ.image (· + v)) = (innerBoundary (zdGraph d) Λ).image (· + v) := by
  ext x
  simp only [mem_innerBoundary_iff, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, y, hy, hadj⟩
    refine ⟨x, ⟨hx, y - v, fun hyv => hy ⟨y - v, hyv, sub_add_cancel y v⟩, ?_⟩, rfl⟩
    rw [← zdGraph_adj_shift_iff v, Site.shift_apply, Site.shift_apply, sub_add_cancel]
    exact hadj
  · rintro ⟨x, ⟨hx, y, hy, hadj⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, y + v, ?_, (zdGraph_adj_shift_iff v x y).2 hadj⟩
    rintro ⟨y', hy', hyy'⟩
    obtain rfl : y' = y := add_right_cancel hyy'
    exact hy hy'

/-- The translated one-arm event `{v ↔ ∂(v + B(n)) in v + B(n)}`: an open path inside the box
`B(n) + v` from its centre `v` to its inner vertex boundary, written as the translate by `v` of
the open crossing event `siteToBoundary d n` (so that `real_openCrossing_shift` applies
verbatim, `real_shiftedOneArm`). These are the events `{(0, k) ↔ ∂B(n, (0, k))}` bounding
`{(0, k) ↔ L_n}` in Grimmett 1999, Thm. (11.11), second proof, p. 294. [folklore] -/
def shiftedOneArm (d n : ℕ) (v : Site d) : Set (BondConfig (Site d)) :=
  openCrossing ((· + v) '' (↑(box d n) : Set (Site d))) ((· + v) '' {0})
    ((· + v) '' ↑(innerBoundary (zdGraph d) (box d n)))

/-- **Translation invariance of the one-arm probability**: `P_p(v ↔ ∂(v + B(n))) = P_p(0 ↔ ∂B(n))`
(Grimmett 1999, §1.6, p. 16, `P_p` "is invariant under translations of the lattice";
`real_openCrossing_shift`). [cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem real_shiftedOneArm (p : unitInterval) (d n : ℕ) (v : Site d) :
    (bondPercolation (zdGraph d) p).real (shiftedOneArm d n v) =
      (bondPercolation (zdGraph d) p).real (siteToBoundary d n) := by
  rw [shiftedOneArm, siteToBoundary_eq_openCrossing]
  exact real_openCrossing_shift p v _ _ _

/-- **`A_n ⊆ ⋃_k {(0, k) ↔ ∂B(n, (0, k))}`** (Grimmett 1999, Thm. (11.11), second proof, p. 294:
"`P_{1/2}(A_n) ≤ Σ_{k=0}^{n} P_{1/2}((0, k) ↔ L_n)`" together with
"`(0, k) ↔ L_n` implies `(0, k) ↔ ∂B(n, (0, k))`"). A left-right open crossing of
`[0, n + 1] × [0, m]` by a lattice configuration starts at some vertex `x` of the left side and
reaches the right side `{x₀ = n + 1}`, which lies outside the box `x + B(n)`; stopped at its
first exit from that box (`exists_mem_innerBoundary_openConnIn`) it is an open path inside
`x + B(n)` from `x` to `∂(x + B(n))`. [cite: GrimmettPercolation1999, Thm. 11.11 (second proof, p. 294)] -/
theorem exists_leftSide_shiftedOneArm {n m : ℕ} {ω : BondConfig (Site 2)}
    (hω : ω ⊆ (zdGraph 2).edgeSet) (h : ω ∈ lrCrossing (n + 1) m) :
    ∃ x ∈ leftSide (n + 1) m, ω ∈ shiftedOneArm 2 n x := by
  obtain ⟨x, hx, y, hy, hxS, hyS, hr⟩ := h
  simp only [Finset.mem_coe] at hx hy
  have hx0 : x 0 = 0 := (Finset.mem_filter.1 hx).2
  have hy0 : y 0 = n + 1 := (Finset.mem_filter.1 hy).2
  have hr' : (openGraph ω).Reachable x y := hr.map (SimpleGraph.Embedding.induce _).toHom
  have hxΛ : x ∈ (box 2 n).image (· + x) := Finset.mem_image.2 ⟨0, zero_mem_box 2 n, zero_add x⟩
  have hyΛ : y ∉ (box 2 n).image (· + x) := by
    simp only [Finset.mem_image, mem_box, not_exists, not_and]
    intro z hz hzx
    have h0 := (hz 0).2
    have : z 0 + x 0 = y 0 := by rw [← hzx]; rfl
    omega
  obtain ⟨z, hz, hconn⟩ := exists_mem_innerBoundary_openConnIn hω _ hxΛ hyΛ hr'
  rw [innerBoundary_image_add_right] at hz
  refine ⟨x, hx, x, ⟨0, rfl, zero_add x⟩, z, ?_, ?_⟩
  · simpa only [Finset.coe_image] using (Finset.mem_coe.2 hz)
  · simpa only [Finset.coe_image] using hconn

/-- The left side of `[0, m'] × [0, m]` consists of the `m + 1` points `(0, k)`, `0 ≤ k ≤ m`. [folklore] -/
theorem leftSide_subset_image (m' m : ℕ) :
    leftSide m' m ⊆ (Finset.range (m + 1)).image fun k : ℕ => (![0, (k : ℤ)] : Site 2) := by
  intro x hx
  simp only [leftSide, Finset.mem_filter, mem_rectangle_iff] at hx
  obtain ⟨⟨-, -, h1, h2⟩, h0⟩ := hx
  refine Finset.mem_image.2 ⟨(x 1).toNat, Finset.mem_range.2 (by omega), ?_⟩
  ext i; fin_cases i
  · simp [h0]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Int.toNat_of_nonneg h1

/-- `|leftSide m' m| ≤ m + 1`. [folklore] -/
theorem card_leftSide_le (m' m : ℕ) : (leftSide m' m).card ≤ m + 1 :=
  (Finset.card_le_card (leftSide_subset_image m' m)).trans
    (Finset.card_image_le.trans (Finset.card_range _).le)

/-- **Union bound** (Grimmett 1999, Thm. (11.11), second proof, p. 294:
"`P(A_n) ≤ Σ_{k=0}^{n} P((0, k) ↔ L_n) ≤ (n + 1) P(0 ↔ ∂B(n))`", by translation invariance):
`P_p(LR([0, n + 1] × [0, m])) ≤ (m + 1) P_p(0 ↔ ∂B(n))`. [cite: GrimmettPercolation1999, Thm. 11.11 (second proof, p. 294)] -/
theorem crossingProb_succ_le (p : unitInterval) (n m : ℕ) :
    crossingProb p (n + 1) m ≤
      (m + 1) * (bondPercolation (zdGraph 2) p).real (siteToBoundary 2 n) := by
  set μ := bondPercolation (zdGraph 2) p
  calc crossingProb p (n + 1) m
      ≤ μ.real (⋃ x ∈ leftSide (n + 1) m, shiftedOneArm 2 n x) := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
        filter_upwards [ae_subset_edgeSet (zdGraph 2) p] with ω hω hc
        obtain ⟨x, hx, hωx⟩ := exists_leftSide_shiftedOneArm hω hc
        exact Set.mem_biUnion (Finset.mem_coe.2 hx) hωx
    _ ≤ ∑ x ∈ leftSide (n + 1) m, μ.real (shiftedOneArm 2 n x) :=
        measureReal_biUnion_finset_le _ _
    _ = (leftSide (n + 1) m).card * μ.real (siteToBoundary 2 n) := by
        rw [Finset.sum_congr rfl fun x _ => real_shiftedOneArm p 2 n x, Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ (m + 1) * μ.real (siteToBoundary 2 n) := by
        gcongr
        exact_mod_cast card_leftSide_le (n + 1) m

/-- **Kesten's upper bound `p_c(ℤ²) ≤ 1/2` from sharpness and self-duality** (Grimmett 1999,
Thm. (11.11), second proof, p. 294, quoted in the module docstring): if `p_c > 1/2` then
`p = 1/2` is subcritical, so by sharpness (`perc_sharpness`, Grimmett Thms. (5.4)/(6.1))
`P_{1/2}(0 ↔ ∂B(n)) ≤ e^{-c n}`, whence by `crossingProb_succ_le`
`1/2 = P_{1/2}(A_n) ≤ (n + 1) e^{-c n} → 0` (`crossingProb_half_succ_self`, Lemma (11.21)),
a contradiction. [cite: GrimmettPercolation1999, Thm. 11.11 (second proof, p. 294)] -/
theorem criticalProb_Z2_le_half_of_sharpness (hS : perc_sharpness)
    (hself : crossingProb_half_succ_self) :
    criticalProb (zdGraph 2) 0 ≤ (1 / 2 : ℝ) := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc, hdecay⟩ := hS (d := 2) le_rfl half (by simpa using hlt)
  have hle : ∀ n : ℕ, (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) * Real.exp (-c * n) := fun n =>
    calc (1 / 2 : ℝ) = crossingProb half (n + 1) n := (hself n).symm
      _ ≤ (n + 1) * (bondPercolation (zdGraph 2) half).real (siteToBoundary 2 n) :=
          crossingProb_succ_le half n n
      _ ≤ (n + 1) * Real.exp (-c * n) := by gcongr; exact hdecay n
  -- `(n + 1) e^{-c n} → 0` ("`(n + 1) e^{-α n} → 0` as `n → ∞`", Grimmett p. 294)
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-c * n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hcn : Tendsto (fun n : ℕ => c * n) atTop atTop :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop hc
    have h2 : Tendsto (fun n : ℕ => (c * n) * Real.exp (-(c * n))) atTop (𝓝 0) := h1.comp hcn
    have h3 : Tendsto (fun n : ℕ => Real.exp (-(c * n))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hcn
    have h4 : Tendsto (fun n : ℕ => c⁻¹ * ((c * n) * Real.exp (-(c * n))) + Real.exp (-(c * n)))
        atTop (𝓝 0) := by
      simpa using (h2.const_mul c⁻¹).add h3
    refine h4.congr fun n => ?_
    have : -c * (n : ℝ) = -(c * n) := by ring
    rw [this]
    field_simp
  have hev : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) * Real.exp (-c * n) < 1 / 2 :=
    hlim.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n, hn⟩ := hev.exists
  exact absurd (hle n) (not_le.2 hn)

/-- **Kesten 1980, Thm. 2 (1.5), from sharpness and self-duality**: `θ(p) > 0` for every
`p > 1/2`, since `p > 1/2 ≥ p_c` (`criticalProb_Z2_le_half_of_sharpness`) and `θ > 0` above
`p_c` (Grimmett 1999, (1.11); the statement `theta_pos_of_criticalProb_lt`, proved as
`theta_pos_of_criticalProb_lt_holds` in `BernoulliPercolationProofs.lean`, downstream of this
file). (Grimmett 1999, Thm. (11.11) with (1.11); Kesten 1980, Thm. 2 (1.5).) [cite: GrimmettPercolation1999, Thm. 11.11] [cite: KestenCMP1980, Thm. 2 (1.5)] -/
theorem Kesten1980_theta_pos_of_sharpness (hS : perc_sharpness)
    (hself : crossingProb_half_succ_self) (hθ : theta_pos_of_criticalProb_lt (V := Site 2)) :
    Kesten1980_theta_pos := fun p hp =>
  hθ (zdGraph 2) 0 p ((criticalProb_Z2_le_half_of_sharpness hS hself).trans_lt hp)

/-- **Conclusion of Kesten's theorem along Grimmett's second proof** (Grimmett 1999,
Thm. (11.11): "`p_c = 1/2`", second proof, p. 294, together with Harris' bound
`p_c ≥ 1/2`, Thm. (11.12)/Lemma (11.12) via `θ(1/2) = 0`): given Harris' theorem
`θ(1/2) = 0`, the sharpness of the phase transition on `ℤ²` and the self-duality lemma (11.21),
the statement `kesten_criticalProb_Z2 : criticalProb (zdGraph 2) 0 = 1/2` holds; the
monotonicity of `θ` is the proved `theta_mono_holds` (`PercolationProofs.lean`). [cite: GrimmettPercolation1999, Thm. 11.11 (second proof)] [cite: KestenCMP1980, Thm. 1] -/
theorem kesten_criticalProb_Z2_of_sharpness (hH : harris_theta_half) (hS : perc_sharpness)
    (hself : crossingProb_half_succ_self) : kesten_criticalProb_Z2 :=
  le_antisymm (criticalProb_Z2_le_half_of_sharpness hS hself)
    (half_le_criticalProb_Z2 hH theta_mono_holds)

end SharpnessReduction

end

end Percolation.Literature
