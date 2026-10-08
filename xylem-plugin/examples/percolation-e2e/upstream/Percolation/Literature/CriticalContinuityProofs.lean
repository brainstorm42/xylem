import Mathlib.Analysis.SpecificLimits.Basic
import Percolation.Literature.BernoulliPercolation
import Percolation.Literature.CriticalContinuity
import Percolation.Literature.DualContours
import Percolation.Literature.SubgraphMonotonicity
import Percolation.Util.Linter

/-!
# Proof of `0 < p_c(ℤ^d) < 1` for `d ≥ 2` (Grimmett 1999, Theorem (1.10))

* `Grimmett1999_criticalProb_pos_lt_one_holds : Grimmett1999_criticalProb_pos_lt_one`.

Source: G. Grimmett, *Percolation*, 2nd ed. (1999), §1.4, Theorem (1.10) p. 14 ("If `d ≥ 2` then
`0 < p_c(d) < 1`"), proof pp. 15–18. We follow the printed proof with two simplifications; the
file introduces no vocabulary (it consists of theorems only; the step words `wordPos` and the
dual walks `dualEdges` come from `DualContours.lean`).

* **Lower bound** (`criticalProb_zd_ge`, `criticalProb_zd_pos`): path counting (1.15)–(1.16).
  If `|C| = ∞` there are open paths of all lengths from the origin; an `n`-step path is coded by
  a word `w ∈ ({1,…,d} × {±})ⁿ` traversing the `n` distinct edges
  `{wordPos w k, wordPos w (k+1)}`, `k < n` (`exists_openWord_of_infinite`), which are all open
  with probability `pⁿ` (`bondPercolation_real_setOf_subset`), so `θ(p) ≤ (2d)ⁿ pⁿ → 0` for
  `p < 1/(2d)`; hence `p_c(ℤ^d) ≥ 1/(2d) > 0` for `d ≥ 1` (Grimmett's `λ(d)⁻¹ ≥ (2d-1)⁻¹` is
  replaced by the cruder `(2d)⁻¹`, which suffices).
* **Upper bound** (`theta_zd_pos_of_le`, `criticalProb_zd_le`): Peierls' argument
  (1.17)–(1.18), run directly inside a coordinate plane `ι : ℤ² ↪ ℤ^d`
  (`exists_zdGraph_two_embedding`; this replaces the comparison (1.9) `p_c(d) ≤ p_c(2)`): the
  configuration restricted along `ι` (`Percolation.Literature.restrictConfig` of
  `SubgraphMonotonicity.lean`) has a finite cluster whenever the original one has
  (`finite_openCluster_restrictConfig`), and a finite planar cluster of the origin is surrounded by a
  closed dual circuit (`Contour.exists_dualCircuit` of `DualContours.lean`) of some length `n`
  through a plaquette `(k, 0)`, `k < n`; there are at most `n(n+1)4ⁿ` candidates, each closed
  with probability `(1-p)ⁿ ≤ 64⁻ⁿ` for `p ≥ 63/64` (`bondPercolation_real_setOf_disjoint`), and
  the sum is `≤ ⅔ < 1`, so `θ(p) ≥ ⅓ > 0` and `p_c(ℤ^d) ≤ 63/64 < 1` for `d ≥ 2`.

Measurability of `{|C| = ∞}` is never needed: only monotonicity and countable subadditivity of
the (outer) measure are used, together with `μ(A) + μ(Aᶜ) ≥ 1`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.3 (product measure), §1.4 pp. 13–18
  (Theorem (1.10), (1.9), (1.13)–(1.18)).
* S. R. Broadbent, J. M. Hammersley, Proc. Cambridge Philos. Soc. 53 (1957) 629–641;
  J. M. Hammersley, Ann. Math. Statist. 28 (1957) 790–795 and Proc. Cambridge Philos. Soc. 55
  (1959) 13–20 (the original proofs, as credited by Grimmett p. 15).
-/

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory LatticeModels Filter Topology
open scoped ENNReal

variable {d : ℕ}

/-! ### From an infinite open cluster to open words of every length -/

/-- The edges `{wordPos w k, wordPos w (k+1)}` traversed by a step word are edges of `𝕃^d`.
[folklore] -/
theorem image_wordPos_subset_edgeSet {n : ℕ} (w : Fin n → Fin d × Bool) :
    (↑((Finset.range n).image fun k => s(wordPos w k, wordPos w (k + 1))) : Set (Sym2 (Site d)))
      ⊆ (zdGraph d).edgeSet := by
  intro e he
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at he
  obtain ⟨k, hk, rfl⟩ := he
  rw [SimpleGraph.mem_edgeSet, zdGraph_adj_iff_stepVec]
  exact ⟨w ⟨k, hk⟩, wordPos_succ w hk⟩

/-- The word read off along the first `n` steps of a walk in a subgraph of `ℤ^d`. [folklore] -/
theorem exists_word_of_walk {G : SimpleGraph (Site d)} (hG : G ≤ zdGraph d) {y : Site d}
    (q : G.Walk 0 y) (n : ℕ) (hn : n ≤ q.length) :
    ∃ w : Fin n → Fin d × Bool, ∀ k ≤ n, wordPos w k = q.getVert k := by
  have hadj : ∀ k : Fin n, ∃ a : Fin d × Bool, q.getVert (k + 1) = q.getVert k + stepVec a :=
    fun k => (zdGraph_adj_iff_stepVec _ _).1 (hG (q.adj_getVert_succ (lt_of_lt_of_le k.2 hn)))
  choose w hw using hadj
  refine ⟨w, fun k => ?_⟩
  induction k with
  | zero => intro; simp
  | succ k ih =>
    intro hk
    rw [wordPos_succ w hk, ih (Nat.le_of_succ_le hk), ← hw ⟨k, hk⟩]

/-- If `C(0)` is infinite (and `ω ⊆ E(𝕃^d)`), then for every `n` some word traversing `n` distinct
edges is open: "if the origin belongs to an infinite open cluster then there exist open paths of
all lengths beginning at the origin" (Grimmett 1999, §1.4 p. 16); the paths of length `n` are coded
by words in `({1,…,d} × {±})ⁿ` (p. 15, `σ(n) ≤ 2d(2d-1)^{n-1}`).
[cite: GrimmettPercolation1999, §1.4 pp. 15–16] -/
theorem exists_openWord_of_infinite {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet)
    (hC : (openCluster ω 0).Infinite) (n : ℕ) :
    ∃ w : Fin n → Fin d × Bool,
      ((Finset.range n).image fun k => s(wordPos w k, wordPos w (k + 1))).card = n ∧
      (↑((Finset.range n).image fun k => s(wordPos w k, wordPos w (k + 1))) : Set (Sym2 (Site d)))
        ⊆ ω := by
  classical
  have hG : openGraph ω ≤ zdGraph d := by
    intro x y hxy
    rw [openGraph_adj] at hxy
    exact hω hxy.1
  -- the finitely many endpoints of words shorter than `n`
  set S : Set (Site d) := ⋃ k : Fin n, Set.range fun w : Fin k → Fin d × Bool => wordPos w k
  have hS : S.Finite := Set.finite_iUnion fun _ => Set.finite_range _
  obtain ⟨y, hyC, hyS⟩ := (hC.sdiff hS).nonempty
  obtain ⟨q⟩ := (hyC : (openGraph ω).Reachable 0 y)
  set r := q.bypass with hr
  have hrp : r.IsPath := q.bypass_isPath
  -- `r` has length at least `n`, for otherwise `y ∈ S`
  have hn : n ≤ r.length := by
    by_contra hlt
    push Not at hlt
    obtain ⟨w, hw⟩ := exists_word_of_walk hG r r.length le_rfl
    exact hyS (Set.mem_iUnion.2 ⟨⟨r.length, hlt⟩, w, by simpa using hw r.length le_rfl⟩)
  obtain ⟨w, hw⟩ := exists_word_of_walk hG r n hn
  have hedge : ∀ k < n, s(wordPos w k, wordPos w (k + 1)) = s(r.getVert k, r.getVert (k + 1)) := by
    intro k hk
    rw [hw k hk.le, hw (k + 1) hk]
  refine ⟨w, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk l hl hkl
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    have hkl' : s(wordPos w k, wordPos w (k + 1)) = s(wordPos w l, wordPos w (l + 1)) := hkl
    rw [hedge k hk, hedge l hl, Sym2.eq_iff] at hkl'
    have hinj := hrp.getVert_injOn
    rcases hkl' with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hinj (by simp; omega) (by simp; omega) h1
    · have := hinj (by simp; omega) (by simp; omega) h1
      have := hinj (by simp; omega) (by simp; omega) h2
      omega
  · intro e he
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at he
    obtain ⟨k, hk, rfl⟩ := he
    rw [hedge k hk]
    exact ((openGraph_adj ω _ _).1 (r.adj_getVert_succ (lt_of_lt_of_le hk hn))).1

/-! ### Path counting: the lower bound -/

/-- **Path counting** (Grimmett 1999, §1.4, (1.15)): if the origin lies in an infinite open cluster
then there are open paths of every length `n` from the origin, so
`θ(p) ≤ P_p(N(n) ≥ 1) ≤ E_p N(n) = σ(n) pⁿ ≤ (2d)ⁿ pⁿ`. [cite: GrimmettPercolation1999, §1.4 (1.15) p. 16] -/
theorem theta_zd_le_pow (d n : ℕ) (p : unitInterval) :
    theta (zdGraph d) 0 p ≤ (2 * d : ℝ) ^ n * (p : ℝ) ^ n := by
  classical
  set μ := bondPercolation (zdGraph d) p with hμ
  -- the edges of a word, and the words traversing `n` distinct edges
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → Fin d × Bool) → Finset (Sym2 (Site d)),
      ∀ w, E w = (Finset.range n).image fun k => s(wordPos w k, wordPos w (k + 1)) :=
    ⟨_, fun _ => rfl⟩
  set good : Finset (Fin n → Fin d × Bool) := Finset.univ.filter fun w => (E w).card = n with hgood
  set bad : Set (BondConfig (Site d)) := {ω | ¬ ω ⊆ (zdGraph d).edgeSet} with hbad
  set U : Set (BondConfig (Site d)) := ⋃ w ∈ good, {ω | (↑(E w) : Set (Sym2 (Site d))) ⊆ ω} with hU
  have hsub : (percolatesAt 0 : Set (BondConfig (Site d))) ⊆ U ∪ bad := by
    intro ω hω
    by_cases hb : ω ⊆ (zdGraph d).edgeSet
    · obtain ⟨w, hw, hwω⟩ := exists_openWord_of_infinite hb hω n
      refine Or.inl (Set.mem_biUnion (x := w) ?_ ?_)
      · rw [hgood, Finset.coe_filter]
        exact ⟨Finset.mem_univ _, by rw [hE]; exact hw⟩
      · show (↑(E w) : Set (Sym2 (Site d))) ⊆ ω
        rw [hE]; exact hwω
    · exact Or.inr hb
  have hbad0 : μ.real bad = 0 := by
    rw [measureReal_eq_zero_iff]
    have := setBernoulli_ae_subset (u := (zdGraph d).edgeSet) (p := p)
    rw [Filter.Eventually, mem_ae_iff, Set.compl_setOf] at this
    exact this
  calc theta (zdGraph d) 0 p = μ.real (percolatesAt 0) := rfl
    _ ≤ μ.real (U ∪ bad) := measureReal_mono hsub
    _ ≤ μ.real U + μ.real bad := measureReal_union_le _ _
    _ = μ.real U := by rw [hbad0, add_zero]
    _ ≤ ∑ w ∈ good, μ.real {ω | (↑(E w) : Set (Sym2 (Site d))) ⊆ ω} :=
        measureReal_biUnion_finset_le _ _
    _ = ∑ w ∈ good, (p : ℝ) ^ n := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [hμ, bondPercolation_real_setOf_subset _ _ _
          (by rw [hE]; exact image_wordPos_subset_edgeSet w)]
        rw [hgood, Finset.mem_filter] at hw
        rw [hw.2]
    _ = good.card * (p : ℝ) ^ n := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * d : ℝ) ^ n * (p : ℝ) ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg p.2.1 n)
        have h1 : good.card ≤ (Finset.univ : Finset (Fin n → Fin d × Bool)).card :=
          Finset.card_le_univ _
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, Fintype.card_bool] at h1
        calc (good.card : ℝ) ≤ ((d * 2) ^ n : ℕ) := by exact_mod_cast h1
          _ = (2 * d : ℝ) ^ n := by push_cast; ring

/-- Below `1/(2d)` there is no percolation on `ℤ^d`: `θ(p) = 0` for `p < 1/(2d)`
(Grimmett 1999, §1.4, (1.16) with `λ(d) ≤ 2d`). [cite: GrimmettPercolation1999, §1.4 (1.16) p. 16] -/
theorem theta_zd_eq_zero_of_lt (d : ℕ) (p : unitInterval) (hp : (p : ℝ) < 1 / (2 * d)) :
    theta (zdGraph d) 0 p = 0 := by
  have hd : (0 : ℝ) < 2 * d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at hp
      exact absurd p.2.1 (not_le.2 hp)
    · positivity
  have hlt : 2 * d * (p : ℝ) < 1 := by
    rwa [lt_div_iff₀ hd, mul_comm] at hp
  have h0 : 0 ≤ 2 * d * (p : ℝ) := mul_nonneg hd.le p.2.1
  have ht : Tendsto (fun n : ℕ => (2 * d * (p : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 hlt
  have hle : theta (zdGraph d) 0 p ≤ 0 :=
    ge_of_tendsto' ht fun n => by rw [mul_pow]; exact theta_zd_le_pow d n p
  exact le_antisymm hle measureReal_nonneg

/-- **`p_c(ℤ^d) ≥ 1/(2d)`** for `d ≥ 1` (Grimmett 1999, §1.4: "`p_c(d) ≥ λ(d)⁻¹`", here with the
crude bound `σ(n) ≤ (2d)ⁿ` in place of the connective constant).
[cite: GrimmettPercolation1999, §1.4 (1.13), (1.16)] -/
theorem criticalProb_zd_ge (d : ℕ) (hd : 1 ≤ d) :
    1 / (2 * d : ℝ) ≤ criticalProb (zdGraph d) 0 := by
  have hd' : (0 : ℝ) < 2 * d := by positivity
  refine le_csInf ⟨1, Or.inr rfl⟩ ?_
  rintro q (⟨hq, hpos⟩ | hq)
  · by_contra hlt
    push Not at hlt
    exact hpos.ne' (theta_zd_eq_zero_of_lt d ⟨q, hq⟩ hlt)
  · rw [Set.mem_singleton_iff] at hq
    rw [hq, div_le_one hd']
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith

/-- **`p_c(ℤ^d) > 0`** for `d ≥ 1` (Grimmett 1999, §1.4, Theorem (1.10), lower bound).
[cite: GrimmettPercolation1999, §1.4 Theorem (1.10)] -/
theorem criticalProb_zd_pos (d : ℕ) (hd : 1 ≤ d) : 0 < criticalProb (zdGraph d) 0 :=
  lt_of_lt_of_le (by positivity) (criticalProb_zd_ge d hd)

/-! ### Closed cylinders -/

/-- For a finite set `F` of edges of `G`, the probability that all edges of `F` are closed is
`(1 - p) ^ |F|` (product measure; Grimmett 1999, §1.3). [cite: GrimmettPercolation1999, §1.3] -/
theorem bondPercolation_real_setOf_disjoint {V : Type*} (G : SimpleGraph V) (p : unitInterval)
    (F : Finset (Sym2 V)) (hF : (F : Set (Sym2 V)) ⊆ G.edgeSet) :
    (bondPercolation G p).real {ω | Disjoint (F : Set (Sym2 V)) ω} = (1 - p : ℝ) ^ F.card := by
  classical
  have hpre : (fun q : Sym2 V → Prop => {i | q i}) ⁻¹'
      {ω : BondConfig V | Disjoint (F : Set (Sym2 V)) ω}
      = Set.pi (F : Set (Sym2 V)) (fun _ => {False}) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.disjoint_left, Finset.mem_coe, Set.mem_pi,
      Set.mem_singleton_iff, eq_iff_iff, iff_false]
  rw [measureReal_def, bondPercolation, setBernoulli_apply', hpre,
    Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)]
  have h1 : ∀ e ∈ F, (unitInterval.toNNReal p • Measure.dirac (e ∈ G.edgeSet) +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False : Measure Prop) {False}
      = unitInterval.toNNReal (unitInterval.symm p) := by
    intro e he
    have heT : (e ∈ G.edgeSet) = True := propext ⟨fun _ => trivial, fun _ => hF he⟩
    simp [heT]
  rw [Finset.prod_congr rfl h1, Finset.prod_const, ENNReal.toReal_pow, ENNReal.coe_toReal]
  rfl

/-! ### Restricting a configuration along an injective map; the coordinate plane `ℤ² ↪ ℤ^d` -/

/-- If the open cluster of `ι x` is finite, so is the open cluster of `x` in the configuration
restricted along the injective map `ι` (`restrictConfig ι ω = {e | e.map ι ∈ ω}`, whose open
clusters `ι` maps into open clusters, `reachable_map_of_restrictConfig`); Grimmett 1999, §1.4
p. 13, for the coordinate embedding `𝕃^d ↪ 𝕃^{d+1}`: "the origin of `𝕃^{d+1}` belongs to an
infinite open cluster for a particular value of `p` whenever it belongs to an infinite open cluster
of the sublattice `𝕃^d`". [cite: GrimmettPercolation1999, §1.4 p. 13] -/
theorem finite_openCluster_restrictConfig {V W : Type*} {ι : V → W} (hι : Function.Injective ι)
    (ω : BondConfig W) (x : V) (h : (openCluster ω (ι x)).Finite) :
    (openCluster (restrictConfig ι ω) x).Finite := by
  refine Set.Finite.of_finite_image (h.subset ?_) hι.injOn
  rintro _ ⟨y, hy, rfl⟩
  exact reachable_map_of_restrictConfig hι ω hy

/-- The coordinate plane `ℤ² ↪ ℤ^d`, `d ≥ 2` (pad with zeros): an injective map fixing the origin
and sending edges of `𝕃²` to edges of `𝕃^d` (Grimmett 1999, §1.4 p. 13, the embedding behind
(1.9) `p_c(d+1) ≤ p_c(d)`). [cite: GrimmettPercolation1999, §1.4 p. 13, (1.9)] -/
theorem exists_zdGraph_two_embedding (hd : 2 ≤ d) :
    ∃ ι : Site 2 → Site d, Function.Injective ι ∧ ι 0 = 0 ∧
      ∀ e ∈ (zdGraph 2).edgeSet, e.map ι ∈ (zdGraph d).edgeSet := by
  obtain ⟨ι, hι⟩ : ∃ ι : Site 2 → Site d,
      ∀ x j, ι x j = if h : (j : ℕ) < 2 then x ⟨j, h⟩ else 0 := ⟨fun x j => _, fun _ _ => rfl⟩
  have hadd : ∀ x y, ι (x + y) = ι x + ι y := by
    intro x y; funext j; by_cases h : (j : ℕ) < 2 <;> simp [hι, h]
  have hsingle : ∀ i : Fin 2, ι (Pi.single i 1) = Pi.single (Fin.castLE hd i) 1 := by
    intro i
    funext j
    by_cases h : (j : ℕ) < 2
    · by_cases hij : (⟨j, h⟩ : Fin 2) = i
      · subst hij
        simp [hι, h]
      · have : j ≠ Fin.castLE hd i := by
          rintro rfl; exact hij rfl
        simp [hι, h, hij, this]
    · have : j ≠ Fin.castLE hd i := by
        rintro rfl; exact h i.2
      simp [hι, h, this]
  have hinj : Function.Injective ι := by
    intro x y hxy
    funext i
    have := congrFun hxy (Fin.castLE hd i)
    simpa [hι, i.2] using this
  refine ⟨ι, hinj, ?_, ?_⟩
  · funext j; simp [hι]
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet, zdGraph_adj_iff]
      rw [SimpleGraph.mem_edgeSet, zdGraph_adj_iff] at he
      obtain ⟨i, h | h⟩ := he
      · exact ⟨Fin.castLE hd i, Or.inl (by rw [h, hadd, hsingle])⟩
      · exact ⟨Fin.castLE hd i, Or.inr (by rw [h, hadd, hsingle])⟩

/-! ### Peierls' estimate on `ℤ^d`, `d ≥ 2` -/

/-- The `n`-th term of the Peierls sum at `p = 63/64` is at most `½ (¼)ⁿ`
(from `2n(n+1) ≤ 4ⁿ`). [folklore] -/
theorem peierls_term_le (n : ℕ) :
    (n : ℝ) * (n + 1) * 4 ^ n * (1 - 63 / 64) ^ n ≤ 1 / 2 * (1 / 4) ^ n := by
  have htwo : 2 * n ≤ 2 ^ n := by
    rcases n with - | m
    · simp
    · rw [pow_succ]
      have := m.lt_two_pow_self
      omega
  have hfour : 2 * n * (n + 1) ≤ 4 ^ n := by
    have h2 : n + 1 ≤ 2 ^ n := n.lt_two_pow_self
    calc 2 * n * (n + 1) ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul htwo h2
      _ = 4 ^ n := by rw [← mul_pow]; norm_num
  have h2 : (2 * n * (n + 1) : ℝ) ≤ 4 ^ n := by exact_mod_cast hfour
  have h8 : (1 - 63 / 64 : ℝ) ^ n = (1 / 4) ^ n * (1 / 4) ^ n * (1 / 4) ^ n := by
    rw [← mul_pow, ← mul_pow]; norm_num
  rw [h8]
  have key : (n : ℝ) * (n + 1) * (1 / 4) ^ n ≤ 1 / 2 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith
  calc (n : ℝ) * (n + 1) * 4 ^ n * ((1 / 4) ^ n * (1 / 4) ^ n * (1 / 4) ^ n)
      = ((4 : ℝ) ^ n * (1 / 4) ^ n) * (1 / 4) ^ n * (n * (n + 1) * (1 / 4) ^ n) := by ring
    _ = (1 / 4) ^ n * (n * (n + 1) * (1 / 4) ^ n) := by
        rw [← mul_pow]; norm_num
    _ ≤ (1 / 4) ^ n * (1 / 2) := by gcongr
    _ = 1 / 2 * (1 / 4) ^ n := by ring

/-- **Peierls' argument** (Grimmett 1999, §1.4 pp. 16–18, (1.17)–(1.18)): for `d ≥ 2` and
`p ≥ 63/64`, `θ_{ℤ^d}(p) > 0`. If the cluster of the origin is finite then so is its cluster in the
configuration restricted to a coordinate plane `ℤ² ↪ ℤ^d`, which by `Contour.exists_dualCircuit`
is surrounded by a closed dual circuit of some length `n` through a plaquette `(k, 0)`, `k < n`,
made of `n` distinct closed edges; there are at most `n (n+1) 4ⁿ` such circuits (position `m ≤ n`
of `(k,0)` on the circuit, `k`, and the word), each closed with probability `(1-p)ⁿ ≤ 64⁻ⁿ`, and
`Σₙ n(n+1)4ⁿ/64ⁿ ≤ ⅔ < 1`. [cite: GrimmettPercolation1999, §1.4 Theorem (1.10), proof pp. 16–18] -/
theorem theta_zd_pos_of_le (hd : 2 ≤ d) (p : unitInterval) (hp : 63 / 64 ≤ (p : ℝ)) :
    0 < theta (zdGraph d) 0 p := by
  classical
  obtain ⟨ι, hιi, hι0, hιE⟩ := exists_zdGraph_two_embedding hd
  set μ := bondPercolation (zdGraph d) p with hμ
  -- the events "the dual walk `(n, k, m, w)` is closed in the coordinate plane"
  let st : (n : ℕ) → ℕ → ℕ → (Fin n → Fin 2 × Bool) → Site 2 := fun n k m w =>
    Pi.single 0 (k : ℤ) - wordPos w m
  let S : (n : ℕ) → ℕ → ℕ → (Fin n → Fin 2 × Bool) → Set (BondConfig (Site d)) :=
    fun n k m w =>
      {ω | Disjoint (↑((dualEdges (st n k m w) w).image (Sym2.map ι)) : Set (Sym2 (Site d))) ω}
  let good : (n : ℕ) → ℕ → ℕ → Finset (Fin n → Fin 2 × Bool) := fun n k m =>
    Finset.univ.filter fun w => (dualEdges (st n k m w) w).card = n
  let V : ℕ → Set (BondConfig (Site d)) := fun n =>
    ⋃ k ∈ Finset.range n, ⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m, S n k m w
  -- a finite cluster forces one of these events
  have hsub : (percolatesAt 0 : Set (BondConfig (Site d)))ᶜ ⊆ ⋃ n, V n := by
    intro ω hω
    have hfin : (openCluster ω (ι 0)).Finite := by rw [hι0]; exact Set.not_infinite.1 hω
    obtain ⟨n, k, hkn, a, w, -, ⟨m, hmn, hpos⟩, hcard, hdisj, -, -⟩ :=
      Contour.exists_dualCircuit (restrictConfig ι ω)
        (finite_openCluster_restrictConfig hιi ω 0 hfin)
    have ha : a = st n k m w := by simp only [st, ← hpos, add_sub_cancel_right]
    subst ha
    refine Set.mem_iUnion.2 ⟨n, Set.mem_biUnion (Finset.mem_range.2 hkn)
      (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hmn))
        (Set.mem_biUnion (x := w) (by simp [good, hcard]) ?_))⟩
    simp only [S, Set.mem_setOf_eq, Finset.coe_image, Set.disjoint_left]
    rintro _ ⟨e, he, rfl⟩ heω
    exact Set.disjoint_left.1 hdisj he heω
  -- each event has probability `(1 - p)^n ≤ (1/64)^n`
  have hS : ∀ n k m, ∀ w ∈ good n k m, μ (S n k m w) ≤ ENNReal.ofReal ((1 - 63 / 64 : ℝ) ^ n) := by
    intro n k m w hw
    have hwn : (dualEdges (st n k m w) w).card = n := (Finset.mem_filter.1 hw).2
    rw [← ofReal_measureReal, hμ, bondPercolation_real_setOf_disjoint]
    · rw [Finset.card_image_of_injective _ (Sym2.map.injective hιi), hwn]
      refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (sub_nonneg.2 p.2.2) (by linarith) n)
    · intro e he
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at he
      obtain ⟨e, he, rfl⟩ := he
      exact hιE e (dualEdges_subset_edgeSet _ _ he)
  have hV : ∀ n, μ (V n) ≤ ENNReal.ofReal (1 / 2 * (1 / 4) ^ n) := by
    intro n
    calc μ (V n)
        ≤ ∑ k ∈ Finset.range n, μ (⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m, S n k m w) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), μ (⋃ w ∈ good n k m, S n k m w) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w ∈ good n k m, μ (S n k m w) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w ∈ good n k m,
            ENNReal.ofReal ((1 - 63 / 64 : ℝ) ^ n) := by
          gcongr with k _ m _ w hw; exact hS n k m w hw
      _ ≤ ∑ k ∈ Finset.range n, ∑ m ∈ Finset.range (n + 1), ∑ w : Fin n → Fin 2 × Bool,
            ENNReal.ofReal ((1 - 63 / 64 : ℝ) ^ n) := by
          gcongr; exact Finset.subset_univ _
      _ = ENNReal.ofReal ((n : ℝ) * (n + 1) * 4 ^ n * (1 - 63 / 64) ^ n) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_range,
            Finset.card_range, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
            Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul, nsmul_eq_mul,
            nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          congr 1
          · congr 1
            · rw [ENNReal.ofReal_natCast, ← Nat.cast_succ, ENNReal.ofReal_natCast]
            · rw [show ((4 : ℝ) ^ n) = ((2 * 2) ^ n : ℕ) by push_cast; ring, ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (1 / 2 * (1 / 4) ^ n) := ENNReal.ofReal_le_ofReal (peierls_term_le n)
  have hsum : (∑' n, ENNReal.ofReal (1 / 2 * (1 / 4 : ℝ) ^ n)) = ENNReal.ofReal (2 / 3) := by
    have hg : Summable fun n : ℕ => (1 / 2 : ℝ) * (1 / 4) ^ n :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hg, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hUnion : μ (⋃ n, V n) ≤ ENNReal.ofReal (2 / 3) :=
    (measure_iUnion_le V).trans ((ENNReal.tsum_le_tsum hV).trans hsum.le)
  -- conclusion
  have hcompl : μ (percolatesAt 0)ᶜ ≤ ENNReal.ofReal (2 / 3) := (measure_mono hsub).trans hUnion
  have hpos : μ (percolatesAt 0) ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 / 3) :=
      calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
        _ ≤ μ (percolatesAt 0) + μ (percolatesAt 0)ᶜ := by
            rw [← Set.union_compl_self (percolatesAt (0 : Site d))]; exact measure_union_le _ _
        _ ≤ ENNReal.ofReal (2 / 3) := by rw [h0, zero_add]; exact hcompl
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h1
    norm_num at h1
  exact ENNReal.toReal_pos hpos (measure_ne_top _ _)

/-- **`p_c(ℤ^d) ≤ 63/64 < 1`** for `d ≥ 2` (Grimmett 1999, §1.4, Theorem (1.10), upper bound;
Grimmett's sharper (1.12) `p_c(2) ≤ 1 - 1/λ(2)` is not needed).
[cite: GrimmettPercolation1999, §1.4 Theorem (1.10)] -/
theorem criticalProb_zd_le (hd : 2 ≤ d) : criticalProb (zdGraph d) 0 ≤ 63 / 64 := by
  refine csInf_le ⟨0, ?_⟩ (Or.inl ⟨⟨by norm_num, by norm_num⟩, theta_zd_pos_of_le hd _ le_rfl⟩)
  rintro q (⟨hq, -⟩ | hq)
  · exact hq.1
  · rw [Set.mem_singleton_iff] at hq
    rw [hq]; exact zero_le_one

/-- **`p_c(ℤ^d) < 1`** for `d ≥ 2`. [cite: GrimmettPercolation1999, §1.4 Theorem (1.10)] -/
theorem criticalProb_zd_lt_one (hd : 2 ≤ d) : criticalProb (zdGraph d) 0 < 1 :=
  (criticalProb_zd_le hd).trans_lt (by norm_num)

end Percolation.Literature
