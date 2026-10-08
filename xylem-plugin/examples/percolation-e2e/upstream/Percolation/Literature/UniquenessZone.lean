import Percolation.Literature.SharpnessDCTProofs
import Percolation.Literature.UniquenessInfiniteCluster
import Percolation.Util.Linter

/-!
# The uniqueness zone: boundary-connected vertices of `Λ_k` are connected inside `Λ_n`, `n ≫ k`

The "uniqueness zone" input of the Martineau–Tassion form of the Grimmett–Marstrand renormalisation
(S. Martineau, V. Tassion, *Locality of percolation for abelian Cayley graphs*, Ann. Probab. 45
(2017), proof of Lemma 3.7: "The number of disjoint clusters (for the configuration restricted to
`B(n+1)`) connecting `B(k)` to `B(n)ᶜ` converges when `n` tends to infinity to the number of
infinite clusters intersecting `B(k)`.

* `uniqZone k n` — the event "any two vertices of `Λ_k`, each joined inside `Λ_n` to `∂Λ_n`, are
  joined to each other inside `Λ_n`" (all the open clusters of the configuration restricted to
  the box `Λ_n` that connect `Λ_k` to `∂Λ_n` coincide). This is the AT-MOST-ONE half of
  Martineau–Tassion's event `A ↔[!C!] B` (§3.1.2: "restricting the configuration to `C` there
  exists a unique component that intersects `A` and `B`") — the half the proof of their Lemma 3.7
  uses ("any pair of open paths crossing this region must be connected inside `B(n+1)`"); the
  existence half is deliberately NOT part of `uniqZone` (e.g. `∅ ∈ uniqZone k n` for `k < n`): in
  the renormalisation it is supplied by the uniform-percolation input `UniformPercolation.lean`.
  The re-indexing `Λ_n / ∂Λ_n` here versus `B(n+1) / B(n)ᶜ` there is immaterial;
* `exists_forall_le_lt_real_uniqZone` — **for every `k` and `η > 0` there is `n₀` with
  `P_p(uniqZone k n) > 1 - η` for all `n ≥ n₀`** (every `d`, every `p`).

The event "`x ↔ ∂Λ_n in Λ_n`" is `DCT16.BdryConn n ω x` (`SharpnessDCT.lean`; for
`x = 0` it is `siteToBoundary d n`); `toBdry n x` below is only the `Set`-bundled spelling of it.

Proof (the printed convergence argument, run pairwise): for fixed `x, y ∈ Λ_k` the events
`Bad_n(x,y) = {x ↔ ∂Λ_n in Λ_n} ∩ {y ↔ ∂Λ_n in Λ_n} ∩ {x ↮ y in Λ_n}` decrease in `n` (first
exit of a path; monotonicity of "`in Λ_n`"), so `P_p(Bad_n) → P_p(⋂ₙ Bad_n)`; and
`⋂ₙ Bad_n ⊆ {|C(x)| = ∞, |C(y)| = ∞, x ↮ y}`, a null event by the uniqueness of the infinite
cluster (`Grimmett1999_numInfiniteClusters_le_one_holds`, `UniquenessInfiniteCluster.lean`:
Aizenman–Kesten–Newman 1987 / Burton–Keane 1989). A union bound over the `|Λ_k|²` pairs concludes.

## References

* S. Martineau, V. Tassion, *Locality of percolation for abelian Cayley graphs*, Ann. Probab. 45
  (2017) 1247–1277, arXiv:1312.1946, §3.1.2 (the events `A ↔[!C!] B`), §3.3 proof of Lemma 3.7
  (uniqueness zone) [MartineauTassion2017].
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §8.2 Thm. (8.1) (uniqueness), §7.2 (use of
  uniqueness-type gluing in renormalisation).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels DCT16
open scoped Topology ENNReal

variable {d : ℕ}

/-! ## Generalities -/

/-- A walk of the graph all of whose vertices lie in `A` is a path inside `A`. -/
theorem pathIn_of_walk_subset {V : Type*} {G : SimpleGraph V} {A : Set V} {u v : V}
    (W : G.Walk u v) (h : ∀ z ∈ W.support, z ∈ A) : PathIn G A u v := by
  induction W with
  | nil => exact PathIn.refl (h _ (SimpleGraph.Walk.start_mem_support _))
  | @cons a b c hab W' ih =>
    have hW' : ∀ z ∈ W'.support, z ∈ A := fun z hz => h z (by simp [hz])
    have ha : a ∈ A := h a (by simp)
    have hb : b ∈ A := hW' b (SimpleGraph.Walk.start_mem_support _)
    exact (PathIn.of_adj ha hb hab).trans (ih hW')

/-! ## The events -/

/-- `{x ↔ ∂Λ_n in Λ_n}` as an event: the set of configurations in which `x` is joined inside the box
 `Λ_n` by an open path to a vertex of its inner vertex boundary. This is the `Set`-bundled form of
 the predicate `DCT16.BdryConn n ω x` (`SharpnessDCT.lean`), `mem_toBdry_iff : Iff.rfl`; for `x = 0`
 it is `siteToBoundary d n`. [cite: GrimmettPercolation1999, §1.4 (A_n)]
-/
abbrev toBdry (n : ℕ) (x : Site d) : Set (BondConfig (Site d)) := {ω | BdryConn n ω x}

/-- **The uniqueness zone** `U(k,n)`: any two vertices of `Λ_k` that are joined inside `Λ_n` to
`∂Λ_n` are joined to each other inside `Λ_n` (the at-most-one half of Martineau–Tassion's
`Λ_k ↔[!Λ_n!] ∂Λ_n`, proof of Lemma 3.7: all clusters of the configuration restricted to the big
box which connect the small box to the boundary coincide; existence is not required).
[cite: MartineauTassion2017, §3.1.2 and proof of Lemma 3.7] -/
def uniqZone (k n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∀ x ∈ box d k, ∀ y ∈ box d k, ω ∈ toBdry n x → ω ∈ toBdry n y →
    ω ∈ openConnIn (↑(box d n) : Set (Site d)) x y}

/-- The bad event for the pair `(x, y)`: both reach `∂Λ_n` inside `Λ_n` but are not joined inside
`Λ_n`. [folklore] -/
def badPair (n : ℕ) (x y : Site d) : Set (BondConfig (Site d)) :=
  toBdry n x ∩ toBdry n y ∩ (openConnIn (↑(box d n) : Set (Site d)) x y)ᶜ

/-- `toBdry` is measurable. [folklore] -/
theorem measurableSet_toBdry (n : ℕ) (x : Site d) : MeasurableSet (toBdry n x) := by
  have : toBdry n x = ⋃ a ∈ innerBoundary (zdGraph d) (box d n),
      openConnIn (↑(box d n) : Set (Site d)) x a := by
    ext ω; simp [toBdry, BdryConn]
  rw [this]
  exact MeasurableSet.biUnion (Finset.countable_toSet _) fun a _ => measurableSet_openConnIn _ x a

/-- `badPair` is measurable. [folklore] -/
theorem measurableSet_badPair (n : ℕ) (x y : Site d) : MeasurableSet (badPair n x y) :=
  ((measurableSet_toBdry n x).inter (measurableSet_toBdry n y)).inter (measurableSet_openConnIn _ x y).compl

/-- The complement of the uniqueness zone is covered by the bad pairs. [folklore] -/
theorem compl_uniqZone_subset (k n : ℕ) :
    (uniqZone (d := d) k n)ᶜ ⊆ ⋃ x ∈ box d k, ⋃ y ∈ box d k, badPair n x y := by
  intro ω hω
  simp only [uniqZone, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, exists_prop] at hω
  obtain ⟨x, hx, y, hy, hbx, hby, hxy⟩ := hω
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨x, hx, y, hy, ⟨hbx, hby⟩, hxy⟩

/-! ## Monotonicity in `n` -/

/-- A vertex of the inner boundary of `Λ_{n+1}` lies outside `Λ_n`. [folklore] -/
theorem notMem_box_of_mem_innerBoundary_succ {n : ℕ} {a : Site d}
    (ha : a ∈ innerBoundary (zdGraph d) (box d (n + 1))) : a ∉ box d n :=
  notMem_box_of_mem_innerBoundary_box (Nat.lt_succ_self n) ha

/-- **`{x ↔ ∂Λ_{n+1} in Λ_{n+1}} ⊆ {x ↔ ∂Λ_n in Λ_n}`** for `x ∈ Λ_n` and `ω ⊆ E(ℤ^d)`: stop the
path at its first exit from `Λ_n`. [cite: GrimmettPercolation1999, §1.4] -/
theorem toBdry_succ_subset {n : ℕ} {x : Site d} (hx : x ∈ box d n) {ω : BondConfig (Site d)}
    (hω : ω ⊆ (zdGraph d).edgeSet) (h : ω ∈ toBdry (n + 1) x) : ω ∈ toBdry n x := by
  obtain ⟨a, ha, hpath⟩ := h
  rw [mem_openConnIn_iff_pathIn] at hpath
  obtain ⟨b, c, hb, hc, -, hbc, hpb⟩ := hpath.exit (R := (↑(box d n) : Set (Site d)))
    (Finset.mem_coe.2 hx) (fun h' => notMem_box_of_mem_innerBoundary_succ ha (Finset.mem_coe.1 h'))
  refine ⟨b, ?_, ?_⟩
  · rw [mem_innerBoundary_iff]
    exact ⟨Finset.mem_coe.1 hb, c, fun h' => hc (Finset.mem_coe.2 h'), adj_of_openGraph_adj hω hbc⟩
  · rw [mem_openConnIn_iff_pathIn]
    exact hpb.mono Set.inter_subset_left

/-- `{x ↔ y in Λ_n} ⊆ {x ↔ y in Λ_{n+1}}`. [folklore] -/
theorem openConnIn_box_mono {n : ℕ} {x y : Site d} {ω : BondConfig (Site d)}
    (h : ω ∈ openConnIn (↑(box d n) : Set (Site d)) x y) :
    ω ∈ openConnIn (↑(box d (n + 1)) : Set (Site d)) x y := by
  rw [mem_openConnIn_iff_pathIn] at h ⊢
  exact h.mono (Finset.coe_subset.2 (box_mono d (Nat.le_succ n)))

/-- The bad events decrease in `n` (for `x, y ∈ Λ_n`, `ω ⊆ E(ℤ^d)`). [folklore] -/
theorem badPair_succ_subset {n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n)
    {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet) (h : ω ∈ badPair (n + 1) x y) :
    ω ∈ badPair n x y :=
  ⟨⟨toBdry_succ_subset hx hω h.1.1, toBdry_succ_subset hy hω h.1.2⟩, fun h' => h.2 (openConnIn_box_mono h')⟩

/-- Iterated monotonicity: `badPair (k + j') ⊆ badPair (k + j)` for `j ≤ j'`, `x, y ∈ Λ_k`. [folklore] -/
theorem badPair_add_antitone {k : ℕ} {x y : Site d} (hx : x ∈ box d k) (hy : y ∈ box d k)
    {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet) {j j' : ℕ} (hjj' : j ≤ j')
    (h : ω ∈ badPair (k + j') x y) : ω ∈ badPair (k + j) x y := by
  induction hjj' with
  | refl => exact h
  | @step m _ ih =>
    exact ih (badPair_succ_subset (box_mono d (Nat.le_add_right k m) hx)
      (box_mono d (Nat.le_add_right k m) hy) hω h)

/-! ## The limit event is null -/

/-- **`⋂ⱼ badPair (k+j) x y ⊆ {|C(x)| = ∞} ∩ {|C(y)| = ∞} ∩ {x ↮ y}`**: reaching every sphere
forces an infinite cluster, and an open path from `x` to `y` lies inside some box.
[cite: GrimmettPercolation1999, §1.4] -/
theorem iInter_badPair_subset (k : ℕ) (x y : Site d) :
    ⋂ j : ℕ, badPair (k + j) x y ⊆
      {ω | ω ∈ percolatesAt x ∧ ω ∈ percolatesAt y ∧ ¬(openGraph ω).Reachable x y} := by
  classical
  intro ω hω
  rw [Set.mem_iInter] at hω
  -- percolation from reaching all spheres
  have hperc : ∀ z : Site d, (∀ j, ω ∈ toBdry (k + j) z) → ω ∈ percolatesAt z := by
    intro z hz hfin
    obtain ⟨N, hN⟩ := exists_subset_box hfin.toFinset
    obtain ⟨a, ha, hpath⟩ := hz (N + 1)
    have haC : a ∈ openCluster ω z := by
      rw [mem_openConnIn_iff_pathIn] at hpath
      exact reachable_of_pathIn hpath
    have haN : a ∈ box d N := hN (hfin.mem_toFinset.2 haC)
    have hlt : N < k + (N + 1) := by omega
    exact notMem_box_of_mem_innerBoundary_box hlt ha haN
  refine ⟨hperc x fun j => (hω j).1.1, hperc y fun j => (hω j).1.2, fun hreach => ?_⟩
  -- an open path from `x` to `y` lies in some box
  obtain ⟨W⟩ := hreach
  obtain ⟨N, hN⟩ := exists_subset_box W.support.toFinset
  have hin : ω ∈ openConnIn (↑(box d (k + N)) : Set (Site d)) x y := by
    rw [mem_openConnIn_iff_pathIn]
    exact pathIn_of_walk_subset W fun z hz =>
      Finset.mem_coe.2 (box_mono d (Nat.le_add_left N k) (hN (List.mem_toFinset.2 hz)))
  exact (hω N).2 hin

/-- The limit event `{|C(x)| = ∞, |C(y)| = ∞, x ↮ y}` is null, by the uniqueness of the infinite
open cluster on `ℤ^d` (Aizenman–Kesten–Newman; Burton–Keane; Grimmett 1999 Thm. (8.1)).
[cite: GrimmettPercolation1999, §8.2 Thm. (8.1)] -/
theorem measure_percolatesAt_inter_not_reachable_eq_zero (p : unitInterval) (x y : Site d) :
    bondPercolation (zdGraph d) p
      {ω | ω ∈ percolatesAt x ∧ ω ∈ percolatesAt y ∧ ¬(openGraph ω).Reachable x y} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [Grimmett1999_numInfiniteClusters_le_one_holds d p] with ω hω
  rintro ⟨hx, hy, hxy⟩
  exact hxy ((numInfiniteClusters_le_one_iff ω).1 hω x y hx hy)

/-- **`P_p(badPair (k+j) x y) → 0`** as `j → ∞` for `x, y ∈ Λ_k`. [cite: GrimmettPercolation1999, §8.2 Thm. (8.1)] -/
theorem tendsto_measure_badPair (p : unitInterval) {k : ℕ} {x y : Site d} (hx : x ∈ box d k)
    (hy : y ∈ box d k) :
    Tendsto (fun j : ℕ => bondPercolation (zdGraph d) p (badPair (k + j) x y)) atTop (𝓝 0) := by
  set μ := bondPercolation (zdGraph d) p with hμ
  -- work with the lattice-configuration versions, which are genuinely decreasing
  set E : Set (BondConfig (Site d)) := {ω | ω ⊆ (zdGraph d).edgeSet} with hE
  have hEae : ∀ᵐ ω ∂μ, ω ∈ E := setBernoulli_ae_subset
  set B : ℕ → Set (BondConfig (Site d)) := fun j => badPair (k + j) x y ∩ E with hB
  have hanti : Antitone B := by
    intro j j' hjj' ω hω
    exact ⟨badPair_add_antitone hx hy hω.2 hjj' hω.1, hω.2⟩
  have hEnull : NullMeasurableSet E μ := by
    have h0 : μ Eᶜ = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hEae] with ω hω using fun h => h hω
    exact (NullMeasurableSet.of_null h0).of_compl
  have hmeas : ∀ j, NullMeasurableSet (B j) μ := fun j =>
    (measurableSet_badPair _ x y).nullMeasurableSet.inter hEnull
  have hlim := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top μ _⟩
  have hzero : μ (⋂ j, B j) = 0 := by
    refine measure_mono_null ?_ (measure_percolatesAt_inter_not_reachable_eq_zero p x y)
    refine Set.Subset.trans (Set.iInter_mono fun j => Set.inter_subset_left) (iInter_badPair_subset k x y)
  rw [hzero] at hlim
  refine hlim.congr fun j => ?_
  exact measure_congr (by
    filter_upwards [hEae] with ω hω
    exact propext ⟨fun h => h.1, fun h => ⟨h, hω⟩⟩)

/-! ## The theorem -/

/-- **The uniqueness zone has probability close to one** (Martineau–Tassion 2017, proof of
Lemma 3.7, on `ℤ^d`): for every `k` and `η > 0` there is `n₀` such that for all `n ≥ n₀`,
`P_p(uniqZone k n) > 1 - η` — with probability `> 1 - η`, any two vertices of `Λ_k` joined inside
`Λ_n` to `∂Λ_n` are joined to each other inside `Λ_n`. Union bound over the `|Λ_k|²` pairs of
`tendsto_measure_badPair`. [cite: MartineauTassion2017, proof of Lemma 3.7] -/
theorem exists_forall_le_lt_real_uniqZone (p : unitInterval) (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 1 - η < (bondPercolation (zdGraph d) p).real (uniqZone k n) := by
  classical
  set μ := bondPercolation (zdGraph d) p with hμ
  set P := (box d k) ×ˢ (box d k) with hP
  have hcard : 0 < (P.card : ℝ) + 1 := by positivity
  set ε : ℝ≥0∞ := ENNReal.ofReal (η / (2 * (P.card + 1))) with hε
  have hεpos : 0 < ε := by
    rw [hε, ENNReal.ofReal_pos]; positivity
  -- for each pair, eventually small
  have hev : ∀ q ∈ P, ∀ᶠ j : ℕ in atTop, μ (badPair (k + j) q.1 q.2) < ε := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
    exact (tendsto_measure_badPair p hq1 hq2).eventually (gt_mem_nhds hεpos)
  have hall : ∀ᶠ j : ℕ in atTop, ∀ q ∈ P, μ (badPair (k + j) q.1 q.2) < ε :=
    (Finset.eventually_all P).2 hev
  obtain ⟨j₀, hj₀⟩ := hall.exists_forall_of_atTop
  refine ⟨k + j₀, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  have hj : j₀ ≤ j := by omega
  -- union bound
  have hcompl : μ (uniqZone k (k + j))ᶜ ≤ ∑ q ∈ P, μ (badPair (k + j) q.1 q.2) := by
    calc μ (uniqZone k (k + j))ᶜ
        ≤ μ (⋃ x ∈ box d k, ⋃ y ∈ box d k, badPair (k + j) x y) := measure_mono (compl_uniqZone_subset k _)
      _ ≤ ∑ x ∈ box d k, μ (⋃ y ∈ box d k, badPair (k + j) x y) := measure_biUnion_finset_le _ _
      _ ≤ ∑ x ∈ box d k, ∑ y ∈ box d k, μ (badPair (k + j) x y) := by
          gcongr; exact measure_biUnion_finset_le _ _
      _ = ∑ q ∈ P, μ (badPair (k + j) q.1 q.2) := by rw [hP, Finset.sum_product]
  have hsum : ∑ q ∈ P, μ (badPair (k + j) q.1 q.2) ≤ P.card * ε := by
    calc ∑ q ∈ P, μ (badPair (k + j) q.1 q.2) ≤ ∑ _q ∈ P, ε :=
          Finset.sum_le_sum fun q hq => (hj₀ j hj q hq).le
      _ = P.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
  have hfin : (P.card : ℝ≥0∞) * ε ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hreal : μ.real (uniqZone k (k + j))ᶜ ≤ P.card * (η / (2 * (P.card + 1))) := by
    have h1 : μ (uniqZone k (k + j))ᶜ ≤ P.card * ε := hcompl.trans hsum
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hε, ENNReal.toReal_ofReal (by positivity)] at h2
    exact h2
  have hlt : (P.card : ℝ) * (η / (2 * (P.card + 1))) < η := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- measurability of the zone via its complement cover is not needed: use `prob_compl_eq_one_sub`
  have hmeasU : MeasurableSet (uniqZone (d := d) k (k + j)) := by
    have : uniqZone (d := d) k (k + j) = ⋂ x ∈ box d k, ⋂ y ∈ box d k,
        (toBdry (k + j) x ∩ toBdry (k + j) y)ᶜ ∪ openConnIn (↑(box d (k + j)) : Set (Site d)) x y := by
      ext ω
      simp only [uniqZone, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
        Set.mem_inter_iff, not_and]
      refine forall₂_congr fun x _ => forall₂_congr fun y _ => ?_
      tauto
    rw [this]
    exact MeasurableSet.biInter (Finset.countable_toSet _) fun x _ =>
      MeasurableSet.biInter (Finset.countable_toSet _) fun y _ =>
        ((measurableSet_toBdry _ x).inter (measurableSet_toBdry _ y)).compl.union (measurableSet_openConnIn _ x y)
  rw [measureReal_compl hmeasU, probReal_univ] at hreal
  linarith

end Percolation.Literature
