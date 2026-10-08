import Percolation.Literature.CerfLem51Proofs
import Percolation.Literature.ConnectivityProofs
import Percolation.Literature.ConstrainedClusters
import Percolation.Literature.FiniteEnergy
import Percolation.Literature.HalfSpaceBrickSeeds
import Percolation.Literature.InequalitiesProofs
import Percolation.Literature.PlanarDuality
import Percolation.Literature.SiteConnectionTools
import Percolation.Util.Linter

/-!
# Seeds on the surface of a box: Lemma (7.9) of Grimmett–Marstrand (Grimmett 1999, §7.2)

The first of the "two key lemmas" of the proof of
Theorem (7.2)(a) of Grimmett, *Percolation*, 2nd ed. (1999), §7.2 (Grimmett–Marstrand 1990),
pp. 150–152, proved here in every dimension `d ≥ 1` (Grimmett writes `d = 3`, "similar when `d > 3`"):

> **(7.9) Lemma.** If `θ(p) > 0` and `η > 0`, there exist integers `m = m(p, η)` and
> `n = n(p, η)` such that `2m < n` and  (7.10)  `P_p(B(m) ↔ K(m,n) in B(n)) > 1 - η`,

## The printed proof and its formalisation (pp. 151–152)

* `P_p(B(m) ↔ ∞) → 1` as `m → ∞` (`tendsto_prob_not_boxPerc`): the zero–one law
  (`Grimmett1999_prob_exists_percolatesAt_holds`) and continuity from below.
* (7.14): `∂B(n)` is covered by the `2^d d!` images of `T(n)` under the signed coordinate
  permutations (`exists_sp_mem_facePiece`), all of the same law
  (`prob_le_card_linked_piece_eq`), so by the square-root trick (`sqrt_trick_holds`) and FKG,
  `P_p(|V(n)| ≥ ℓ') ≥ 1 - P_p(|U(n)| < k ℓ')^{1/k}` with `U(n) = {x ∈ ∂B(n) : x ↔ B(m) in B(n)}`
  and `k = 2^d d!` (`prob_le_card_linked_faceFin_ge`).
* (7.15)–(7.16): `P_p(|U(n)| < ℓ) ≤ P_p(1 ≤ |U(n)| < ℓ) + P_p(B(m) ↮ ∞)` and
  `P_p(1 ≤ |U(n)| < ℓ) ≤ (1-p)^{-2dℓ} P_p(U(n+1) = ∅ ≠ U(n)) → 0` as `n → ∞`
  (`prob_bdLinked_lt_le`, `prob_fewLinked_le`, finite energy `bondPercolation_real_finiteEnergy`: "`U(n+1) = ∅`
  if every edge exiting `∂B(n)` from `U(n)` is closed"; the events `{U(n+1) = ∅ ≠ U(n)}` are
  pairwise disjoint, `tendsto_measureReal_of_pairwise_disjoint`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2, Lemma (7.9),
  pp. 150–152, with (7.5)–(7.16).
* G. R. Grimmett, J. M. Marstrand, *The supercritical phase of percolation is well behaved*,
  Proc. Roy. Soc. London A 430 (1990) 439–457.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels PlanarDuality unitInterval
open scoped ENNReal Topology Classical

namespace GM

variable {d : ℕ}

/-! ## Geometry: translated boxes, seeds, the face quadrant `T(n)` and the strip `T(m,n)` -/

/-- The translate `c + B(m)` of the box `B(m) = [-m,m]^d`. [cite: GrimmettPercolation1999, §7.2 p. 150 (x + B(m))] -/
def ball (c : Site d) (m : ℕ) : Finset (Site d) := (box d m).image (· + c)

/-- Membership in `c + B(m)`: every coordinate is within `m` of that of `c`. [folklore] -/
theorem mem_ball {c : Site d} {m : ℕ} {z : Site d} :
    z ∈ ball c m ↔ ∀ i, -(m : ℤ) ≤ z i - c i ∧ z i - c i ≤ m := by
  simp only [ball, Finset.mem_image, mem_box]
  constructor
  · rintro ⟨w, hw, rfl⟩ i
    simpa using hw i
  · intro h
    exact ⟨z - c, fun i => by simpa using h i, sub_add_cancel z c⟩

/-- `0 + B(m) = B(m)`. [folklore] -/
@[simp] theorem ball_zero (m : ℕ) : ball (0 : Site d) m = box d m := by
  ext z; simp [mem_ball, mem_box]

/-- The face quadrant `T(n) = {x : x₀ = n, 0 ≤ x_j ≤ n (j ≠ 0)}` of `∂B(n)` ((7.6), p. 150).
[cite: GrimmettPercolation1999, §7.2 (7.6) p. 150] -/
def facePiece (d n : ℕ) [NeZero d] : Set (Site d) :=
  {x | x 0 = n ∧ ∀ j : Fin d, j ≠ 0 → 0 ≤ x j ∧ x j ≤ n}

/-! ## First exit of an open path from a box -/

/-- **First exit.** A walk of `H` from `u ∈ S` to `v ∉ S` contains a step from a vertex `f ∈ S` to
a vertex `g ∉ S`, with `f` reachable from `u` inside `S`. [folklore] -/
theorem exists_exit_of_walk {V : Type*} {H : SimpleGraph V} (S : Set V) :
    ∀ {u v : V} (_ : H.Walk u v), u ∈ S → v ∉ S →
      ∃ f g, ∃ (hu : u ∈ S) (hf : f ∈ S), g ∉ S ∧ H.Adj f g ∧ (H.induce S).Reachable ⟨u, hu⟩ ⟨f, hf⟩ := by
  intro u v W
  induction W with
  | nil => intro hu hv; exact absurd hu hv
  | @cons a b c hab W ih =>
    intro ha hc
    by_cases hb : b ∈ S
    · obtain ⟨f, g, hb', hf, hg, hadj, hr⟩ := ih hb hc
      refine ⟨f, g, ha, hf, hg, hadj, ?_⟩
      have hstep : (H.induce S).Adj ⟨a, ha⟩ ⟨b, hb'⟩ := hab
      exact hstep.reachable.trans hr
    · exact ⟨a, b, ha, ha, hb, hab, SimpleGraph.Reachable.refl _⟩

/-- Open paths inside `S`: `openConnIn S x y ω` iff `(openGraph ω).induce S` joins them. [folklore] -/
theorem mem_openConnIn_iff' {V : Type*} {S : Set V} {x y : V} {ω : BondConfig V} :
    ω ∈ openConnIn S x y ↔ ∃ (hx : x ∈ S) (hy : y ∈ S), ((openGraph ω).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ :=
  Iff.rfl

/-- `openConnIn` is symmetric in its endpoints. [folklore] -/
theorem openConnIn_comm {V : Type*} {S : Set V} {x y : V} {ω : BondConfig V} :
    ω ∈ openConnIn S x y ↔ ω ∈ openConnIn S y x := by
  simp only [mem_openConnIn_iff']
  exact ⟨fun ⟨hx, hy, h⟩ => ⟨hy, hx, h.symm⟩, fun ⟨hy, hx, h⟩ => ⟨hx, hy, h.symm⟩⟩

/-- `openConnIn` is transitive. [folklore] -/
theorem openConnIn_trans {V : Type*} {S : Set V} {x y z : V} {ω : BondConfig V}
    (h1 : ω ∈ openConnIn S x y) (h2 : ω ∈ openConnIn S y z) : ω ∈ openConnIn S x z := by
  obtain ⟨hx, hy, h⟩ := h1
  obtain ⟨hy', hz, h'⟩ := h2
  exact ⟨hx, hz, h.trans h'⟩

/-- The vertices of the inner boundary of `B(n)` have a coordinate of modulus `n`. [folklore] -/
theorem exists_abs_eq_of_mem_innerBoundary {n : ℕ} {x : Site d}
    (hx : x ∈ innerBoundary (zdGraph d) (box d n)) : ∃ i, |x i| = n := by
  rw [mem_innerBoundary_iff] at hx
  obtain ⟨hxB, y, hy, hadj⟩ := hx
  rw [mem_box] at hxB
  rw [mem_box] at hy
  push Not at hy
  obtain ⟨i, hi⟩ := hy
  refine ⟨i, ?_⟩
  rw [zdGraph_adj_iff] at hadj
  obtain ⟨k, hk | hk⟩ := hadj
  · have h1 : y i = x i + (Pi.single k (1 : ℤ) : Site d) i := by rw [hk]; rfl
    rcases eq_or_ne i k with rfl | hik
    · simp at h1; have := hxB i; rw [abs_eq (by positivity)]; omega
    · rw [Pi.single_eq_of_ne hik] at h1; have := hxB i; omega
  · have h1 : x i = y i + (Pi.single k (1 : ℤ) : Site d) i := by rw [hk]; rfl
    rcases eq_or_ne i k with rfl | hik
    · simp at h1; have := hxB i; rw [abs_eq (by positivity)]; omega
    · rw [Pi.single_eq_of_ne hik] at h1; have := hxB i; omega

/-! ## Linked vertices: `U(n)` and `V(n)` -/

/-- The vertices of `S` joined to `B(m)` inside `B(n)` (for `S = ∂B(n)` this is Grimmett's `U(n)`,
for `S = T(n)` his `V(n)`, p. 151). [cite: GrimmettPercolation1999, §7.2 p. 151 (U(n), V(n))] -/
def linked (S : Finset (Site d)) (m n : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  S.filter fun x => ∃ y ∈ box d m, ω ∈ openConnIn (↑(box d n) : Set (Site d)) y x

/-- Membership in `linked`. [folklore] -/
theorem mem_linked {S : Finset (Site d)} {m n : ℕ} {ω : BondConfig (Site d)} {x : Site d} :
    x ∈ linked S m n ω ↔ x ∈ S ∧ ∃ y ∈ box d m, ω ∈ openConnIn (↑(box d n) : Set (Site d)) y x :=
  Finset.mem_filter

/-- `U(n)`: the vertices of `∂B(n)` joined to `B(m)` inside `B(n)`. [cite: GrimmettPercolation1999, §7.2 p. 151 (U(n))] -/
abbrev bdLinked (m n : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  linked (innerBoundary (zdGraph d) (box d n)) m n ω

/-- `linked` is monotone in the configuration. [folklore] -/
theorem linked_mono (S : Finset (Site d)) (m n : ℕ) {ω ω' : BondConfig (Site d)} (h : ω ⊆ ω') :
    linked S m n ω ⊆ linked S m n ω' := by
  intro x hx
  rw [mem_linked] at hx ⊢
  obtain ⟨hxS, y, hy, hc⟩ := hx
  exact ⟨hxS, y, hy, isUpperSet_openConnIn _ y x h hc⟩

/-- The event `{linked S = v}` is determined by the pairs of vertices of `B(n)`. [folklore] -/
theorem determinedBy_linked_eq (S : Finset (Site d)) (m n : ℕ) (v : Finset (Site d)) :
    DeterminedBy {ω : BondConfig (Site d) | linked S m n ω = v} ↑(box d n).sym2 := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_setOf_eq]
  suffices linked S m n ω = linked S m n ω' by rw [this]
  ext x
  simp only [mem_linked]
  refine and_congr_right fun _ => exists_congr fun y => and_congr_right fun _ => ?_
  exact (determinedBy_iff _ _).1 (determinedBy_openConnIn (box d n) y x) ω ω' h

/-- Any predicate of `linked S` is a measurable event. [folklore] -/
theorem measurableSet_linked (S : Finset (Site d)) (m n : ℕ) (P : Finset (Site d) → Prop) :
    MeasurableSet {ω : BondConfig (Site d) | P (linked S m n ω)} := by
  have : {ω : BondConfig (Site d) | P (linked S m n ω)} = ⋃ v : Finset (Site d), ⋃ (_ : P v), {ω | linked S m n ω = v} := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun _ =>
    (determinedBy_linked_eq S m n v).measurableSet_of_finset

/-- The event `{ℓ ≤ |linked S|}` is increasing. [folklore] -/
theorem isUpperSet_le_card_linked (S : Finset (Site d)) (m n ℓ : ℕ) :
    IsUpperSet {ω : BondConfig (Site d) | ℓ ≤ (linked S m n ω).card} := fun _ _ h hω =>
  hω.trans (Finset.card_le_card (linked_mono S m n h))

/-- **If `B(m)` percolates then `U(n) ≠ ∅`** (`m ≤ n`): an infinite open cluster meeting `B(m)`
leaves `B(n)`, and its first exit vertex is joined to `B(m)` inside `B(n)` (Grimmett p. 151,
(7.15): `P(|U(n)| < l) ≤ P(|U(n)| < l, B(m) ↔ ∞) + P(B(m) ↮ ∞)`). [cite: GrimmettPercolation1999, §7.2 (7.15) p. 151] -/
theorem bdLinked_nonempty_of_percolates {m n : ℕ} (hmn : m ≤ n) {ω : BondConfig (Site d)}
    (hω : ω ⊆ (zdGraph d).edgeSet) {y : Site d} (hy : y ∈ box d m) (hperc : ω ∈ percolatesAt y) :
    (bdLinked m n ω).Nonempty := by
  -- the infinite cluster of `y` contains a vertex outside `B(n)`
  have hinf : (openCluster ω y).Infinite := hperc
  obtain ⟨z, hz, hzB⟩ : ∃ z ∈ openCluster ω y, z ∉ (↑(box d n) : Set (Site d)) := by
    by_contra h
    push Not at h
    exact hinf ((box d n).finite_toSet.subset h)
  obtain ⟨W⟩ := (hz : (openGraph ω).Reachable y z)
  obtain ⟨f, g, hyB, hfB, hgB, hadj, hr⟩ := exists_exit_of_walk (↑(box d n) : Set (Site d)) W
    (Finset.mem_coe.2 (box_mono d hmn hy)) hzB
  refine ⟨f, mem_linked.2 ⟨?_, y, hy, hyB, hfB, hr⟩⟩
  rw [mem_innerBoundary_iff]
  refine ⟨hfB, g, hgB, ?_⟩
  exact hω ((openGraph_adj ω f g).1 hadj).1

/-- A vertex joined to `B(m)` inside a larger box `B(n')`, `n' > n ≥ m`, but lying outside `B(n)`,
forces `U(n) ≠ ∅` (first exit from `B(n)`). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem bdLinked_nonempty_of_openConnIn {m n n' : ℕ} (hmn : m ≤ n) {ω : BondConfig (Site d)}
    (hω : ω ⊆ (zdGraph d).edgeSet) {y x : Site d} (hy : y ∈ box d m) (hx : x ∉ box d n)
    (hc : ω ∈ openConnIn (↑(box d n') : Set (Site d)) y x) : (bdLinked m n ω).Nonempty := by
  obtain ⟨hyB', hxB', hr⟩ := hc
  obtain ⟨W⟩ := hr
  -- push the walk down to `openGraph ω`
  let W' : (openGraph ω).Walk y x := W.map (SimpleGraph.Embedding.induce _).toHom
  obtain ⟨f, g, hyB, hfB, hgB, hadj, hr'⟩ := exists_exit_of_walk (↑(box d n) : Set (Site d)) W'
    (Finset.mem_coe.2 (box_mono d hmn hy)) (fun h => hx (Finset.mem_coe.1 h))
  refine ⟨f, mem_linked.2 ⟨?_, y, hy, hyB, hfB, hr'⟩⟩
  rw [mem_innerBoundary_iff]
  exact ⟨hfB, g, fun h => hgB (Finset.mem_coe.2 h), hω ((openGraph_adj ω f g).1 hadj).1⟩

/-- `U(n') ≠ ∅ ⇒ U(n) ≠ ∅` for `m ≤ n < n'` (configurations of lattice edges). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem bdLinked_nonempty_of_lt {m n n' : ℕ} (hmn : m ≤ n) (hnn' : n < n') {ω : BondConfig (Site d)}
    (hω : ω ⊆ (zdGraph d).edgeSet) (h : (bdLinked m n' ω).Nonempty) : (bdLinked m n ω).Nonempty := by
  obtain ⟨x, hx⟩ := h
  rw [mem_linked] at hx
  obtain ⟨hxbd, y, hy, hc⟩ := hx
  obtain ⟨i, hi⟩ := exists_abs_eq_of_mem_innerBoundary hxbd
  refine bdLinked_nonempty_of_openConnIn hmn hω hy (fun hxn => ?_) hc
  have := (mem_box.1 hxn) i
  have h1 : |x i| ≤ n := abs_le.2 ⟨this.1, this.2⟩
  omega

/-! ## Finite energy: `P(1 ≤ |U(n)| < ℓ)` is small ((7.16)) -/

/-- The lattice edges leaving `B(n)` from the vertices of `u` ("every edge exiting `∂B(n)` from
`U(n)`", p. 151). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
def exits (n : ℕ) (u : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  u.biUnion fun x => (((zdGraph d).neighborFinset x).filter fun y => y ∉ box d n).image fun y => s(x, y)

/-- Membership in `exits`. [folklore] -/
theorem mem_exits {n : ℕ} {u : Finset (Site d)} {e : Sym2 (Site d)} :
    e ∈ exits n u ↔ ∃ x ∈ u, ∃ y, (zdGraph d).Adj x y ∧ y ∉ box d n ∧ e = s(x, y) := by
  simp only [exits, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨x, hx, y, ⟨hadj, hy⟩, rfl⟩; exact ⟨x, hx, y, hadj, hy, rfl⟩
  · rintro ⟨x, hx, y, hadj, hy, rfl⟩; exact ⟨x, hx, y, ⟨hadj, hy⟩, rfl⟩

/-- At most `2d |u|` edges leave `B(n)` from `u`. [folklore] -/
theorem card_exits_le (n : ℕ) (u : Finset (Site d)) : (exits n u).card ≤ 2 * d * u.card := by
  unfold exits
  refine Finset.card_biUnion_le.trans ?_
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun x _ => Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
  exact card_neighborFinset_zdGraph_le x

/-- Exit edges are not pairs of vertices of `B(n)`. [folklore] -/
theorem exits_disjoint_sym2 (n : ℕ) (u : Finset (Site d)) :
    Disjoint (↑(exits n u) : Set (Sym2 (Site d))) ↑(box d n).sym2 := by
  rw [Finset.disjoint_coe, Finset.disjoint_left]
  intro e he he'
  obtain ⟨x, -, y, -, hy, rfl⟩ := mem_exits.1 he
  rw [Finset.mk_mem_sym2_iff] at he'
  exact hy he'.2

/-- The event `{U(n) ≠ ∅, U(n+1) = ∅}` (on lattice configurations), (7.16). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
def lastLevel (d m n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ω ⊆ (zdGraph d).edgeSet ∧ (bdLinked m n ω).Nonempty ∧ bdLinked m (n + 1) ω = ∅}

/-- The event "`ω` consists of lattice edges" is measurable. [folklore] -/
theorem measurableSet_subset_edgeSet : MeasurableSet {ω : BondConfig (Site d) | ω ⊆ (zdGraph d).edgeSet} := by
  have : {ω : BondConfig (Site d) | ω ⊆ (zdGraph d).edgeSet} = ⋂ e ∈ (zdGraph d).edgeSetᶜ, {ω | e ∉ ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun h e he heω => he (h heω), fun h e heω => by_contra fun he => h e he heω⟩
  rw [this]
  exact MeasurableSet.biInter (Set.to_countable _) fun e _ => measurableSet_notMem e

/-- `lastLevel` is measurable. [folklore] -/
theorem measurableSet_lastLevel (m n : ℕ) : MeasurableSet (lastLevel d m n) :=
  measurableSet_subset_edgeSet.inter ((measurableSet_linked _ m n Finset.Nonempty).inter
    (measurableSet_linked _ m (n + 1) (· = ∅)))

/-- The events `{U(n) ≠ ∅, U(n+1) = ∅}`, `n ≥ m`, are pairwise disjoint (`U(k) ≠ ∅` is decreasing
in `k`). [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem pairwise_disjoint_lastLevel (m : ℕ) :
    Pairwise (Function.onFun Disjoint fun k : ℕ => lastLevel d m (m + k)) := by
  intro k k' hkk'
  wlog hlt : k < k' generalizing k k'
  · exact (this hkk'.symm (lt_of_le_of_ne (not_lt.1 hlt) hkk'.symm)).symm
  rw [Function.onFun, Set.disjoint_left]
  rintro ω ⟨hω, -, hk⟩ ⟨-, hk', -⟩
  have h : (bdLinked m (m + k + 1) ω).Nonempty := by
    rcases (show m + k + 1 ≤ m + k' by omega).eq_or_lt with heq | hlt'
    · rw [heq]; exact hk'
    · exact bdLinked_nonempty_of_lt (d := d) (by omega) hlt' hω hk'
  rw [hk] at h
  exact Finset.not_nonempty_empty h

/-- `P_p(U(n) ≠ ∅, U(n+1) = ∅) → 0` as `n → ∞`. [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem tendsto_prob_lastLevel (p : unitInterval) (m : ℕ) :
    Tendsto (fun k : ℕ => (bondPercolation (zdGraph d) p).real (lastLevel d m (m + k))) atTop (𝓝 0) :=
  tendsto_measureReal_of_pairwise_disjoint _ (fun k => measurableSet_lastLevel m (m + k))
    (pairwise_disjoint_lastLevel m)

/-- The event `{1 ≤ |U(n)| < ℓ}`. [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
def fewLinked (d m n ℓ : ℕ) : Set (BondConfig (Site d)) :=
  {ω | (bdLinked m n ω).Nonempty ∧ (bdLinked m n ω).card < ℓ}

/-- `fewLinked` is a function of `U(n)`, hence determined by the pairs of `B(n)`. [folklore] -/
theorem determinedBy_fewLinked_inter (m n ℓ : ℕ) (b : Finset (Site d)) :
    DeterminedBy (fewLinked d m n ℓ ∩ (bdLinked m n) ⁻¹' {b}) ↑(box d n).sym2 := by
  have : fewLinked d m n ℓ ∩ (bdLinked m n) ⁻¹' {b} =
      {ω | (fun v => (v.Nonempty ∧ v.card < ℓ) ∧ v = b) (bdLinked m n ω)} := by
    ext ω; simp [fewLinked]
  rw [this, show {ω : BondConfig (Site d) | (fun v => (v.Nonempty ∧ v.card < ℓ) ∧ v = b) (bdLinked m n ω)} =
      ⋃ v : Finset (Site d), ⋃ (_ : (v.Nonempty ∧ v.card < ℓ) ∧ v = b), {ω | bdLinked m n ω = v} by ext ω; simp]
  exact DeterminedBy.iUnion fun v => DeterminedBy.iUnion fun _ => determinedBy_linked_eq _ m n v

/-- **(7.16)**: `(1-p)^{2dℓ} P_p(1 ≤ |U(n)| < ℓ) ≤ P_p(U(n) ≠ ∅, U(n+1) = ∅)` for `m ≤ n`: close every
edge exiting `B(n)` from `U(n)` (finite energy, `bondPercolation_real_finiteEnergy`); then no open
path from `B(m)` reaches `∂B(n+1)`. [cite: GrimmettPercolation1999, §7.2 (7.16) p. 151] -/
theorem prob_fewLinked_le {m n : ℕ} (hmn : m ≤ n) (ℓ : ℕ) (p : unitInterval) :
    (1 - (p : ℝ)) ^ (2 * d * ℓ) * (bondPercolation (zdGraph d) p).real (fewLinked d m n ℓ) ≤
      (bondPercolation (zdGraph d) p).real (lastLevel d m n) := by
  set μ := bondPercolation (zdGraph d) p
  have hfe := bondPercolation_real_finiteEnergy (zdGraph d) p (A := fewLinked d m n ℓ)
    (S := ↑(box d n).sym2) (Ψ := bdLinked m n) (φ := exits n) (k := 2 * d * ℓ)
    (fun b => determinedBy_fewLinked_inter m n ℓ b)
    (fun b => (determinedBy_fewLinked_inter m n ℓ b).measurableSet_of_finset)
    (fun ω _ => exits_disjoint_sym2 n _)
    (fun ω hω => (card_exits_le n _).trans (Nat.mul_le_mul_left _ hω.2.le))
  refine hfe.trans ?_
  -- `{1 ≤ |U(n)| < ℓ} ∩ {exits closed} ⊆ lastLevel` almost surely
  have hae : ∀ᵐ ω ∂μ, ω ⊆ (zdGraph d).edgeSet := setBernoulli_ae_subset
  refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  filter_upwards [hae] with ω hω
  intro hmem
  obtain ⟨⟨hne, -⟩, hclosed⟩ := hmem
  refine ⟨hω, hne, ?_⟩
  by_contra hne'
  obtain ⟨x', hx'⟩ := Finset.nonempty_iff_ne_empty.2 hne'
  rw [mem_linked] at hx'
  obtain ⟨hx'bd, y, hy, hc⟩ := hx'
  obtain ⟨i, hi⟩ := exists_abs_eq_of_mem_innerBoundary hx'bd
  have hx'B : x' ∉ box d n := fun h => by
    have := (mem_box.1 h) i
    have h1 : |x' i| ≤ n := abs_le.2 ⟨this.1, this.2⟩
    omega
  obtain ⟨hyB', hxB', hr⟩ := hc
  obtain ⟨W⟩ := hr
  let W' : (openGraph ω).Walk y x' := W.map (SimpleGraph.Embedding.induce _).toHom
  obtain ⟨f, g, hyB, hfB, hgB, hadj, hr'⟩ := exists_exit_of_walk (↑(box d n) : Set (Site d)) W'
    (Finset.mem_coe.2 (box_mono d hmn hy)) (fun h => hx'B (Finset.mem_coe.1 h))
  have hfg : s(f, g) ∈ ω := ((openGraph_adj ω f g).1 hadj).1
  have hadjG : (zdGraph d).Adj f g := hω hfg
  have hfU : f ∈ bdLinked m n ω := by
    refine mem_linked.2 ⟨?_, y, hy, hyB, hfB, hr'⟩
    rw [mem_innerBoundary_iff]
    exact ⟨hfB, g, fun h => hgB (Finset.mem_coe.2 h), hadjG⟩
  exact hclosed _ (mem_exits.2 ⟨f, hfU, g, hadjG, fun h => hgB (Finset.mem_coe.2 h), rfl⟩) hfg

/-! ## The zero–one law input: `P_p(B(m) ↔ ∞) → 1` -/

/-- The event `{B(m) ↔ ∞}`: some vertex of `B(m)` lies in an infinite open cluster. [cite: GrimmettPercolation1999, §7.2 p. 151] -/
def boxPerc (d m : ℕ) : Set (BondConfig (Site d)) := {ω | ∃ y ∈ box d m, ω ∈ percolatesAt y}

/-- `boxPerc` is measurable. [folklore] -/
theorem measurableSet_boxPerc (m : ℕ) : MeasurableSet (boxPerc d m) := by
  have : boxPerc d m = ⋃ y ∈ box d m, percolatesAt y := by ext ω; simp [boxPerc]
  rw [this]
  exact MeasurableSet.biUnion (box d m).countable_toSet fun y _ => measurableSet_percolatesAt_holds y

/-- **"Since `θ(p) > 0`, there exists a.s. an infinite open cluster, whence `P_p(B(m) ↔ ∞) → 1`
as `m → ∞`"** (p. 151; zero–one law, Thm (1.11)). [cite: GrimmettPercolation1999, §7.2 p. 151] -/
theorem tendsto_prob_boxPerc (p : unitInterval) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) :
    Tendsto (fun m : ℕ => (bondPercolation (zdGraph d) p).real (boxPerc d m)) atTop (𝓝 1) := by
  set μ := bondPercolation (zdGraph d) p
  have h1 : μ.real {ω | ∃ x : Site d, ω ∈ percolatesAt x} = 1 :=
    (Grimmett1999_prob_exists_percolatesAt_holds d p).2 hθ
  have hunion : ⋃ m : ℕ, boxPerc d m = {ω | ∃ x : Site d, ω ∈ percolatesAt x} := by
    ext ω
    simp only [boxPerc, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, y, -, hy⟩; exact ⟨y, hy⟩
    · rintro ⟨y, hy⟩
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 ((iUnion_coe_box d).symm ▸ Set.mem_univ y : y ∈ ⋃ L : ℕ, (↑(box d L) : Set (Site d)))
      exact ⟨m, y, hm, hy⟩
  have hmono : Monotone (boxPerc d) := fun m m' h ω ⟨y, hy, hω⟩ => ⟨y, box_mono d h hy, hω⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hunion] at ht
  have ht' := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ht
  rwa [← measureReal_def, h1] at ht'

/-- `P_p(B(m) ↮ ∞) → 0`. [cite: GrimmettPercolation1999, §7.2 (7.11) p. 151] -/
theorem tendsto_prob_not_boxPerc (p : unitInterval) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) :
    Tendsto (fun m : ℕ => (bondPercolation (zdGraph d) p).real (boxPerc d m)ᶜ) atTop (𝓝 0) := by
  have h := tendsto_prob_boxPerc p hθ
  have heq : ∀ m, (bondPercolation (zdGraph d) p).real (boxPerc d m)ᶜ =
      1 - (bondPercolation (zdGraph d) p).real (boxPerc d m) := fun m => by
    rw [measureReal_compl (measurableSet_boxPerc m), probReal_univ]
  simp_rw [heq]
  simpa using h.const_sub 1

/-- **(7.15)**: `P_p(|U(n)| < ℓ) ≤ P_p(1 ≤ |U(n)| < ℓ) + P_p(B(m) ↮ ∞)` (`m ≤ n`), since
`B(m) ↔ ∞` forces `U(n) ≠ ∅`. [cite: GrimmettPercolation1999, §7.2 (7.15) p. 151] -/
theorem prob_bdLinked_lt_le {m n : ℕ} (hmn : m ≤ n) (ℓ : ℕ) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real {ω | (bdLinked m n ω).card < ℓ} ≤
      (bondPercolation (zdGraph d) p).real (fewLinked d m n ℓ) +
        (bondPercolation (zdGraph d) p).real (boxPerc d m)ᶜ := by
  set μ := bondPercolation (zdGraph d) p
  have hae : ∀ᵐ ω ∂μ, ω ⊆ (zdGraph d).edgeSet := setBernoulli_ae_subset
  calc μ.real {ω | (bdLinked m n ω).card < ℓ}
      ≤ μ.real (fewLinked d m n ℓ ∪ (boxPerc d m)ᶜ) := by
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
        filter_upwards [hae] with ω hω
        intro hlt
        by_cases hperc : ω ∈ boxPerc d m
        · obtain ⟨y, hy, hyp⟩ := hperc
          exact Or.inl ⟨bdLinked_nonempty_of_percolates hmn hω hy hyp, hlt⟩
        · exact Or.inr hperc
    _ ≤ μ.real (fewLinked d m n ℓ) + μ.real (boxPerc d m)ᶜ := measureReal_union_le _ _

/-! ## Symmetry: the `2^d d!` images of `T(n)` cover `∂B(n)` and have the same law ((7.14)) -/

/-- The hyperoctahedral symmetries of `ℤ^d` fixing the origin, as pairs (permutation, signs).
[cite: GrimmettPercolation1999, §7.2 p. 151 ("the symmetries of L³ obtained by reflections")] -/
abbrev HOct (d : ℕ) : Type := Equiv.Perm (Fin d) × (Fin d → ℤˣ)

/-- The signed coordinate permutation of `g`. [folklore] -/
abbrev sp (g : HOct d) : Site d ≃ Site d := Site.signedPerm g.1 g.2

/-- The signed coordinate permutation of `g` as a graph automorphism of `ℤ^d`. [folklore] -/
abbrev spIso (g : HOct d) : zdGraph d ≃g zdGraph d := zdSignedPermIso g.1 g.2

/-- The identity element acts trivially. [folklore] -/
@[simp] theorem sp_one_apply (x : Site d) : sp (1 : HOct d) x = x := by
  funext i; simp [Site.signedPerm_apply]; rfl

/-- The image of `T(n)` under `g⁻¹`, i.e. the vertices `x` of `B(n)` with `g x ∈ T(n)`; for
`g = 1` this is `T(n)` itself. [cite: GrimmettPercolation1999, §7.2 p. 151 (24 copies of T(n))] -/
def piece [NeZero d] (g : HOct d) (n : ℕ) : Finset (Site d) := (box d n).filter fun x => sp g x ∈ facePiece d n

/-- `T(n)` as a finite set. [cite: GrimmettPercolation1999, §7.2 (7.6) p. 150] -/
def faceFin (d n : ℕ) [NeZero d] : Finset (Site d) := (box d n).filter fun x => x ∈ facePiece d n

/-- Membership in `faceFin`. [folklore] -/
theorem mem_faceFin [NeZero d] {n : ℕ} {x : Site d} : x ∈ faceFin d n ↔ x ∈ facePiece d n := by
  rw [faceFin, Finset.mem_filter, and_iff_right_iff_imp]
  intro hx
  rw [mem_box]
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [hx.1]; omega
  · have := hx.2 i hi; omega

/-- `piece 1 n = T(n)`. [folklore] -/
@[simp] theorem piece_one [NeZero d] (n : ℕ) : piece (1 : HOct d) n = faceFin d n := by
  ext x; simp [piece, faceFin]

/-- **Covering**: every vertex of `∂B(n)` lies in some image of `T(n)` ("`∂B(n)` has six faces, and
therefore 24 copies of `T(n)`", p. 151). [cite: GrimmettPercolation1999, §7.2 p. 151] -/
theorem exists_sp_mem_facePiece [NeZero d] {n : ℕ} {x : Site d} (hx : x ∈ innerBoundary (zdGraph d) (box d n)) :
    ∃ g : HOct d, sp g x ∈ facePiece d n := by
  obtain ⟨i, hi⟩ := exists_abs_eq_of_mem_innerBoundary hx
  have hxB := mem_box.1 (mem_innerBoundary_iff.1 hx).1
  let π : Equiv.Perm (Fin d) := Equiv.swap 0 i
  let ε : Fin d → ℤˣ := fun j => if 0 ≤ x (π.symm j) then 1 else -1
  refine ⟨(π, ε), ?_⟩
  have key : ∀ j, sp ((π, ε) : HOct d) x j = |x (π.symm j)| := by
    intro j
    simp only [Site.signedPerm_apply, ε]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · push Not at h; simp [abs_of_neg h]
  refine ⟨?_, fun j _ => ?_⟩
  · rw [key]
    have : π.symm 0 = i := by simp [π]
    rw [this, hi]
  · rw [key]
    have := hxB (π.symm j)
    exact ⟨abs_nonneg _, abs_le.2 ⟨this.1, this.2⟩⟩

/-- **Relabelling and open paths inside a set**: `φ·ω ∈ {φ a ↔ φ b in S} ↔ ω ∈ {a ↔ b in φ⁻¹ S}`.
[folklore] -/
theorem relabel_mem_openConnIn_iff {V W : Type*} (φ : V ≃ W) (S : Set W) (a b : V) (ω : BondConfig V) :
    BondConfig.relabel (sym2Equiv φ) ω ∈ openConnIn S (φ a) (φ b) ↔ ω ∈ openConnIn (φ ⁻¹' S) a b := by
  let ψ : (openGraph ω).induce (φ ⁻¹' S) ≃g (openGraph (BondConfig.relabel (sym2Equiv φ) ω)).induce S :=
    { toEquiv := φ.subtypeEquiv fun v => Iff.rfl
      map_rel_iff' := fun {u v} => by
        simp only [SimpleGraph.comap_adj, Function.Embedding.subtype_apply]
        exact openGraph_relabel_adj_iff φ ω u v }
  constructor
  · rintro ⟨ha, hb, hr⟩
    refine ⟨ha, hb, ?_⟩
    have := (SimpleGraph.Iso.reachable_iff (φ := ψ) (u := ⟨a, ha⟩) (v := ⟨b, hb⟩)).1
    exact this hr
  · rintro ⟨ha, hb, hr⟩
    exact ⟨ha, hb, (SimpleGraph.Iso.reachable_iff (φ := ψ) (u := ⟨a, ha⟩) (v := ⟨b, hb⟩)).2 hr⟩

/-- Signed permutations preserve boxes (set form). [folklore] -/
theorem sp_preimage_box (g : HOct d) (n : ℕ) : sp g ⁻¹' (↑(box d n) : Set (Site d)) = ↑(box d n) := by
  ext x
  simp only [Set.mem_preimage, Finset.mem_coe]
  exact signedPerm_mem_box_iff g.1 g.2

/-- The linked part of `T(n)` in the relabelled configuration `g·ω` is the `g`-image of the linked
part of `g⁻¹ T(n)` in `ω`. [cite: GrimmettPercolation1999, §7.2 p. 151 (symmetry)] -/
theorem linked_faceFin_relabel [NeZero d] (g : HOct d) (m n : ℕ) (ω : BondConfig (Site d)) :
    linked (faceFin d n) m n (BondConfig.relabel (sym2Equiv (sp g)) ω) = (linked (piece g n) m n ω).image (sp g) := by
  ext x'
  simp only [mem_linked, Finset.mem_image, mem_faceFin, piece, Finset.mem_filter]
  constructor
  · rintro ⟨hx', y', hy', hc⟩
    refine ⟨(sp g).symm x', ⟨⟨?_, by simpa using hx'⟩, (sp g).symm y', ?_, ?_⟩, by simp⟩
    · rw [← signedPerm_mem_box_iff g.1 g.2]; simpa using (mem_faceFin.2 hx' : x' ∈ faceFin d n) |> fun h => (Finset.mem_filter.1 h).1
    · rw [← signedPerm_mem_box_iff g.1 g.2]; simpa using hy'
    · have := (relabel_mem_openConnIn_iff (sp g) (↑(box d n)) ((sp g).symm y') ((sp g).symm x') ω).1
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, sp_preimage_box] at this
      exact this hc
  · rintro ⟨x, ⟨⟨-, hx⟩, y, hy, hc⟩, rfl⟩
    refine ⟨hx, sp g y, (signedPerm_mem_box_iff g.1 g.2).2 hy, ?_⟩
    rw [relabel_mem_openConnIn_iff (sp g) (↑(box d n)) y x ω, sp_preimage_box]
    exact hc

/-- **Equal laws**: `P_p(ℓ ≤ |V_g(n)|) = P_p(ℓ ≤ |V(n)|)` for every symmetry `g` ("By symmetry",
p. 151). [cite: GrimmettPercolation1999, §7.2 (7.14) p. 151] -/
theorem prob_le_card_linked_piece_eq [NeZero d] (g : HOct d) (m n ℓ : ℕ) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real {ω | ℓ ≤ (linked (piece g n) m n ω).card} =
      (bondPercolation (zdGraph d) p).real {ω | ℓ ≤ (linked (faceFin d n) m n ω).card} := by
  have hpre : BondConfig.relabel (sym2Equiv (spIso g).toEquiv) ⁻¹' {ω | ℓ ≤ (linked (faceFin d n) m n ω).card} =
      {ω | ℓ ≤ (linked (piece g n) m n ω).card} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    change ℓ ≤ (linked (faceFin d n) m n (BondConfig.relabel (sym2Equiv (sp g)) ω)).card ↔ _
    rw [linked_faceFin_relabel, Finset.card_image_of_injective _ (sp g).injective]
  rw [← hpre]
  exact bondPercolation_real_preimage_relabel_iso (spIso g) p _

/-- **(7.14)**: `P_p(ℓ' ≤ |V(n)|) ≥ 1 - P_p(|U(n)| < k ℓ')^{1/k}` with `k = 2^d d!`, by the
square-root trick (FKG) and symmetry. [cite: GrimmettPercolation1999, §7.2 (7.14) p. 151] -/
theorem prob_le_card_linked_faceFin_ge [NeZero d] (m n ℓ' : ℕ) (p : unitInterval) :
    1 - ((bondPercolation (zdGraph d) p).real
        {ω | (bdLinked m n ω).card < Fintype.card (HOct d) * ℓ'}) ^ ((Fintype.card (HOct d) : ℝ)⁻¹) ≤
      (bondPercolation (zdGraph d) p).real {ω | ℓ' ≤ (linked (faceFin d n) m n ω).card} := by
  set μ := bondPercolation (zdGraph d) p
  set k := Fintype.card (HOct d) with hk
  set A : HOct d → Set (BondConfig (Site d)) := fun g => {ω | ℓ' ≤ (linked (piece g n) m n ω).card} with hA
  obtain ⟨g₀, hg₀⟩ := sqrt_trick_holds (zdGraph d) p A (fun g => isUpperSet_le_card_linked _ m n ℓ')
    (fun g => measurableSet_linked _ m n (ℓ' ≤ Finset.card ·))
  rw [show μ.real (A g₀) = μ.real {ω | ℓ' ≤ (linked (faceFin d n) m n ω).card} from
    prob_le_card_linked_piece_eq g₀ m n ℓ' p] at hg₀
  refine le_trans ?_ hg₀
  -- monotonicity in the union probability: `{k ℓ' ≤ |U|} ⊆ ⋃ A_g`
  have hsub : {ω | k * ℓ' ≤ (bdLinked m n ω).card} ⊆ ⋃ g, A g := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    simp only [Set.mem_iUnion, hA, Set.mem_setOf_eq]
    by_contra hall
    push Not at hall
    -- `U ⊆ ⋃_g linked (piece g)`
    have hcover : bdLinked m n ω ⊆ Finset.univ.biUnion fun g : HOct d => linked (piece g n) m n ω := by
      intro x hx
      rw [mem_linked] at hx
      obtain ⟨hxbd, y, hy, hc⟩ := hx
      obtain ⟨g, hg⟩ := exists_sp_mem_facePiece hxbd
      refine Finset.mem_biUnion.2 ⟨g, Finset.mem_univ _, mem_linked.2 ⟨?_, y, hy, hc⟩⟩
      exact Finset.mem_filter.2 ⟨(mem_innerBoundary_iff.1 hxbd).1, hg⟩
    have h1 : (bdLinked m n ω).card ≤ ∑ g : HOct d, (linked (piece g n) m n ω).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h2 : ∑ g : HOct d, (linked (piece g n) m n ω).card ≤ ∑ _g : HOct d, (ℓ' - 1) :=
      Finset.sum_le_sum fun g _ => Nat.le_sub_one_of_lt (hall g)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← hk] at h2
    rcases Nat.eq_zero_or_pos ℓ' with hℓ | hℓ
    · have := hall g₀; omega
    · have hkpos : 0 < k := Fintype.card_pos
      have : k * (ℓ' - 1) < k * ℓ' := (Nat.mul_lt_mul_left hkpos).2 (Nat.sub_lt hℓ one_pos)
      omega
  have hmono : μ.real {ω | k * ℓ' ≤ (bdLinked m n ω).card} ≤ μ.real (⋃ g, A g) := measureReal_mono hsub
  have hcompl : μ.real {ω | (bdLinked m n ω).card < k * ℓ'} = 1 - μ.real {ω | k * ℓ' ≤ (bdLinked m n ω).card} := by
    have : {ω : BondConfig (Site d) | (bdLinked m n ω).card < k * ℓ'} = {ω | k * ℓ' ≤ (bdLinked m n ω).card}ᶜ := by
      ext ω; simp [not_le]
    rw [this, measureReal_compl (measurableSet_linked _ m n (k * ℓ' ≤ Finset.card ·)), probReal_univ]
  rw [hcompl]
  have hk0 : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
  have hx1 : 0 ≤ 1 - μ.real (⋃ g, A g) := sub_nonneg.2 measureReal_le_one
  linarith [Real.rpow_le_rpow hx1 (by linarith : 1 - μ.real (⋃ g, A g) ≤
    1 - μ.real {ω | k * ℓ' ≤ (bdLinked m n ω).card}) hk0]

end GM

end Percolation.Literature
