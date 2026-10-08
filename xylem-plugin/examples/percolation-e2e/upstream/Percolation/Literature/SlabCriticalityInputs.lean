import Percolation.Literature.CriticalContinuityProofs
import Percolation.Literature.FiniteEnergy
import Percolation.Literature.SlabCriticality
import Percolation.Literature.ZeroOneLaw
import Percolation.Util.Linter

/-!
# Critical bond percolation on slabs: the Duminil-Copin–Sidoravicius–Tassion argument, II (DST 2016, §2.2 proved; eq. (1) from the uniqueness of the infinite cluster)

Continuation of `SlabCriticality.lean` (the bottom-up
decomposition of the named fact `DuminilCopinSidoraviciusTassion2016` of `HalfSpace.lean`, DST 2016,
Thm. 1, arXiv:1401.7130), which left three named inputs: eq. (1), the Gluing Lemma 6 and the
renormalisation step of §2.2 (`DuminilCopinSidoraviciusTassion2016_renormalisation`). Here the
renormalisation step is proved and eq. (1) is proved from the uniqueness of the infinite cluster on
slabs, the input DST cite for it; Thm. 1 thus follows from exactly two named facts.

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: §2.1, eq. (1) (= arXiv (2.1), p. 5: "The infinite cluster in `S_k` being
  unique almost surely [AKN87, BK89], one can construct a sequence `(u_n)` …"); §2.2 (journal
  p. 6 = arXiv p. 9: the good edges, `4`-dependence, "there exists `η > 0` such that whenever
  the probability to be good exceeds `1 - η`, the set of good edges percolates (this fact
  follows from a Peierls argument presented for example in [BBW05], or from the classical
  result of [LSS97] …)", "an infinite path of good edges … implies … an infinite path of open
  edges … As a consequence, `q ≥ p_c(k)`").
* M. Aizenman, H. Kesten, C. M. Newman, Comm. Math. Phys. 111 (1987), 505–531; R. M. Burton,
  M. Keane, Comm. Math. Phys. 121 (1989), 501–505 (uniqueness of the infinite cluster; only
  through `DuminilCopinSidoraviciusTassion2016_uniqueCluster`).
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.4 (`θ`, `p_c`; Thm. (1.11): an
  infinite cluster exists a.s. iff `θ > 0`; (1.17)–(1.18): Peierls' argument), §7.3, p. 165
  (zero–one law for the invariant σ-field), §7.4, p. 178, (7.64) (`k`-dependence) and
  Thm. (7.65) (Liggett–Schonmann–Stacey).
* T. M. Liggett, R. H. Schonmann, A. M. Stacey, *Domination by product measures*, Ann. Probab.
  25 (1997), 71–95; P. Balister, B. Bollobás, M. Walters, *Continuum percolation with steps in
  the square or the disc*, Random Structures Algorithms 26 (2005), 392–403 (Peierls argument
  for `k`-dependent bond percolation on `ℤ²`). Both are only cited by DST for the statement
  `DuminilCopinSidoraviciusTassion2016_dependentPercolation`, which is proved here directly.

## Design choices

* The coarse lattice of §2.2 is this library's `Site 2` (so that `percolatesAt`, `zdGraph 2` and
  the dual contours of `DualContours.lean` apply to the good-edge configuration), bridged to
  the planar coordinates `ℤ × ℤ` of `SlabCriticality.lean` by `coarsePt n x = 4n·x`.
* `DuminilCopinSidoraviciusTassion2016_dependentPercolation` renders "`K`-dependent" as:
  events determined by finite edge sets whose vertices are pairwise at sup-distance `≥ K` are
  independent (for the laws of finitely many coordinates this is the definition of Grimmett
  1999, (7.64) / LSS97 up to the choice of metric, and it extends to the generated σ-algebras
  by a π-λ argument), and "percolates" as `μ[0 ↔ ∞] > 0`, which is what stochastic domination
  by a supercritical Bernoulli bond percolation on `ℤ²` delivers, what the Peierls argument
  proves, and what §2.2 uses. It is kept as a `def` with a discharge `…_holds` (the statement
  is the reusable classical fact).
* `DuminilCopinSidoraviciusTassion2016_uniqueCluster` is stated in the paper's regime only
  (`k > 0`, `θ_{S_k}(p) > 0`), in the form `numInfiniteClusters ω ≤ 1` a.s. of
  `Grimmett1999_numInfiniteClusters_le_one` (`Connectivity.lean`, the `ℤ^d` statement).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory Filter LatticeModels

/-! ## §2.2 of DST 2016 decomposed: the good-edge configuration as a dependent bond
percolation on `ℤ²`, and the renormalisation step from a classical dependent-percolation input -/

section Renormalisation

variable (k : ℕ)

/-- The base point `4n · x ∈ ℤ²` of the coarse vertex `x ∈ ℤ²` (the coarse-grained lattice
`4nℤ²` of DST 2016, §2.2). [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
def coarsePt (n : ℕ) (x : Site 2) : ℤ × ℤ := (4 * (n : ℤ) * x 0, 4 * (n : ℤ) * x 1)

/-- `coarsePt` of a lattice neighbour: `4n · (x + eᵢ) = 4n · x + 4n eᵢ`. [folklore] -/
theorem coarsePt_add_single (n : ℕ) (x : Site 2) (i : Fin 2) :
    coarsePt n (x + Pi.single i 1) = coarsePt n x + coarseShift (4 * n) i := by
  fin_cases i <;> simp [coarsePt, coarseShift, mul_add]

/-- **The good-edge configuration** (DST 2016, §2.2: "Call an edge `{z, z'}` of `4nℤ²` good if
…"): the set of nearest-neighbour edges `{x, x + eᵢ}` of the coarse lattice `ℤ² ≅ 4nℤ²` whose
good-edge event `goodEvent k n u (4n·x) i` occurs. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
def coarseConfig (n u : ℕ) (ω : BondConfig (slab 3 k)) : BondConfig (Site 2) :=
  {e | ∃ (x : Site 2) (i : Fin 2), e = s(x, x + Pi.single i 1) ∧ ω ∈ goodEvent k n u (coarsePt n x) i}

/-- Coarse edges have a unique presentation `{x, x + eᵢ}`. [folklore] -/
theorem coarseEdge_eq_iff (x x' : Site 2) (i j : Fin 2) :
    s(x, x + Pi.single i (1 : ℤ)) = s(x', x' + Pi.single j 1) ↔ x = x' ∧ i = j := by
  constructor
  · intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨h1, ?_⟩
      subst h1
      have := congrFun (add_left_cancel h2) i
      fin_cases i <;> fin_cases j <;> simp_all
    · exfalso
      subst h1
      have := congrFun h2 i
      fin_cases i <;> fin_cases j <;> simp at this <;> omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Membership of a coarse edge in the good-edge configuration. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem mk_mem_coarseConfig_iff (n u : ℕ) (ω : BondConfig (slab 3 k)) (x : Site 2) (i : Fin 2) :
    s(x, x + Pi.single i 1) ∈ coarseConfig k n u ω ↔ ω ∈ goodEvent k n u (coarsePt n x) i := by
  constructor
  · rintro ⟨x', j, he, hg⟩
    obtain ⟨rfl, rfl⟩ := (coarseEdge_eq_iff x x' i j).1 he
    exact hg
  · intro h
    exact ⟨x, i, rfl, h⟩

/-- The good-edge event is measurable. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem measurableSet_goodEvent (n u : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    MeasurableSet (goodEvent k n u z i) :=
  measurableSet_of_isLocalEvent_holds (isLocalEvent_goodEvent k n u z i)

/-- The good-edge configuration is a measurable function of the slab configuration.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem measurable_coarseConfig (n u : ℕ) : Measurable (coarseConfig k n u) := by
  refine measurable_set_iff.2 fun e => ?_
  refine measurableSet_setOf.1 ?_
  have : {ω : BondConfig (slab 3 k) | e ∈ coarseConfig k n u ω} =
      ⋃ x : Site 2, ⋃ i : Fin 2, {ω | e = s(x, x + Pi.single i 1) ∧ ω ∈ goodEvent k n u (coarsePt n x) i} := by
    ext ω
    simp only [coarseConfig, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [this]
  refine MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun i => ?_
  by_cases he : e = s(x, x + Pi.single i 1)
  · simp only [he, true_and]
    exact measurableSet_goodEvent k n u _ i
  · simp only [he, false_and, Set.setOf_false]
    exact MeasurableSet.empty

/-- **Translation invariance of the good-edge probability**: every coarse edge of direction `i`
is good with the probability of the origin edge of direction `i` (DST 2016, §2.2: "the
probability to be good"). [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem real_goodEvent_shift (p : unitInterval) (n u : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    (bondPercolation (slabGraph 3 k) p).real (goodEvent k n u z i) =
      (bondPercolation (slabGraph 3 k) p).real (goodEvent k n u 0 i) := by
  rw [← real_preimage_slabRelabel k (planarShift z) (planarAdj_planarShift z) p (goodEvent k n u z i)]
  congr 1
  have e1 : z + coarseShift (2 * n) i = 0 + coarseShift (2 * n) i + z := by abel
  have e2 : z + coarseShift (4 * n) i = 0 + coarseShift (4 * n) i + z := by abel
  have e3 : z = 0 + z := (zero_add z).symm
  unfold goodEvent
  conv_lhs => rw [e1, e2]; rw [show sqBox z u = sqBox (0 + z) u by rw [zero_add],
    show sqBox z (3 * n) = sqBox (0 + z) (3 * n) by rw [zero_add],
    show sqSphere z (3 * n) = sqSphere (0 + z) (3 * n) by rw [zero_add]]
  simp only [← image_planarShift_sqBox z, ← image_planarShift_sqSphere z, Set.preimage_inter,
    preimage_slabRelabel_slabConn, preimage_slabRelabel_slabUniqueConn]

/-- **the classical input of DST 2016, §2.2: dependent bond percolation on `ℤ²`
with high density percolates** (arXiv p. 9: "the set of good edges follows a percolation law
which is `4`-dependent. In particular, there exists `η > 0` such that whenever the probability
to be good exceeds `1 - η`, the set of good edges percolates (this fact follows from a Peierls
argument presented for example in [Balister–Bollobás–Walters 2005], or from the classical
result of [Liggett–Schonmann–Stacey 1997] comparing `4`-dependent percolation to Bernoulli
percolation)"; Grimmett 1999, Thm. (7.65) [= LSS 1997, Thm. 0.0]: a `k`-dependent family of
density `≥ δ` dominates a Bernoulli family of density `π(δ) → 1`, whence — Bernoulli
percolation on `ℤ²` being supercritical near density `1` — the origin lies in an infinite
cluster with positive probability). Stated for `K`-dependent bond percolation measures `μ` on
`ℤ²` (independence of measurable events determined by finite edge sets whose vertices are at
sup-distance `≥ K`) whose nearest-neighbour edges are open with probability `≥ 1 - η`;
"percolates" in the form used: `μ[0 ↔ ∞] > 0`. Users take
`(h : DuminilCopinSidoraviciusTassion2016_dependentPercolation)`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] [cite: GrimmettPercolation1999, Thm. (7.65)] -/
def DuminilCopinSidoraviciusTassion2016_dependentPercolation : Prop :=
  ∀ K : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ (μ : Measure (BondConfig (Site 2))) [IsProbabilityMeasure μ],
    (∀ (F₁ F₂ : Finset (Sym2 (Site 2))),
      (∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ a ∈ e₁, ∀ b ∈ e₂, (K : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1|) →
      ∀ (A B : Set (BondConfig (Site 2))), DeterminedBy A (↑F₁ : Set (Sym2 (Site 2))) →
        DeterminedBy B (↑F₂ : Set (Sym2 (Site 2))) → MeasurableSet A → MeasurableSet B →
        μ (A ∩ B) = μ A * μ B) →
    (∀ e ∈ (zdGraph 2).edgeSet, 1 - η ≤ μ.real {ω | e ∈ ω}) →
    0 < μ.real (percolatesAt (0 : Site 2))

/-! ### From an infinite good cluster to an infinite open cluster (DST 2016, §2.2: "an infinite
path of good edges in the coarse-grained lattice immediately implies the existence of an
infinite path of open edges in the original lattice") -/

/-- `X ⟷^B Y` is symmetric in `X`, `Y`. [folklore] -/
theorem slabConn_comm (B X Y : Set (ℤ × ℤ)) : slabConn k B X Y = slabConn k B Y X := by
  ext ω
  simp only [slabConn, mem_openCrossing_iff]
  constructor <;> rintro ⟨x, hx, y, hy, h⟩ <;> exact ⟨y, hy, x, hx, openConnIn_reverse h⟩

/-- `coarsePt n 0 = 0`. [folklore] -/
@[simp] theorem coarsePt_zero (n : ℕ) : coarsePt n (0 : Site 2) = 0 := by
  simp [coarsePt]

/-- Coordinates of coarse base points dominate the coarse coordinates (`n ≥ 1`). [folklore] -/
theorem abs_le_abs_coarsePt {n : ℕ} (hn : 1 ≤ n) (x : Site 2) :
    |x 0| ≤ |(coarsePt n x).1| ∧ |x 1| ≤ |(coarsePt n x).2| := by
  simp only [coarsePt, abs_mul]
  have h4 : (1 : ℤ) ≤ |(4 : ℤ)| * |(n : ℤ)| := by
    rw [abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 4), abs_of_nonneg (by positivity)]
    omega
  exact ⟨le_mul_of_one_le_left (abs_nonneg _) h4, le_mul_of_one_le_left (abs_nonneg _) h4⟩

/-- Off the origin, the coarse base point is at sup-distance `≥ 4n` from `0`. [folklore] -/
theorem coarsePt_far {n : ℕ} {x : Site 2} (hx : x ≠ 0) :
    4 * (n : ℤ) ≤ |(coarsePt n x).1| ∨ 4 * (n : ℤ) ≤ |(coarsePt n x).2| := by
  have h : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  simp only [coarsePt, abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ 4 * (n : ℤ) by positivity)]
  rcases h with h | h
  · exact Or.inl (le_mul_of_one_le_right (by positivity) (Int.one_le_abs h))
  · exact Or.inr (le_mul_of_one_le_right (by positivity) (Int.one_le_abs h))

/-- A block `S = c + B_u` neighbouring the block at `c'` (at sup-distance `4n`, `u ≤ n`) meets
`c' + B_{3n}` only on its boundary. [folklore] -/
theorem sqBox_shift_inter_subset_sqSphere {n u : ℕ} (hu : u ≤ n) (c : ℤ × ℤ) (i : Fin 2) :
    sqBox (c + coarseShift (4 * n) i) u ∩ sqBox c (3 * n) ⊆ sqSphere c (3 * n) ∧
    sqBox c u ∩ sqBox (c + coarseShift (4 * n) i) (3 * n) ⊆ sqSphere (c + coarseShift (4 * n) i) (3 * n) := by
  constructor
  · rintro w ⟨hw1, hw2⟩
    rw [mem_sqSphere_iff]
    refine ⟨hw2, ?_⟩
    rw [le_abs, le_abs]
    simp only [sqBox, Set.mem_setOf_eq, abs_le, coarseShift] at hw1 hw2
    fin_cases i <;> simp at hw1 hw2 ⊢ <;> omega
  · rintro w ⟨hw1, hw2⟩
    rw [mem_sqSphere_iff]
    refine ⟨hw2, ?_⟩
    rw [le_abs, le_abs]
    simp only [sqBox, Set.mem_setOf_eq, abs_le, coarseShift] at hw1 hw2 ⊢
    fin_cases i <;> simp at hw1 hw2 ⊢ <;> omega

/-- The origin block meets a block `c + B_{3n}` centred at a coarse point `c ≠ 0` only on its
boundary. [folklore] -/
theorem sqBox_zero_inter_subset_sqSphere {n u : ℕ} (hu : u ≤ n) {x : Site 2} (hx : x ≠ 0) :
    sqBox 0 u ∩ sqBox (coarsePt n x) (3 * n) ⊆ sqSphere (coarsePt n x) (3 * n) := by
  rintro w ⟨hw1, hw2⟩
  rw [mem_sqSphere_iff]
  refine ⟨hw2, ?_⟩
  have hfar := coarsePt_far (n := n) hx
  rw [le_abs, le_abs] at hfar ⊢
  simp only [sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hw1 hw2
  omega

/-- **Chaining good edges** (DST 2016, §2.2: "By construction, an infinite path of good edges
in the coarse-grained lattice immediately implies the existence of an infinite path of open
edges in the original lattice"; the mechanism is the gluing-by-uniqueness lemma
`slabConn_of_glue`): if the coarse vertex `y ≠ 0` is joined to `0` by good edges, then
`S̄ = \overline{B_u}` is joined by an open path of the slab to `\overline{4n·y + B_u}` (lattice
configurations). [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem slabConn_of_coarse_reachable {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) {n u : ℕ} (hu : u ≤ n) {y : Site 2}
    (hy : (openGraph (coarseConfig k n u ω)).Reachable 0 y) (hy0 : y ≠ 0) :
    ω ∈ slabConn k Set.univ (sqBox 0 u) (sqBox (coarsePt n y) u) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hy
  suffices h : y = 0 ∨ ω ∈ slabConn k Set.univ (sqBox 0 u) (sqBox (coarsePt n y) u) by tauto
  clear hy0
  induction hy with
  | refl => exact Or.inl rfl
  | @tail b c _ hbc ih =>
    right
    obtain ⟨hmem, -⟩ := (openGraph_adj _ b c).1 hbc
    obtain ⟨x, i, he, hcross, huz, huz'⟩ := hmem
    have hmono : ∀ {B X Y : Set (ℤ × ℤ)}, ω ∈ slabConn k B X Y → ω ∈ slabConn k Set.univ X Y :=
      fun h => openCrossing_mono (slabLift_mono k (Set.subset_univ _)) subset_rfl subset_rfl h
    rw [Sym2.eq_iff] at he
    by_cases hb0 : b = 0
    · -- the first edge of the chain
      subst hb0
      rcases he with ⟨hx, hc⟩ | ⟨hx, hc⟩
      · subst hc
        subst hx
        rw [coarsePt_add_single]
        simpa using hmono hcross
      · subst hc
        have h0 : coarsePt n c + coarseShift (4 * n) i = 0 := by
          rw [← coarsePt_add_single, ← hx, coarsePt_zero]
        rw [h0] at hcross
        rw [slabConn_comm]
        exact hmono hcross
    · -- gluing through the block at `b`
      have hb : ω ∈ slabConn k Set.univ (sqBox 0 u) (sqBox (coarsePt n b) u) := by tauto
      rcases he with ⟨hx, hc⟩ | ⟨hx, hc⟩
      · -- `b = x`, `c = x + eᵢ`
        subst hc
        subst hx
        rw [coarsePt_add_single]
        refine slabConn_of_glue k hω (T := Set.univ) (B₁ := Set.univ)
          (B₂ := sqBox (coarsePt n b + coarseShift (2 * n) i) (6 * n)) (S' := sqBox (coarsePt n b) u)
          (c := coarsePt n b) (m := 3 * n) subset_rfl (Set.subset_univ _) (Set.subset_univ _)
          (sqBox_mono _ (by omega)) (sqBox_zero_inter_subset_sqSphere hu hb0)
          (sqBox_shift_inter_subset_sqSphere hu (coarsePt n b) i).1 hb ?_ huz
        rw [slabConn_comm]
        exact hcross
      · -- `b = x + eᵢ`, `c = x`
        subst hc
        have hcb : coarsePt n b = coarsePt n c + coarseShift (4 * n) i := by
          rw [hx, coarsePt_add_single]
        rw [hcb] at hb
        have hfar : sqBox 0 u ∩ sqBox (coarsePt n c + coarseShift (4 * n) i) (3 * n) ⊆
            sqSphere (coarsePt n c + coarseShift (4 * n) i) (3 * n) := by
          rw [← hcb]; exact sqBox_zero_inter_subset_sqSphere hu hb0
        exact slabConn_of_glue k hω (T := Set.univ) (B₁ := Set.univ)
          (B₂ := sqBox (coarsePt n c + coarseShift (2 * n) i) (6 * n))
          (S' := sqBox (coarsePt n c + coarseShift (4 * n) i) u)
          (c := coarsePt n c + coarseShift (4 * n) i) (m := 3 * n) subset_rfl (Set.subset_univ _)
          (Set.subset_univ _) (sqBox_mono _ (by omega)) hfar
          (sqBox_shift_inter_subset_sqSphere hu (coarsePt n c) i).2 hb hcross huz'

/-- An open path inside `S` is an open path. [folklore] -/
theorem reachable_of_openConnIn {V : Type*} {S : Set V} {ω : BondConfig V} {x y : V}
    (h : ω ∈ openConnIn S x y) : (openGraph ω).Reachable x y := by
  obtain ⟨hx, hy, hr⟩ := h
  exact hr.map (SimpleGraph.Embedding.induce S).toHom

/-- **An infinite good cluster of the origin forces an infinite open cluster meeting `S̄`**
(DST 2016, §2.2, "an infinite path of good edges … implies the existence of an infinite path
of open edges in the original lattice"; here for the cluster of `0` in the coarse
configuration and lattice configurations `ω`). [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem exists_infinite_openCluster_of_coarse {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) {n u : ℕ} (hn : 1 ≤ n) (hu : u ≤ n)
    (hinf : (openCluster (coarseConfig k n u ω) (0 : Site 2)).Infinite) :
    ∃ a ∈ slabLift k (sqBox 0 u), (openCluster ω a).Infinite := by
  by_contra hcon
  push Not at hcon
  have hX0fin : (slabLift k (sqBox 0 u)).Finite := slabLift_finite k (sqBox_finite 0 u)
  have hU : (⋃ a ∈ slabLift k (sqBox 0 u), openCluster ω a).Finite :=
    hX0fin.biUnion fun a ha => hcon a ha
  -- a bound on the planar coordinates of the finitely many clusters
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ v ∈ ⋃ a ∈ slabLift k (sqBox 0 u), openCluster ω a,
      |(planar k v).1| ≤ M ∧ |(planar k v).2| ≤ M := by
    have himg := hU.image fun v => max |(planar k v).1| |(planar k v).2|
    obtain ⟨B, hB⟩ := himg.bddAbove
    refine ⟨B.toNat, fun v hv => ?_⟩
    have h := hB (Set.mem_image_of_mem _ hv)
    have h' : max |(planar k v).1| |(planar k v).2| ≤ (B.toNat : ℤ) := h.trans (Int.self_le_toNat B)
    exact ⟨(le_max_left _ _).trans h', (le_max_right _ _).trans h'⟩
  -- a far coarse vertex in the good cluster of `0`
  obtain ⟨y, hy, hyF⟩ := hinf.exists_notMem_finset (box 2 (M + u))
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hyF
    rw [mem_box]
    intro i
    simp only [Pi.zero_apply]
    push_cast
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := slabConn_of_coarse_reachable k hω hu hy hy0
  have hbU : b ∈ ⋃ a ∈ slabLift k (sqBox 0 u), openCluster ω a :=
    Set.mem_biUnion ha (reachable_of_openConnIn hab)
  obtain ⟨hb1, hb2⟩ := hM b hbU
  -- but `planar b ∈ 4n·y + B_u` is far
  have hyfar : (M : ℤ) + u + 1 ≤ |y 0| ∨ (M : ℤ) + u + 1 ≤ |y 1| := by
    simp only [mem_box, not_forall, not_and_or, not_le] at hyF
    obtain ⟨j, hj⟩ := hyF
    fin_cases j
    · left; rw [le_abs]; simp at hj; omega
    · right; rw [le_abs]; simp at hj; omega
  have hcp := abs_le_abs_coarsePt hn y
  simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq] at hb
  rw [abs_le] at hb1 hb2
  obtain ⟨hb3, hb4⟩ := hb
  rw [abs_le] at hb3 hb4
  rcases hyfar with h | h
  · have h1 : (M : ℤ) + u + 1 ≤ |(coarsePt n y).1| := h.trans hcp.1
    rw [le_abs] at h1
    omega
  · have h1 : (M : ℤ) + u + 1 ≤ |(coarsePt n y).2| := h.trans hcp.2
    rw [le_abs] at h1
    omega

/-! ### The renormalisation step from the dependent-percolation input -/

/-- The slab edges on which the state of the coarse edge `e` depends: for `e = {x, x + eᵢ}`,
the edges inside `\overline{R_n} = \overline{4n·x + 2n eᵢ + B_{6n}}` (none for other pairs).
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
def coarseRegion (n : ℕ) (e : Sym2 (Site 2)) : Set (Sym2 (slab 3 k)) :=
  {d | ∃ (x : Site 2) (i : Fin 2), e = s(x, x + Pi.single i 1) ∧
    d ∈ Set.sym2 (slabLift k (sqBox (coarsePt n x + coarseShift (2 * n) i) (6 * n)))}

/-- Events of the coarse configuration determined by the coarse edges in `F` pull back to
events determined by the slab edges in `⋃_{e ∈ F} coarseRegion e` ("being good depends only on
the state of the edges in a finite box"). [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem determinedBy_preimage_coarseConfig (n u : ℕ) {A : Set (BondConfig (Site 2))}
    {F : Finset (Sym2 (Site 2))} (hA : DeterminedBy A (↑F : Set (Sym2 (Site 2)))) :
    DeterminedBy (coarseConfig k n u ⁻¹' A) (⋃ e ∈ F, coarseRegion k n e) := by
  rw [determinedBy_iff] at hA ⊢
  intro ω ω' h
  have key : ∀ e ∈ F, (e ∈ coarseConfig k n u ω ↔ e ∈ coarseConfig k n u ω') := by
    intro e he
    simp only [coarseConfig, Set.mem_setOf_eq]
    refine exists_congr fun x => exists_congr fun i => and_congr_right fun hex => ?_
    refine (determinedBy_iff _ _).1 (determinedBy_goodEvent k n u (coarsePt n x) i) ω ω' ?_
    have hsub : Set.sym2 (slabLift k (sqBox (coarsePt n x + coarseShift (2 * n) i) (6 * n))) ⊆
        ⋃ e ∈ F, coarseRegion k n e :=
      fun d hd => Set.mem_biUnion (Finset.mem_coe.2 he) ⟨x, i, hex, hd⟩
    calc ω ∩ Set.sym2 (slabLift k (sqBox (coarsePt n x + coarseShift (2 * n) i) (6 * n)))
        = (ω ∩ ⋃ e ∈ F, coarseRegion k n e) ∩
            Set.sym2 (slabLift k (sqBox (coarsePt n x + coarseShift (2 * n) i) (6 * n))) := by
          rw [Set.inter_assoc, Set.inter_eq_right.2 hsub]
      _ = (ω' ∩ ⋃ e ∈ F, coarseRegion k n e) ∩
            Set.sym2 (slabLift k (sqBox (coarsePt n x + coarseShift (2 * n) i) (6 * n))) := by
          rw [h]
      _ = ω' ∩ Set.sym2 (slabLift k (sqBox (coarsePt n x + coarseShift (2 * n) i) (6 * n))) := by
          rw [Set.inter_assoc, Set.inter_eq_right.2 hsub]
  simp only [Set.mem_preimage]
  apply hA
  ext e
  simp only [Set.mem_inter_iff, Finset.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(key e h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(key e h2).2 h1, h2⟩

/-- **`4`-dependence** (DST 2016, §2.2: "the set of good edges follows a percolation law which
is `4`-dependent"): coarse edges whose vertices are at sup-distance `≥ 5` depend on disjoint
sets of slab edges. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem disjoint_coarseRegion {n : ℕ} (hn : 1 ≤ n) {F₁ F₂ : Finset (Sym2 (Site 2))}
    (hfar : ∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ a ∈ e₁, ∀ b ∈ e₂, (5 : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1|) :
    Disjoint (⋃ e ∈ F₁, coarseRegion k n e) (⋃ e ∈ F₂, coarseRegion k n e) := by
  rw [Set.disjoint_left]
  intro d hd1 hd2
  simp only [Set.mem_iUnion, coarseRegion, Set.mem_setOf_eq, exists_prop] at hd1 hd2
  obtain ⟨e₁, he₁, x₁, i₁, hex₁, hd₁⟩ := hd1
  obtain ⟨e₂, he₂, x₂, i₂, hex₂, hd₂⟩ := hd2
  have h5 := hfar e₁ he₁ e₂ he₂ x₁ (by rw [hex₁]; exact Sym2.mem_mk_left _ _) x₂
    (by rw [hex₂]; exact Sym2.mem_mk_left _ _)
  obtain ⟨v, hv⟩ : ∃ v, v ∈ d := ⟨d.out.1, Sym2.out_fst_mem d⟩
  have hv₁ : v ∈ slabLift k _ := Set.mem_sym2_iff_subset.1 hd₁ hv
  have hv₂ : v ∈ slabLift k _ := Set.mem_sym2_iff_subset.1 hd₂ hv
  simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_add, Prod.snd_add,
    coarseShift] at hv₁ hv₂
  have e1 : (coarsePt n x₁).1 - (coarsePt n x₂).1 = 4 * n * (x₁ 0 - x₂ 0) := by
    simp only [coarsePt]; ring
  have e2 : (coarsePt n x₁).2 - (coarsePt n x₂).2 = 4 * n * (x₁ 1 - x₂ 1) := by
    simp only [coarsePt]; ring
  have hcp : 5 * (4 * (n : ℤ)) ≤ |(coarsePt n x₁).1 - (coarsePt n x₂).1| ∨
      5 * (4 * (n : ℤ)) ≤ |(coarsePt n x₁).2 - (coarsePt n x₂).2| := by
    rcases le_max_iff.1 h5 with h | h
    · left
      rw [e1, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 4 * n)]
      have := mul_le_mul_of_nonneg_left h (show (0 : ℤ) ≤ 4 * n by positivity)
      linarith
    · right
      rw [e2, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 4 * n)]
      have := mul_le_mul_of_nonneg_left h (show (0 : ℤ) ≤ 4 * n by positivity)
      linarith
  rw [le_abs, le_abs] at hcp
  fin_cases i₁ <;> fin_cases i₂ <;> simp at hv₁ hv₂ <;> omega

/-- With no open edges, no coarse edge is good (`n ≥ 1`, `u ≤ n`: the two blocks are disjoint).
[folklore] -/
theorem empty_notMem_goodEvent {n u : ℕ} (hn : 1 ≤ n) (hu : u ≤ n) (i : Fin 2) :
    (∅ : BondConfig (slab 3 k)) ∉ goodEvent k n u 0 i := by
  rintro ⟨⟨x, hx, y, hy, hxy⟩, -⟩
  have hpath := mem_openConnIn_iff_pathIn.1 hxy
  have hxy' : x = y := by
    obtain ⟨-, hr⟩ := hpath
    induction hr with
    | refl => rfl
    | tail _ hbc _ =>
      exfalso
      have := (openGraph_adj (∅ : BondConfig (slab 3 k)) _ _).1 hbc.1
      exact this.1
  subst hxy'
  simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_add, Prod.snd_add,
    Prod.fst_zero, Prod.snd_zero, sub_zero, coarseShift] at hx hy
  fin_cases i <;> simp at hy <;> omega

/-! ### From `θ_a(q) > 0` at some vertex to `p_c ≤ q` -/

/-- The vertex of height `h ≤ k` over the planar point `z`. [folklore] -/
def slabVertex (z : ℤ × ℤ) (h : ℕ) (hh : (h : ℤ) ≤ k) : slab 3 k :=
  ⟨![h, z.1, z.2], ⟨by simp, hh⟩⟩

/-- Every vertex of the slab is a `slabVertex`. [folklore] -/
theorem eq_slabVertex (a : slab 3 k) :
    ∃ (h : ℕ) (hh : (h : ℤ) ≤ k), a = slabVertex k (planar k a) h hh := by
  refine ⟨(a.1 0).toNat, ?_, ?_⟩
  · have := a.2.2; have h0 := a.2.1; rw [Int.toNat_of_nonneg h0]; exact this
  · apply Subtype.ext
    funext j
    fin_cases j
    · simp [slabVertex, Int.toNat_of_nonneg a.2.1]
    · simp [slabVertex, planar]
    · simp [slabVertex, planar]

/-- The origin of the slab is the base vertex over `0`. [folklore] -/
theorem slabOrigin_eq_baseVertex : slabOrigin 3 k = baseVertex k 0 := by
  apply Subtype.ext
  funext j
  fin_cases j <;> rfl

/-- Climbing in the full configuration: the base vertex over `z ∈ T` is joined inside `T̄` to
every vertex over `z`. [folklore] -/
theorem edgeSet_openConnIn_climb {T : Set (ℤ × ℤ)} {z : ℤ × ℤ} (hz : z ∈ T) :
    ∀ (h : ℕ) (hh : (h : ℤ) ≤ k),
      (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k T) (baseVertex k z) (slabVertex k z h hh) := by
  intro h
  induction h with
  | zero =>
    intro hh
    have : slabVertex k z 0 hh = baseVertex k z := Subtype.ext (by funext j; fin_cases j <;> rfl)
    rw [this, mem_openConnIn_iff_pathIn]
    exact PathIn.refl (by simpa using hz)
  | succ h ih =>
    intro hh
    have hh' : ((h : ℕ) : ℤ) ≤ k := by push_cast at hh ⊢; omega
    refine SlabCriticality.openConnIn_trans (ih hh') ?_
    rw [mem_openConnIn_iff_pathIn]
    refine PathIn.of_adj ?_ ?_ ?_
    · show planar k (slabVertex k z h hh') ∈ T
      simpa [planar, slabVertex] using hz
    · show planar k (slabVertex k z (h + 1) hh) ∈ T
      simpa [planar, slabVertex] using hz
    · rw [openGraph_adj]
      have hadj : (slabGraph 3 k).Adj (slabVertex k z h hh') (slabVertex k z (h + 1) hh) := by
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
        rw [zdGraph_three_adj_iff]
        right
        simp [slabVertex]
      exact ⟨(SimpleGraph.mem_edgeSet _).2 hadj, hadj.ne⟩

/-- Base paths in the full configuration: the origin base vertex is joined inside
`\overline{B_M}` to the base vertex over any `z ∈ B_M`. [folklore] -/
theorem edgeSet_openConnIn_baseVertex (M : ℕ) (z : ℤ × ℤ) (hz : z ∈ sqBox 0 M) :
    (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 M)) (baseVertex k 0)
      (baseVertex k z) := by
  obtain ⟨hz1, hz2⟩ := hz
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le] at hz1 hz2
  -- horizontal leg from `(0,0)` to `(z.1, 0)`
  have hleg1 : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 M)) (baseVertex k 0)
      (baseVertex k (z.1, 0)) := by
    rcases le_or_gt 0 z.1 with h0 | h0
    · have h := edgeSet_openConnIn_horizontal k (T := sqBox 0 M) 0 0 z.1.toNat (fun j hj => by
        simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]; omega)
      have e : ((0 : ℤ) + (z.1.toNat : ℕ), (0 : ℤ)) = (z.1, 0) := by
        simp only [Prod.mk.injEq, and_true]; omega
      rw [e] at h
      exact h
    · have h := edgeSet_openConnIn_horizontal k (T := sqBox 0 M) z.1 0 (-z.1).toNat (fun j hj => by
        simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]; omega)
      have e : (z.1 + ((-z.1).toNat : ℕ), (0 : ℤ)) = (0, 0) := by
        simp only [Prod.mk.injEq, and_true]; omega
      rw [e] at h
      exact openConnIn_reverse h
  -- vertical leg from `(z.1, 0)` to `z`
  have hleg2 : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 M)) (baseVertex k (z.1, 0))
      (baseVertex k z) := by
    rcases le_or_gt 0 z.2 with h0 | h0
    · have h := edgeSet_openConnIn_vertical k (T := sqBox 0 M) z.1 0 z.2.toNat (fun j hj => by
        simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]; omega)
      have e : (z.1, (0 : ℤ) + (z.2.toNat : ℕ)) = z := by
        ext <;> simp; omega
      rw [e] at h
      exact h
    · have h := edgeSet_openConnIn_vertical k (T := sqBox 0 M) z.1 z.2 (-z.2).toNat (fun j hj => by
        simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]; omega)
      have e : (z.1, z.2 + ((-z.2).toNat : ℕ)) = (z.1, 0) := by
        simp only [Prod.mk.injEq, true_and]; omega
      have e' : (z.1, z.2) = z := rfl
      rw [e, e'] at h
      exact openConnIn_reverse h
  exact SlabCriticality.openConnIn_trans hleg1 hleg2

/-- **`θ_a(q) > 0` at some vertex gives `θ_0(q) > 0` at the origin** (`q > 0`; Grimmett 1999,
§1.4 / Thm. (2.8): `p_c` is independent of the choice of origin — here by Harris' inequality:
`P[0 ↔ ∞] ≥ P[all edges of a fixed finite box open] · P[a ↔ ∞] > 0`).
[cite: GrimmettPercolation1999, §1.4 (1.9) and Thm. 2.4 (Harris)] -/
theorem theta_slabOrigin_pos_of_percolatesAt {q : unitInterval} (hq : 0 < (q : ℝ)) (a : slab 3 k)
    (ha : 0 < (bondPercolation (slabGraph 3 k) q).real (percolatesAt a)) :
    0 < theta (slabGraph 3 k) (slabOrigin 3 k) q := by
  set P := bondPercolation (slabGraph 3 k) q with hP
  -- a finite box containing `0` and `planar a`
  set M : ℕ := (max |(planar k a).1| |(planar k a).2|).toNat with hM
  have haM : planar k a ∈ sqBox 0 M := by
    have h1 : |(planar k a).1| ≤ (M : ℤ) := by
      rw [hM, Int.toNat_of_nonneg (le_max_of_le_left (abs_nonneg _))]; exact le_max_left _ _
    have h2 : |(planar k a).2| ≤ (M : ℤ) := by
      rw [hM, Int.toNat_of_nonneg (le_max_of_le_left (abs_nonneg _))]; exact le_max_right _ _
    simpa [sqBox] using And.intro h1 h2
  -- the full configuration joins the origin to `a` inside the box
  obtain ⟨h, hh, hah⟩ := eq_slabVertex k a
  have hfull : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 M)) (slabOrigin 3 k) a := by
    rw [slabOrigin_eq_baseVertex]
    have h1 := edgeSet_openConnIn_baseVertex k M (planar k a) haM
    have h2 := edgeSet_openConnIn_climb k (T := sqBox 0 M) haM h hh
    rw [← hah] at h2
    exact SlabCriticality.openConnIn_trans h1 h2
  -- the cylinder `A`: all lattice edges of the box are open
  have hFfin : ((slabGraph 3 k).edgeSet ∩ Set.sym2 (slabLift k (sqBox 0 M))).Finite :=
    (finite_sym2 (slabLift_finite k (sqBox_finite 0 M))).inter_of_right _
  set F := hFfin.toFinset with hF
  set A : Set (BondConfig (slab 3 k)) := {ω | ∀ e ∈ F, e ∈ ω} with hA
  have hAcyl : A = localCylinder (↑F : Set (Sym2 (slab 3 k))) ↑F := by
    ext ω
    simp only [hA, localCylinder, Set.mem_setOf_eq, Finset.mem_coe]
    exact forall₂_congr fun e he => (iff_true_right he).symm
  have hAm : MeasurableSet A := by
    rw [hAcyl]; exact measurableSet_localCylinder F.finite_toSet.countable _
  have hAup : IsUpperSet A := fun ω ω' hle hω e he => hle (hω e he)
  have hApos : 0 < P.real A := by
    rw [hAcyl, hP, show bondPercolation (slabGraph 3 k) q =
      ProbabilityTheory.setBernoulli (slabGraph 3 k).edgeSet q from rfl,
      Russo.setBernoulli_real_localCylinder]
    refine Finset.prod_pos fun e he => ?_
    have heE : e ∈ (slabGraph 3 k).edgeSet := ((hFfin.mem_toFinset).1 he).1
    have heF : e ∈ (↑F : Set (Sym2 (slab 3 k))) := he
    simp only [Russo.weight, heF, heE, if_true]
    exact hq
  -- `A ⊆ {0 ↔ a in the box}`
  have hAconn : A ⊆ openConnIn (slabLift k (sqBox 0 M)) (slabOrigin 3 k) a := by
    intro ω hω
    have hcongr : (slabGraph 3 k).edgeSet ∩ Set.sym2 (slabLift k (sqBox 0 M)) ∈
        openConnIn (slabLift k (sqBox 0 M)) (slabOrigin 3 k) a := by
      refine (openConnIn_congr (fun e he => ?_) _ _).1 hfull
      simp [he]
    refine isUpperSet_openConnIn _ _ _ (fun e he => ?_) hcongr
    exact hω e ((hFfin.mem_toFinset).2 he)
  -- Harris and the inclusion `A ∩ {a ↔ ∞} ⊆ {0 ↔ ∞}`
  have hincl : A ∩ percolatesAt a ⊆ percolatesAt (slabOrigin 3 k) := by
    rintro ω ⟨hωA, hωa⟩
    have hr : (openGraph ω).Reachable (slabOrigin 3 k) a := reachable_of_openConnIn (hAconn hωA)
    refine Set.Infinite.mono (fun y hy => ?_) hωa
    exact hr.trans hy
  have hHarris := harris_fkg_holds (slabGraph 3 k) q hAup (isUpperSet_percolatesAt a) hAm
    (measurableSet_percolatesAt_holds a)
  have hmono : P.real (A ∩ percolatesAt a) ≤ P.real (percolatesAt (slabOrigin 3 k)) :=
    measureReal_mono hincl
  have hprod : 0 < P.real A * P.real (percolatesAt a) := mul_pos hApos ha
  unfold theta
  linarith

/-- **the renormalisation step of DST 2016, §2.2, from the dependent-percolation
input** `DuminilCopinSidoraviciusTassion2016_dependentPercolation`: the good-edge
configuration is the image of `P_q` under a measurable map, `4`-dependent
(`disjoint_coarseRegion`, `bondPercolation_inter_of_disjoint` of `FiniteEnergy.lean`) with
all edge densities equal to those of the two origin edges (`real_goodEvent_shift`); if it
percolates, "an infinite path of good edges … implies … an infinite path of open edges"
(`exists_infinite_openCluster_of_coarse`), so `θ_a(q) > 0` for some `a ∈ S̄`, whence
`θ_0(q) > 0` (`theta_slabOrigin_pos_of_percolatesAt`) and "`q ≥ p_c(k)`".
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem DuminilCopinSidoraviciusTassion2016_renormalisation_of_dependentPercolation
    (hD : DuminilCopinSidoraviciusTassion2016_dependentPercolation) :
    DuminilCopinSidoraviciusTassion2016_renormalisation := by
  intro k hk
  obtain ⟨η, hη, hD5⟩ := hD 5
  refine ⟨min η 1, lt_min hη one_pos, ?_⟩
  intro n u hn hu q hgood
  set P := bondPercolation (slabGraph 3 k) q with hP
  -- `q > 0`
  have hq0 : 0 < (q : ℝ) := by
    rcases eq_or_lt_of_le q.2.1 with h0 | h0
    · exfalso
      have hq : q = 0 := Subtype.ext h0.symm
      have h1 := hgood 0
      have hzero : P.real (goodEvent k n u 0 0) = 0 := by
        rw [hP, hq, show bondPercolation (slabGraph 3 k) 0 =
          ProbabilityTheory.setBernoulli (slabGraph 3 k).edgeSet 0 from rfl,
          ProbabilityTheory.setBernoulli_zero, measureReal_def,
          Measure.dirac_apply' _ (measurableSet_goodEvent k n u 0 0),
          Set.indicator_of_notMem (empty_notMem_goodEvent k hn hu 0)]
        simp
      have : min η 1 ≤ 1 := min_le_right _ _
      linarith
    · exact h0
  -- the good-edge configuration as a dependent bond percolation on `ℤ²`
  set μ := P.map (coarseConfig k n u) with hμ
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_coarseConfig k n u).aemeasurable
  have hdep : ∀ (F₁ F₂ : Finset (Sym2 (Site 2))),
      (∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ a ∈ e₁, ∀ b ∈ e₂, ((5 : ℕ) : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1|) →
      ∀ (A B : Set (BondConfig (Site 2))), DeterminedBy A (↑F₁ : Set (Sym2 (Site 2))) →
        DeterminedBy B (↑F₂ : Set (Sym2 (Site 2))) → MeasurableSet A → MeasurableSet B →
        μ (A ∩ B) = μ A * μ B := by
    intro F₁ F₂ hfar A B hA hB hAm hBm
    rw [hμ, Measure.map_apply (measurable_coarseConfig k n u) (hAm.inter hBm),
      Measure.map_apply (measurable_coarseConfig k n u) hAm,
      Measure.map_apply (measurable_coarseConfig k n u) hBm, Set.preimage_inter]
    exact bondPercolation_inter_of_disjoint (slabGraph 3 k) q
      (disjoint_coarseRegion k hn (by exact_mod_cast hfar))
      (determinedBy_preimage_coarseConfig k n u hA) (determinedBy_preimage_coarseConfig k n u hB)
      (hAm.preimage (measurable_coarseConfig k n u)) (hBm.preimage (measurable_coarseConfig k n u))
  have hmarg : ∀ e ∈ (zdGraph 2).edgeSet, 1 - η ≤ μ.real {ω | e ∈ ω} := by
    intro e he
    have hη1 : min η 1 ≤ η := min_le_left _ _
    have key : ∀ (x : Site 2) (i : Fin 2),
        1 - η ≤ μ.real {ω : BondConfig (Site 2) | s(x, x + Pi.single i 1) ∈ ω} := by
      intro x i
      rw [hμ, map_measureReal_apply (measurable_coarseConfig k n u) (measurableSet_mem _)]
      have hpre : coarseConfig k n u ⁻¹' {ω : BondConfig (Site 2) | s(x, x + Pi.single i 1) ∈ ω} =
          goodEvent k n u (coarsePt n x) i := by
        ext ω; exact mk_mem_coarseConfig_iff k n u ω x i
      rw [hpre, hP, real_goodEvent_shift]
      have h1 := hgood i
      linarith
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨i, hab | hab⟩ := (zdGraph_adj_iff a b).1 he
      · rw [hab]; exact key a i
      · rw [hab, Sym2.eq_swap]; exact key b i
  -- percolation of the good edges, transferred to the slab
  have hperc := hD5 μ hdep hmarg
  rw [hμ, map_measureReal_apply (measurable_coarseConfig k n u) (measurableSet_percolatesAt_holds 0)]
    at hperc
  have hle : P.real (coarseConfig k n u ⁻¹' percolatesAt 0) ≤
      P.real (⋃ a ∈ slabLift k (sqBox 0 u), percolatesAt a) := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := (slabGraph 3 k).edgeSet)
      (p := q)] with ω hω hmem
    obtain ⟨a, ha, hinf⟩ := exists_infinite_openCluster_of_coarse k hω hn hu hmem
    exact Set.mem_biUnion ha hinf
  obtain ⟨a, -, hθa⟩ : ∃ a ∈ slabLift k (sqBox 0 u), 0 < P.real (percolatesAt a) := by
    by_contra hcon
    push Not at hcon
    have hnull : P (⋃ a ∈ slabLift k (sqBox 0 u), percolatesAt a) = 0 := by
      refine (measure_biUnion_null_iff (slabLift_finite k (sqBox_finite 0 u)).countable).2
        fun a ha => ?_
      have := hcon a ha
      have h0 : P.real (percolatesAt a) = 0 := le_antisymm this measureReal_nonneg
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h0
    have : P.real (⋃ a ∈ slabLift k (sqBox 0 u), percolatesAt a) = 0 := by
      rw [measureReal_def, hnull]; simp
    linarith
  -- conclusion
  exact criticalProb_le_of_theta_pos (slabGraph 3 k) (slabOrigin 3 k) q
    (theta_slabOrigin_pos_of_percolatesAt k hq0 a hθa)

end Renormalisation

/-! ## Eq. (1) of DST 2016 from the uniqueness of the infinite cluster
("The infinite cluster in `S_k` being unique almost surely [AKN87, BK89], one can construct a
sequence `(u_n)` such that `u_n ≤ n/3` and `lim_n P_p[B_{u_n} ⟷^{!B_n!} ∂B_n] = 1`", §2.1, p. 4) -/

section UniquenessInput

open unitInterval

variable (k : ℕ)

/-- — **uniqueness of the infinite open cluster on slabs** (DST 2016, §2.1,
p. 4 = arXiv p. 5: "The infinite cluster in `S_k` being unique almost surely [AKN87, BK89]";
Aizenman–Kesten–Newman 1987 and Burton–Keane 1989: a translation-invariant finite-energy
percolation on an amenable lattice has at most one infinite cluster). In the paper's regime —
`k > 0` and `p` with `P_p[0 ↔ ∞ in S_k] > 0` (§2: "we fix `p` and `k` and we assume that
`P_p[0 ↔ ∞] > 0`") — `P_p`-almost surely nearest-neighbour bond percolation on the slab
`S_k = {x ∈ ℤ³ | 0 ≤ x₀ ≤ k}` has at most one infinite open cluster (the form of
`Grimmett1999_numInfiniteClusters_le_one` of `Connectivity.lean`, there for `ℤ^d`; for
`θ = 0` the bound is elementary and not part of the fact).
Users take `(h : DuminilCopinSidoraviciusTassion2016_uniqueCluster)`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 4)] -/
def DuminilCopinSidoraviciusTassion2016_uniqueCluster : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∀ᵐ ω ∂(bondPercolation (slabGraph 3 k) p), numInfiniteClusters ω ≤ 1

/-- Pairwise form of "at most one infinite cluster": two vertices with infinite open clusters
are joined by an open path. [folklore] -/
theorem reachable_of_numInfiniteClusters_le_one {V : Type*} {ω : BondConfig V}
    (h : numInfiniteClusters ω ≤ 1) {a b : V} (ha : (openCluster ω a).Infinite)
    (hb : (openCluster ω b).Infinite) : (openGraph ω).Reachable a b := by
  have hsupp : ∀ x : V, ((openGraph ω).connectedComponentMk x).supp = openCluster ω x := by
    intro x
    ext y
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      openCluster, Set.mem_setOf_eq]
    exact SimpleGraph.reachable_comm
  have hmem : ∀ x : V, (openCluster ω x).Infinite →
      (openGraph ω).connectedComponentMk x ∈
        {C : (openGraph ω).ConnectedComponent | C.supp.Infinite} := by
    intro x hx
    simpa only [Set.mem_setOf_eq, hsupp] using hx
  have heq := (Set.encard_le_one_iff.1 h) _ _ (hmem a ha) (hmem b hb)
  exact SimpleGraph.ConnectedComponent.exact heq

/-! ### The zero–one law on the slab: an infinite open cluster exists almost surely -/

/-- `P_p = P^{setOf}` on any graph: the coordinate encoding `q ↦ {e | q e}` carries the product
of the one-edge laws to `bondPercolation` (Mathlib's `setBernoulli_eq_map`; the `ℤ^d` copy is
`measurePreserving_setOf_bondPercolation` of `ZeroOneLaw.lean`). [folklore] -/
theorem measurePreserving_setOf_bondPercolation' {V : Type*} (G : SimpleGraph V)
    (p : unitInterval) :
    MeasurePreserving (fun q : Sym2 V → Prop => {i | q i})
      (Measure.infinitePi fun e : Sym2 V =>
        toNNReal p • Measure.dirac (e ∈ G.edgeSet) + toNNReal (σ p) • Measure.dirac False)
      (bondPercolation G p) :=
  ⟨measurable_setOf, by rw [bondPercolation, ProbabilityTheory.setBernoulli_eq_map]⟩

/-- A map with an additive integer "drift" `c ≠ 0` along a functional eventually moves every
finite set off itself (the mechanism of `exists_iterate_sym2Map_add_notMem` of
`ZeroOneLaw.lean`). [folklore] -/
theorem exists_iterate_notMem_of_drift {α : Type*} (f : α → α) (φ : α → ℤ) {c : ℤ} (hc : c ≠ 0)
    (hφ : ∀ a, φ (f a) = φ a + c) (s : Finset α) : ∃ n : ℕ, ∀ a ∈ s, f^[n] a ∉ s := by
  classical
  have hiter : ∀ (n : ℕ) (a : α), φ (f^[n] a) = φ a + n * c := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih => intro a; rw [Function.iterate_succ_apply', hφ, ih]; push_cast; ring
  let M : ℕ := s.sup fun a => (φ a).natAbs
  have hM : ∀ a ∈ s, |φ a| ≤ M := by
    intro a ha
    have h : (φ a).natAbs ≤ M := Finset.le_sup (f := fun a => (φ a).natAbs) ha
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  refine ⟨2 * M + 1, fun a ha hmem => ?_⟩
  have h1 := hM a ha
  have h2 := hM _ hmem
  rw [hiter] at h2
  have hc1 : 1 ≤ |c| := Int.one_le_abs hc
  have h3 : |((2 * M + 1 : ℕ) : ℤ) * c| ≤ 2 * M := by
    calc |((2 * M + 1 : ℕ) : ℤ) * c| = |(φ a + ((2 * M + 1 : ℕ) : ℤ) * c) - φ a| := by ring_nf
      _ ≤ |φ a + ((2 * M + 1 : ℕ) : ℤ) * c| + |φ a| := abs_sub _ _
      _ ≤ M + M := add_le_add h2 h1
      _ = 2 * M := by ring
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((2 * M + 1 : ℕ) : ℤ))] at h3
  push_cast at h3
  nlinarith

/-- The edge translation of the slab by `-v` drifts the functional `s(x, y) ↦ x_j + y_j` of the
planar coordinate `j` by `-2 v_j`. [folklore] -/
theorem exists_iterate_slabShift_notMem {v : ℤ × ℤ} (hv : v ≠ 0) (s : Finset (Sym2 (slab 3 k))) :
    ∃ n : ℕ, ∀ e ∈ s, (⇑(sym2Equiv (slabEquiv k (planarShift v))).symm)^[n] e ∉ s := by
  by_cases h1 : v.1 ≠ 0
  · refine exists_iterate_notMem_of_drift _
      (Sym2.lift ⟨fun x y => (planar k x).1 + (planar k y).1, fun x y => add_comm _ _⟩)
      (c := -(2 * v.1)) (by omega) (fun e => ?_) s
    induction e using Sym2.ind with
    | h x y =>
      rw [sym2Equiv_symm, sym2Equiv_apply, Sym2.map_mk, Sym2.lift_mk, Sym2.lift_mk]
      simp [planarShift, Equiv.addRight_symm]
      ring
  · have h2 : v.2 ≠ 0 := by
      intro h2
      apply hv
      push Not at h1
      exact Prod.ext h1 h2
    refine exists_iterate_notMem_of_drift _
      (Sym2.lift ⟨fun x y => (planar k x).2 + (planar k y).2, fun x y => add_comm _ _⟩)
      (c := -(2 * v.2)) (by omega) (fun e => ?_) s
    induction e using Sym2.ind with
    | h x y =>
      rw [sym2Equiv_symm, sym2Equiv_apply, Sym2.map_mk, Sym2.lift_mk, Sym2.lift_mk]
      simp [planarShift, Equiv.addRight_symm]
      ring

/-- **Planar translations act ergodically on bond percolation of the slab** (the slab copy of
`ergodic_relabel_shift_bondPercolation` of `ZeroOneLaw.lean`, Grimmett 1999, §7.3, p. 165:
"the zero–one law for the invariant σ-field of a family of independent random variables indexed
by `ℤ²`"): for `v ≠ 0` the relabelling `slabRelabel k (planarShift v)` is `Ergodic` for `P_p`.
[cite: GrimmettPercolation1999, §7.3 (p. 165, zero–one law for the invariant σ-field)] -/
theorem ergodic_slabRelabel_shift (p : unitInterval) {v : ℤ × ℤ} (hv : v ≠ 0) :
    Ergodic (slabRelabel k (planarShift v)) (bondPercolation (slabGraph 3 k) p) := by
  classical
  set μ : Sym2 (slab 3 k) → Measure Prop := fun e =>
    toNNReal p • Measure.dirac (e ∈ (slabGraph 3 k).edgeSet) + toNNReal (σ p) • Measure.dirac False
    with hμ
  set g : Sym2 (slab 3 k) → Sym2 (slab 3 k) := ⇑(sym2Equiv (slabEquiv k (planarShift v))).symm
    with hg
  have herg : Ergodic (coordShift (X := Prop) g) (Measure.infinitePi μ) := by
    refine ergodic_coordShift_infinitePi μ (sym2Equiv (slabEquiv k (planarShift v))).symm.injective
      (fun e => ?_) fun s => ?_
    · have he : (g e ∈ (slabGraph 3 k).edgeSet) = (e ∈ (slabGraph 3 k).edgeSet) := by
        rw [hg, sym2Equiv_symm]
        exact propext (sym2Equiv_mem_edgeSet_iff
          (slabIso k (planarShift v) (planarAdj_planarShift v)).symm e)
      simp only [hμ, he]
    · rw [hg]
      exact exists_iterate_slabShift_notMem k hv s
  refine (measurePreserving_setOf_bondPercolation' (slabGraph 3 k) p).ergodic_of_ergodic_semiconj
    herg (slabRelabel k (planarShift v)).measurable fun q => ?_
  ext e
  rw [BondConfig.mem_relabel_iff]
  rfl

/-- The event "some open cluster is infinite". [folklore] -/
def existsInfiniteCluster : Set (BondConfig (slab 3 k)) := ⋃ a : slab 3 k, percolatesAt a

/-- `existsInfiniteCluster` is measurable. [folklore] -/
theorem measurableSet_existsInfiniteCluster : MeasurableSet (existsInfiniteCluster k) :=
  MeasurableSet.iUnion fun a => measurableSet_percolatesAt_holds a

/-- Relabelling along a bijection `φ` of the vertices transports open paths (the graph
homomorphism `v ↦ φ v` between the open graphs, `openGraph_relabel_adj_iff`). [folklore] -/
theorem reachable_relabel {V W : Type*} (φ : V ≃ W) (ω : BondConfig V) {x y : V}
    (h : (openGraph ω).Reachable x y) :
    (openGraph (BondConfig.relabel (sym2Equiv φ) ω)).Reachable (φ x) (φ y) :=
  h.map { toFun := φ, map_rel' := fun {a b} hab => (openGraph_relabel_adj_iff φ ω a b).2 hab }

/-- Relabelling along a bijection `φ` of the vertices maps open clusters to open clusters:
`C_{φ·ω}(φ a) = φ '' C_ω(a)`. [folklore] -/
theorem openCluster_relabel {V W : Type*} (φ : V ≃ W) (ω : BondConfig V) (a : V) :
    openCluster (BondConfig.relabel (sym2Equiv φ) ω) (φ a) = φ '' openCluster ω a := by
  ext w
  simp only [openCluster, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
    have h' := reachable_relabel φ.symm (BondConfig.relabel (sym2Equiv φ) ω) h
    rwa [relabel_symm_relabel, Equiv.symm_apply_apply] at h'
  · rintro ⟨y, hy, rfl⟩
    exact reachable_relabel φ ω hy

/-- `existsInfiniteCluster` is invariant under every planar relabelling of the slab. [folklore] -/
theorem preimage_slabRelabel_existsInfiniteCluster (g : ℤ × ℤ ≃ ℤ × ℤ) :
    slabRelabel k g ⁻¹' existsInfiniteCluster k = existsInfiniteCluster k := by
  ext ω
  simp only [existsInfiniteCluster, Set.mem_preimage, Set.mem_iUnion, percolatesAt,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(slabEquiv k g).symm b, ?_⟩
    have h := openCluster_relabel (slabEquiv k g) ω ((slabEquiv k g).symm b)
    rw [Equiv.apply_symm_apply] at h
    change (openCluster (BondConfig.relabel (sym2Equiv (slabEquiv k g)) ω) b).Infinite at hb
    rw [h] at hb
    exact Set.Infinite.of_image _ hb
  · rintro ⟨a, ha⟩
    refine ⟨slabEquiv k g a, ?_⟩
    change (openCluster (BondConfig.relabel (sym2Equiv (slabEquiv k g)) ω) (slabEquiv k g a)).Infinite
    rw [openCluster_relabel]
    exact ha.image (slabEquiv k g).injective.injOn

/-- **An infinite open cluster exists almost surely when `θ > 0`** (Grimmett 1999, §1.4,
Thm. (1.11): `ψ(p) = P_p(∃` an infinite open cluster`) = 1` if `θ(p) > 0`; here on the slab, by
the zero–one law for the translation-invariant event `existsInfiniteCluster` and
`P_p[∃ ∞ cluster] ≥ θ(p) > 0`). [cite: GrimmettPercolation1999, §1.4 Thm. (1.11)] -/
theorem bondPercolation_existsInfiniteCluster_eq_one {p : unitInterval}
    (hθ : 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p) :
    bondPercolation (slabGraph 3 k) p (existsInfiniteCluster k) = 1 := by
  have h01 := (ergodic_slabRelabel_shift k p (v := (1, 0)) (by simp)).toPreErgodic.prob_eq_zero_or_one
    (measurableSet_existsInfiniteCluster k)
    (preimage_slabRelabel_existsInfiniteCluster k (planarShift (1, 0)))
  rcases h01 with h0 | h1
  · exfalso
    have hle : theta (slabGraph 3 k) (slabOrigin 3 k) p ≤
        (bondPercolation (slabGraph 3 k) p).real (existsInfiniteCluster k) :=
      measureReal_mono (Set.subset_iUnion (fun a : slab 3 k => (percolatesAt a : Set _)) _)
    rw [measureReal_def, h0, ENNReal.toReal_zero] at hle
    exact absurd hθ (not_lt.2 hle)
  · exact h1

/-- The event `{B̄_u ↔ ∞}`: some vertex over the box `B_u` has an infinite open cluster.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (eq. (1))] -/
def boxToInfinity (u : ℕ) : Set (BondConfig (slab 3 k)) := ⋃ a ∈ slabLift k (sqBox 0 u), percolatesAt a

/-- `{B̄_u ↔ ∞}` increases with `u`. [folklore] -/
theorem boxToInfinity_mono : Monotone (boxToInfinity k) := by
  intro u u' h ω hω
  simp only [boxToInfinity, Set.mem_iUnion] at hω ⊢
  obtain ⟨a, ha, hω⟩ := hω
  exact ⟨a, slabLift_mono k (sqBox_mono 0 h) ha, hω⟩

/-- `⋃_u {B̄_u ↔ ∞} = {∃ an infinite open cluster}`. [folklore] -/
theorem iUnion_boxToInfinity : ⋃ u, boxToInfinity k u = existsInfiniteCluster k := by
  ext ω
  simp only [boxToInfinity, existsInfiniteCluster, Set.mem_iUnion]
  constructor
  · rintro ⟨u, a, -, h⟩; exact ⟨a, h⟩
  · rintro ⟨a, h⟩
    refine ⟨(max |(planar k a).1| |(planar k a).2|).toNat, a, ?_, h⟩
    simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
    constructor
    · exact (Int.self_le_toNat _).trans' (le_max_left _ _)
    · exact (Int.self_le_toNat _).trans' (le_max_right _ _)

/-- **`P_p[B̄_u ↔ ∞] → 1`** as `u → ∞` when `θ_{S_k}(p) > 0` (continuity of measure along
`{B̄_u ↔ ∞} ↑ {∃ ∞ cluster}` and the zero–one law). [cite: GrimmettPercolation1999, §1.4 Thm. (1.11)] -/
theorem tendsto_real_boxToInfinity {p : unitInterval}
    (hθ : 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p) :
    Tendsto (fun u => (bondPercolation (slabGraph 3 k) p).real (boxToInfinity k u)) atTop (nhds 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := bondPercolation (slabGraph 3 k) p) (boxToInfinity_mono k)
  rw [iUnion_boxToInfinity, bondPercolation_existsInfiniteCluster_eq_one k hθ] at h
  have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  rw [ENNReal.toReal_one] at h'
  exact h'

/-! ### From uniqueness to eq. (1): `liminf_n P_p[B_u ⟷^{!B_n!} ∂B_n] ≥ P_p[B̄_u ↔ ∞]` -/

/-- An open path is an open path inside `Set.univ` (`PathIn` form of `Reachable`). [folklore] -/
theorem pathIn_univ_of_reachable {V : Type*} {G : SimpleGraph V} {x y : V} (h : G.Reachable x y) :
    PathIn G Set.univ x y := by
  obtain ⟨W⟩ := h
  induction W with
  | nil => exact PathIn.refl (Set.mem_univ _)
  | cons hadj _ ih => exact (PathIn.of_adj (Set.mem_univ _) (Set.mem_univ _) hadj).trans ih

/-- A path visits finitely many vertices: a path inside `A` is a path inside a finite subset of
`A`. [folklore] -/
theorem pathIn_exists_finite {V : Type*} {G : SimpleGraph V} {A : Set V} {x y : V}
    (h : PathIn G A x y) : ∃ F : Set V, F.Finite ∧ F ⊆ A ∧ PathIn G F x y := by
  obtain ⟨hx, hr⟩ := h
  induction hr with
  | refl => exact ⟨{x}, Set.finite_singleton x, by simpa using hx, PathIn.refl rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨F, hF, hFA, hp⟩ := ih
    refine ⟨insert c F, hF.insert c, Set.insert_subset hbc.2 hFA, ?_⟩
    exact (hp.mono (Set.subset_insert _ _)).tail hbc.1 (Set.mem_insert _ _)

/-- A finite set of slab vertices lies over some box `B_M`. [folklore] -/
theorem exists_subset_slabLift_sqBox {F : Set (slab 3 k)} (hF : F.Finite) :
    ∃ M : ℕ, F ⊆ slabLift k (sqBox 0 M) := by
  obtain ⟨B, hB⟩ := (hF.image fun v => max |(planar k v).1| |(planar k v).2|).bddAbove
  refine ⟨B.toNat, fun v hv => ?_⟩
  have h := hB (Set.mem_image_of_mem _ hv)
  have h' : max |(planar k v).1| |(planar k v).2| ≤ (B.toNat : ℤ) := h.trans (Int.self_le_toNat B)
  simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero]
  exact ⟨(le_max_left _ _).trans h', (le_max_right _ _).trans h'⟩

/-- Two vertices joined by an open path are joined inside `\overline{B_n}` for all large `n`.
[folklore] -/
theorem eventually_openConnIn_of_reachable {ω : BondConfig (slab 3 k)} {x y : slab 3 k}
    (h : (openGraph ω).Reachable x y) :
    ∀ᶠ n in atTop, ω ∈ openConnIn (slabLift k (sqBox 0 n)) x y := by
  obtain ⟨F, hF, -, hp⟩ := pathIn_exists_finite (pathIn_univ_of_reachable h)
  obtain ⟨M, hM⟩ := exists_subset_slabLift_sqBox k hF
  refine Filter.eventually_atTop.2 ⟨M, fun n hn => ?_⟩
  exact mem_openConnIn_iff_pathIn.2 (hp.mono (hM.trans (slabLift_mono k (sqBox_mono 0 hn))))

/-- A vertex with a finite open cluster is, for all large `n`, not joined inside
`\overline{B_n}` to `\overline{∂B_n}`. [folklore] -/
theorem eventually_not_openConnIn_sqSphere {ω : BondConfig (slab 3 k)} {x : slab 3 k}
    (hx : (openCluster ω x).Finite) :
    ∀ᶠ n in atTop, ∀ y ∈ slabLift k (sqSphere 0 n),
      ω ∉ openConnIn (slabLift k (sqBox 0 n)) x y := by
  obtain ⟨M, hM⟩ := exists_subset_slabLift_sqBox k hx
  refine Filter.eventually_atTop.2 ⟨M + 1, fun n hn y hy hxy => ?_⟩
  have hyC : y ∈ openCluster ω x := reachable_of_openConnIn hxy
  have hyM := hM hyC
  simp only [mem_slabLift_iff, sqBox, sqSphere, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero,
    sub_zero] at hyM hy
  have h1 := max_le hyM.1 hyM.2
  rw [hy] at h1
  omega

/-- An infinite open cluster at `a ∈ \overline{B_n}` reaches `\overline{∂B_n}` inside
`\overline{B_n}` (lattice configurations; boundary entry applied to a path leaving the box).
[folklore] -/
theorem exists_sqSphere_openConnIn_of_infinite {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) {a : slab 3 k} (ha : (openCluster ω a).Infinite) {n : ℕ}
    (han : a ∈ slabLift k (sqBox 0 n)) :
    ∃ e ∈ slabLift k (sqSphere 0 n), ω ∈ openConnIn (slabLift k (sqBox 0 n)) a e := by
  obtain ⟨y, hy, hyn⟩ := ha.exists_notMem_finset (slabLift_finite k (sqBox_finite 0 n)).toFinset
  rw [Set.Finite.mem_toFinset] at hyn
  have hya : ω ∈ openConnIn (slabLift k Set.univ) y a := by
    rw [mem_openConnIn_iff_pathIn]
    have huniv : slabLift k Set.univ = Set.univ := by ext; simp
    rw [huniv]
    exact pathIn_univ_of_reachable (SimpleGraph.Reachable.symm hy)
  exact exists_sqSphere_openConnIn k hω hya han (fun h => absurd h hyn)

/-- **Uniqueness transfers to boxes** (the mechanism of DST 2016, §2.1, eq. (1)): for a lattice
configuration in which any two infinite open clusters coincide and some infinite cluster meets
`\overline{B_u}`, the event `B_u ⟷^{!B_n!} ∂B_n` holds for all large `n` (an infinite cluster
leaves every box through its boundary; two boundary-reaching vertices of `\overline{B_u}`
either have infinite clusters — then they are joined by a path, which lies in `\overline{B_n}`
for `n` large — or one of them has a finite cluster, which for `n` large does not reach
`\overline{∂B_n}`). [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (eq. (1))] -/
theorem eventually_mem_slabUniqueConn {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet)
    (huniq : ∀ a b : slab 3 k, (openCluster ω a).Infinite → (openCluster ω b).Infinite →
      (openGraph ω).Reachable a b)
    {u : ℕ} (hu : ω ∈ boxToInfinity k u) :
    ∀ᶠ n in atTop, ω ∈ slabUniqueConn k (sqBox 0 n) (sqBox 0 u) (sqSphere 0 n) := by
  simp only [boxToInfinity, Set.mem_iUnion] at hu
  obtain ⟨a, ha, hainf⟩ := hu
  -- existence of the crossing, for `n ≥ u`
  have hex : ∀ᶠ n in atTop, ω ∈ slabConn k (sqBox 0 n) (sqBox 0 u) (sqSphere 0 n) := by
    refine Filter.eventually_atTop.2 ⟨u, fun n hn => ?_⟩
    obtain ⟨e, he, hae⟩ :=
      exists_sqSphere_openConnIn_of_infinite k hω hainf (slabLift_mono k (sqBox_mono 0 hn) ha)
    exact ⟨a, ha, e, he, hae⟩
  -- uniqueness, pair by pair
  have hpair : ∀ x ∈ slabLift k (sqBox 0 u), ∀ x' ∈ slabLift k (sqBox 0 u), ∀ᶠ n in atTop,
      ∀ y ∈ slabLift k (sqSphere 0 n), ∀ y' ∈ slabLift k (sqSphere 0 n),
        ω ∈ openConnIn (slabLift k (sqBox 0 n)) x y →
          ω ∈ openConnIn (slabLift k (sqBox 0 n)) x' y' →
            ω ∈ openConnIn (slabLift k (sqBox 0 n)) x x' := by
    intro x _ x' _
    by_cases hx : (openCluster ω x).Infinite
    · by_cases hx' : (openCluster ω x').Infinite
      · filter_upwards [eventually_openConnIn_of_reachable k (huniq x x' hx hx')] with n hn
        intro _ _ _ _ _ _
        exact hn
      · filter_upwards [eventually_not_openConnIn_sqSphere k (Set.not_infinite.1 hx')] with n hn
        intro y _ y' hy' _ h'
        exact absurd h' (hn y' hy')
    · filter_upwards [eventually_not_openConnIn_sqSphere k (Set.not_infinite.1 hx)] with n hn
      intro y hy _ _ h _
      exact absurd h (hn y hy)
  have hfin : (slabLift k (sqBox 0 u)).Finite := slabLift_finite k (sqBox_finite 0 u)
  have hall : ∀ᶠ n in atTop, ∀ x ∈ slabLift k (sqBox 0 u), ∀ x' ∈ slabLift k (sqBox 0 u),
      ∀ y ∈ slabLift k (sqSphere 0 n), ∀ y' ∈ slabLift k (sqSphere 0 n),
        ω ∈ openConnIn (slabLift k (sqBox 0 n)) x y →
          ω ∈ openConnIn (slabLift k (sqBox 0 n)) x' y' →
            ω ∈ openConnIn (slabLift k (sqBox 0 n)) x x' :=
    hfin.eventually_all.2 fun x hx => hfin.eventually_all.2 fun x' hx' => hpair x hx x' hx'
  filter_upwards [hex, hall] with n hn1 hn2
  exact ⟨hn1, fun x hx x' hx' y hy y' hy' h h' => hn2 x hx x' hx' y hy y' hy' h h'⟩

/-- **`liminf_n P_p[B_u ⟷^{!B_n!} ∂B_n] ≥ P_p[B̄_u ↔ ∞]`** under almost sure uniqueness of the
infinite cluster (Fatou along `eventually_mem_slabUniqueConn`: the events
`⋂_{n ≥ N} {B_u ⟷^{!B_n!} ∂B_n}` increase to an event containing `{B̄_u ↔ ∞}` a.s.).
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (eq. (1))] -/
theorem le_eventually_real_slabUniqueConn {p : unitInterval}
    (hU : ∀ᵐ ω ∂(bondPercolation (slabGraph 3 k) p), numInfiniteClusters ω ≤ 1)
    (u : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (bondPercolation (slabGraph 3 k) p).real (boxToInfinity k u) - ε ≤
      (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox 0 n) (sqBox 0 u) (sqSphere 0 n)) := by
  set P := bondPercolation (slabGraph 3 k) p with hP
  set V : ℕ → Set (BondConfig (slab 3 k)) :=
    fun N => ⋂ n, ⋂ (_ : N ≤ n), slabUniqueConn k (sqBox 0 n) (sqBox 0 u) (sqSphere 0 n) with hV
  have hVmono : Monotone V := by
    intro N N' h ω hω
    simp only [hV, Set.mem_iInter] at hω ⊢
    exact fun n hn => hω n (h.trans hn)
  -- almost surely `{B̄_u ↔ ∞} ⊆ ⋃_N V_N`
  have hle : P.real (boxToInfinity k u) ≤ P.real (⋃ N, V N) := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := (slabGraph 3 k).edgeSet)
      (p := p), hU] with ω hω huniq hbox
    have h := eventually_mem_slabUniqueConn k hω
      (fun a b ha hb => reachable_of_numInfiniteClusters_le_one huniq ha hb) hbox
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
    show ω ∈ ⋃ N, V N
    simp only [Set.mem_iUnion, hV, Set.mem_iInter]
    exact ⟨N, fun n hn => hN n hn⟩
  -- continuity of measure along `V_N ↑`
  have htend : Tendsto (fun N => P.real (V N)) atTop (nhds (P.real (⋃ N, V N))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hVmono)
  have hev : ∀ᶠ N in atTop, P.real (⋃ N, V N) - ε < P.real (V N) :=
    htend.eventually (lt_mem_nhds (by linarith))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine Filter.eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩
  have h1 := hN₀ N₀ le_rfl
  have h2 : P.real (V N₀) ≤
      P.real (slabUniqueConn k (sqBox 0 n) (sqBox 0 u) (sqSphere 0 n)) := by
    refine measureReal_mono fun ω hω => ?_
    simp only [hV, Set.mem_iInter] at hω
    exact hω n hn
  linarith

end UniquenessInput

/-! ## The dependent-percolation input discharged: Peierls' argument for finite-range
dependent bond percolation on `ℤ²` (DST 2016, §2.2: "this fact follows from a Peierls argument
presented for example in [BBW05]") -/

section DependentPeierls

open scoped ENNReal

/-- Every edge of `𝕃²` has a presentation `{x, x + eᵢ}`. [folklore] -/
theorem exists_base_of_mem_edgeSet {e : Sym2 (Site 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    ∃ (x : Site 2) (i : Fin 2), e = s(x, x + Pi.single i 1) := by
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    obtain ⟨i, h | h⟩ := (zdGraph_adj_iff a b).1 he
    · exact ⟨a, i, by rw [h]⟩
    · exact ⟨b, i, by rw [h, Sym2.eq_swap]⟩

/-- The residue class of an edge of `𝕃²` modulo `M`: its direction and the residues of the two
coordinates of its base point (arbitrary off the edge set). Distinct edges in one class are far
apart, and there are `2M²` classes (the bookkeeping of a Peierls argument for dependent
percolation, cf. Balister–Bollobás–Walters 2005). [folklore] -/
def edgeClass (M : ℕ) (e : Sym2 (Site 2)) : Fin 2 × ℕ × ℕ :=
  if he : e ∈ (zdGraph 2).edgeSet then
    ((exists_base_of_mem_edgeSet he).choose_spec.choose,
      ((exists_base_of_mem_edgeSet he).choose 0 % M).toNat,
      ((exists_base_of_mem_edgeSet he).choose 1 % M).toNat)
  else (0, 0, 0)

/-- The defining property of `edgeClass`. [folklore] -/
theorem edgeClass_spec (M : ℕ) {e : Sym2 (Site 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    ∃ (x : Site 2) (i : Fin 2), e = s(x, x + Pi.single i 1) ∧
      edgeClass M e = (i, (x 0 % M).toNat, (x 1 % M).toNat) := by
  refine ⟨(exists_base_of_mem_edgeSet he).choose, (exists_base_of_mem_edgeSet he).choose_spec.choose,
    (exists_base_of_mem_edgeSet he).choose_spec.choose_spec, ?_⟩
  simp only [edgeClass, he, dif_pos]

/-- The classes of edges lie in a set of size `2M²`. [folklore] -/
theorem edgeClass_mem (M : ℕ) (hM : 1 ≤ M) {e : Sym2 (Site 2)} (he : e ∈ (zdGraph 2).edgeSet) :
    edgeClass M e ∈ (Finset.univ : Finset (Fin 2)) ×ˢ (Finset.range M ×ˢ Finset.range M) := by
  obtain ⟨x, i, -, hcl⟩ := edgeClass_spec M he
  rw [hcl]
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  constructor
  · have h1 := Int.emod_nonneg (x 0) hM'.ne'
    have h2 := Int.emod_lt_of_pos (x 0) hM'
    omega
  · have h1 := Int.emod_nonneg (x 1) hM'.ne'
    have h2 := Int.emod_lt_of_pos (x 1) hM'
    omega

/-- **Distinct edges of one class are far apart**: all their vertices are at sup-distance
`≥ M - 1`. [folklore] -/
theorem far_of_edgeClass_eq (M : ℕ) (hM : 1 ≤ M) {e e' : Sym2 (Site 2)}
    (he : e ∈ (zdGraph 2).edgeSet) (he' : e' ∈ (zdGraph 2).edgeSet) (hne : e ≠ e')
    (hcl : edgeClass M e = edgeClass M e') :
    ∀ a ∈ e, ∀ b ∈ e', (M : ℤ) - 1 ≤ max |a 0 - b 0| |a 1 - b 1| := by
  obtain ⟨x, i, rfl, hc⟩ := edgeClass_spec M he
  obtain ⟨x', i', rfl, hc'⟩ := edgeClass_spec M he'
  rw [hc, hc'] at hcl
  simp only [Prod.mk.injEq] at hcl
  obtain ⟨rfl, h0, h1⟩ := hcl
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  -- congruences of the base points
  have hmod : ∀ j : Fin 2, (M : ℤ) ∣ x j - x' j := by
    intro j
    have hj : x j % M = x' j % M := by
      fin_cases j
      · have a1 := Int.emod_nonneg (x 0) hM'.ne'
        have a2 := Int.emod_nonneg (x' 0) hM'.ne'
        simp only [Fin.zero_eta, Fin.isValue]
        omega
      · have a1 := Int.emod_nonneg (x 1) hM'.ne'
        have a2 := Int.emod_nonneg (x' 1) hM'.ne'
        simp only [Fin.mk_one, Fin.isValue]
        omega
    have := (Int.ModEq.dvd hj.symm)
    -- `Int.ModEq.dvd : a ≡ b [ZMOD n] → n ∣ b - a`
    simpa using this
  -- the base points differ
  have hxx' : x ≠ x' := by
    rintro rfl
    exact hne rfl
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, x j ≠ x' j := by
    by_contra h
    push Not at h
    exact hxx' (funext h)
  have hfar : (M : ℤ) ≤ |x j - x' j| := by
    obtain ⟨c, hc⟩ := hmod j
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hj
      have : x j - x' j = 0 := by rw [hc, mul_zero]
      linarith
    rw [hc, abs_mul, abs_of_nonneg hM'.le]
    have : 1 ≤ |c| := Int.one_le_abs hc0
    nlinarith
  intro a ha b hb
  rw [Sym2.mem_iff] at ha hb
  have key : (M : ℤ) - 1 ≤ |a j - b j| := by
    have ha' : a j = x j ∨ a j = x j + (Pi.single i (1 : ℤ) : Site 2) j := by
      rcases ha with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hb' : b j = x' j ∨ b j = x' j + (Pi.single i (1 : ℤ) : Site 2) j := by
      rcases hb with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hs : (Pi.single i (1 : ℤ) : Site 2) j = 0 ∨ (Pi.single i (1 : ℤ) : Site 2) j = 1 := by
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    rw [le_abs] at hfar ⊢
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rcases hs with hs | hs <;>
      rw [ha', hb'] <;> (try rw [hs]) <;> omega
  fin_cases j
  · exact key.trans (le_max_left _ _)
  · exact key.trans (le_max_right _ _)

/-- The event "the edge `a` is closed" is determined by the coordinate `a`. [folklore] -/
theorem determinedBy_notMem {ι : Type*} (a : ι) : DeterminedBy {ω : Set ι | a ∉ ω} {a} := by
  rw [determinedBy_iff]
  intro ω ω' h
  have := Set.ext_iff.1 h a
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, and_true] at this
  simp only [Set.mem_setOf_eq, this]

/-- The event "all edges of `s` are closed" is determined by the coordinates in `s`. [folklore] -/
theorem determinedBy_iInter_notMem {ι : Type*} (s : Finset ι) :
    DeterminedBy (⋂ e ∈ s, {ω : Set ι | e ∉ ω}) (↑s : Set ι) := by
  rw [determinedBy_iff]
  intro ω ω' h
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  refine forall₂_congr fun e he => ?_
  have := Set.ext_iff.1 h e
  simp only [Set.mem_inter_iff, Finset.mem_coe, he, and_true] at this
  rw [this]

/-- The event "all edges of `s` are closed" is measurable. [folklore] -/
theorem measurableSet_iInter_notMem {ι : Type*} (s : Finset ι) :
    MeasurableSet (⋂ e ∈ s, {ω : Set ι | e ∉ ω}) :=
  Finset.measurableSet_biInter s fun e _ => (measurableSet_mem e).compl

/-- **Independence of far-apart closed edges** under a `K`-dependent law: for a finite set of
edges of `𝕃²` any two of which have all their vertices at sup-distance `≥ K`, the probability
that all are closed is the product of the one-edge probabilities (induction on the set, splitting
off one edge with the `K`-dependence hypothesis). [cite: GrimmettPercolation1999, §7.4 (7.64) (k-dependence)] -/
theorem measure_iInter_notMem_eq_prod {K : ℕ} (μ : Measure (BondConfig (Site 2)))
    [IsProbabilityMeasure μ]
    (hdep : ∀ (F₁ F₂ : Finset (Sym2 (Site 2))),
      (∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ a ∈ e₁, ∀ b ∈ e₂, (K : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1|) →
      ∀ (A B : Set (BondConfig (Site 2))), DeterminedBy A (↑F₁ : Set (Sym2 (Site 2))) →
        DeterminedBy B (↑F₂ : Set (Sym2 (Site 2))) → MeasurableSet A → MeasurableSet B →
        μ (A ∩ B) = μ A * μ B)
    (D : Finset (Sym2 (Site 2)))
    (hfar : ∀ e ∈ D, ∀ e' ∈ D, e ≠ e' → ∀ a ∈ e, ∀ b ∈ e', (K : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1|) :
    μ (⋂ e ∈ D, {ω | e ∉ ω}) = ∏ e ∈ D, μ {ω | e ∉ ω} := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hfar_s : ∀ e ∈ s, ∀ e' ∈ s, e ≠ e' → ∀ a ∈ e, ∀ b ∈ e',
        (K : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1| :=
      fun e he e' he' => hfar e (Finset.mem_insert_of_mem he) e' (Finset.mem_insert_of_mem he')
    rw [Finset.prod_insert has, Finset.set_biInter_insert, ← ih hfar_s]
    refine hdep {a} s (fun e₁ he₁ e₂ he₂ => ?_) _ _ ?_ (determinedBy_iInter_notMem s)
      (measurableSet_mem a).compl (measurableSet_iInter_notMem s)
    · rw [Finset.mem_singleton] at he₁
      subst he₁
      have hne : e₁ ≠ e₂ := by rintro rfl; exact has he₂
      exact hfar e₁ (Finset.mem_insert_self _ _) e₂ (Finset.mem_insert_of_mem he₂) hne
    · simpa using determinedBy_notMem (ι := Sym2 (Site 2)) a

/-- **The dependent Peierls bound for one contour**: under a `K`-dependent law on the edges of
`𝕃²` with one-edge densities `≥ 1 - η`, `η = 64^{-8(K+1)²}`, a given set of `n` distinct edges
of `𝕃²` is entirely closed with probability `≤ 64⁻ⁿ` (pigeonhole a residue class modulo `K + 1`
containing `≥ n / (2(K+1)²)` of the edges; these are pairwise far, hence independent).
[cite: DuminilCopinSidoraviciusTassion2016, §2.2 (Peierls argument for dependent percolation, [BBW05])] -/
theorem measure_disjoint_le_of_dependent (K : ℕ) (μ : Measure (BondConfig (Site 2)))
    [IsProbabilityMeasure μ]
    (hdep : ∀ (F₁ F₂ : Finset (Sym2 (Site 2))),
      (∀ e₁ ∈ F₁, ∀ e₂ ∈ F₂, ∀ a ∈ e₁, ∀ b ∈ e₂, (K : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1|) →
      ∀ (A B : Set (BondConfig (Site 2))), DeterminedBy A (↑F₁ : Set (Sym2 (Site 2))) →
        DeterminedBy B (↑F₂ : Set (Sym2 (Site 2))) → MeasurableSet A → MeasurableSet B →
        μ (A ∩ B) = μ A * μ B)
    (hmarg : ∀ e ∈ (zdGraph 2).edgeSet,
      1 - ((1 / 64 : ℝ) ^ (2 * (K + 1) ^ 2)) ≤ μ.real {ω | e ∈ ω})
    (D : Finset (Sym2 (Site 2))) (hD : (↑D : Set (Sym2 (Site 2))) ⊆ (zdGraph 2).edgeSet) :
    μ {ω | Disjoint (↑D : Set (Sym2 (Site 2))) ω} ≤ ENNReal.ofReal ((1 / 64 : ℝ) ^ D.card) := by
  classical
  set M : ℕ := K + 1 with hM
  set c : ℕ := 2 * (K + 1) ^ 2 with hc
  set η : ℝ := (1 / 64 : ℝ) ^ c with hη
  have hM1 : 1 ≤ M := by omega
  -- a populous residue class
  set t : Finset (Fin 2 × ℕ × ℕ) := (Finset.univ : Finset (Fin 2)) ×ˢ (Finset.range M ×ˢ Finset.range M)
    with ht
  have htcard : t.card = c := by
    simp only [ht, Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_range, hc, hM]
    ring
  have hmaps : (↑D : Set (Sym2 (Site 2))).MapsTo (edgeClass M) t :=
    fun e he => edgeClass_mem M hM1 (hD he)
  have htne : t.Nonempty := ⟨(0, 0, 0), by simp [ht, hM]⟩
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image t (fun y => (D.filter fun e => edgeClass M e = y).card) htne
  set D' := D.filter fun e => edgeClass M e = y with hD'
  have hcardle : D.card ≤ c * D'.card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps, ← htcard, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun z hz => hy z hz
  -- the edges of `D'` are pairwise far apart, hence independent
  have hD'sub : D' ⊆ D := Finset.filter_subset _ _
  have hfar : ∀ e ∈ D', ∀ e' ∈ D', e ≠ e' → ∀ a ∈ e, ∀ b ∈ e',
      (K : ℤ) ≤ max |a 0 - b 0| |a 1 - b 1| := by
    intro e he e' he' hne a ha b hb
    rw [hD', Finset.mem_filter] at he he'
    have h := far_of_edgeClass_eq M hM1 (hD he.1) (hD he'.1) hne (he.2.trans he'.2.symm) a ha b hb
    have : (M : ℤ) - 1 = K := by rw [hM]; push_cast; ring
    rwa [this] at h
  have hprod := measure_iInter_notMem_eq_prod μ hdep D' hfar
  -- one-edge bound
  have hedge : ∀ e ∈ D', μ {ω | e ∉ ω} ≤ ENNReal.ofReal η := by
    intro e he
    have heE : e ∈ (zdGraph 2).edgeSet := hD (hD'sub he)
    have hcomp : {ω : BondConfig (Site 2) | e ∉ ω} = {ω | e ∈ ω}ᶜ := rfl
    rw [← ofReal_measureReal, hcomp, measureReal_compl (measurableSet_mem e), probReal_univ]
    exact ENNReal.ofReal_le_ofReal (by linarith [hmarg e heE])
  -- assemble
  calc μ {ω | Disjoint (↑D : Set (Sym2 (Site 2))) ω}
      ≤ μ (⋂ e ∈ D', {ω | e ∉ ω}) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_setOf_eq] at hω
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        exact fun e he => Set.disjoint_left.1 hω (Finset.mem_coe.2 (hD'sub he))
    _ = ∏ e ∈ D', μ {ω | e ∉ ω} := hprod
    _ ≤ ∏ _e ∈ D', ENNReal.ofReal η := Finset.prod_le_prod' hedge
    _ = ENNReal.ofReal (η ^ D'.card) := by
        rw [Finset.prod_const]
        exact (ENNReal.ofReal_pow (by positivity) _).symm
    _ ≤ ENNReal.ofReal ((1 / 64 : ℝ) ^ D.card) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hη, ← pow_mul]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hcardle

/-- **the dependent-percolation input** `DuminilCopinSidoraviciusTassion2016_dependentPercolation`
(DST 2016, §2.2: "there exists `η > 0` such that whenever the probability to be good exceeds
`1 - η`, the set of good edges percolates (this fact follows from a Peierls argument presented
for example in [Balister–Bollobás–Walters 2005] …)"), by **Peierls' argument** exactly as in
Grimmett 1999, §1.4, (1.17)–(1.18) (`theta_zd_pos_of_le` of `CriticalContinuityProofs.lean`,
whose counting we repeat): a finite open cluster of the origin is surrounded by a closed dual
circuit (`Contour.exists_dualCircuit` of `DualContours.lean`) of some length `n` through a
plaquette `(k, 0)`, `k < n`, made of `n` distinct closed edges; there are at most `n(n+1)4ⁿ`
candidates, each closed with probability `≤ 64⁻ⁿ` by `measure_disjoint_le_of_dependent` (with
`η = 64^{-2(K+1)²}`), and `Σₙ n(n+1)4ⁿ/64ⁿ ≤ ⅔ < 1`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] [cite: GrimmettPercolation1999, §1.4 (1.17)–(1.18)] -/
theorem DuminilCopinSidoraviciusTassion2016_dependentPercolation_holds :
    DuminilCopinSidoraviciusTassion2016_dependentPercolation := by
  classical
  intro K
  refine ⟨(1 / 64 : ℝ) ^ (2 * (K + 1) ^ 2), by positivity, ?_⟩
  intro μ _ hdep hmarg
  -- the events "the dual walk `(n, k, m, w)` is closed"
  let st : (n : ℕ) → ℕ → ℕ → (Fin n → Fin 2 × Bool) → Site 2 := fun n k m w =>
    Pi.single 0 (k : ℤ) - wordPos w m
  let S : (n : ℕ) → ℕ → ℕ → (Fin n → Fin 2 × Bool) → Set (BondConfig (Site 2)) :=
    fun n k m w => {ω | Disjoint (↑(dualEdges (st n k m w) w) : Set (Sym2 (Site 2))) ω}
  let good : (n : ℕ) → ℕ → ℕ → Finset (Fin n → Fin 2 × Bool) := fun n k m =>
    Finset.univ.filter fun w => (dualEdges (st n k m w) w).card = n
  let V : ℕ → Set (BondConfig (Site 2)) := fun n =>
    ⋃ k ∈ Finset.range n, ⋃ m ∈ Finset.range (n + 1), ⋃ w ∈ good n k m, S n k m w
  -- a finite cluster forces one of these events
  have hsub : (percolatesAt 0 : Set (BondConfig (Site 2)))ᶜ ⊆ ⋃ n, V n := by
    intro ω hω
    have hfin : (openCluster ω 0).Finite := Set.not_infinite.1 hω
    obtain ⟨n, k, hkn, a, w, -, ⟨m, hmn, hpos⟩, hcard, hdisj, -, -⟩ :=
      Contour.exists_dualCircuit ω hfin
    have ha : a = st n k m w := by simp only [st, ← hpos, add_sub_cancel_right]
    subst ha
    refine Set.mem_iUnion.2 ⟨n, Set.mem_biUnion (Finset.mem_range.2 hkn)
      (Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hmn))
        (Set.mem_biUnion (x := w) (by simp [good, hcard]) ?_))⟩
    exact hdisj
  -- each event has probability `≤ (1/64)^n`
  have hS : ∀ n k m, ∀ w ∈ good n k m, μ (S n k m w) ≤ ENNReal.ofReal ((1 - 63 / 64 : ℝ) ^ n) := by
    intro n k m w hw
    have hwn : (dualEdges (st n k m w) w).card = n := (Finset.mem_filter.1 hw).2
    have h := measure_disjoint_le_of_dependent K μ hdep hmarg (dualEdges (st n k m w) w)
      (dualEdges_subset_edgeSet _ _)
    rw [hwn] at h
    norm_num at h ⊢
    exact h
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
            rw [← Set.union_compl_self (percolatesAt (0 : Site 2))]; exact measure_union_le _ _
        _ ≤ ENNReal.ofReal (2 / 3) := by rw [h0, zero_add]; exact hcompl
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h1
    norm_num at h1
  exact ENNReal.toReal_pos hpos (measure_ne_top _ _)

/-- the renormalisation step of DST 2016, §2.2, outright
(`DuminilCopinSidoraviciusTassion2016_renormalisation_of_dependentPercolation` and
`DuminilCopinSidoraviciusTassion2016_dependentPercolation_holds`).
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem DuminilCopinSidoraviciusTassion2016_renormalisation_holds :
    DuminilCopinSidoraviciusTassion2016_renormalisation :=
  DuminilCopinSidoraviciusTassion2016_renormalisation_of_dependentPercolation
    DuminilCopinSidoraviciusTassion2016_dependentPercolation_holds

end DependentPeierls

end Percolation.Literature

end
