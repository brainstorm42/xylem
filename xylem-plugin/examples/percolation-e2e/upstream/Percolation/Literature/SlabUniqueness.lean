import Percolation.Literature.SlabCriticalityInputs
import Percolation.Literature.UniquenessInfiniteCluster
import Percolation.Util.Linter

/-!
# Uniqueness of the infinite open cluster on slabs (Burton–Keane, after Bollobás–Riordan), and DST 2016, Thm. 1 from the Gluing Lemma alone

Third file of the bottom-up decomposition of the named
fact `DuminilCopinSidoraviciusTassion2016` (`HalfSpace.lean`; Duminil-Copin–Sidoravicius– Tassion
2016, Thm. 1: no infinite cluster at criticality for bond percolation on the slab `S_k = ℤ² ×
{0,…,k}`, `k > 0`), after `SlabCriticality.lean` (§2.1 of the paper: the finite-size criterion,
Lemmata 4–5, eqs. (10)–(13)) and `SlabCriticalityInputs.lean` (§2.2: renormalisation and dependent
percolation, proved; eq. (1) proved from the uniqueness of the infinite cluster). Here the first one
is proved:

* `DuminilCopinSidoraviciusTassion2016_uniqueCluster_holds` — proved: for `k > 0` and
  `θ_{S_k}(p) > 0` (indeed for every `p > 0`, `ae_numInfiniteClusters_slab_le_one`), `P_p`-almost
  surely bond percolation on the slab has at most one infinite open cluster;

## The proof (Bollobás–Riordan 2006, Ch. 5, Lemma 2 and Thm. 4, pp. 105–109, for the slab)

DST cite Aizenman–Kesten–Newman 1987 and Burton–Keane 1989; we follow the Burton–Keane argument
in the form of Bollobás–Riordan, *Percolation* (2006), Ch. 5, exactly as this library's
`UniquenessInfiniteCluster.lean` does for `ℤ^d` (`Grimmett1999_numInfiniteClusters_le_one_holds`),
whose graph-generic layer is reused verbatim at `G := slabGraph 3 k` (an induced subgraph of
`zdGraph 3`, locally finite by `instLocallyFiniteInduce`): the events `I₂ = exactlyTwoInfClusters`,
`{N ≥ 3} = threeInfClusters`, `I₁ = exactlyOneInfCluster` with their measurability, transport
and the decomposition `{N ≤ 1}ᶜ ⊆ I₂ ∪ {N ≥ 3}`; the merge lemma
`openEdges_edgesIn_mem_exactlyOneInfCluster`; cut sets `IsCutSet` with
`isCutSet_openEdges_of_three`, `IsCutSet.isHub`, `IsCutSet.image`; the counting lemma
`card_add_two_le_card_of_isHub` (`BurtonKeaneCombinatorics.lean`, B.–R. Lemma 3); insertion
tolerance (`InsertionTolerance.lean`, B.–R. p. 106). What is specific to the slab, and proved
here, is the geometry: the balls are the full-height COLUMN BALLS `\overline{c + B_r}`
(`ballFinset`, connected through lattice edges inside them, `ballFinset_conn`), on which the
planar translations of the slab act transitively (`slabRelabel k (planarShift v)`, ergodic by
`ergodic_slabRelabel_shift` of `SlabCriticalityInputs.lean` — B.–R. Lemma 1, p. 105: "invariance
under a single automorphism `φ` of `Λ` corresponding to a translation … is enough"), and the
amenability count `|\overline{∂B_n}| = O(n)` against `(2m+1)²` disjoint column balls in
`\overline{B_n}`.

* `N = 2` has probability `0` (`bondPercolation_exactlyTwoInfClusters_slab_eq_zero`; B.–R.
  Lemma 2, pp. 105–106, the case `k = 2` — the cases `3 ≤ k < ∞` are absorbed in `N ≥ 3` as in
  the proof of Thm. 4): `I₂` is translation invariant, so has probability `0` or `1`; if `1`,
  both clusters meet some `\overline{B_m}` with positive probability (`twoInfNear`), and opening
  the lattice edges of `\overline{B_m}` gives `I₁` (merge lemma), so `I₁ ⊆ I₂ᶜ` would have
  positive probability by insertion tolerance ("changing the state of every site in `B_n(x₀)` to
  open, we see that `P(I₁) > 0` … As `I_k ∩ I₁ = ∅`, this is impossible", p. 106).
* `N ≥ 3` has probability `0` (`bondPercolation_threeInfClusters_slab_eq_zero`; B.–R. Thm. 4,
  pp. 107–109). If `N ≥ 3` has positive probability, some `\overline{B_r}` meets three disjoint
  infinite clusters with positive probability (`threeNear`; "there is an `r` such that, with
  positive probability, `B_r(x₀)` contains sites from (at least) three infinite open clusters",
  p. 107), so the CUT-BALL event `slabCutBall 0 r = {IsCutSet (slabGraph 3 k) \overline{B_r}}`
  has positive probability `c₀` (`real_slabCutBall_pos`: `isCutSet_openEdges_of_three` and
  insertion tolerance; "Hence, `P(T_r(x₀)) > 0`", p. 107), and the same probability at every
  planar translate (`slabCutBallAt`, `real_slabCutBallAt`, `isCutSet_of_mem_slabCutBallAt` by
  `IsCutSet.image` along `slabIso`; "(2) `P(T_r(x)) = a`", p. 107). In a lattice configuration a
  cut-ball at `c + B_r` with `c + B_{r+1} ⊆ B_n` is a hub of the open graph of `\overline{B_n}`
  relative to its inner boundary (`IsCutSet.isHub`), which lies over `∂B_n`
  (`innerBoundary_subset`). With the `(2m+1)²` centres `(2r+1)(i, j)`, `|i|, |j| ≤ m`
  (`slabCentres`; pairwise disjoint balls, `disjoint_ball_of_ne`; `c + B_{r+1} ⊆ B_n` for
  `n = (2r+1)m + r + 1 = gridBox r m`) the counting lemma bounds the number of centres carrying a
  cut-ball by `|\overline{∂B_n}| ≤ 4(2n+1)(k+1)` (`card_filter_slabCutBallAt_le`,
  `card_le_of_slabLift`, `card_sphereFinset_le`), whence, integrating ("by linearity of
  expectation the expected number of cut-balls is `Σ_w P(T_r(w)) = a|W|`", p. 108),
  `(2m+1)² c₀ ≤ 4(2n+1)(k+1)` (`card_mul_real_slabCutBall_le`), absurd for `m` large.

Hence `N ≤ 1` almost surely for `p > 0` (`ae_numInfiniteClusters_slab_le_one`), and the DST
regime `θ_{S_k}(p) > 0` forces `p > 0` (`coe_pos_of_theta_slab_pos`).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: Thm. 1 (p. 2); §2.1, p. 4 (= arXiv p. 5): "The infinite cluster in `S_k`
  being unique almost surely [AKN87, BK89]"; Lemma 6 (p. 5) and §2.3.
* B. Bollobás, O. Riordan, *Percolation*, Cambridge University Press (2006), Ch. 5, §5.1:
  Lemma 1 (pp. 104–105, the zero–one law for translation-invariant events), Lemma 2
  (pp. 105–106, Newman–Schulman: `P(⋃_{2≤k<∞} I_k) = 0`), Lemma 3 (p. 106, the counting lemma)
  and Thm. 4 with its proof (pp. 107–109: `T_r(x)`, cut-balls, `Σ_w P(T_r(w)) = a|W|`,
  `t ≤ |S_{n+1}(x₀)|`, `|L| ≥ s + 2`). Page numbers are those of the held PDF, as in `BurtonKeaneCombinatorics.lean`.
* M. Aizenman, H. Kesten, C. M. Newman, Comm. Math. Phys. 111 (1987), 505–531; R. M. Burton,
  M. Keane, Comm. Math. Phys. 121 (1989), 501–505 (the results cited by DST; not used directly).
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2, Thm. (8.1) (uniqueness on `ℤ^d`,
  `N ∈ {0, 1}` a.s.; this library's `Grimmett1999_numInfiniteClusters_le_one`, `Connectivity.lean`,
  is the `ℤ^d` statement, of which this file proves the slab analogue), §1.6 p. 16 (lattice
  symmetries preserve `P_p`).

## Design choices

* Balls are column boxes `slabLift k (sqBox c r)` of the existing slab vocabulary
  (`SlabCriticality.lean`), as `Finset`s (`ballFinset`), so that planar translations
  (`slabRelabel k (planarShift v)`, `real_preimage_slabRelabel`) act transitively on them.
* `p > 0` is the only hypothesis of the two probability-zero statements; the named fact is in
  DST's regime `k > 0`, `θ_{S_k}(p) > 0`, which implies it.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels Filter Topology

/-! ## Generic complements -/

section Generic

variable {V : Type*}

/-- **Induced subgraphs of locally finite graphs are locally finite** (so that the finite-volume
vocabulary of `LatticeGraph.lean` and the cut sets of `UniquenessInfiniteCluster.lean` apply to
`slabGraph 3 k = (zdGraph 3).induce (slab 3 k)`). [folklore] -/
noncomputable instance instLocallyFiniteInduce (G : SimpleGraph V) [G.LocallyFinite] (s : Set V) :
    (G.induce s).LocallyFinite := fun x =>
  (((G.neighborSet x.1).toFinite.preimage Subtype.val_injective.injOn).subset
    fun y (hy : (G.induce s).Adj x y) => by simpa [SimpleGraph.mem_neighborSet] using hy).fintype

/-- A `PathIn G A` joins its endpoints in `withinGraph G A`. [folklore] -/
theorem reachable_withinGraph_of_pathIn {G : SimpleGraph V} {A : Set V} {u v : V}
    (h : PathIn G A u v) : (withinGraph G A).Reachable u v := by
  obtain ⟨hu, h⟩ := h
  induction h with
  | refl => exact .refl _
  | @tail b c hab hbc ih =>
    have hb : b ∈ A := PathIn.right_mem ⟨hu, hab⟩
    exact ih.trans (SimpleGraph.Adj.reachable ⟨hbc.1, hb, hbc.2⟩)

/-- Pairwise distinctness of three clusters, in the `Fin 3` form used by `IsCutSet`. [folklore] -/
theorem fin3_of_pairwise {P : V → V → Prop} (hsymm : ∀ x y, P x y → P y x) {a b c : V}
    (hab : ¬P a b) (hac : ¬P a c) (hbc : ¬P b c) :
    ∀ i j : Fin 3, P (![a, b, c] i) (![a, b, c] j) → i = j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · exact hab hij
  · exact hac hij
  · exact hab (hsymm _ _ hij)
  · exact hbc hij
  · exact hac (hsymm _ _ hij)
  · exact hbc (hsymm _ _ hij)

end Generic

/-! ## Column balls of the slab -/

section ColumnBalls

variable (k : ℕ)

/-- A slab-lattice neighbour of a vertex over `c + B_r` lies over `c + B_{r+1}`. [folklore] -/
theorem mem_slabLift_sqBox_succ_of_adj {c : ℤ × ℤ} {r : ℕ} {x y : slab 3 k}
    (hadj : (slabGraph 3 k).Adj x y) (hx : x ∈ slabLift k (sqBox c r)) :
    y ∈ slabLift k (sqBox c (r + 1)) := by
  have h := (zdGraph_three_adj_iff x.1 y.1).1 hadj
  simp only [mem_slabLift_iff, planar, sqBox, Set.mem_setOf_eq] at hx ⊢
  obtain ⟨hx1, hx2⟩ := hx
  rw [abs_le] at hx1 hx2
  rw [abs_le, abs_le]
  push_cast
  rcases h with ⟨-, hpa⟩ | ⟨hpe, -⟩
  · simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at hpa
    omega
  · simp only [Prod.mk.injEq] at hpe
    omega

/-- In the full configuration, the base vertex over `0` is joined inside `\overline{B_m}` to every
vertex of `\overline{B_m}`. [folklore] -/
theorem edgeSet_openConnIn_of_mem {m : ℕ} {a : slab 3 k} (ha : a ∈ slabLift k (sqBox 0 m)) :
    (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 m)) (baseVertex k 0) a := by
  obtain ⟨h, hh, hEq⟩ := eq_slabVertex k a
  have hz : planar k a ∈ sqBox 0 m := ha
  rw [hEq]
  exact SlabCriticality.openConnIn_trans (edgeSet_openConnIn_baseVertex k m _ hz)
    (edgeSet_openConnIn_climb k hz h hh)

/-! ### Connectivity of the column balls in the full configuration -/

/-- A planar lattice symmetry fixes the full configuration `E(S_k)`. [folklore] -/
theorem relabel_edgeSet_eq (g : ℤ × ℤ ≃ ℤ × ℤ) (hg : ∀ z w, planarAdj (g z) (g w) ↔ planarAdj z w) :
    BondConfig.relabel (sym2Equiv (slabEquiv k g)) (slabGraph 3 k).edgeSet =
      (slabGraph 3 k).edgeSet := by
  ext e
  rw [BondConfig.mem_relabel_iff, sym2Equiv_symm]
  exact sym2Equiv_mem_edgeSet_iff (slabIso k g hg).symm e

/-- `slabEquiv (planarShift c)` moves the base vertex over `0` to the base vertex over `c`.
[folklore] -/
theorem slabEquiv_planarShift_baseVertex (c : ℤ × ℤ) :
    slabEquiv k (planarShift c) (baseVertex k 0) = baseVertex k c := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [slabEquiv, baseVertex, planar]

/-- In the full configuration, the base vertex over `c` is joined inside `\overline{c + B_M}` to
every vertex of `\overline{c + B_M}`. [folklore] -/
theorem edgeSet_openConnIn_center (c : ℤ × ℤ) {M : ℕ} {a : slab 3 k}
    (ha : a ∈ slabLift k (sqBox c M)) :
    (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox c M)) (baseVertex k c) a := by
  set φ := slabEquiv k (planarShift c) with hφ
  have ha' : φ.symm a ∈ slabLift k (sqBox 0 M) := by
    rw [mem_slabLift_iff, planar_slabEquiv_symm]
    rw [mem_slabLift_iff] at ha
    simp only [planarShift, Equiv.addRight_symm, Equiv.coe_addRight, sqBox, Set.mem_setOf_eq,
      Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero,
      sub_zero] at ha ⊢
    simpa only [sub_eq_add_neg] using ha
  have h0 := edgeSet_openConnIn_of_mem k ha'
  have h1 := (relabel_mem_openConnIn_iff φ (slabGraph 3 k).edgeSet (slabLift k (sqBox 0 M))
    (baseVertex k 0) (φ.symm a)).2 h0
  rwa [relabel_edgeSet_eq k _ (planarAdj_planarShift c), image_slabEquiv_slabLift,
    image_planarShift_sqBox, zero_add, slabEquiv_planarShift_baseVertex,
    Equiv.apply_symm_apply] at h1

/-- The full configuration `E(S_k)` has open graph `S_k` itself. [folklore] -/
theorem openGraph_edgeSet : openGraph (slabGraph 3 k).edgeSet = slabGraph 3 k :=
  SimpleGraph.fromEdgeSet_edgeSet _

/-- **The column ball `\overline{c + B_r}` is connected in the slab through lattice edges inside
it** (the hypothesis `hKconn`/`hB` of `IsCutSet.isHub` and of the merge lemma). [folklore] -/
theorem reachable_withinGraph_slabLift_sqBox (c : ℤ × ℤ) (r : ℕ) {x y : slab 3 k}
    (hx : x ∈ slabLift k (sqBox c r)) (hy : y ∈ slabLift k (sqBox c r)) :
    (withinGraph (slabGraph 3 k) (slabLift k (sqBox c r))).Reachable x y := by
  have key : ∀ a ∈ slabLift k (sqBox c r),
      (withinGraph (slabGraph 3 k) (slabLift k (sqBox c r))).Reachable (baseVertex k c) a := by
    intro a ha
    have h := edgeSet_openConnIn_center k c ha
    rw [mem_openConnIn_iff_pathIn, openGraph_edgeSet] at h
    exact reachable_withinGraph_of_pathIn h
  exact (key x hx).symm.trans (key y hy)

/-- The column ball as a `Finset`. [folklore] -/
def ballFinset (c : ℤ × ℤ) (r : ℕ) : Finset (slab 3 k) := (slabLift_finite k (sqBox_finite c r)).toFinset

/-- The underlying set of `ballFinset`. [folklore] -/
@[simp] theorem coe_ballFinset (c : ℤ × ℤ) (r : ℕ) :
    (↑(ballFinset k c r) : Set (slab 3 k)) = slabLift k (sqBox c r) := Set.Finite.coe_toFinset _

/-- Membership in `ballFinset`. [folklore] -/
@[simp] theorem mem_ballFinset {c : ℤ × ℤ} {r : ℕ} {x : slab 3 k} :
    x ∈ ballFinset k c r ↔ x ∈ slabLift k (sqBox c r) := Set.Finite.mem_toFinset _

/-- The base vertex over the centre lies in the ball. [folklore] -/
theorem baseVertex_mem_ballFinset (c : ℤ × ℤ) (r : ℕ) : baseVertex k c ∈ ballFinset k c r := by
  simp [sqBox]

/-- Connectivity of the column ball, `Finset` form. [folklore] -/
theorem ballFinset_conn (c : ℤ × ℤ) (r : ℕ) :
    ∀ x ∈ ballFinset k c r, ∀ y ∈ ballFinset k c r,
      (withinGraph (slabGraph 3 k) ↑(ballFinset k c r)).Reachable x y := by
  intro x hx y hy
  rw [coe_ballFinset]
  exact reachable_withinGraph_slabLift_sqBox k c r ((mem_ballFinset k).1 hx) ((mem_ballFinset k).1 hy)

end ColumnBalls

/-! ## No two infinite clusters on the slab (Bollobás–Riordan 2006, Ch. 5, Lemma 2) -/

section TwoClusters

variable (k : ℕ)

/-- Two infinite open clusters, not joined, both meeting `\overline{B_m}`. [folklore] -/
def twoInfNear (m : ℕ) : Set (BondConfig (slab 3 k)) :=
  {ω | ∃ a ∈ slabLift k (sqBox 0 m), ∃ b ∈ slabLift k (sqBox 0 m),
    ω ∈ percolatesAt a ∧ ω ∈ percolatesAt b ∧ ¬(openGraph ω).Reachable a b}

/-- `I₂ ⊆ ⋃_m twoInfNear m`. [folklore] -/
theorem exactlyTwoInfClusters_subset_iUnion_twoInfNear :
    exactlyTwoInfClusters (slab 3 k) ⊆ ⋃ m, twoInfNear k m := by
  rintro ω ⟨a, b, ha, hb, hab, -⟩
  obtain ⟨m, hm⟩ := exists_subset_slabLift_sqBox k (Set.toFinite {a, b})
  exact Set.mem_iUnion.2 ⟨m, a, hm (by simp), b, hm (by simp), ha, hb, hab⟩

/-- **No two infinite clusters** (Bollobás–Riordan 2006, Ch. 5, Lemma 2, pp. 105–106, the case
`k = 2`: "Suppose for a contradiction that `P(I_k) > 0` … there is an `n` such that
`P(T_{n,k}) > 0` … `P(I₁) > 0`. But then `P(I_k) = P(I₁) = 1` by Lemma 1. As `I_k ∩ I₁ = ∅`, this
is impossible"): `P_p(I₂) = 0` on the slab for `p > 0`. By the ergodicity of planar translations
(`ergodic_slabRelabel_shift`) the invariant event `I₂` has probability `0` or `1`; if `1`, both
clusters meet some `\overline{B_m}` with positive probability, and opening the lattice edges of
`\overline{B_m}` gives `I₁` by the merge lemma `openEdges_edgesIn_mem_exactlyOneInfCluster` of
`UniquenessInfiniteCluster.lean` (whose `ℤ^d` instance is `bondPercolation_exactlyTwoInfClusters_eq_zero`
there), so `I₁ ⊆ I₂ᶜ` would have positive probability by insertion tolerance.
[cite: BollobasRiordanPercolation2006, Ch. 5, Lemma 2 (pp. 105–106)] -/
theorem bondPercolation_exactlyTwoInfClusters_slab_eq_zero {p : unitInterval} (hp : 0 < (p : ℝ)) :
    bondPercolation (slabGraph 3 k) p (exactlyTwoInfClusters (slab 3 k)) = 0 := by
  classical
  set P := bondPercolation (slabGraph 3 k) p with hP
  have hmeas : MeasurableSet (exactlyTwoInfClusters (slab 3 k)) := measurableSet_exactlyTwoInfClusters
  rcases (ergodic_slabRelabel_shift k p (v := (1, 0)) (by simp)).toPreErgodic.prob_eq_zero_or_one
      hmeas (preimage_relabel_exactlyTwoInfClusters (slabEquiv k (planarShift (1, 0)))) with h0 | h1
  · exact h0
  exfalso
  have hU : P (⋃ m, twoInfNear k m ∩ exactlyTwoInfClusters (slab 3 k)) ≠ 0 := by
    have hsub : exactlyTwoInfClusters (slab 3 k) ⊆
        ⋃ m, twoInfNear k m ∩ exactlyTwoInfClusters (slab 3 k) := fun ω hω => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 (exactlyTwoInfClusters_subset_iUnion_twoInfNear k hω)
      exact Set.mem_iUnion.2 ⟨m, hm, hω⟩
    intro h0
    have h := measure_mono_null hsub h0
    rw [h1] at h
    exact one_ne_zero h
  rw [Ne, measure_iUnion_null_iff, not_forall] at hU
  obtain ⟨m, hm⟩ := hU
  set B : Finset (slab 3 k) := ballFinset k 0 m with hB
  set F : Finset (Sym2 (slab 3 k)) := edgesIn (slabGraph 3 k) B with hF
  have hFE : (↑F : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet := fun e he =>
    (mem_edgesIn_iff.1 (Finset.mem_coe.1 he)).1
  have hpos : 0 < P.real (twoInfNear k m ∩ exactlyTwoInfClusters (slab 3 k)) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hm (measure_ne_top _ _)
  -- opening the edges of the box gives `I₁`
  have hone : 0 < P.real (exactlyOneInfCluster (slab 3 k)) :=
    bondPercolation_real_pos_of_openEdges (slabGraph 3 k) hp F hFE measurableSet_exactlyOneInfCluster
      hpos fun ω hω => by
        obtain ⟨⟨a₀, ha₀, b₀, hb₀, ha₀p, hb₀p, hab₀⟩, a₁, b₁, ha₁, hb₁, hab₁, hall⟩ := hω
        refine openEdges_edgesIn_mem_exactlyOneInfCluster (ballFinset_conn k 0 m) ⟨a₀, ha₀p⟩
          fun c hc => ?_
        -- every infinite cluster is joined to `a₀` or to `b₀`, both in the box
        have key : (openGraph ω).Reachable c a₀ ∨ (openGraph ω).Reachable c b₀ := by
          rcases hall a₀ ha₀p with h0 | h0 <;> rcases hall b₀ hb₀p with h0' | h0' <;>
            rcases hall c hc with hc' | hc'
          · exact absurd (h0.trans h0'.symm) hab₀
          · exact absurd (h0.trans h0'.symm) hab₀
          · exact Or.inl (hc'.trans h0.symm)
          · exact Or.inr (hc'.trans h0'.symm)
          · exact Or.inr (hc'.trans h0'.symm)
          · exact Or.inl (hc'.trans h0.symm)
          · exact absurd (h0.trans h0'.symm) hab₀
          · exact absurd (h0.trans h0'.symm) hab₀
        rcases key with h | h
        · exact ⟨a₀, (mem_ballFinset k).2 ha₀, h⟩
        · exact ⟨b₀, (mem_ballFinset k).2 hb₀, h⟩
  have hnull : P (exactlyOneInfCluster (slab 3 k)) = 0 :=
    measure_mono_null (fun ω h1' h2 => Set.disjoint_left.1 disjoint_exactlyOne_exactlyTwo h1' h2)
      ((prob_compl_eq_zero_iff hmeas).2 h1)
  rw [measureReal_def, hnull, ENNReal.toReal_zero] at hone
  exact lt_irrefl _ hone

end TwoClusters

/-! ## No three infinite clusters on the slab: cut-balls (Bollobás–Riordan 2006, Ch. 5, Thm. 4) -/

section CutBalls

variable (k : ℕ)

/-- Three infinite open clusters, pairwise not joined, all meeting `\overline{B_r}`. [folklore] -/
def threeNear (r : ℕ) : Set (BondConfig (slab 3 k)) :=
  {ω | ∃ a ∈ slabLift k (sqBox 0 r), ∃ b ∈ slabLift k (sqBox 0 r), ∃ c ∈ slabLift k (sqBox 0 r),
    ω ∈ percolatesAt a ∧ ω ∈ percolatesAt b ∧ ω ∈ percolatesAt c ∧
    ¬(openGraph ω).Reachable a b ∧ ¬(openGraph ω).Reachable a c ∧ ¬(openGraph ω).Reachable b c}

/-- `{N ≥ 3} ⊆ ⋃_r threeNear r`. [folklore] -/
theorem threeInfClusters_subset_iUnion_threeNear :
    threeInfClusters (slab 3 k) ⊆ ⋃ r, threeNear k r := by
  rintro ω ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  obtain ⟨r, hr⟩ := exists_subset_slabLift_sqBox k (Set.toFinite {a, b, c})
  exact Set.mem_iUnion.2 ⟨r, a, hr (by simp), b, hr (by simp), c, hr (by simp), ha, hb, hc,
    hab, hac, hbc⟩

/-- **The cut-ball event at `c + B_r`**: the column ball `\overline{c + B_r}` is a cut set
(`IsCutSet`, `UniquenessInfiniteCluster.lean`: all lattice edges inside it are open, and three
open neighbours lie in distinct infinite clusters of the configuration with steps avoiding it) —
the slab copy of `cutBall` there (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, p. 107,
`T_r(x)`). [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 107, the event T_r(x))] -/
def slabCutBall (c : ℤ × ℤ) (r : ℕ) : Set (BondConfig (slab 3 k)) :=
  {ω | IsCutSet (slabGraph 3 k) (ballFinset k c r) ω}

/-- `slabCutBall` is measurable (as `measurableSet_cutBall` of `UniquenessInfiniteCluster.lean`).
[folklore] -/
theorem measurableSet_slabCutBall (c : ℤ × ℤ) (r : ℕ) : MeasurableSet (slabCutBall k c r) := by
  classical
  set K := ballFinset k c r with hK
  set S : SimpleGraph (slab 3 k) := withinGraph ⊤ (↑K : Set (slab 3 k))ᶜ with hS
  have heq : slabCutBall k c r = {ω | (↑(edgesIn (slabGraph 3 k) K) : Set (Sym2 (slab 3 k))) ⊆ ω} ∩
      ⋃ w : Fin 3 → slab 3 k, ((⋂ i, {_ω | w i ∉ K}) ∩
        (⋂ i, ⋃ x ∈ K, {ω : BondConfig (slab 3 k) | s(x, w i) ∈ ω ∧ x ≠ w i}) ∩
        (⋂ i, ⋂ j, {_ω | i = j} ∪ (openConnVia S (w i) (w j))ᶜ) ∩
        (⋂ i, percolatesVia S (w i))) := by
    ext ω
    simp only [slabCutBall, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff, exists_prop]
    constructor
    · rintro ⟨h1, w, h2, h3, h4, h5⟩
      refine ⟨h1, w, ⟨⟨h2, h3⟩, fun i j => ?_⟩, h5⟩
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr fun h => hij (h4 i j h)
    · rintro ⟨h1, w, ⟨⟨h2, h3⟩, h4⟩, h5⟩
      refine ⟨h1, w, h2, h3, fun i j h => ?_, h5⟩
      rcases h4 i j with hij | hij
      · exact hij
      · exact absurd h hij
  rw [heq]
  refine (measurableSet_setOf_subset (Finset.countable_toSet _)).inter
    (MeasurableSet.iUnion fun w => (((MeasurableSet.iInter fun i => MeasurableSet.const _).inter
      (MeasurableSet.iInter fun i => MeasurableSet.biUnion (Finset.countable_toSet _)
        fun x _ => (measurableSet_mem _).inter (MeasurableSet.const _))).inter
      (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (MeasurableSet.const _).union
        (measurableSet_openConnVia S (w i) (w j)).compl)).inter
      (MeasurableSet.iInter fun i => measurableSet_percolatesVia S (w i)))

/-- **Cut-balls have positive probability** as soon as three disjoint infinite clusters meet
`\overline{B_r}` with positive probability (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4,
pp. 107–108: "Hence `P(T_r(x₀)) > 0`"): opening the edges of the ball turns three disjoint
infinite clusters meeting it into a cut set (`isCutSet_openEdges_of_three`), at a bounded cost
(insertion tolerance, `bondPercolation_real_pos_of_openEdges`).
[cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (pp. 107–108)] -/
theorem real_slabCutBall_pos {p : unitInterval} (hp : 0 < (p : ℝ)) {r : ℕ}
    (hr : bondPercolation (slabGraph 3 k) p (threeNear k r) ≠ 0) :
    0 < (bondPercolation (slabGraph 3 k) p).real (slabCutBall k 0 r) := by
  classical
  set P := bondPercolation (slabGraph 3 k) p with hP
  set K := ballFinset k 0 r with hK
  set F : Finset (Sym2 (slab 3 k)) := edgesIn (slabGraph 3 k) K with hF
  have hFE : (↑F : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet := fun e he =>
    (mem_edgesIn_iff.1 (Finset.mem_coe.1 he)).1
  have hpos : 0 < P.real (threeNear k r ∩ {ω | ω ⊆ (slabGraph 3 k).edgeSet}) := by
    have : P.real (threeNear k r) ≤ P.real (threeNear k r ∩ {ω | ω ⊆ (slabGraph 3 k).edgeSet}) := by
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := (slabGraph 3 k).edgeSet)
        (p := p)] with ω hω hmem
      exact ⟨hmem, hω⟩
    refine lt_of_lt_of_le ?_ this
    rw [measureReal_def]
    exact ENNReal.toReal_pos hr (measure_ne_top _ _)
  refine bondPercolation_real_pos_of_openEdges (slabGraph 3 k) hp F hFE
    (measurableSet_slabCutBall k 0 r) hpos fun ω hω => ?_
  obtain ⟨⟨a, ha, b, hb, c, hc, hap, hbp, hcp, hab, hac, hbc⟩, hωE⟩ := hω
  refine isCutSet_openEdges_of_three (x := ![a, b, c]) hωE (fun i => ?_) (fun i => ?_)
    (fin3_of_pairwise (fun x y h => h.symm) hab hac hbc)
  · fin_cases i <;> simp [ha, hb, hc]
  · fin_cases i
    · simpa using hap
    · simpa using hbp
    · simpa using hcp

/-- The cut-ball event at centre `c`, as the translate of the cut-ball event at the origin.
[cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 108, T_r(x))] -/
def slabCutBallAt (c : ℤ × ℤ) (r : ℕ) : Set (BondConfig (slab 3 k)) :=
  slabRelabel k (planarShift (-c)) ⁻¹' slabCutBall k 0 r

/-- `slabCutBallAt` is measurable. [folklore] -/
theorem measurableSet_slabCutBallAt (c : ℤ × ℤ) (r : ℕ) : MeasurableSet (slabCutBallAt k c r) :=
  (measurableSet_slabCutBall k 0 r).preimage (slabRelabel k (planarShift (-c))).measurable

/-- Translation invariance: `P_p(slabCutBallAt c r) = P_p(slabCutBall 0 r)` (Bollobás–Riordan 2006,
Ch. 5, (2), p. 107: "for all sites `x ∈ X₀` we have `P(T_r(x)) = a`").
[cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 ((2), p. 107)] -/
theorem real_slabCutBallAt (p : unitInterval) (c : ℤ × ℤ) (r : ℕ) :
    (bondPercolation (slabGraph 3 k) p).real (slabCutBallAt k c r) =
      (bondPercolation (slabGraph 3 k) p).real (slabCutBall k 0 r) :=
  real_preimage_slabRelabel k (planarShift (-c)) (planarAdj_planarShift (-c)) p _

/-- A configuration in `slabCutBallAt c r` has a cut set at `\overline{c + B_r}` (transport of
cut sets by the lattice isomorphism `slabIso`, `IsCutSet.image`). [folklore] -/
theorem isCutSet_of_mem_slabCutBallAt {c : ℤ × ℤ} {r : ℕ} {ω : BondConfig (slab 3 k)}
    (h : ω ∈ slabCutBallAt k c r) : IsCutSet (slabGraph 3 k) (ballFinset k c r) ω := by
  classical
  set ψ := (slabIso k (planarShift (-c)) (planarAdj_planarShift (-c))).symm with hψ
  have h' := IsCutSet.image ψ h
  have hball : (ballFinset k 0 r).image ψ = ballFinset k c r := by
    apply Finset.coe_injective
    rw [Finset.coe_image, coe_ballFinset, coe_ballFinset]
    ext y
    rw [show (⇑ψ : slab 3 k → slab 3 k) = ⇑(slabEquiv k (planarShift (-c))).symm from rfl,
      Set.mem_image_equiv, Equiv.symm_symm, mem_slabLift_iff, planar_slabEquiv, mem_slabLift_iff]
    simp only [planarShift_apply, sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero,
      sub_zero, ← sub_eq_add_neg, Prod.fst_sub, Prod.snd_sub]
  have hω : BondConfig.relabel (sym2Equiv ψ.toEquiv) (slabRelabel k (planarShift (-c)) ω) = ω :=
    relabel_symm_relabel (slabEquiv k (planarShift (-c))) ω
  rw [hball, hω] at h'
  exact h'

/-! ### The grid of centres and the counting -/

/-- The grid of ball slabCentres `(2r+1)·(i, j)`, `|i|, |j| ≤ m`. [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 109)] -/
def slabCentres (r m : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(m : ℤ)) m ×ˢ Finset.Icc (-(m : ℤ)) m).image
    fun ij => ((2 * r + 1 : ℤ) * ij.1, (2 * r + 1 : ℤ) * ij.2)

/-- The half-width of the box containing the `r+1`-neighbourhoods of all slabCentres. [folklore] -/
def gridBox (r m : ℕ) : ℕ := (2 * r + 1) * m + r + 1

/-- There are `(2m+1)²` slabCentres. [folklore] -/
theorem card_slabCentres (r m : ℕ) : (slabCentres r m).card = (2 * m + 1) ^ 2 := by
  have hA : (2 * r + 1 : ℤ) ≠ 0 := by positivity
  have hinj : Function.Injective fun ij : ℤ × ℤ => ((2 * r + 1 : ℤ) * ij.1, (2 * r + 1 : ℤ) * ij.2) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (mul_left_cancel₀ hA h.1) (mul_left_cancel₀ hA h.2)
  have hI : (Finset.Icc (-(m : ℤ)) m).card = 2 * m + 1 := by
    rw [Int.card_Icc]; omega
  rw [slabCentres, Finset.card_image_of_injective _ hinj, Finset.card_product, hI]
  ring

/-- Description of the slabCentres. [folklore] -/
theorem mem_slabCentres_iff {r m : ℕ} {c : ℤ × ℤ} :
    c ∈ slabCentres r m ↔ ∃ i j : ℤ, |i| ≤ m ∧ |j| ≤ m ∧ c = ((2 * r + 1 : ℤ) * i, (2 * r + 1 : ℤ) * j) := by
  simp only [slabCentres, Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Prod.exists, abs_le]
  constructor
  · rintro ⟨i, j, ⟨⟨hi1, hi2⟩, hj1, hj2⟩, rfl⟩
    exact ⟨i, j, ⟨hi1, hi2⟩, ⟨hj1, hj2⟩, rfl⟩
  · rintro ⟨i, j, ⟨hi1, hi2⟩, ⟨hj1, hj2⟩, rfl⟩
    exact ⟨i, j, ⟨⟨hi1, hi2⟩, hj1, hj2⟩, rfl⟩

/-- The `r+1`-neighbourhood of every centre lies in `B_{gridBox r m}`. [folklore] -/
theorem sqBox_succ_subset_of_mem_slabCentres {r m : ℕ} {c : ℤ × ℤ} (hc : c ∈ slabCentres r m) :
    sqBox c (r + 1) ⊆ sqBox 0 (gridBox r m) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_slabCentres_iff.1 hc
  have hA : (0 : ℤ) ≤ 2 * r + 1 := by positivity
  have hi' : |(2 * r + 1 : ℤ) * i| ≤ (2 * r + 1 : ℤ) * m := by
    rw [abs_mul, abs_of_nonneg hA]; exact mul_le_mul_of_nonneg_left hi hA
  have hj' : |(2 * r + 1 : ℤ) * j| ≤ (2 * r + 1 : ℤ) * m := by
    rw [abs_mul, abs_of_nonneg hA]; exact mul_le_mul_of_nonneg_left hj hA
  intro z hz
  simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, gridBox] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  rw [abs_le] at hi' hj' hz1 hz2
  rw [abs_le, abs_le]
  push_cast at hz1 hz2 ⊢
  constructor <;> constructor <;> linarith

/-- Distinct slabCentres have disjoint column balls. [folklore] -/
theorem disjoint_ball_of_ne {r m : ℕ} {c c' : ℤ × ℤ} (hc : c ∈ slabCentres r m) (hc' : c' ∈ slabCentres r m)
    (hne : c ≠ c') : Disjoint (slabLift k (sqBox c r)) (slabLift k (sqBox c' r)) := by
  obtain ⟨i, j, -, -, rfl⟩ := mem_slabCentres_iff.1 hc
  obtain ⟨i', j', -, -, rfl⟩ := mem_slabCentres_iff.1 hc'
  have hA : (0 : ℤ) ≤ 2 * r + 1 := by positivity
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq, abs_le] at hx hx'
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := hx'
  apply hne
  have key : ∀ a a' : ℤ, (∃ t : ℤ, -(r : ℤ) ≤ t - (2 * r + 1) * a ∧ t - (2 * r + 1) * a ≤ r ∧
      -(r : ℤ) ≤ t - (2 * r + 1) * a' ∧ t - (2 * r + 1) * a' ≤ r) → a = a' := by
    intro a a' ⟨t, ha1, ha2, ha3, ha4⟩
    by_contra hne'
    have h1 : (1 : ℤ) ≤ |a - a'| := Int.one_le_abs (sub_ne_zero.2 hne')
    have h2 : |(2 * r + 1 : ℤ) * (a - a')| ≤ 2 * r := by
      rw [abs_le]; constructor <;> nlinarith
    rw [abs_mul, abs_of_nonneg hA] at h2
    nlinarith
  rw [key i i' ⟨_, h1, h2, h1', h2'⟩, key j j' ⟨_, h3, h4, h3', h4'⟩]

/-- The boundary `∂B_n` as a finite set. [folklore] -/
def sphereFinset (n : ℕ) : Finset (ℤ × ℤ) :=
  ({-(n : ℤ), (n : ℤ)} ×ˢ Finset.Icc (-(n : ℤ)) n) ∪ (Finset.Icc (-(n : ℤ)) n ×ˢ {-(n : ℤ), (n : ℤ)})

/-- `∂B_n ⊆ sphereFinset n`. [folklore] -/
theorem mem_sphereFinset_of_mem_sqSphere {n : ℕ} {z : ℤ × ℤ} (hz : z ∈ sqSphere 0 n) :
    z ∈ sphereFinset n := by
  simp only [sqSphere, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero] at hz
  have h1 := abs_le.1 (le_of_max_le_left hz.le)
  have h2 := abs_le.1 (le_of_max_le_right hz.le)
  have hz' : |z.1| = n ∨ |z.2| = n := by
    rcases max_choice |z.1| |z.2| with h | h
    · exact Or.inl (h ▸ hz)
    · exact Or.inr (h ▸ hz)
  simp only [sphereFinset, Finset.mem_union, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_Icc]
  rcases hz' with h | h
  · rw [abs_eq (by positivity)] at h
    left
    exact ⟨by omega, h2.1, h2.2⟩
  · rw [abs_eq (by positivity)] at h
    right
    exact ⟨⟨h1.1, h1.2⟩, by omega⟩

/-- `|sphereFinset n| ≤ 4(2n+1)`. [folklore] -/
theorem card_sphereFinset_le (n : ℕ) : (sphereFinset n).card ≤ 4 * (2 * n + 1) := by
  have hI : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc]; omega
  have h2 : ({-(n : ℤ), (n : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  calc (sphereFinset n).card
      ≤ ({-(n : ℤ), (n : ℤ)} ×ˢ Finset.Icc (-(n : ℤ)) n).card +
          (Finset.Icc (-(n : ℤ)) n ×ˢ ({-(n : ℤ), (n : ℤ)} : Finset ℤ)).card := Finset.card_union_le _ _
    _ ≤ 2 * (2 * n + 1) + (2 * n + 1) * 2 := by
        rw [Finset.card_product, Finset.card_product, hI]
        exact add_le_add (Nat.mul_le_mul_right _ h2) (Nat.mul_le_mul_left _ h2)
    _ = 4 * (2 * n + 1) := by ring

/-- A finite set of slab vertices over a planar finite set `T` has at most `|T|·(k+1)` elements.
[folklore] -/
theorem card_le_of_slabLift {S : Set (ℤ × ℤ)} (T : Finset (ℤ × ℤ)) (hST : S ⊆ ↑T)
    (Lf : Finset (slab 3 k)) (hLf : (↑Lf : Set (slab 3 k)) = slabLift k S) :
    Lf.card ≤ T.card * (k + 1) := by
  have hmaps : Set.MapsTo (fun x : slab 3 k => (planar k x, x.1 0)) ↑Lf
      ↑(T ×ˢ Finset.Icc (0 : ℤ) k) := by
    intro x hx
    rw [hLf, mem_slabLift_iff] at hx
    simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Finset.mem_coe, Set.mem_Icc]
    exact ⟨hST hx, x.2.1, x.2.2⟩
  have hinj : Set.InjOn (fun x : slab 3 k => (planar k x, x.1 0)) ↑Lf := by
    intro x _ y _ hxy
    simp only [Prod.mk.injEq, planar] at hxy
    obtain ⟨⟨h1, h2⟩, h0⟩ := hxy
    apply Subtype.ext
    funext j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have h := Finset.card_le_card_of_injOn _ hmaps hinj
  have hI : (Finset.Icc (0 : ℤ) k).card = k + 1 := by rw [Int.card_Icc]; omega
  rwa [Finset.card_product, hI] at h

/-- The inner boundary of `\overline{B_n}` (as a `Finset`) lies over `∂B_n`. [folklore] -/
theorem innerBoundary_subset (n : ℕ) (Lf : Finset (slab 3 k))
    (hLf : (↑Lf : Set (slab 3 k)) = slabLift k (sqSphere 0 n)) :
    innerBoundary (slabGraph 3 k) (ballFinset k 0 n) ⊆ Lf := by
  intro x hx
  rw [mem_innerBoundary_iff] at hx
  obtain ⟨hxB, y, hyB, hxy⟩ := hx
  rw [← Finset.mem_coe, hLf]
  exact mem_slabLift_sqSphere_of_adj k hxy.symm (fun h => hyB ((mem_ballFinset k).2 h))
    ((mem_ballFinset k).1 hxB)

/-- **The counting step** (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, p. 109, via their
Lemma 3 = `card_add_two_le_card_of_isHub`): in a lattice configuration, the number of centres of
the grid carrying a cut-ball is at most `|\overline{∂B_n}|`, `n = gridBox r m`, since the
cut-balls are pairwise disjoint hubs (`IsCutSet.isHub`) of the open graph of `\overline{B_n}`
relative to its inner boundary. [cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (p. 109)] -/
theorem card_filter_slabCutBallAt_le {ω : BondConfig (slab 3 k)} (hω : ω ⊆ (slabGraph 3 k).edgeSet)
    (r m : ℕ) (Lf : Finset (slab 3 k))
    (hLf : (↑Lf : Set (slab 3 k)) = slabLift k (sqSphere 0 (gridBox r m)))
    [DecidablePred fun c => ω ∈ slabCutBallAt k c r] :
    ((slabCentres r m).filter fun c => ω ∈ slabCutBallAt k c r).card ≤ Lf.card := by
  classical
  set S := (slabCentres r m).filter fun c => ω ∈ slabCutBallAt k c r with hS
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · rw [hS0, Finset.card_empty]; exact Nat.zero_le _
  set Λf : Finset (slab 3 k) := ballFinset k 0 (gridBox r m) with hΛf
  have hScen : ∀ c ∈ S, c ∈ slabCentres r m := fun c hc => (Finset.mem_filter.1 hc).1
  have hinj : Set.InjOn (fun c : ℤ × ℤ => ballFinset k c r) ↑S := by
    intro c hc c' hc' h
    by_contra hne
    have hdisj := disjoint_ball_of_ne k (hScen c hc) (hScen c' hc') hne
    have h' : ballFinset k c r = ballFinset k c' r := h
    have h1 : baseVertex k c ∈ slabLift k (sqBox c' r) := by
      rw [← mem_ballFinset k, ← h']; exact baseVertex_mem_ballFinset k c r
    exact Set.disjoint_left.1 hdisj ((mem_ballFinset k).1 (baseVertex_mem_ballFinset k c r)) h1
  have hcard : (S.image fun c => ballFinset k c r).card = S.card := Finset.card_image_of_injOn hinj
  have hhub := card_add_two_le_card_of_isHub (withinGraph (openGraph ω) ↑Λf)
    (innerBoundary (slabGraph 3 k) Λf) (S.image fun c => ballFinset k c r) (hSne.image _) ?_ ?_
  · have := Finset.card_le_card (innerBoundary_subset k (gridBox r m) Lf hLf)
    rw [← hΛf] at this
    omega
  · intro K hK K' hK' hKK'
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hK
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 hK'
    have hcc' : c ≠ c' := fun h => hKK' (h ▸ rfl)
    rw [← Finset.disjoint_coe, coe_ballFinset, coe_ballFinset]
    exact disjoint_ball_of_ne k (hScen c hc) (hScen c' hc') hcc'
  · intro K hK
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hK
    have hcn := sqBox_succ_subset_of_mem_slabCentres (hScen c hc)
    refine (isCutSet_of_mem_slabCutBallAt k (Finset.mem_filter.1 hc).2).isHub hω
      ⟨_, baseVertex_mem_ballFinset k c r⟩ (fun x hx => ?_) (fun x hx v hxv => ?_) (ballFinset_conn k c r)
    · rw [mem_ballFinset] at hx ⊢
      exact slabLift_mono k ((sqBox_mono c (Nat.le_succ r)).trans hcn) hx
    · rw [mem_ballFinset] at hx ⊢
      exact slabLift_mono k hcn (mem_slabLift_sqBox_succ_of_adj k hxv hx)

/-- **Expected number of cut-balls** (Bollobás–Riordan 2006, Ch. 5, proof of Thm. 4, p. 108:
"by linearity of expectation the expected number of cut-balls is `Σ_w P(T_r(w)) = a|W|`"):
`(2m+1)² · P_p(slabCutBall 0 r) ≤ 4(2n+1)(k+1)`, `n = gridBox r m`.
[cite: BollobasRiordanPercolation2006, Ch. 5, proof of Thm. 4 (pp. 108–109)] -/
theorem card_mul_real_slabCutBall_le (p : unitInterval) (r m : ℕ) :
    (2 * m + 1 : ℝ) ^ 2 * (bondPercolation (slabGraph 3 k) p).real (slabCutBall k 0 r) ≤
      ((4 * (2 * gridBox r m + 1) * (k + 1) : ℕ) : ℝ) := by
  classical
  set P := bondPercolation (slabGraph 3 k) p with hP
  set n := gridBox r m with hn
  have hSfin : (sqSphere (0 : ℤ × ℤ) n).Finite := (sqBox_finite 0 n).subset (sqSphere_subset_sqBox 0 n)
  set Lf : Finset (slab 3 k) := (slabLift_finite k hSfin).toFinset with hLfdef
  have hLf : (↑Lf : Set (slab 3 k)) = slabLift k (sqSphere 0 n) := Set.Finite.coe_toFinset _
  have hLcard : Lf.card ≤ 4 * (2 * n + 1) * (k + 1) :=
    (card_le_of_slabLift k (sphereFinset n) (fun z hz => mem_sphereFinset_of_mem_sqSphere hz)
      Lf hLf).trans (Nat.mul_le_mul_right _ (card_sphereFinset_le n))
  have hInt : ∀ c, Integrable ((slabCutBallAt k c r).indicator (1 : BondConfig (slab 3 k) → ℝ)) P :=
    fun c => (integrable_const (1 : ℝ)).indicator (measurableSet_slabCutBallAt k c r)
  have hsum : ∑ c ∈ slabCentres r m, P.real (slabCutBallAt k c r) =
      ∫ ω, ∑ c ∈ slabCentres r m, (slabCutBallAt k c r).indicator (1 : BondConfig (slab 3 k) → ℝ) ω ∂P := by
    rw [integral_finsetSum _ fun c _ => hInt c]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_indicator_one (measurableSet_slabCutBallAt k c r)]
  have hpt : ∀ᵐ ω ∂P, ∑ c ∈ slabCentres r m,
      (slabCutBallAt k c r).indicator (1 : BondConfig (slab 3 k) → ℝ) ω ≤ (Lf.card : ℝ) := by
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := (slabGraph 3 k).edgeSet)
      (p := p)] with ω hω
    have heq : ∑ c ∈ slabCentres r m, (slabCutBallAt k c r).indicator (1 : BondConfig (slab 3 k) → ℝ) ω =
        (((slabCentres r m).filter fun c => ω ∈ slabCutBallAt k c r).card : ℝ) := by
      simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole]
    rw [heq]
    exact_mod_cast card_filter_slabCutBallAt_le k hω r m Lf hLf
  have hint : ∫ ω, ∑ c ∈ slabCentres r m,
      (slabCutBallAt k c r).indicator (1 : BondConfig (slab 3 k) → ℝ) ω ∂P ≤ ∫ _ω, (Lf.card : ℝ) ∂P :=
    integral_mono_ae (integrable_finsetSum _ fun c _ => hInt c) (integrable_const _) hpt
  rw [integral_const, smul_eq_mul, probReal_univ, one_mul] at hint
  have hconst : ∑ c ∈ slabCentres r m, P.real (slabCutBallAt k c r) =
      (2 * m + 1 : ℝ) ^ 2 * P.real (slabCutBall k 0 r) := by
    rw [Finset.sum_congr rfl fun c _ => real_slabCutBallAt k p c r, Finset.sum_const, card_slabCentres,
      nsmul_eq_mul]
    push_cast
    ring
  rw [← hconst, hsum]
  refine hint.trans ?_
  exact_mod_cast hLcard

/-- **No three infinite clusters** (Bollobás–Riordan 2006, Ch. 5, Thm. 4, main step; Grimmett
1999, §8.2, Thm. (8.1), the case `N ≥ 3` via trifurcations; the `ℤ^d` instance is
`bondPercolation_threeInfClusters_eq_zero` of `UniquenessInfiniteCluster.lean`): `P_p(N ≥ 3) = 0`
on the slab. Otherwise some `\overline{B_r}` meets three disjoint infinite clusters with positive
probability, cut-balls have positive probability `c₀`, and `(2m+1)² c₀ ≤ 4(2n+1)(k+1)` with
`n = (2r+1)m + r + 1` fails for large `m` (the slab is amenable: `O(m²)` centres against an
`O(m)` boundary). [cite: BollobasRiordanPercolation2006, Ch. 5, Thm. 4] -/
theorem bondPercolation_threeInfClusters_slab_eq_zero {p : unitInterval} (hp : 0 < (p : ℝ)) :
    bondPercolation (slabGraph 3 k) p (threeInfClusters (slab 3 k)) = 0 := by
  set P := bondPercolation (slabGraph 3 k) p with hP
  by_contra hne
  have hU : P (⋃ r, threeNear k r) ≠ 0 := fun h0 =>
    hne (measure_mono_null (threeInfClusters_subset_iUnion_threeNear k) h0)
  rw [Ne, measure_iUnion_null_iff, not_forall] at hU
  obtain ⟨r, hr⟩ := hU
  have hc₀ := real_slabCutBall_pos k hp hr
  set c₀ := P.real (slabCutBall k 0 r) with hc₀def
  set A : ℝ := 4 * (2 * r + 3) * (k + 1) with hA
  obtain ⟨m, hm⟩ := exists_nat_gt (A / c₀)
  have hbound := card_mul_real_slabCutBall_le k p r m
  have hM : (0 : ℝ) < 2 * m + 1 := by positivity
  have h1 : ((4 * (2 * gridBox r m + 1) * (k + 1) : ℕ) : ℝ) ≤ A * (2 * m + 1) := by
    rw [hA, gridBox]
    push_cast
    nlinarith
  have h2 : A < c₀ * (2 * m + 1) := by
    rw [div_lt_iff₀ hc₀] at hm
    nlinarith
  nlinarith

end CutBalls

/-! ## Uniqueness of the infinite cluster on slabs, and DST 2016 Thm. 1 from Lemma 6 -/

section Conclusion

variable (k : ℕ)

/-- **Almost surely at most one infinite open cluster on the slab** (`p > 0`; for `p = 0` there
is no open edge): the slab case of Aizenman–Kesten–Newman 1987 (Prop. 1.1, p. 3: "In any
irreducible, translation invariant model: if `P_∞ > 0`, then there is exactly one infinite
cluster (with probability one)") and Burton–Keane 1989 (Thm. 2, p. 3: "If `μ` is stationary and
has finite energy, then `μ`-almost every `x ∈ X` has at most one infinite cluster"), proved here
along Bollobás–Riordan 2006, Ch. 5, Lemma 2 and Thm. 4.
[cite: BurtonKeane1989, Thm. 2] [cite: AizenmanKestenNewmanCMP1987, Prop. 1.1] [cite: BollobasRiordanPercolation2006, Ch. 5, Thm. 4] -/
theorem ae_numInfiniteClusters_slab_le_one {p : unitInterval} (hp : 0 < (p : ℝ)) :
    ∀ᵐ ω ∂(bondPercolation (slabGraph 3 k) p), numInfiniteClusters ω ≤ 1 := by
  rw [ae_iff]
  exact measure_mono_null (fun ω hω => mem_union_of_not_numInfiniteClusters_le_one hω)
    (measure_union_null (bondPercolation_exactlyTwoInfClusters_slab_eq_zero k hp)
      (bondPercolation_threeInfClusters_slab_eq_zero k hp))

/-- **uniqueness of the infinite open cluster on slabs**
(`DuminilCopinSidoraviciusTassion2016_uniqueCluster`, DST 2016, §2.1, p. 4: "The infinite cluster
in `S_k` being unique almost surely [AKN87, BK89]"), proved by the Burton–Keane argument in the
cut-ball form of Bollobás–Riordan 2006, Ch. 5, Thm. 4 (`ae_numInfiniteClusters_slab_le_one`).
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 4)] [cite: BurtonKeane1989, Thm. 2] -/
theorem DuminilCopinSidoraviciusTassion2016_uniqueCluster_holds :
    DuminilCopinSidoraviciusTassion2016_uniqueCluster := by
  intro k _ p hθ
  exact ae_numInfiniteClusters_slab_le_one k (coe_pos_of_theta_slab_pos hθ)

end Conclusion

end Percolation.Literature
