import Mathlib.Analysis.SpecificLimits.Basic
import Percolation.Literature.BondPercolationSymmetry
import Percolation.Literature.Crossings
import Percolation.Literature.HalfSpace
import Percolation.Literature.HalfSpaceBGN
import Percolation.Literature.InequalitiesProofs
import Percolation.Literature.LatticeSymmetry
import Percolation.Literature.RSW
import Percolation.Literature.RussoFormula
import Percolation.Literature.SitePaths
import Percolation.Util.Linter

/-!
# Critical bond percolation on slabs: the Duminil-Copin–Sidoravicius–Tassion argument, I (DST 2016, §2.1: the finite-size criterion, Lemmata 4–5, eqs. (10)–(13), and the named inputs eq. (1), Lemma 6 and the renormalisation step of §2.2)

Towards the statement `DuminilCopinSidoraviciusTassion2016` of `HalfSpace.lean` (DST 2016, Thm. 1:
`θ_{S_k}(p_c(S_k)) = 0` for every slab `S_k = ℤ² × {0,…,k}`, `k > 0`), following the printed
proof (arXiv:1401.7130, §2); the multi-valued map principle (Lemma 7) is the sibling file
`MultiValuedMapPrinciple.lean`, and the argument is continued (§2.2 proved, eq. (1)
proved from uniqueness) in `SlabCriticalityInputs.lean`.

## The architecture of the printed proof (DST 2016, §2, "Outline of the proof", p. 4)

Fix `k` and `p` and assume `P_p[0 ↔ ∞ in S_k] > 0`. §2.1 constructs a finite-size criterion
(a "good edge" event of a `4n`-block, eq. (13) together with the uniqueness input eq. (1),
via Lemma 4 (square-root trick), Lemma 5 (a growth lemma on integer sequences), the gluing
Lemma 6 (proved in §2.3 from the multi-valued map principle, Lemma 7) and Harris' inequality);
§2.2 is the classical block (renormalisation) step: good edges form a `4`-dependent bond
percolation on `ℤ²` which percolates once `P[good] > 1 - η` (Liggett–Schonmann–Stacey 1997 /
Balister–Bollobás–Walters 2005), and since being good is a local event its probability is
continuous in the parameter, so some `q < p` still percolates: "`q ≥ p_c(k)` and therefore
`p > p_c(k)`" (p. 6). Hence `θ_{S_k}(p) > 0 ⇒ p > p_c(k)`, which is exactly the statement that
`θ_{S_k}(p_c(k)) = 0`.

## Content of this file

* `DuminilCopinSidoraviciusTassion2016_lemma5` — proved (DST 2016, Lemma 5, p. 5): if `1 ≤ α_n ≤ n` for all `n ≥ 1`, then
  `α_{3n} ≤ 4 α_n` for infinitely many `n` ("a sequence of positive integers such that
  `α_{3n} > 4α_n` for `n` large enough grows super-linearly").
* The vocabulary of DST 2016, "Notation" (p. 3) and §2.2 (p. 6): planar coordinates `planar`,
  lifts `slabLift k E = Ē`, the boxes `sqBox c n = c + B_n` (`B_n = [-n,n]²`) and their
  boundaries `sqSphere c n = c + ∂B_n`, the events `slabConn k B X Y = {X ⟷^B Y}` ("there
  exists an open cluster in `B̄` connecting `X̄` to `Ȳ`") and
  `slabUniqueConn k B X Y = {X ⟷^{!B!} Y}` (a unique such cluster), and the **good-edge event**
  `goodEvent k n u z i` of the coarse edge `{z, z + 4n eᵢ}` of `4nℤ²` (§2.2), with `S_{3n} = B_u`.
* Locality: `determinedBy_openConnIn` (the event `{x ↔ y in S}` is determined by the edges
  inside `S`, coordinates `Set.sym2 S`), `determinedBy_goodEvent` / `isLocalEvent_goodEvent`
  ("being good depends only on the state of the edges in a finite box", p. 6), and
  `continuous_real_goodEvent` (an instance of `continuous_bondPercolation_real_of_isLocalEvent`
  of `HalfSpaceBGN.lean`: the probability of a local event is continuous in `p`).
* `DuminilCopinSidoraviciusTassion2016_goodEvent_likely` — statement (DST 2016, §2.1, eq. (13) with eq. (1); §2.2:
  "Equations (13) and (1) guarantee the existence of `n` such that the `P_p`-probability that
  an edge is good is larger than `1 - η`"): the finite-size criterion holds at `p` when
  `θ_{S_k}(p) > 0`; derived below from eqs. (1) and (13).
* `DuminilCopinSidoraviciusTassion2016_renormalisation` — statement (DST 2016, §2.2: good edges form a `4`-dependent bond
  percolation on `4nℤ²`; "there exists `η > 0` such that whenever the probability to be good
  exceeds `1 - η`, the set of good edges percolates" [Liggett–Schonmann–Stacey 1997;
  Balister–Bollobás–Walters 2005] … "an infinite path of good edges … implies the existence of
  an infinite path of open edges … As a consequence, `q ≥ p_c(k)`"); proved in
  `SlabCriticalityInputs.lean`.
* `DuminilCopinSidoraviciusTassion2016_criticalProb_lt_of_criterion` — proved: §2.2's conclusion "there exists `q < p` such
  that an edge is good with `P_q`-probability larger than `1 - η` … therefore `p > p_c(k)`" from
  the two preceding statements and the proved continuity; whence
  `DuminilCopinSidoraviciusTassion2016.of_criterion`.
* Symmetries (Grimmett 1999, §1.6: invariance of `P_p` under lattice automorphisms), proved:
  `iff` forms of the transport lemmas of `LatticeSymmetry.lean` (`relabel_mem_openConnIn`,
  `preimage_relabel_openCrossing`), the automorphism `slabIso k g` of the slab induced by a
  bijection `g` of `ℤ²` preserving adjacency, `real_preimage_slabRelabel` (invariance of `P_p`),
  the transport of `X ⟷^B Y`, `X ⟷^{!B!} Y` (`preimage_slabRelabel_slabConn`,
  `preimage_slabRelabel_slabUniqueConn`), translations (`planarShift = Equiv.addRight`) and the
  diagonal reflection (`planarSwap = Equiv.prodComm`) with their action on boxes,
  `real_goodEvent_one_eq` (both coarse directions are equally likely to be good) and
  `real_slabUniqueConn_shift` (translation invariance of the uniqueness event).
* Paths (proved): `mem_openConnIn_iff_pathIn` (bridge to `PathIn` of `SitePaths.lean`),
  concatenation/reversal of open paths (`openConnIn_trans`, `openConnIn_reverse`; cf.
  `Percolation.Literature.PlanarDuality.openConnIn_trans` / `openConnIn_comm` of `PlanarDuality.lean`), boundary entry
  (`exists_sqSphere_openConnIn`), and the **gluing-by-uniqueness lemma** `slabConn_of_glue` /
  `real_glue_le` (DST 2016, §2.1, display before eq. (13): two crossings into a block carrying
  a unique boundary-touching cluster are joined), valid for lattice configurations, i.e.
  `P_p`-a.s.
* `sideSeg`, `sideEvent k n u s t = E_n(s, t)` (with `S_n = B_u`), `planarFlip` (reflection in
  a horizontal axis) with its action on boxes and segments, `real_sideEvent_translate` (the
  events `{S'_n ⟷^{B'_n} Y_n^±}` have the probability of `E_n(α_n, n)`, proved).
* `DuminilCopinSidoraviciusTassion2016_lemma4` — statement (DST 2016, Lemma 4, square-root trick), lattice form; proved below
  (`DuminilCopinSidoraviciusTassion2016_lemma4_holds`).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: Thm. 1 (p. 2), Notation (p. 3), §2.1: eq. (1), Lemma 4, Lemma 5, eqs.
  (10)–(13) and the displays between them, Lemma 6 (pp. 4–5); §2.2 (p. 6).
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §1.4 (`θ`, `p_c`), §1.6 (p. 16,
  invariance of `P_p` under lattice symmetries), §2.2 (local events).
* T. M. Liggett, R. H. Schonmann, A. M. Stacey, *Domination by product measures*, Ann. Probab.
  25 (1997), 71–95; P. Balister, B. Bollobás, M. Walters, *Continuum percolation with steps in
  the square or the disc*, Random Structures Algorithms 26 (2005), 392–403 (the classical
  dependent-percolation input of §2.2, cited by DST; only through
  `DuminilCopinSidoraviciusTassion2016_renormalisation`, which `SlabCriticalityInputs.lean`
  proves).
* L. Russo, Z. Wahrsch. Verw. Gebiete 56 (1981), 229–237, §4 (probabilities of local events are
  polynomials in `p`; `RussoFormula.lean`).

## Design choices

* The openness of the supercritical phase (`θ_{S_k}(p) > 0 ⇒ p_c(S_k) < p`) is stated with
  `criticalProb (slabGraph 3 k) (slabOrigin 3 k)` (a real number) and `p : unitInterval`,
  exactly the objects of `DuminilCopinSidoraviciusTassion2016`, and only as a hypothesis /
  conclusion of proved theorems (it is equivalent to the fact itself).
* Lemma 5 is stated for a sequence `α : ℕ → ℕ` with `1 ≤ α n ≤ n` for `n ≥ 1` (DST: "with
  values in `[0,n]`", and `α_n ∈ {1,…,n-1}` by construction, p. 5), conclusion
  `∀ N, ∃ n ≥ N, α (3n) ≤ 4 α n`; the value `α 0` is irrelevant.
* Planar sets are subsets of `ℤ × ℤ`; DST's `ℤ²`-coordinates of a slab vertex `x` are
  `(x 1, x 2)` here (the finite coordinate of `slab 3 k` is `x 0`, `HalfSpace.lean`). Boxes are
  written with an explicit centre, `sqBox c n = c + B_n`, `sqSphere c n = c + ∂B_n` (sup-norm
  ball and sphere of `ℤ × ℤ`; for `n ≥ 1` the latter is `B_n ∖ B_{n-1}` translated, and
  `sqSphere c 0 = {c}`), avoiding pointwise-translation machinery; the coarse lattice of §2.2
  is `Site 2` of `LatticeGraph.lean` (so that `percolatesAt`, `zdGraph 2` apply to the good-edge
  configuration), bridged by `coarsePt`. `X ⟷^B Y` is `openCrossing` of `Crossings.lean`
  applied to the lifts; "a unique open cluster in `B̄` connecting `X̄` to `Ȳ`" is spelled: some
  `x ∈ X̄`, `y ∈ Ȳ` are joined in `B̄`, and any two such pairs `(x, y)`, `(x', y')` have
  `x ↔ x'` in `B̄` (equivalent to uniqueness of the cluster, and usable without naming
  components of a random graph).
* The good-edge event is parameterised by the block size `n`, the radius `u` of
  `S_{3n} = B_{u_{3n}}` (`u_{3n} ≤ n`, from eq. (1); a datum of the construction depending on
  `p`), the base point `z` and the direction `i : Fin 2` (`z' = z + 4n eᵢ`,
  `R_n = z + 2n eᵢ + B_{6n}`). The statements quantify the good-edge probabilities at the
  base point `z = 0` only, for both directions: DST speak of "the probability to be good"
  (p. 6), one number by the invariance of `P_p` under the translations and the rotation by `π/2`
  of the slab; both directions are carried along, and the translation invariance is proved in
  `SlabCriticalityInputs.lean` (`real_goodEvent_shift`). In
  `DuminilCopinSidoraviciusTassion2016_renormalisation` the threshold `η` may depend on `k`
  (DST: a universal constant of `4`-dependent percolation on `ℤ²`); this is weaker, hence
  safe, and is all the proof uses (the proof in `SlabCriticalityInputs.lean` yields a
  universal `η`).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory Filter LatticeModels

/-! ## The openness of the supercritical phase of a slab (DST 2016, §2) -/

/-- `criticalProbIOf` unfolds to `criticalProb`. [folklore] -/
@[simp] theorem coe_criticalProbIOf {V : Type} (G : SimpleGraph V) (x : V) :
    (criticalProbIOf G x : ℝ) = criticalProb G x := rfl

/-- If `θ_x(q) > 0` then `p_c(x) ≤ q` (`p_c = inf ({p | θ_x(p) > 0} ∪ {1})`; Grimmett 1999,
§1.4, (1.8), p. 13). [cite: GrimmettPercolation1999, §1.4 (1.8) p. 13] -/
theorem criticalProb_le_of_theta_pos {V : Type} (G : SimpleGraph V) (x : V) (q : unitInterval)
    (h : 0 < theta G x q) : criticalProb G x ≤ q := by
  refine csInf_le ⟨0, ?_⟩ (Or.inl ⟨q.2, by simpa using h⟩)
  rintro r (⟨hr, -⟩ | hr)
  · exact hr.1
  · rw [Set.mem_singleton_iff] at hr
    rw [hr]; exact zero_le_one

/-- **Reduction** — DST 2016, Thm. 1 from **the openness of the supercritical phase**, the form in
 which §2 of the paper concludes (p. 4: "we assume that `P_p[0 ↔ ∞] > 0`" … p. 6: "As a consequence,
 `q ≥ p_c(k)` and therefore `p > p_c(k)`"; "Outline of the proof", p. 4: "This immediately implies
 that `P_{p_c}[0 ↔ ∞] = 0`"): if `θ_{S_k}(p) > 0 ⇒ p_c(k) < p` for every `p`, then at `p = p_c(k)`
 positivity of `θ` would give `p_c(k) < p_c(k)`; and `θ ≥ 0`. The hypothesis is equivalent to
 `DuminilCopinSidoraviciusTassion2016`, so it is not recorded as a separate statement. [cite:
 DuminilCopinSidoraviciusTassion2016, §2 (p. 4, Outline of the proof)]
-/
theorem DuminilCopinSidoraviciusTassion2016.of_criticalProb_lt
    (h : ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
      criticalProb (slabGraph 3 k) (slabOrigin 3 k) < (p : ℝ)) :
    DuminilCopinSidoraviciusTassion2016 := by
  intro k hk
  by_contra hne
  have hpos : 0 < theta (slabGraph 3 k) (slabOrigin 3 k)
      (criticalProbIOf (slabGraph 3 k) (slabOrigin 3 k)) :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hlt := h k hk _ hpos
  simp only [coe_criticalProbIOf, lt_self_iff_false] at hlt

/-! ## Lemma 5: a linearly bounded positive sequence cannot grow by `4` at every tripling -/

/-- Auxiliary growth estimate for Lemma 5: if `α (3n) > 4 α n` for all `n ≥ N` and
`1 ≤ α N`, then `4^j ≤ α (3^j N)` for every `j`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 5 (proof)] -/
theorem DuminilCopinSidoraviciusTassion2016_lemma5_growth (α : ℕ → ℕ) (N : ℕ) (hαN : 1 ≤ α N)
    (h : ∀ n, N ≤ n → 4 * α n < α (3 * n)) (j : ℕ) : 4 ^ j ≤ α (3 ^ j * N) := by
  induction j with
  | zero => simpa using hαN
  | succ j ih =>
    have hle : N ≤ 3 ^ j * N := Nat.le_mul_of_pos_left N (pow_pos (by norm_num) j)
    have hstep := h (3 ^ j * N) hle
    calc 4 ^ (j + 1) = 4 * 4 ^ j := by ring
      _ ≤ 4 * α (3 ^ j * N) := Nat.mul_le_mul_left 4 ih
      _ ≤ α (3 * (3 ^ j * N)) := hstep.le
      _ = α (3 ^ (j + 1) * N) := by ring_nf

/-- **DST 2016, Lemma 5** (p. 5): "There exist infinitely many `n` such that
`α_{3n} ≤ 4α_n`. *Proof.* A sequence of positive integers such that `α_{3n} > 4α_n` for `n`
large enough grows super-linearly. Since `α_n ≤ n`, we obtain the result." Stated for
`α : ℕ → ℕ` with `1 ≤ α n ≤ n` for `n ≥ 1`.
[cite: DuminilCopinSidoraviciusTassion2016, Lemma 5] -/
theorem DuminilCopinSidoraviciusTassion2016_lemma5 (α : ℕ → ℕ) (hpos : ∀ n, 1 ≤ n → 1 ≤ α n) (hle : ∀ n, 1 ≤ n → α n ≤ n) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧ 1 ≤ n ∧ α (3 * n) ≤ 4 * α n := by
  intro N
  by_contra hcon
  push Not at hcon
  -- work above `N' = max N 1`
  set N' := max N 1 with hN'
  have hN'1 : 1 ≤ N' := le_max_right _ _
  have hgrow : ∀ n, N' ≤ n → 4 * α n < α (3 * n) := fun n hn =>
    hcon n ((le_max_left _ _).trans hn) (hN'1.trans hn)
  have hj : ∀ j : ℕ, (4 : ℝ) ^ j ≤ 3 ^ j * N' := by
    intro j
    have h1 := DuminilCopinSidoraviciusTassion2016_lemma5_growth α N' (hpos N' hN'1) hgrow j
    have h2 := hle (3 ^ j * N') (Nat.le_mul_of_pos_left N' (pow_pos (by norm_num) j) |>.trans' hN'1)
    exact_mod_cast h1.trans h2
  -- but `(4/3)^j → ∞`
  have hlim : Tendsto (fun j : ℕ => ((4 : ℝ) / 3) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨j, hj'⟩ := (hlim.eventually_gt_atTop (N' : ℝ)).exists
  have h3pos : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
  have : ((4 : ℝ) / 3) ^ j ≤ N' := by
    rw [div_pow, div_le_iff₀ h3pos]
    simpa [mul_comm] using hj j
  exact absurd hj' (not_lt.mpr this)

/-! ## Notation of DST 2016: planar coordinates, lifts, boxes, connection events -/

section Vocabulary

variable {V : Type*}

/-- `Set.sym2` is monotone. The unordered pairs with both endpoints in `S`, Mathlib's
`Set.sym2 S`, are the coordinates on which an event "in `S`" depends (as in
`SharpnessDCT.lean`); Mathlib has the `Finset` form `Finset.sym2_mono` only. [folklore] -/
theorem sym2_mono {S T : Set V} (h : S ⊆ T) : S.sym2 ⊆ T.sym2 := by
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    rw [Set.mk_mem_sym2_iff] at he ⊢
    exact ⟨h he.1, h he.2⟩

/-- The unordered pairs inside a finite set form a finite set (`Set.sym2_eq_mk_image`).
[folklore] -/
theorem finite_sym2 {S : Set V} (hS : S.Finite) : S.sym2.Finite := by
  rw [Set.sym2_eq_mk_image]
  exact (hS.prod hS).image _

/-- Two configurations agreeing on the edges inside `S` have the same open subgraph induced on
`S`, hence the same events `{x ↔ y in S}`. [folklore] -/
theorem openConnIn_congr {S : Set V} {ω ω' : BondConfig V}
    (h : ∀ e ∈ S.sym2, e ∈ ω ↔ e ∈ ω') (x y : V) :
    ω ∈ openConnIn S x y ↔ ω' ∈ openConnIn S x y := by
  have hG : (openGraph ω).induce S = (openGraph ω').induce S := by
    ext a b
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype, openGraph_adj]
    rw [h s((a : V), b) (Set.mk_mem_sym2_iff.2 ⟨a.2, b.2⟩)]
  simp only [openConnIn, Set.mem_setOf_eq, hG]

/-- The open-crossing event `{X ↔ Y in S}` is determined by the edges inside any `T ⊇ S`
(`Set` generalisation of `Percolation.Literature.PlanarDuality.determinedBy_openCrossing` of `PlanarDuality.lean`,
cf. `determinedBy_openConnIn`). [cite: GrimmettPercolation1999, §2.2] -/
theorem SlabCriticality.determinedBy_openCrossing {S T : Set V} (X Y : Set V) (hST : S ⊆ T) :
    DeterminedBy (openCrossing S X Y) T.sym2 := by
  rw [determinedBy_iff]
  intro ω ω' h
  have hc : ∀ x y, ω ∈ openConnIn S x y ↔ ω' ∈ openConnIn S x y := by
    refine openConnIn_congr fun e he => ?_
    have := Set.ext_iff.1 h e
    simpa [Set.mem_inter_iff, sym2_mono hST he] using this
  simp only [mem_openCrossing_iff, hc]

variable (k : ℕ)

/-- The planar (`ℤ²`) coordinates of a slab vertex: DST's "two first coordinates" of a point of
`ℤ² × {0,…,k}`; here `slab 3 k = {0 ≤ x₀ ≤ k}`, so they are `(x₁, x₂)`.
[cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3)] -/
def planar (x : slab 3 k) : ℤ × ℤ := (x.1 1, x.1 2)

/-- The lift `Ē ⊆ S_k` of a planar set `E ⊆ ℤ²`: "the set of sites in `S_k` whose two first
coordinates are in `E`". [cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3)] -/
def slabLift (E : Set (ℤ × ℤ)) : Set (slab 3 k) := {x | planar k x ∈ E}

/-- Membership in a lift. [cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3)] -/
@[simp] theorem mem_slabLift_iff (E : Set (ℤ × ℤ)) (x : slab 3 k) :
    x ∈ slabLift k E ↔ planar k x ∈ E := Iff.rfl

/-- Lifts are monotone. [folklore] -/
theorem slabLift_mono {E F : Set (ℤ × ℤ)} (h : E ⊆ F) : slabLift k E ⊆ slabLift k F :=
  fun _ hx => h hx

/-- The translated box `c + B_n`, `B_n = [-n, n]²` (sup-norm ball of radius `n` about `c`).
[cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3), B_n = [-n,n]^2] -/
def sqBox (c : ℤ × ℤ) (n : ℕ) : Set (ℤ × ℤ) := {z | |z.1 - c.1| ≤ n ∧ |z.2 - c.2| ≤ n}

/-- The translated inner boundary `c + ∂B_n`, `∂B_n = B_n ∖ B_{n-1}` (the sup-norm sphere of
radius `n` about `c`; `sqSphere c 0 = {c}`).
[cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3), ∂B_n = B_n ∖ B_{n-1}] -/
def sqSphere (c : ℤ × ℤ) (n : ℕ) : Set (ℤ × ℤ) := {z | max |z.1 - c.1| |z.2 - c.2| = n}

/-- `c + ∂B_n ⊆ c + B_n`. [folklore] -/
theorem sqSphere_subset_sqBox (c : ℤ × ℤ) (n : ℕ) : sqSphere c n ⊆ sqBox c n := by
  intro z hz
  simp only [sqSphere, Set.mem_setOf_eq] at hz
  exact ⟨by rw [← hz]; exact le_max_left _ _, by rw [← hz]; exact le_max_right _ _⟩

/-- Boxes grow with the radius. [folklore] -/
theorem sqBox_mono (c : ℤ × ℤ) {m n : ℕ} (h : m ≤ n) : sqBox c m ⊆ sqBox c n :=
  fun _ hz => ⟨hz.1.trans (by exact_mod_cast h), hz.2.trans (by exact_mod_cast h)⟩

/-- A translated box is finite. [folklore] -/
theorem sqBox_finite (c : ℤ × ℤ) (n : ℕ) : (sqBox c n).Finite := by
  refine ((Set.finite_Icc (c.1 - n) (c.1 + n)).prod (Set.finite_Icc (c.2 - n) (c.2 + n))).subset ?_
  intro z hz
  simp only [sqBox, Set.mem_setOf_eq, abs_sub_le_iff] at hz
  simp only [Set.mem_prod, Set.mem_Icc]
  omega

/-- The lift of a finite planar set is finite (the slab has `k + 1` layers). [folklore] -/
theorem slabLift_finite {E : Set (ℤ × ℤ)} (hE : E.Finite) : (slabLift k E).Finite := by
  let g : slab 3 k → ℤ × (ℤ × ℤ) := fun x => (x.1 0, planar k x)
  have hg : Function.Injective g := by
    intro x y hxy
    simp only [g, planar, Prod.mk.injEq] at hxy
    apply Subtype.ext
    funext i
    fin_cases i
    · exact hxy.1
    · exact hxy.2.1
    · exact hxy.2.2
  have hsub : slabLift k E ⊆ g ⁻¹' (Set.Icc (0 : ℤ) k ×ˢ E) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, g]
    exact ⟨⟨x.2.1, x.2.2⟩, hx⟩
  exact (((Set.finite_Icc (0 : ℤ) k).prod hE).preimage hg.injOn).subset hsub

/-- **`X ⟷^B Y`** (DST 2016, Notation, p. 3): "there exists an open cluster in `B̄` connecting
`X̄` to `Ȳ`", i.e. some vertex of `X̄` is joined to some vertex of `Ȳ` by an open path of the
slab all of whose vertices lie in `B̄` (`openCrossing` of the lifts).
[cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3)] -/
def slabConn (B X Y : Set (ℤ × ℤ)) : Set (BondConfig (slab 3 k)) :=
  openCrossing (slabLift k B) (slabLift k X) (slabLift k Y)

/-- **`X ⟷^{!B!} Y`** (DST 2016, Notation, p. 3): "there exists a *unique* open cluster in `B̄`
connecting `X̄` to `Ȳ`": `X ⟷^B Y` holds and any two vertices of `X̄` that are joined inside
`B̄` to `Ȳ` are joined inside `B̄` to each other (so all open clusters of `B̄` meeting both `X̄`
and `Ȳ` coincide). [cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3)] -/
def slabUniqueConn (B X Y : Set (ℤ × ℤ)) : Set (BondConfig (slab 3 k)) :=
  {ω | ω ∈ slabConn k B X Y ∧
    ∀ x ∈ slabLift k X, ∀ x' ∈ slabLift k X, ∀ y ∈ slabLift k Y, ∀ y' ∈ slabLift k Y,
      ω ∈ openConnIn (slabLift k B) x y → ω ∈ openConnIn (slabLift k B) x' y' →
        ω ∈ openConnIn (slabLift k B) x x'}

/-- `X ⟷^{!B!} Y ⊆ X ⟷^B Y`. [cite: DuminilCopinSidoraviciusTassion2016, Notation (p. 3)] -/
theorem slabUniqueConn_subset_slabConn (B X Y : Set (ℤ × ℤ)) :
    slabUniqueConn k B X Y ⊆ slabConn k B X Y := fun _ h => h.1

/-- `X ⟷^B Y` is determined by the edges inside `T̄` for any `T ⊇ B`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2 ("depends only on the state of the edges in a finite box")] -/
theorem determinedBy_slabConn {B T : Set (ℤ × ℤ)} (X Y : Set (ℤ × ℤ)) (hBT : B ⊆ T) :
    DeterminedBy (slabConn k B X Y) (Set.sym2 (slabLift k T)) :=
  SlabCriticality.determinedBy_openCrossing _ _ (slabLift_mono k hBT)

/-- `X ⟷^{!B!} Y` is determined by the edges inside `T̄` for any `T ⊇ B`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2 ("depends only on the state of the edges in a finite box")] -/
theorem determinedBy_slabUniqueConn {B T : Set (ℤ × ℤ)} (X Y : Set (ℤ × ℤ)) (hBT : B ⊆ T) :
    DeterminedBy (slabUniqueConn k B X Y) (Set.sym2 (slabLift k T)) := by
  rw [determinedBy_iff]
  intro ω ω' h
  have hc : ∀ x y, ω ∈ openConnIn (slabLift k B) x y ↔ ω' ∈ openConnIn (slabLift k B) x y := by
    refine openConnIn_congr fun e he => ?_
    have := Set.ext_iff.1 h e
    simpa [Set.mem_inter_iff, sym2_mono (slabLift_mono k hBT) he] using this
  have hc' := (determinedBy_iff _ _).1 (determinedBy_slabConn k X Y hBT) ω ω' h
  simp only [slabUniqueConn, Set.mem_setOf_eq, hc, hc']

/-! ## The good-edge event of the renormalisation (DST 2016, §2.2) -/

/-- The planar vector `m • eᵢ` (`e₀ = (1,0)`, `e₁ = (0,1)`): the two directions of the edges of
the coarse-grained lattice `4nℤ²`. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
def coarseShift (m : ℤ) (i : Fin 2) : ℤ × ℤ := if i = 0 then (m, 0) else (0, m)

/-- **The good-edge event** (DST 2016, §2.2, p. 6). For the coarse edge `{z, z'}` of `4nℤ²`,
`z' = z + 4n eᵢ`, and `S_{3n} = B_u`: "`z + S_{3n} ⟷^{R_n} z' + S_{3n}` with
`R_n = (z + z')/2 + B_{6n}`" and "`z + S_{3n} ⟷^{!z + B_{3n}!} z + ∂B_{3n}` and
`z' + S_{3n} ⟷^{!z' + B_{3n}!} z' + ∂B_{3n}`".
[cite: DuminilCopinSidoraviciusTassion2016, §2.2 (definition of a good edge)] -/
def goodEvent (n u : ℕ) (z : ℤ × ℤ) (i : Fin 2) : Set (BondConfig (slab 3 k)) :=
  slabConn k (sqBox (z + coarseShift (2 * n) i) (6 * n)) (sqBox z u)
      (sqBox (z + coarseShift (4 * n) i) u) ∩
    (slabUniqueConn k (sqBox z (3 * n)) (sqBox z u) (sqSphere z (3 * n)) ∩
      slabUniqueConn k (sqBox (z + coarseShift (4 * n) i) (3 * n))
        (sqBox (z + coarseShift (4 * n) i) u) (sqSphere (z + coarseShift (4 * n) i) (3 * n)))

/-- `z + B_{3n} ⊆ R_n = z + 2n eᵢ + B_{6n}`. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem sqBox_subset_region_left (n : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    sqBox z (3 * n) ⊆ sqBox (z + coarseShift (2 * n) i) (6 * n) := by
  intro w hw
  simp only [sqBox, Set.mem_setOf_eq, abs_sub_le_iff, coarseShift] at hw ⊢
  fin_cases i <;> simp <;> push_cast at hw ⊢ <;> omega

/-- `z' + B_{3n} ⊆ R_n = z + 2n eᵢ + B_{6n}` for `z' = z + 4n eᵢ`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem sqBox_subset_region_right (n : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    sqBox (z + coarseShift (4 * n) i) (3 * n) ⊆ sqBox (z + coarseShift (2 * n) i) (6 * n) := by
  intro w hw
  simp only [sqBox, Set.mem_setOf_eq, abs_sub_le_iff, coarseShift] at hw ⊢
  fin_cases i <;> simp at hw ⊢ <;> omega

/-- "Being good depends only on the state of the edges in a finite box" (DST 2016, §2.2, p. 6):
the good-edge event is determined by the edges inside `R̄_n`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem determinedBy_goodEvent (n u : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    DeterminedBy (goodEvent k n u z i)
      (Set.sym2 (slabLift k (sqBox (z + coarseShift (2 * n) i) (6 * n)))) :=
  (determinedBy_slabConn k _ _ subset_rfl).inter
    ((determinedBy_slabUniqueConn k _ _ (sqBox_subset_region_left n z i)).inter
      (determinedBy_slabUniqueConn k _ _ (sqBox_subset_region_right n z i)))

/-- The set of edges inside `R̄_n` is finite. [folklore] -/
theorem sym2_region_finite (n : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    (Set.sym2 (slabLift k (sqBox (z + coarseShift (2 * n) i) (6 * n)))).Finite :=
  finite_sym2 (slabLift_finite k (sqBox_finite _ _))

/-- The good-edge event is a local event. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem isLocalEvent_goodEvent (n u : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    IsLocalEvent (goodEvent k n u z i) :=
  ⟨(sym2_region_finite k n z i).toFinset, by
    rw [Set.Finite.coe_toFinset]; exact determinedBy_goodEvent k n u z i⟩

/-- The probability of the good-edge event is continuous in the parameter (DST 2016, §2.2,
p. 6 = arXiv p. 9: "Since being good depends only on the state of the edges in a finite box,
there exists `q < p` such that an edge is good with `P_q`-probability larger than `1 - η`");
an instance of `continuous_bondPercolation_real_of_isLocalEvent` (`HalfSpaceBGN.lean`,
Grimmett 1999, §7.3, p. 162: a polynomial in `p`).
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem continuous_real_goodEvent (n u : ℕ) (z : ℤ × ℤ) (i : Fin 2) :
    Continuous fun q : unitInterval =>
      (bondPercolation (slabGraph 3 k) q).real (goodEvent k n u z i) :=
  continuous_bondPercolation_real_of_isLocalEvent (slabGraph 3 k) (isLocalEvent_goodEvent k n u z i)

end Vocabulary

/-! ## The finite-size criterion and the renormalisation step (DST 2016, §§2.1–2.2) -/

/-- **DST 2016, §2.1: the finite-size criterion holds when `θ_{S_k}(p) > 0`** (statement).
For `k > 0` and `p` with `P_p[0 ↔ ∞ in S_k] > 0`, and any `η > 0`, there is a block size
`n ≥ 1` and a radius `u ≤ n` (`S_{3n} = B_{u_{3n}}`, `u_{3n} ≤ 3n/3`, eq. (1)) such that both
coarse edges at the origin, `{0, 4n e₀}` and `{0, 4n e₁}`, are good with `P_p`-probability
`> 1 - η` (DST 2016, eq. (13): `limsup_n P_p[S_{3n} ⟷^{(2n,0)+B_{6n}} (4n,0)+S_{3n}] = 1`,
with eq. (1): `lim_n P_p[S_n ⟷^{!B_n!} ∂B_n] = 1`, and the symmetries of the slab; §2.2:
"Equations (13) and (1) guarantee the existence of `n` such that the `P_p`-probability that an
edge is good is larger than `1 - η`"). This packages Lemmata 4–6 and eqs. (1)–(13) of the paper.
Users take `(h : DuminilCopinSidoraviciusTassion2016_goodEvent_likely)`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 eq. (13) and §2.2] -/
def DuminilCopinSidoraviciusTassion2016_goodEvent_likely : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∀ η : ℝ, 0 < η → ∃ n u : ℕ, 1 ≤ n ∧ u ≤ n ∧
      ∀ i : Fin 2, 1 - η < (bondPercolation (slabGraph 3 k) p).real (goodEvent k n u 0 i)

/-- **DST 2016, §2.2: the renormalisation step** (statement). For `k > 0` there is `η > 0`
such that for every block size `n ≥ 1`, radius `u ≤ n` and parameter `q`: if both coarse
edges at the origin are good with `P_q`-probability `> 1 - η` (hence, by the invariance of
`P_q` under planar translations and the rotation by `π/2`, every edge of `4nℤ²` is), then
`p_c(S_k) ≤ q` (DST 2016, p. 6: "the set of good edges follows a percolation law which is
`4`-dependent. In particular, there exists `η > 0` such that whenever the probability to be
good exceeds `1 - η`, the set of good edges percolates (… a Peierls argument
[Balister–Bollobás–Walters 2005], or … [Liggett–Schonmann–Stacey 1997]) … By construction, an
infinite path of good edges in the coarse-grained lattice immediately implies the existence of
an infinite path of open edges in the original lattice. As a consequence, `q ≥ p_c(k)`").
Users take `(h : DuminilCopinSidoraviciusTassion2016_renormalisation)`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2 (p. 6)] -/
def DuminilCopinSidoraviciusTassion2016_renormalisation : Prop :=
  ∀ k : ℕ, 0 < k → ∃ η : ℝ, 0 < η ∧ ∀ n u : ℕ, 1 ≤ n → u ≤ n → ∀ q : unitInterval,
    (∀ i : Fin 2, 1 - η < (bondPercolation (slabGraph 3 k) q).real (goodEvent k n u 0 i)) →
      criticalProb (slabGraph 3 k) (slabOrigin 3 k) ≤ (q : ℝ)

/-- A parameter at which the slab percolates is positive (`θ(0) = 0`). [cite: GrimmettPercolation1999, §1.4] -/
theorem coe_pos_of_theta_slab_pos {k : ℕ} {p : unitInterval}
    (h : 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p) : 0 < (p : ℝ) := by
  rcases eq_or_lt_of_le p.2.1 with h0 | h0
  · exfalso
    have hp : p = 0 := Subtype.ext h0.symm
    rw [hp, theta_bot] at h
    exact lt_irrefl _ h
  · exact h0

/-- **DST 2016, §2.2, conclusion of the proof of Thm. 1** from the finite-size
criterion (`DuminilCopinSidoraviciusTassion2016_goodEvent_likely`) and the renormalisation step
(`DuminilCopinSidoraviciusTassion2016_renormalisation`): "Equations (13) and (1) guarantee the existence of `n` such that
the `P_p`-probability that an edge is good is larger than `1 - η`. Since being good depends
only on the state of the edges in a finite box, there exists `q < p` such that an edge is good
with `P_q`-probability larger than `1 - η` … As a consequence, `q ≥ p_c(k)` and therefore
`p > p_c(k)`" (p. 6). The continuity step is `continuous_real_goodEvent`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2 (p. 6)] -/
theorem DuminilCopinSidoraviciusTassion2016_criticalProb_lt_of_criterion (hF : DuminilCopinSidoraviciusTassion2016_goodEvent_likely)
    (hR : DuminilCopinSidoraviciusTassion2016_renormalisation) (k : ℕ) (hk : 0 < k) (p : unitInterval)
    (hθ : 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p) :
    criticalProb (slabGraph 3 k) (slabOrigin 3 k) < (p : ℝ) := by
  obtain ⟨η, hη, hRk⟩ := hR k hk
  obtain ⟨n, u, hn, hu, hgood⟩ := hF k hk p hθ η hη
  -- the set of parameters at which both origin edges are good with probability `> 1 - η`
  set U : Set unitInterval :=
    {q | ∀ i : Fin 2, 1 - η < (bondPercolation (slabGraph 3 k) q).real (goodEvent k n u 0 i)}
    with hU
  have hUo : IsOpen U := by
    rw [hU, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (continuous_real_goodEvent k n u 0 i)
  have hpU : p ∈ U := hgood
  have hp0 : 0 < (p : ℝ) := coe_pos_of_theta_slab_pos hθ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo p hpU
  -- a parameter `q < p` within `ε` of `p`
  let q : unitInterval := ⟨max 0 ((p : ℝ) - ε / 2), le_max_left _ _,
    max_le zero_le_one (by linarith [p.2.2])⟩
  have hqp : (q : ℝ) < p := by
    change max 0 ((p : ℝ) - ε / 2) < p
    exact max_lt hp0 (by linarith)
  have hqU : q ∈ U := by
    apply hball
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_sub_lt_iff]
    change max 0 ((p : ℝ) - ε / 2) - p < ε ∧ (p : ℝ) - max 0 ((p : ℝ) - ε / 2) < ε
    constructor
    · linarith [hqp]
    · have : (p : ℝ) - ε / 2 ≤ max 0 ((p : ℝ) - ε / 2) := le_max_right _ _
      linarith
  exact (hRk n u hn hu q hqU).trans_lt hqp

/-- DST 2016, Thm. 1 from the two statements of §§2.1–2.2 (composition of
`DuminilCopinSidoraviciusTassion2016.of_criticalProb_lt` and `DuminilCopinSidoraviciusTassion2016_criticalProb_lt_of_criterion`).
[cite: DuminilCopinSidoraviciusTassion2016, §2 (proof of Thm. 1)] -/
theorem DuminilCopinSidoraviciusTassion2016.of_criterion (hF : DuminilCopinSidoraviciusTassion2016_goodEvent_likely)
    (hR : DuminilCopinSidoraviciusTassion2016_renormalisation) : DuminilCopinSidoraviciusTassion2016 :=
  DuminilCopinSidoraviciusTassion2016.of_criticalProb_lt (DuminilCopinSidoraviciusTassion2016_criticalProb_lt_of_criterion hF hR)

/-! ## Symmetries I: transporting connection events along a relabelling of the vertices
(`iff` forms of the transport lemmas of `LatticeSymmetry.lean`) -/

section Transport

variable {V W : Type*}

/-- Relabelling transports restricted connections both ways: `e '' ω ∈ {e x ↔ e y in e '' S}`
iff `ω ∈ {x ↔ y in S}` (the `iff` form of `Percolation.Literature.relabel_mem_openConnIn` of
`LatticeSymmetry.lean`, obtained by transporting back along `e⁻¹`; Grimmett 1999, §1.6:
invariance under lattice symmetries). [folklore] -/
theorem relabel_mem_openConnIn_iff (e : V ≃ W) (ω : BondConfig V) (S : Set V) (x y : V) :
    BondConfig.relabel (sym2Equiv e) ω ∈ openConnIn (e '' S) (e x) (e y) ↔
      ω ∈ openConnIn S x y := by
  refine ⟨fun h => ?_, relabel_mem_openConnIn e⟩
  have h' := relabel_mem_openConnIn e.symm h
  simpa only [relabel_symm_relabel, Equiv.symm_image_image, Equiv.symm_apply_apply] using h'

/-- Relabelling transports open crossings both ways (`preimage_relabel_openCrossing` of
`LatticeSymmetry.lean`, membership form). [folklore] -/
theorem relabel_mem_openCrossing_iff (e : V ≃ W) (ω : BondConfig V) (S A B : Set V) :
    BondConfig.relabel (sym2Equiv e) ω ∈ openCrossing (e '' S) (e '' A) (e '' B) ↔
      ω ∈ openCrossing S A B := by
  rw [← Set.mem_preimage, preimage_relabel_openCrossing]

end Transport

/-! ## Symmetries II: planar lattice symmetries of the slab -/

section SlabSymmetry

/-- Adjacency of the square lattice `ℤ²`: the two points differ by `±(1,0)` or `±(0,1)`.
[folklore] -/
def planarAdj (z w : ℤ × ℤ) : Prop :=
  (w = z + (1, 0) ∨ z = w + (1, 0)) ∨ (w = z + (0, 1) ∨ z = w + (0, 1))

/-- Equality of points of `ℤ³ = Fin 3 → ℤ` with a translate, coordinatewise. [folklore] -/
theorem site3_eq_add_iff (x y v : Site 3) :
    y = x + v ↔ y 0 = x 0 + v 0 ∧ y 1 = x 1 + v 1 ∧ y 2 = x 2 + v 2 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j
    · simpa using h0
    · simpa using h1
    · simpa using h2

/-- Existential quantification over `Fin 3`, enumerated. [folklore] -/
theorem exists_fin_three {q : Fin 3 → Prop} : (∃ i, q i) ↔ q 0 ∨ q 1 ∨ q 2 := by
  constructor
  · rintro ⟨i, h⟩
    fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h) <;> exact ⟨_, h⟩

/-- Adjacency in `ℤ³` in slab coordinates: either the heights (`x 0`) agree and the planar
parts are adjacent in `ℤ²`, or the planar parts agree and the heights differ by one. [folklore] -/
theorem zdGraph_three_adj_iff (x y : Site 3) :
    (zdGraph 3).Adj x y ↔
      (y 0 = x 0 ∧ planarAdj (x 1, x 2) (y 1, y 2)) ∨
        ((x 1, x 2) = (y 1, y 2) ∧ (y 0 = x 0 + 1 ∨ x 0 = y 0 + 1)) := by
  rw [zdGraph_adj_iff, exists_fin_three]
  simp +decide only [site3_eq_add_iff, Pi.single_apply, planarAdj, Prod.mk.injEq, Prod.mk_add_mk,
    if_true, if_false, add_zero]
  omega

variable (k : ℕ)

/-- The bijection of the slab induced by a bijection `g` of `ℤ²` acting on the planar
coordinates (heights unchanged). [folklore] -/
def slabEquiv (g : ℤ × ℤ ≃ ℤ × ℤ) : slab 3 k ≃ slab 3 k where
  toFun x := ⟨![x.1 0, (g (planar k x)).1, (g (planar k x)).2], x.2⟩
  invFun x := ⟨![x.1 0, (g.symm (planar k x)).1, (g.symm (planar k x)).2], x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [planar]
  right_inv x := by
    apply Subtype.ext
    funext j
    fin_cases j <;> simp [planar]

variable (g : ℤ × ℤ ≃ ℤ × ℤ)

/-- The height is unchanged by `slabEquiv`. [folklore] -/
@[simp] theorem slabEquiv_apply_zero (x : slab 3 k) : (slabEquiv k g x).1 0 = x.1 0 := rfl

/-- The planar part is moved by `g`. [folklore] -/
@[simp] theorem planar_slabEquiv (x : slab 3 k) : planar k (slabEquiv k g x) = g (planar k x) := by
  simp [planar, slabEquiv]

/-- The planar part of the inverse is moved by `g⁻¹`. [folklore] -/
@[simp] theorem planar_slabEquiv_symm (x : slab 3 k) :
    planar k ((slabEquiv k g).symm x) = g.symm (planar k x) := by
  simp [planar, slabEquiv]

/-- `slabEquiv` maps lifts to lifts: `slabEquiv g '' Ē = \overline{g '' E}`. [folklore] -/
theorem image_slabEquiv_slabLift (E : Set (ℤ × ℤ)) :
    slabEquiv k g '' slabLift k E = slabLift k (g '' E) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_slabLift_iff, planar_slabEquiv]
    exact Set.mem_image_of_mem g hx
  · intro hy
    rw [mem_slabLift_iff, Set.mem_image_equiv] at hy
    refine ⟨(slabEquiv k g).symm y, ?_, Equiv.apply_symm_apply _ _⟩
    rw [mem_slabLift_iff, planar_slabEquiv_symm]
    exact hy

/-- A bijection of `ℤ²` preserving adjacency in both directions induces an automorphism of the
slab graph. [folklore] -/
def slabIso (hg : ∀ z w, planarAdj (g z) (g w) ↔ planarAdj z w) :
    slabGraph 3 k ≃g slabGraph 3 k where
  toEquiv := slabEquiv k g
  map_rel_iff' := by
    intro x y
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
    rw [zdGraph_three_adj_iff, zdGraph_three_adj_iff]
    have h1 : ∀ x : slab 3 k, ((slabEquiv k g x).1 1, (slabEquiv k g x).1 2) = g (planar k x) :=
      fun x => planar_slabEquiv k g x
    rw [h1, h1, slabEquiv_apply_zero, slabEquiv_apply_zero, hg, g.injective.eq_iff]
    rfl

/-- The relabelling of slab configurations induced by a planar bijection `g`. [folklore] -/
abbrev slabRelabel : BondConfig (slab 3 k) ≃ᵐ BondConfig (slab 3 k) :=
  BondConfig.relabel (sym2Equiv (slabEquiv k g))

/-- **Invariance of `P_p` on the slab under planar lattice symmetries** (Grimmett 1999, §1.6,
p. 16; DST 2016 use the invariance under translations, reflections and the rotation by `π/2`
throughout §2): `P_p {ω | g·ω ∈ A} = P_p(A)`. [cite: GrimmettPercolation1999, §1.6 (p. 16)] -/
theorem real_preimage_slabRelabel (hg : ∀ z w, planarAdj (g z) (g w) ↔ planarAdj z w)
    (p : unitInterval) (A : Set (BondConfig (slab 3 k))) :
    (bondPercolation (slabGraph 3 k) p).real (slabRelabel k g ⁻¹' A) =
      (bondPercolation (slabGraph 3 k) p).real A :=
  bondPercolation_real_preimage_relabel_iso (slabIso k g hg) p A

/-- Transport of `X ⟷^B Y`: `{ω | g·ω ∈ (gX ⟷^{gB} gY)} = (X ⟷^B Y)`. [folklore] -/
theorem preimage_slabRelabel_slabConn (B X Y : Set (ℤ × ℤ)) :
    slabRelabel k g ⁻¹' slabConn k (g '' B) (g '' X) (g '' Y) = slabConn k B X Y := by
  ext ω
  simp only [Set.mem_preimage, slabConn, ← image_slabEquiv_slabLift]
  exact relabel_mem_openCrossing_iff (slabEquiv k g) ω _ _ _

/-- Transport of `X ⟷^{!B!} Y`: `{ω | g·ω ∈ (gX ⟷^{!gB!} gY)} = (X ⟷^{!B!} Y)`. [folklore] -/
theorem preimage_slabRelabel_slabUniqueConn (B X Y : Set (ℤ × ℤ)) :
    slabRelabel k g ⁻¹' slabUniqueConn k (g '' B) (g '' X) (g '' Y) = slabUniqueConn k B X Y := by
  ext ω
  have hc := preimage_slabRelabel_slabConn k g B X Y
  rw [Set.ext_iff] at hc
  specialize hc ω
  rw [Set.mem_preimage] at hc ⊢
  simp only [slabUniqueConn, Set.mem_setOf_eq, hc, ← image_slabEquiv_slabLift, Set.forall_mem_image,
    relabel_mem_openConnIn_iff]

/-! ### The concrete symmetries: translations and the diagonal reflection -/

/-- Planar translation by `c` (notation for Mathlib's `Equiv.addRight c`). [folklore] -/
def planarShift (c : ℤ × ℤ) : ℤ × ℤ ≃ ℤ × ℤ := Equiv.addRight c

/-- The diagonal reflection `(a, b) ↦ (b, a)`, which exchanges the two coarse-edge directions
(notation for Mathlib's `Equiv.prodComm ℤ ℤ`). [folklore] -/
def planarSwap : ℤ × ℤ ≃ ℤ × ℤ := Equiv.prodComm ℤ ℤ

/-- `planarShift c` acts as `z ↦ z + c`. [folklore] -/
@[simp] theorem planarShift_apply (c z : ℤ × ℤ) : planarShift c z = z + c := rfl

/-- `planarSwap` acts as `(a, b) ↦ (b, a)`. [folklore] -/
@[simp] theorem planarSwap_apply (z : ℤ × ℤ) : planarSwap z = z.swap := rfl

/-- Translations preserve planar adjacency. [folklore] -/
theorem planarAdj_planarShift (c z w : ℤ × ℤ) :
    planarAdj (planarShift c z) (planarShift c w) ↔ planarAdj z w := by
  simp only [planarShift_apply, planarAdj, add_right_comm _ c, add_left_inj]

/-- The diagonal reflection preserves planar adjacency. [folklore] -/
theorem planarAdj_planarSwap (z w : ℤ × ℤ) :
    planarAdj (planarSwap z) (planarSwap w) ↔ planarAdj z w := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  simp only [planarSwap_apply, Prod.swap_prod_mk, planarAdj, Prod.mk_add_mk, Prod.mk.injEq,
    add_zero]
  tauto

/-- Translates of boxes: `(c + B_n) + v = (c + v) + B_n`. [folklore] -/
theorem image_planarShift_sqBox (v c : ℤ × ℤ) (n : ℕ) :
    planarShift v '' sqBox c n = sqBox (c + v) n := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarShift, Equiv.addRight_symm, Equiv.coe_addRight, sqBox, Set.mem_setOf_eq,
    Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  have h1 : w.1 + -v.1 - c.1 = w.1 - (c.1 + v.1) := by ring
  have h2 : w.2 + -v.2 - c.2 = w.2 - (c.2 + v.2) := by ring
  rw [h1, h2]

/-- Translates of box boundaries. [folklore] -/
theorem image_planarShift_sqSphere (v c : ℤ × ℤ) (n : ℕ) :
    planarShift v '' sqSphere c n = sqSphere (c + v) n := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarShift, Equiv.addRight_symm, Equiv.coe_addRight, sqSphere, Set.mem_setOf_eq,
    Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  have h1 : w.1 + -v.1 - c.1 = w.1 - (c.1 + v.1) := by ring
  have h2 : w.2 + -v.2 - c.2 = w.2 - (c.2 + v.2) := by ring
  rw [h1, h2]

/-- Reflected boxes: the diagonal reflection maps `c + B_n` to `c.swap + B_n`. [folklore] -/
theorem image_planarSwap_sqBox (c : ℤ × ℤ) (n : ℕ) :
    planarSwap '' sqBox c n = sqBox c.swap n := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarSwap, Equiv.prodComm_symm, Equiv.prodComm_apply, sqBox, Set.mem_setOf_eq,
    Prod.fst_swap, Prod.snd_swap]
  exact and_comm

/-- Reflected box boundaries. [folklore] -/
theorem image_planarSwap_sqSphere (c : ℤ × ℤ) (n : ℕ) :
    planarSwap '' sqSphere c n = sqSphere c.swap n := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarSwap, Equiv.prodComm_symm, Equiv.prodComm_apply, sqSphere, Set.mem_setOf_eq,
    Prod.fst_swap, Prod.snd_swap, max_comm]

/-- The diagonal reflection exchanges the two coarse directions. [folklore] -/
@[simp] theorem swap_coarseShift_zero (m : ℤ) : (coarseShift m 0).swap = coarseShift m 1 := by
  simp [coarseShift]

/-- **The two coarse-edge directions are equally likely to be good** (rotation/reflection
symmetry of the slab; DST 2016, §2.2 speak of "the probability to be good"):
`{ω | swap·ω ∈ good(n,u,z.swap,e₁)} = good(n,u,z,e₀)`. [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem preimage_slabRelabel_swap_goodEvent (n u : ℕ) (z : ℤ × ℤ) :
    slabRelabel k planarSwap ⁻¹' goodEvent k n u z.swap 1 = goodEvent k n u z 0 := by
  have e1 : z.swap + coarseShift (2 * n) 1 = (z + coarseShift (2 * n) 0).swap := by
    simp [coarseShift]
  have e2 : z.swap + coarseShift (4 * n) 1 = (z + coarseShift (4 * n) 0).swap := by
    simp [coarseShift]
  simp only [goodEvent, e1, e2, ← image_planarSwap_sqBox, ← image_planarSwap_sqSphere,
    Set.preimage_inter, preimage_slabRelabel_slabConn, preimage_slabRelabel_slabUniqueConn]

/-- Both coarse edges at the origin are equally likely to be good.
[cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem real_goodEvent_one_eq (p : unitInterval) (n u : ℕ) :
    (bondPercolation (slabGraph 3 k) p).real (goodEvent k n u 0 1) =
      (bondPercolation (slabGraph 3 k) p).real (goodEvent k n u 0 0) := by
  have h := preimage_slabRelabel_swap_goodEvent k n u 0
  rw [show (0 : ℤ × ℤ).swap = 0 from rfl] at h
  rw [← h, real_preimage_slabRelabel k planarSwap planarAdj_planarSwap p]

/-- **Translation invariance of the uniqueness event** `z + S ⟷^{!z + B_m!} z + ∂B_m`
(DST 2016, eq. (1) is used at every vertex of `4nℤ²` in §2.2). [cite: DuminilCopinSidoraviciusTassion2016, §2.2] -/
theorem real_slabUniqueConn_shift (p : unitInterval) (z : ℤ × ℤ) (m u : ℕ) :
    (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox z m) (sqBox z u) (sqSphere z m)) =
      (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox 0 m) (sqBox 0 u) (sqSphere 0 m)) := by
  rw [← real_preimage_slabRelabel k (planarShift z) (planarAdj_planarShift z) p
    (slabUniqueConn k (sqBox z m) (sqBox z u) (sqSphere z m))]
  have himg : slabUniqueConn k (sqBox z m) (sqBox z u) (sqSphere z m) =
      slabUniqueConn k (planarShift z '' sqBox 0 m) (planarShift z '' sqBox 0 u)
        (planarShift z '' sqSphere 0 m) := by
    rw [image_planarShift_sqBox, image_planarShift_sqBox, image_planarShift_sqSphere, zero_add]
  rw [himg, preimage_slabRelabel_slabUniqueConn]

end SlabSymmetry

/-! ## §2.1 of DST 2016: the uniqueness input (1), the two-block estimate (13), and the proof
of the finite-size criterion from them -/

section FiniteSizeCriterion

variable (k : ℕ)

/-- `X ⟷^{c + B_m} Y` is measurable (a local event). [folklore] -/
theorem measurableSet_slabConn (c : ℤ × ℤ) (m : ℕ) (X Y : Set (ℤ × ℤ)) :
    MeasurableSet (slabConn k (sqBox c m) X Y) := by
  have hfin := finite_sym2 (slabLift_finite k (sqBox_finite c m))
  have hdet := determinedBy_slabConn k X Y (subset_rfl : sqBox c m ⊆ sqBox c m)
  rw [← hfin.coe_toFinset] at hdet
  exact hdet.measurableSet_of_finset

/-- `X ⟷^{!c + B_m!} Y` is measurable (a local event). [folklore] -/
theorem measurableSet_slabUniqueConn (c : ℤ × ℤ) (m : ℕ) (X Y : Set (ℤ × ℤ)) :
    MeasurableSet (slabUniqueConn k (sqBox c m) X Y) := by
  have hfin := finite_sym2 (slabLift_finite k (sqBox_finite c m))
  have hdet := determinedBy_slabUniqueConn k X Y (subset_rfl : sqBox c m ⊆ sqBox c m)
  rw [← hfin.coe_toFinset] at hdet
  exact hdet.measurableSet_of_finset

/-- The elementary union bound `P(A ∩ B) ≥ P(A) + P(B) - 1` (used in DST 2016, §2.1, display
before eq. (13)). [folklore] -/
theorem measureReal_inter_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B) := by
  have h := measureReal_union_add_inter (μ := μ) (s := A) hB
  have h2 : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  linarith

end FiniteSizeCriterion

/-! ## Paths: the bridge to `PathIn`, concatenation, boundary entry, and gluing by uniqueness -/

section Paths

variable {V : Type*}

/-- `{u ↔ v in S}` in terms of the chain predicate `PathIn` of `SitePaths.lean`: an open path
inside `S` is a chain of open edges with all vertices in `S`. [folklore] -/
theorem mem_openConnIn_iff_pathIn {S : Set V} {ω : BondConfig V} {u v : V} :
    ω ∈ openConnIn S u v ↔ PathIn (openGraph ω) S u v := by
  constructor
  · rintro ⟨hu, hv, ⟨W⟩⟩
    refine ⟨hu, ?_⟩
    suffices h : ∀ (a b : S) (_ : ((openGraph ω).induce S).Walk a b),
        Relation.ReflTransGen (fun x y => (openGraph ω).Adj x y ∧ y ∈ S) a.1 b.1 from h _ _ W
    intro a b W
    induction W with
    | nil => exact Relation.ReflTransGen.refl
    | @cons a c b hadj _ ih => exact Relation.ReflTransGen.head ⟨hadj, c.2⟩ ih
  · rintro ⟨hu, h⟩
    induction h with
    | refl => exact ⟨hu, hu, SimpleGraph.Reachable.refl _⟩
    | @tail b c _ hbc ih =>
      obtain ⟨_, hb, hr⟩ := ih
      refine ⟨hu, hbc.2, hr.trans (SimpleGraph.Adj.reachable ?_)⟩
      exact hbc.1

/-- Concatenation of open paths inside `S`: the relation `x ↔ y in S` (Grimmett 1999, §1.3
p. 12: "`A ↔ B` if there exists an open path joining some vertex in `A` to some vertex in `B`",
"`A ↔ B` off `D`" if the path avoids `D`) is transitive (also in `PlanarDuality.lean`, a heavy
file outside this import closure; local copy via `PathIn.trans`).
[cite: GrimmettPercolation1999, §1.3 p. 12 (open paths, `A ↔ B` off `D`)] -/
theorem SlabCriticality.openConnIn_trans {S : Set V} {ω : BondConfig V} {u v w : V}
    (h₁ : ω ∈ openConnIn S u v) (h₂ : ω ∈ openConnIn S v w) : ω ∈ openConnIn S u w := by
  rw [mem_openConnIn_iff_pathIn] at *
  exact h₁.trans h₂

/-- Reversal of an open path inside `S` (cf. `PlanarDuality.lean`; local copy via
`PathIn.symm`). [folklore] -/
theorem openConnIn_reverse {S : Set V} {ω : BondConfig V} {u v : V}
    (h : ω ∈ openConnIn S u v) : ω ∈ openConnIn S v u := by
  rw [mem_openConnIn_iff_pathIn] at *
  exact h.symm

variable (k : ℕ)

/-- A lattice neighbour, inside the box `c + B_m`, of a point outside the box lies on the
boundary `c + ∂B_m`. [folklore] -/
theorem mem_sqSphere_of_planarAdj {c z w : ℤ × ℤ} {m : ℕ} (h : planarAdj z w)
    (hz : z ∉ sqBox c m) (hw : w ∈ sqBox c m) : w ∈ sqSphere c m := by
  obtain ⟨hw1, hw2⟩ := hw
  simp only [sqBox, Set.mem_setOf_eq, not_and_or, not_le] at hz
  simp only [sqSphere, Set.mem_setOf_eq]
  refine le_antisymm (max_le hw1 hw2) ?_
  rw [abs_le] at hw1 hw2
  rw [le_max_iff, le_abs, le_abs]
  simp only [lt_abs] at hz
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at h
  simp only at hz hw1 hw2 ⊢
  omega

/-- Slab version: a slab-lattice neighbour, inside `\overline{c + B_m}`, of a vertex outside it
lies in `\overline{c + ∂B_m}` (vertical edges do not change the planar position). [folklore] -/
theorem mem_slabLift_sqSphere_of_adj {c : ℤ × ℤ} {m : ℕ} {x y : slab 3 k}
    (hadj : (slabGraph 3 k).Adj x y) (hx : x ∉ slabLift k (sqBox c m))
    (hy : y ∈ slabLift k (sqBox c m)) : y ∈ slabLift k (sqSphere c m) := by
  have h := (zdGraph_three_adj_iff x.1 y.1).1 hadj
  rcases h with ⟨-, hpa⟩ | ⟨hpe, -⟩
  · exact mem_sqSphere_of_planarAdj hpa hx hy
  · exfalso
    apply hx
    have : planar k x = planar k y := hpe
    rw [mem_slabLift_iff, this]
    exact hy

/-- **Boundary entry.** Let `ω` be a lattice configuration and `a ↔ b` an open path inside `T̄`
ending at `b ∈ \overline{c + B_m}`, whose start `a` is not in the interior of
the box. Then `b` is joined inside `\overline{c + B_m}` to a vertex of `\overline{c + ∂B_m}`
(the last entry point of the path into the box). [folklore] -/
theorem exists_sqSphere_openConnIn {ω : BondConfig (slab 3 k)} (hω : ω ⊆ (slabGraph 3 k).edgeSet)
    {T : Set (ℤ × ℤ)} {c : ℤ × ℤ} {m : ℕ} {a b : slab 3 k}
    (hab : ω ∈ openConnIn (slabLift k T) a b) (hb : b ∈ slabLift k (sqBox c m))
    (ha : a ∈ slabLift k (sqBox c m) → a ∈ slabLift k (sqSphere c m)) :
    ∃ e ∈ slabLift k (sqSphere c m), ω ∈ openConnIn (slabLift k (sqBox c m)) b e := by
  have hba : PathIn (openGraph ω) (slabLift k T) b a := (mem_openConnIn_iff_pathIn.1 hab).symm
  rcases hba.exit_or (R := slabLift k (sqBox c m)) hb with h | ⟨e, d, he, hd, -, hadj, hpath⟩
  · have haB : a ∈ slabLift k (sqBox c m) := h.right_mem.1
    exact ⟨a, ha haB, mem_openConnIn_iff_pathIn.2 (h.mono Set.inter_subset_left)⟩
  · refine ⟨e, ?_, mem_openConnIn_iff_pathIn.2 (hpath.mono Set.inter_subset_left)⟩
    have hlat : (slabGraph 3 k).Adj d e := by
      have he' := (openGraph_adj ω e d).1 hadj
      exact ((SimpleGraph.mem_edgeSet _).1 (hω he'.1)).symm
    exact mem_slabLift_sqSphere_of_adj k hlat hd he

/-- **Gluing through a uniqueness block** (DST 2016, §2.1, the display before eq. (13): "paths
coming from `S̄_{3n}` and `\overline{(4n,0)+S_{3n}}` and going to `S̄'_n` must be connected to
each other in `B̄'_n` by uniqueness of the cluster in `B̄'_n` from `S̄'_n` to `∂B̄'_n`"; the same
mechanism concatenates consecutive good edges in §2.2). For a lattice configuration `ω`: if
`X ⟷^{B₁} S'`, `X' ⟷^{B₂} S'` and `S' ⟷^{!c+B_m!} c+∂B_m`, where `S' ⊆ c + B_m ⊆ B₁`,
`B₁ ∪ B₂ ⊆ T`, and `X`, `X'` do not meet the interior of `c + B_m`, then `X ⟷^{T} X'`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (display before eq. (13))] -/
theorem slabConn_of_glue {ω : BondConfig (slab 3 k)} (hω : ω ⊆ (slabGraph 3 k).edgeSet)
    {T B₁ B₂ X X' S' : Set (ℤ × ℤ)} {c : ℤ × ℤ} {m : ℕ}
    (h₁T : B₁ ⊆ T) (h₂T : B₂ ⊆ T) (hc₁ : sqBox c m ⊆ B₁)
    (hS' : S' ⊆ sqBox c m) (hX : X ∩ sqBox c m ⊆ sqSphere c m)
    (hX' : X' ∩ sqBox c m ⊆ sqSphere c m)
    (hω₁ : ω ∈ slabConn k B₁ X S') (hω₂ : ω ∈ slabConn k B₂ X' S')
    (hωu : ω ∈ slabUniqueConn k (sqBox c m) S' (sqSphere c m)) :
    ω ∈ slabConn k T X X' := by
  obtain ⟨a, ha, b, hb, hab⟩ := hω₁
  obtain ⟨a', ha', b', hb', hab'⟩ := hω₂
  obtain ⟨e, he, hbe⟩ := exists_sqSphere_openConnIn k hω hab (slabLift_mono k hS' hb)
    (fun haB => hX ⟨ha, haB⟩)
  obtain ⟨e', he', hbe'⟩ := exists_sqSphere_openConnIn k hω hab' (slabLift_mono k hS' hb')
    (fun haB => hX' ⟨ha', haB⟩)
  have hbb' : ω ∈ openConnIn (slabLift k (sqBox c m)) b b' := hωu.2 b hb b' hb' e he e' he' hbe hbe'
  refine ⟨a, ha, a', ha', ?_⟩
  have h1 : ω ∈ openConnIn (slabLift k T) a b := openConnIn_mono (slabLift_mono k h₁T) _ _ hab
  have h2 : ω ∈ openConnIn (slabLift k T) b b' :=
    openConnIn_mono (slabLift_mono k (hc₁.trans h₁T)) _ _ hbb'
  have h3 : ω ∈ openConnIn (slabLift k T) b' a' :=
    openConnIn_reverse (openConnIn_mono (slabLift_mono k h₂T) _ _ hab')
  exact SlabCriticality.openConnIn_trans (SlabCriticality.openConnIn_trans h1 h2) h3

/-- The gluing inclusion holds `P_p`-almost surely (`P_p` is carried by lattice configurations,
`setBernoulli_ae_subset`), hence at the level of probabilities.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (display before eq. (13))] -/
theorem real_glue_le (p : unitInterval) {T B₁ B₂ X X' S' : Set (ℤ × ℤ)} {c : ℤ × ℤ} {m : ℕ}
    (h₁T : B₁ ⊆ T) (h₂T : B₂ ⊆ T) (hc₁ : sqBox c m ⊆ B₁)
    (hS' : S' ⊆ sqBox c m) (hX : X ∩ sqBox c m ⊆ sqSphere c m)
    (hX' : X' ∩ sqBox c m ⊆ sqSphere c m) :
    (bondPercolation (slabGraph 3 k) p).real
        (slabConn k B₁ X S' ∩ slabConn k B₂ X' S' ∩ slabUniqueConn k (sqBox c m) S' (sqSphere c m)) ≤
      (bondPercolation (slabGraph 3 k) p).real (slabConn k T X X') := by
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := (slabGraph 3 k).edgeSet) (p := p)]
    with ω hω hmem
  exact slabConn_of_glue k hω h₁T h₂T hc₁ hS' hX hX' hmem.1.1 hmem.1.2 hmem.2

end Paths

/-! ## From eq. (12) to eq. (13): reflection, Harris' inequality and gluing by uniqueness -/

section TwoBlock

variable (k : ℕ)

/-- The reflection `(a, b) ↦ (t - a, b)` of `ℤ²` in the vertical axis `{a = t/2}` (DST 2016,
§2.1: "the reflection across the axis `{2n} × ℝ`", `t = 4n`). [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (proof of eq. (13))] -/
def planarReflect (t : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun z := (t - z.1, z.2)
  invFun z := (t - z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- `planarReflect t` acts as `(a, b) ↦ (t - a, b)`. [folklore] -/
@[simp] theorem planarReflect_apply (t : ℤ) (z : ℤ × ℤ) : planarReflect t z = (t - z.1, z.2) := rfl

/-- `planarReflect t` is an involution. [folklore] -/
@[simp] theorem planarReflect_symm (t : ℤ) : (planarReflect t).symm = planarReflect t := rfl

/-- The vertical-axis reflection preserves planar adjacency. [folklore] -/
theorem planarAdj_planarReflect (t : ℤ) (z w : ℤ × ℤ) :
    planarAdj (planarReflect t z) (planarReflect t w) ↔ planarAdj z w := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  simp only [planarReflect_apply, planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero]
  omega

/-- Reflected boxes: `planarReflect t '' (c + B_n) = (t - c₁, c₂) + B_n`. [folklore] -/
theorem image_planarReflect_sqBox (t : ℤ) (c : ℤ × ℤ) (n : ℕ) :
    planarReflect t '' sqBox c n = sqBox (t - c.1, c.2) n := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarReflect_symm, planarReflect_apply, sqBox, Set.mem_setOf_eq]
  rw [show t - w.1 - c.1 = -(w.1 - (t - c.1)) by ring, abs_neg]

/-- Membership in `c + ∂B_m`, linearised. [folklore] -/
theorem mem_sqSphere_iff (c w : ℤ × ℤ) (m : ℕ) :
    w ∈ sqSphere c m ↔ (|w.1 - c.1| ≤ m ∧ |w.2 - c.2| ≤ m) ∧ ((m : ℤ) ≤ |w.1 - c.1| ∨ (m : ℤ) ≤ |w.2 - c.2|) := by
  simp only [sqSphere, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← h]; exact le_max_left _ _
    · rw [← h]; exact le_max_right _ _
    · rw [← le_max_iff, h]
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact le_antisymm (max_le h1 h2) (le_max_iff.2 h3)

end TwoBlock

/-! ## §2.1 of DST 2016 continued: the events `E_n(α, β)`, Lemmata 4 and 6, and the proof
of eq. (12) (via eqs. (10)–(11)) -/

section CrossingEstimates

variable (k : ℕ)

/-- The vertical lattice segment `{x} × [s, t]`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (E_n(α,β), Y_n^±, Z_n)] -/
def sideSeg (x s t : ℤ) : Set (ℤ × ℤ) := {z | z.1 = x ∧ s ≤ z.2 ∧ z.2 ≤ t}

/-- Segments are monotone in the interval. [folklore] -/
theorem sideSeg_mono (x : ℤ) {s t s' t' : ℤ} (hs : s' ≤ s) (ht : t ≤ t') :
    sideSeg x s t ⊆ sideSeg x s' t' :=
  fun _ ⟨h1, h2, h3⟩ => ⟨h1, hs.trans h2, h3.trans ht⟩

/-- **The event `E_n(α, β) = {S_n ⟷^{B_n} {n} × [α, β]}`** (DST 2016, §2.1, p. 4), with
`S_n = B_u`; lattice form (integer endpoints). [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (definition of E_n(α,β))] -/
def sideEvent (n u : ℕ) (s t : ℤ) : Set (BondConfig (slab 3 k)) :=
  slabConn k (sqBox 0 n) (sqBox 0 u) (sideSeg n s t)

/-- The reflection `(a, b) ↦ (a, t - b)` of `ℤ²` in the horizontal axis `{b = t/2}` (DST 2016,
§2.1: "the invariance of `P_p` under reflection", used for `Y_n^-`). [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (proof of eq. (11))] -/
def planarFlip (t : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun z := (z.1, t - z.2)
  invFun z := (z.1, t - z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- `planarFlip t` acts as `(a, b) ↦ (a, t - b)`. [folklore] -/
@[simp] theorem planarFlip_apply (t : ℤ) (z : ℤ × ℤ) : planarFlip t z = (z.1, t - z.2) := rfl

/-- `planarFlip t` is an involution. [folklore] -/
@[simp] theorem planarFlip_symm (t : ℤ) : (planarFlip t).symm = planarFlip t := rfl

/-- The horizontal-axis reflection preserves planar adjacency. [folklore] -/
theorem planarAdj_planarFlip (t : ℤ) (z w : ℤ × ℤ) :
    planarAdj (planarFlip t z) (planarFlip t w) ↔ planarAdj z w := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  simp only [planarFlip_apply, planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero]
  omega

/-- Reflected boxes: `planarFlip t '' (c + B_n) = (c₁, t - c₂) + B_n`. [folklore] -/
theorem image_planarFlip_sqBox (t : ℤ) (c : ℤ × ℤ) (n : ℕ) :
    planarFlip t '' sqBox c n = sqBox (c.1, t - c.2) n := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarFlip_symm, planarFlip_apply, sqBox, Set.mem_setOf_eq]
  rw [show t - w.2 - c.2 = -(w.2 - (t - c.2)) by ring, abs_neg]

/-- Reflected segments: `planarFlip t '' ({x} × [s, s']) = {x} × [t - s', t - s]`. [folklore] -/
theorem image_planarFlip_sideSeg (t x s s' : ℤ) :
    planarFlip t '' sideSeg x s s' = sideSeg x (t - s') (t - s) := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarFlip_symm, planarFlip_apply, sideSeg, Set.mem_setOf_eq]
  omega

/-- Translated segments. [folklore] -/
theorem image_planarShift_sideSeg (v : ℤ × ℤ) (x s s' : ℤ) :
    planarShift v '' sideSeg x s s' = sideSeg (x + v.1) (s + v.2) (s' + v.2) := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarShift, Equiv.addRight_symm, Equiv.coe_addRight, sideSeg, Set.mem_setOf_eq,
    Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
  omega

/-- **DST 2016, Lemma 4** (p. 4), lattice form (statement). For `k > 0`, `p` with
`P_p[0 ↔ ∞ in S_k] > 0`, and `(u_n)` as in eq. (1) (`S_n = B_{u_n}`): "There exist two
sequences `(y_n)` and `(α_n)` with values in `[0, n]`, such that
`lim P[E_n(α_n, n)] = 1` (4) and `lim P[E_n(y_n - α_n/4, y_n + α_n/4)] = 1` (5)", where
`E_n(α, β) = {S_n ⟷^{B_n} {n} × [α, β]}`; in the printed proof `α_n ∈ {1, …, n-1}` (for `n`
large) and `y_n ∈ {α_n/4, 3α_n/4}`, i.e. the interval in (5) is one of the two halves of
`[0, α_n]` (eq. (9) and the square-root trick). Lattice form of (5): an integer interval
`[a_n, b_n] ⊆ [0, α_n]` of length `b_n - a_n ≤ ⌈α_n / 2⌉` with `lim P[E_n(a_n, b_n)] = 1`.
The bounds `1 ≤ α_n ≤ n`, `a_n ≤ b_n ≤ α_n` are required for all `n ≥ 1` (a modification of
finitely many terms), `α_n ≤ n - 1` eventually. Users take `(h : DuminilCopinSidoraviciusTassion2016_lemma4)`.
[cite: DuminilCopinSidoraviciusTassion2016, Lemma 4] -/
def DuminilCopinSidoraviciusTassion2016_lemma4 : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < theta (slabGraph 3 k) (slabOrigin 3 k) p →
    ∀ u : ℕ → ℕ, (∀ n, 3 * u n ≤ n) →
      Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
        (slabUniqueConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n))) atTop (nhds 1) →
      ∃ α a b : ℕ → ℕ,
        (∀ n, 1 ≤ n → 1 ≤ α n ∧ α n ≤ n ∧ a n ≤ b n ∧ b n ≤ α n ∧ 2 * (b n - a n) ≤ α n + 1) ∧
        (∀ᶠ n in atTop, α n + 1 ≤ n) ∧
        Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
          (sideEvent k n (u n) (α n) n)) atTop (nhds 1) ∧
        Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
          (sideEvent k n (u n) (a n) (b n))) atTop (nhds 1)

/-- `X ⟷^B Y` is measurable for any finite planar `B`. [folklore] -/
theorem measurableSet_slabConn_of_finite {B : Set (ℤ × ℤ)} (hB : B.Finite) (X Y : Set (ℤ × ℤ)) :
    MeasurableSet (slabConn k B X Y) := by
  have hfin := finite_sym2 (slabLift_finite k hB)
  have hdet := determinedBy_slabConn k X Y (subset_rfl : B ⊆ B)
  rw [← hfin.coe_toFinset] at hdet
  exact hdet.measurableSet_of_finset

/-- **The symmetric copies of `E_n(α, n)`** (DST 2016, §2.1, proof of eq. (11): "Using Harris
inequality and the invariance of `P_p` under reflection"): the events
`{S'_n ⟷^{B'_n} Y_n^+}` and `{S'_n ⟷^{B'_n} Y_n^-}` have the probability of `E_n(α_n, n)`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 (proof of eq. (11))] -/
theorem real_sideEvent_translate (p : unitInterval) (n u α : ℕ) (y : ℤ) :
    (bondPercolation (slabGraph 3 k) p).real
        (slabConn k (sqBox (2 * (n : ℤ), y) n) (sqBox (2 * (n : ℤ), y) u)
          (sideSeg (3 * n) (y + α) (y + n))) =
      (bondPercolation (slabGraph 3 k) p).real (sideEvent k n u α n) ∧
    (bondPercolation (slabGraph 3 k) p).real
        (slabConn k (sqBox (2 * (n : ℤ), y) n) (sqBox (2 * (n : ℤ), y) u)
          (sideSeg (3 * n) (y - n) (y - α))) =
      (bondPercolation (slabGraph 3 k) p).real (sideEvent k n u α n) := by
  unfold sideEvent
  set v : ℤ × ℤ := (2 * (n : ℤ), y) with hv
  constructor
  · -- `Y_n^+`: translate by `v`
    have himg : slabConn k (sqBox v n) (sqBox v u) (sideSeg (3 * n) (y + α) (y + n)) =
        slabConn k (planarShift v '' sqBox 0 n) (planarShift v '' sqBox 0 u)
          (planarShift v '' sideSeg n α n) := by
      rw [image_planarShift_sqBox, image_planarShift_sqBox, image_planarShift_sideSeg, zero_add]
      congr 1
      simp only [hv]
      congr 1 <;> ring
    rw [himg, ← real_preimage_slabRelabel k (planarShift v) (planarAdj_planarShift v) p
      (slabConn k (planarShift v '' sqBox 0 n) (planarShift v '' sqBox 0 u)
        (planarShift v '' sideSeg n α n)), preimage_slabRelabel_slabConn]
  · -- `Y_n^-`: reflect in the horizontal axis, then translate by `v`
    have hflip : (bondPercolation (slabGraph 3 k) p).real
        (slabConn k (sqBox 0 n) (sqBox 0 u) (sideSeg n (-(n : ℤ)) (-(α : ℤ)))) =
        (bondPercolation (slabGraph 3 k) p).real
          (slabConn k (sqBox 0 n) (sqBox 0 u) (sideSeg n α n)) := by
      have himg : slabConn k (sqBox 0 n) (sqBox 0 u) (sideSeg n (-(n : ℤ)) (-(α : ℤ))) =
          slabConn k (planarFlip 0 '' sqBox 0 n) (planarFlip 0 '' sqBox 0 u)
            (planarFlip 0 '' sideSeg n α n) := by
        rw [image_planarFlip_sqBox, image_planarFlip_sqBox, image_planarFlip_sideSeg]
        simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, zero_sub]
        rfl
      rw [himg, ← real_preimage_slabRelabel k (planarFlip 0) (planarAdj_planarFlip 0) p
        (slabConn k (planarFlip 0 '' sqBox 0 n) (planarFlip 0 '' sqBox 0 u)
          (planarFlip 0 '' sideSeg n α n)), preimage_slabRelabel_slabConn]
    rw [← hflip]
    have himg : slabConn k (sqBox v n) (sqBox v u) (sideSeg (3 * n) (y - n) (y - α)) =
        slabConn k (planarShift v '' sqBox 0 n) (planarShift v '' sqBox 0 u)
          (planarShift v '' sideSeg n (-(n : ℤ)) (-(α : ℤ))) := by
      rw [image_planarShift_sqBox, image_planarShift_sqBox, image_planarShift_sideSeg, zero_add]
      congr 1
      simp only [hv]
      congr 1 <;> ring
    rw [himg, ← real_preimage_slabRelabel k (planarShift v) (planarAdj_planarShift v) p
      (slabConn k (planarShift v '' sqBox 0 n) (planarShift v '' sqBox 0 u)
        (planarShift v '' sideSeg n (-(n : ℤ)) (-(α : ℤ)))), preimage_slabRelabel_slabConn]

end CrossingEstimates

/-! ## The proof of Lemma 4, I: unions of targets, symmetric pairs and the square-root trick,
closed neighbourhoods and the local bound `P[E_n(s, s)] ≤ c < 1` -/

section Lemma4Tools

variable (k : ℕ)

/-- `X ⟷^B (Y₁ ∪ Y₂) = (X ⟷^B Y₁) ∪ (X ⟷^B Y₂)`. [folklore] -/
theorem slabConn_union_right (B X Y₁ Y₂ : Set (ℤ × ℤ)) :
    slabConn k B X (Y₁ ∪ Y₂) = slabConn k B X Y₁ ∪ slabConn k B X Y₂ := by
  ext ω
  simp only [slabConn, mem_openCrossing_iff, Set.mem_union, mem_slabLift_iff]
  constructor
  · rintro ⟨x, hx, y, hy | hy, h⟩
    · exact Or.inl ⟨x, hx, y, hy, h⟩
    · exact Or.inr ⟨x, hx, y, hy, h⟩
  · rintro (⟨x, hx, y, hy, h⟩ | ⟨x, hx, y, hy, h⟩)
    · exact ⟨x, hx, y, Or.inl hy, h⟩
    · exact ⟨x, hx, y, Or.inr hy, h⟩

/-- Reflected segments: `planarReflect t '' ({x} × [s, s']) = {t - x} × [s, s']`. [folklore] -/
theorem image_planarReflect_sideSeg (t x s s' : ℤ) :
    planarReflect t '' sideSeg x s s' = sideSeg (t - x) s s' := by
  ext w
  rw [Set.mem_image_equiv]
  simp only [planarReflect_symm, planarReflect_apply, sideSeg, Set.mem_setOf_eq]
  omega

/-- **Square-root trick, general two-event form** (DST 2016, eq. (3), `m = 2`): for increasing
measurable `A, B` and `C ⊆ A ∪ B`, `max(P[A], P[B]) ≥ 1 - (1 - P[C])^{1/2}`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.1 eq. (3)] -/
theorem sqrt_trick_two (p : unitInterval) {A B C : Set (BondConfig (slab 3 k))}
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hC : C ⊆ A ∪ B) :
    1 - (1 - (bondPercolation (slabGraph 3 k) p).real C) ^ ((2 : ℝ)⁻¹) ≤
      max ((bondPercolation (slabGraph 3 k) p).real A) ((bondPercolation (slabGraph 3 k) p).real B) := by
  set P := bondPercolation (slabGraph 3 k) p with hP
  have h := sqrt_trick_holds (slabGraph 3 k) p (ι := Bool) (fun b => if b then A else B)
    (fun b => by cases b <;> simpa) (fun b => by cases b <;> simpa)
  obtain ⟨i, hi⟩ := h
  have hU : (⋃ b : Bool, (if b then A else B)) = A ∪ B := by
    ext ω; simp [or_comm]
  rw [hU] at hi
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hi
  have hmono : 1 - (1 - P.real C) ^ ((2 : ℝ)⁻¹) ≤ 1 - (1 - P.real (A ∪ B)) ^ ((2 : ℝ)⁻¹) := by
    have h1 : P.real C ≤ P.real (A ∪ B) := measureReal_mono hC
    have h2 : P.real (A ∪ B) ≤ 1 := measureReal_le_one
    have := Real.rpow_le_rpow (by linarith) (by linarith : 1 - P.real (A ∪ B) ≤ 1 - P.real C)
      (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    linarith
  refine hmono.trans ?_
  cases i
  · exact hi.trans (le_max_right _ _)
  · exact hi.trans (le_max_left _ _)

/-- Squeeze for the square-root trick: if `1 - (1 - x_n)^{r} ≤ f_n ≤ 1` and `x_n → 1` then
`f_n → 1` (`r > 0`). [folklore] -/
theorem tendsto_one_of_sqrt_trick {x f : ℕ → ℝ} {r : ℝ} (hr : 0 < r)
    (hx : Tendsto x atTop (nhds 1)) (hf1 : ∀ n, f n ≤ 1)
    (hle : ∀ᶠ n in atTop, 1 - (1 - x n) ^ r ≤ f n) : Tendsto f atTop (nhds 1) := by
  have h0 : Tendsto (fun n => 1 - (1 - x n) ^ r) atTop (nhds 1) := by
    have h1 : Tendsto (fun n => 1 - x n) atTop (nhds (1 - 1)) := tendsto_const_nhds.sub hx
    rw [sub_self] at h1
    have h2 : Tendsto (fun n => (1 - x n) ^ r) atTop (nhds ((0 : ℝ) ^ r)) :=
      h1.rpow_const (Or.inr hr.le)
    rw [Real.zero_rpow hr.ne'] at h2
    simpa using tendsto_const_nhds.sub h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 tendsto_const_nhds hle
    (Filter.Eventually.of_forall hf1)

/-- The event that all edges inside `T̄` are closed. [folklore] -/
def allClosed (T : Set (ℤ × ℤ)) : Set (BondConfig (slab 3 k)) :=
  {ω | ∀ e ∈ Set.sym2 (slabLift k T), e ∉ ω}

variable (g : ℤ × ℤ ≃ ℤ × ℤ)

/-- Transport of `allClosed`. [folklore] -/
theorem preimage_slabRelabel_allClosed (T : Set (ℤ × ℤ)) :
    slabRelabel k g ⁻¹' allClosed k (g '' T) = allClosed k T := by
  ext ω
  simp only [Set.mem_preimage, allClosed, Set.mem_setOf_eq]
  constructor
  · intro h e he heω
    have hmem : sym2Equiv (slabEquiv k g) e ∈ Set.sym2 (slabLift k (g '' T)) := by
      rw [Set.mem_sym2_iff_subset] at he ⊢
      intro v hv
      rw [SetLike.mem_coe, sym2Equiv_apply, Sym2.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      rw [← image_slabEquiv_slabLift]
      exact Set.mem_image_of_mem _ (he hw)
    have := h _ hmem
    rw [BondConfig.mem_relabel_iff, Equiv.symm_apply_apply] at this
    exact this heω
  · intro h e he heω
    rw [BondConfig.mem_relabel_iff] at heω
    refine h _ ?_ heω
    rw [Set.mem_sym2_iff_subset] at he ⊢
    intro v hv
    rw [SetLike.mem_coe, sym2Equiv_symm, sym2Equiv_apply, Sym2.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have : w ∈ slabLift k (g '' T) := he hw
    rw [← image_slabEquiv_slabLift, Set.mem_image_equiv] at this
    exact this

/-- `allClosed T` is a cylinder event, hence measurable, for finite `T`. [folklore] -/
theorem allClosed_eq_localCylinder {T : Set (ℤ × ℤ)} (hT : T.Finite) :
    allClosed k T = localCylinder
      (↑(finite_sym2 (slabLift_finite k hT)).toFinset) (∅ : Set (Sym2 (slab 3 k))) := by
  ext ω
  simp [allClosed, localCylinder]

/-- `allClosed T` is measurable for finite `T`. [folklore] -/
theorem measurableSet_allClosed {T : Set (ℤ × ℤ)} (hT : T.Finite) :
    MeasurableSet (allClosed k T) := by
  rw [allClosed_eq_localCylinder k hT]
  exact measurableSet_localCylinder (Finset.finite_toSet _).countable _

/-- For `p < 1`, all edges of a fixed finite region are closed with positive probability.
[folklore] -/
theorem real_allClosed_pos (p : unitInterval) (hp : (p : ℝ) < 1) {T : Set (ℤ × ℤ)}
    (hT : T.Finite) : 0 < (bondPercolation (slabGraph 3 k) p).real (allClosed k T) := by
  rw [allClosed_eq_localCylinder k hT, show bondPercolation (slabGraph 3 k) p =
    ProbabilityTheory.setBernoulli (slabGraph 3 k).edgeSet p from rfl,
    Russo.setBernoulli_real_localCylinder]
  refine Finset.prod_pos fun e _ => ?_
  simp only [Russo.weight, Set.mem_empty_iff_false, if_false]
  split_ifs
  · linarith
  · norm_num

/-- **The local bound** (DST 2016, proof of Lemma 4: "The probability of the event `E_n(0,0)`
is smaller than some constant `c < 1` uniformly in `n`"): for `u < n`, an open path from `S̄_n`
to the single column `\overline{(n, s)}` uses an open edge inside `\overline{(n,s) + B_1}`, so
`P[E_n(s, s)] ≤ 1 - P[all edges of \overline{(n,s) + B_1} closed] = 1 - P[all edges of
\overline{B_1} closed]` (translation invariance). [cite: DuminilCopinSidoraviciusTassion2016, Lemma 4 (proof)] -/
theorem real_sideEvent_point_le (p : unitInterval) {n u : ℕ} (hun : u < n) (s : ℤ) :
    (bondPercolation (slabGraph 3 k) p).real (sideEvent k n u s s) ≤
      1 - (bondPercolation (slabGraph 3 k) p).real (allClosed k (sqBox 0 1)) := by
  set P := bondPercolation (slabGraph 3 k) p with hP
  set c : ℤ × ℤ := ((n : ℤ), s) with hc
  -- translation invariance of the closed neighbourhood
  have htr : P.real (allClosed k (sqBox c 1)) = P.real (allClosed k (sqBox 0 1)) := by
    rw [hP, ← real_preimage_slabRelabel k (planarShift c) (planarAdj_planarShift c) p
      (allClosed k (sqBox c 1))]
    have : sqBox c 1 = planarShift c '' sqBox 0 1 := by rw [image_planarShift_sqBox, zero_add]
    rw [this, preimage_slabRelabel_allClosed]
  rw [← htr]
  have hle : P.real (sideEvent k n u s s) ≤ P.real (allClosed k (sqBox c 1))ᶜ := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [ProbabilityTheory.setBernoulli_ae_subset (u := (slabGraph 3 k).edgeSet)
      (p := p)] with ω hω hE
    obtain ⟨a, ha, b, hb, hab⟩ := hE
    have hpath : PathIn (openGraph ω) (slabLift k (sqBox 0 n)) b a :=
      (mem_openConnIn_iff_pathIn.1 hab).symm
    intro hcl
    rcases hpath.exit_or (R := slabLift k (sideSeg n s s)) hb with h | ⟨x, y, hx, hy, -, hadj, -⟩
    · -- the path stays in the column: then `a` is in the column, contradicting `u < n`
      have haC : a ∈ slabLift k (sideSeg n s s) := h.right_mem.1
      simp only [mem_slabLift_iff, sideSeg, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero,
        Prod.snd_zero, sub_zero] at haC ha
      omega
    · -- the exit edge is open and lies inside `\overline{c + B_1}`
      have hopen : s(x, y) ∈ ω := ((openGraph_adj ω x y).1 hadj).1
      refine hcl s(x, y) ?_ hopen
      rw [Set.mk_mem_sym2_iff]
      have hlat : (slabGraph 3 k).Adj x y := (SimpleGraph.mem_edgeSet _).1 (hω hopen)
      have hxy := (zdGraph_three_adj_iff x.1 y.1).1 hlat
      simp only [mem_slabLift_iff, sideSeg, Set.mem_setOf_eq] at hx hy
      simp only [mem_slabLift_iff, sqBox, Set.mem_setOf_eq, abs_le, hc, planar]
      have hpx : planar k x = (x.1 1, x.1 2) := rfl
      rw [hpx] at hx
      have hpy : planar k y = (y.1 1, y.1 2) := rfl
      rw [hpy] at hy
      simp only at hx hy
      rcases hxy with ⟨-, hpa⟩ | ⟨hpe, -⟩
      · simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at hpa
        push_cast
        omega
      · simp only [Prod.mk.injEq] at hpe
        push_cast
        omega
  have hcompl : P.real (allClosed k (sqBox c 1))ᶜ = 1 - P.real (allClosed k (sqBox c 1)) :=
    probReal_compl_eq_one_sub (measurableSet_allClosed k (sqBox_finite c 1))
  linarith

end Lemma4Tools

/-! ## The proof of Lemma 4, II: `P[E_n(0, n)] → 1`, the case `p = 1`, and the construction
of `α_n`, `[a_n, b_n]` -/

section Lemma4Proof

variable (k : ℕ)

/-- Invariance of `P[X ⟷^B Y]` under a planar symmetry, image form. [cite: GrimmettPercolation1999, §1.6 (p. 16)] -/
theorem real_slabConn_image (g : ℤ × ℤ ≃ ℤ × ℤ) (hg : ∀ z w, planarAdj (g z) (g w) ↔ planarAdj z w)
    (p : unitInterval) (B X Y : Set (ℤ × ℤ)) :
    (bondPercolation (slabGraph 3 k) p).real (slabConn k (g '' B) (g '' X) (g '' Y)) =
      (bondPercolation (slabGraph 3 k) p).real (slabConn k B X Y) := by
  rw [← preimage_slabRelabel_slabConn k g B X Y, real_preimage_slabRelabel k g hg]

/-- Reflected segments under the diagonal reflection: `swap '' ({x} × [s, s'])` is the
horizontal segment `[s, s'] × {x}`. [folklore] -/
theorem mem_image_planarSwap_sideSeg (x s s' : ℤ) (w : ℤ × ℤ) :
    w ∈ planarSwap '' sideSeg x s s' ↔ w.2 = x ∧ s ≤ w.1 ∧ w.1 ≤ s' := by
  rw [Set.mem_image_equiv]
  simp [planarSwap, sideSeg]

/-- **`P[E_n(0, n)] → 1`** (DST 2016, proof of Lemma 4: "Applying the square-root trick and
using the symmetries of the box, we obtain `P[E_n(0,n)] ≥ 1 - (1 - P[S_n ⟷^{B_n} ∂B_n])^{1/8}`
which implies that `P[E_n(0,n)]` also tends to `1`"). Here in three symmetric halvings
(`∂B_n =` right-and-left `∪` top-and-bottom sides; right `∪` left; upper `∪` lower half of the
right side), each an instance of the two-event square-root trick.
[cite: DuminilCopinSidoraviciusTassion2016, Lemma 4 (proof)] -/
theorem tendsto_real_sideEvent_zero (p : unitInterval) (u : ℕ → ℕ)
    (hD : Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real
      (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n))) atTop (nhds 1)) :
    Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real (sideEvent k n (u n) 0 n))
      atTop (nhds 1) := by
  -- notation for scale `n`
  have hmeas : ∀ (n : ℕ) (Y : Set (ℤ × ℤ)), MeasurableSet (slabConn k (sqBox 0 n) (sqBox 0 (u n)) Y) :=
    fun n Y => measurableSet_slabConn k 0 n _ _
  have hup : ∀ (n : ℕ) (Y : Set (ℤ × ℤ)), IsUpperSet (slabConn k (sqBox 0 n) (sqBox 0 (u n)) Y) :=
    fun n Y => isUpperSet_openCrossing _ _ _
  have hbox_swap : ∀ m : ℕ, planarSwap '' sqBox (0 : ℤ × ℤ) m = sqBox 0 m := fun m => by
    rw [image_planarSwap_sqBox]; rfl
  have hbox_refl : ∀ m : ℕ, planarReflect 0 '' sqBox (0 : ℤ × ℤ) m = sqBox 0 m := fun m => by
    rw [image_planarReflect_sqBox]; rfl
  have hbox_flip : ∀ m : ℕ, planarFlip 0 '' sqBox (0 : ℤ × ℤ) m = sqBox 0 m := fun m => by
    rw [image_planarFlip_sqBox]; rfl
  -- step 1: right-and-left sides
  set RL : ℕ → Set (ℤ × ℤ) := fun n => sideSeg n (-(n : ℤ)) n ∪ sideSeg (-(n : ℤ)) (-(n : ℤ)) n
    with hRL
  have h1 : Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (RL n))) atTop (nhds 1) := by
    refine tendsto_one_of_sqrt_trick (r := (2 : ℝ)⁻¹) (by norm_num) hD
      (fun n => measureReal_le_one) (Filter.Eventually.of_forall fun n => ?_)
    have hsym : (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (RL n)) =
        (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (planarSwap '' RL n)) := by
      have := real_slabConn_image k planarSwap planarAdj_planarSwap p (sqBox 0 n) (sqBox 0 (u n)) (RL n)
      rw [hbox_swap, hbox_swap] at this
      exact this.symm
    have hcov : slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n) ⊆
        slabConn k (sqBox 0 n) (sqBox 0 (u n)) (RL n) ∪
          slabConn k (sqBox 0 n) (sqBox 0 (u n)) (planarSwap '' RL n) := by
      rw [← slabConn_union_right]
      refine openCrossing_mono subset_rfl subset_rfl (slabLift_mono k ?_)
      intro w hw
      rw [mem_sqSphere_iff] at hw
      simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le, le_abs] at hw
      simp only [hRL, Set.image_union, Set.mem_union, mem_image_planarSwap_sideSeg]
      simp only [sideSeg, Set.mem_setOf_eq]
      omega
    have := sqrt_trick_two k p (hup n _) (hup n _) (hmeas n _) (hmeas n _) hcov
    rwa [← hsym, max_self] at this
  -- step 2: the right side
  have h2 : Tendsto (fun n => (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n))
      (sideSeg n (-(n : ℤ)) n))) atTop (nhds 1) := by
    refine tendsto_one_of_sqrt_trick (r := (2 : ℝ)⁻¹) (by norm_num) h1
      (fun n => measureReal_le_one) (Filter.Eventually.of_forall fun n => ?_)
    have hsym : (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg n (-(n : ℤ)) n)) =
        (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg (-(n : ℤ)) (-(n : ℤ)) n)) := by
      have := real_slabConn_image k (planarReflect 0) (planarAdj_planarReflect 0) p (sqBox 0 n)
        (sqBox 0 (u n)) (sideSeg n (-(n : ℤ)) n)
      rw [hbox_refl, hbox_refl, image_planarReflect_sideSeg, zero_sub] at this
      exact this.symm
    have hcov : slabConn k (sqBox 0 n) (sqBox 0 (u n)) (RL n) ⊆
        slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg n (-(n : ℤ)) n) ∪
          slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg (-(n : ℤ)) (-(n : ℤ)) n) := by
      rw [← slabConn_union_right]
    have := sqrt_trick_two k p (hup n _) (hup n _) (hmeas n _) (hmeas n _) hcov
    rwa [← hsym, max_self] at this
  -- step 3: the upper half of the right side
  refine tendsto_one_of_sqrt_trick (r := (2 : ℝ)⁻¹) (by norm_num) h2
    (fun n => measureReal_le_one) (Filter.Eventually.of_forall fun n => ?_)
  have hsym : (bondPercolation (slabGraph 3 k) p).real (sideEvent k n (u n) 0 n) =
      (bondPercolation (slabGraph 3 k) p).real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg n (-(n : ℤ)) 0)) := by
    have := real_slabConn_image k (planarFlip 0) (planarAdj_planarFlip 0) p (sqBox 0 n)
      (sqBox 0 (u n)) (sideSeg n 0 n)
    rw [hbox_flip, hbox_flip, image_planarFlip_sideSeg, zero_sub, sub_zero] at this
    exact this.symm
  have hcov : slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg n (-(n : ℤ)) n) ⊆
      sideEvent k n (u n) 0 n ∪ slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sideSeg n (-(n : ℤ)) 0) := by
    unfold sideEvent
    rw [← slabConn_union_right]
    refine openCrossing_mono subset_rfl subset_rfl (slabLift_mono k ?_)
    intro w hw
    simp only [sideSeg, Set.mem_setOf_eq, Set.mem_union] at hw ⊢
    omega
  have := sqrt_trick_two k p (A := sideEvent k n (u n) 0 n) (isUpperSet_openCrossing _ _ _)
    (hup n _) (measurableSet_slabConn k 0 n _ _) (hmeas n _) hcov
  rwa [← hsym, max_self] at this

/-! ### The case `p = 1`: connections hold surely -/

/-- The vertex of height `0` over the planar point `z`. [folklore] -/
def baseVertex (z : ℤ × ℤ) : slab 3 k := ⟨![0, z.1, z.2], ⟨le_rfl, by simp⟩⟩

/-- The planar part of `baseVertex z` is `z`. [folklore] -/
@[simp] theorem planar_baseVertex (z : ℤ × ℤ) : planar k (baseVertex k z) = z := by
  simp [planar, baseVertex]

/-- Planar-adjacent base vertices are adjacent in the slab. [folklore] -/
theorem baseVertex_adj {z w : ℤ × ℤ} (h : planarAdj z w) :
    (slabGraph 3 k).Adj (baseVertex k z) (baseVertex k w) := by
  simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
  rw [zdGraph_three_adj_iff]
  left
  refine ⟨rfl, ?_⟩
  simpa [baseVertex] using h

/-- In the full configuration `ω = E(S_k)`, adjacent base vertices of `T̄` are joined in `T̄`.
[folklore] -/
theorem edgeSet_openConnIn_of_planarAdj {T : Set (ℤ × ℤ)} {z w : ℤ × ℤ} (h : planarAdj z w)
    (hz : z ∈ T) (hw : w ∈ T) :
    (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k T) (baseVertex k z) (baseVertex k w) := by
  rw [mem_openConnIn_iff_pathIn]
  refine PathIn.of_adj (by simpa using hz) (by simpa using hw) ?_
  rw [openGraph_adj]
  exact ⟨(SimpleGraph.mem_edgeSet _).2 (baseVertex_adj k h), (baseVertex_adj k h).ne⟩

/-- Horizontal lattice paths in the full configuration. [folklore] -/
theorem edgeSet_openConnIn_horizontal {T : Set (ℤ × ℤ)} (a b : ℤ) (m : ℕ)
    (hT : ∀ j : ℕ, j ≤ m → (a + j, b) ∈ T) :
    (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k T) (baseVertex k (a, b))
      (baseVertex k (a + m, b)) := by
  induction m with
  | zero =>
    rw [mem_openConnIn_iff_pathIn]
    simpa using PathIn.refl (G := openGraph (slabGraph 3 k).edgeSet)
      (A := slabLift k T) (u := baseVertex k (a, b)) (by simpa using hT 0 le_rfl)
  | succ m ih =>
    have h1 := ih fun j hj => hT j (hj.trans (Nat.le_succ m))
    have h2 : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k T) (baseVertex k (a + m, b))
        (baseVertex k (a + (m + 1 : ℕ), b)) := by
      refine edgeSet_openConnIn_of_planarAdj k ?_ (hT m (Nat.le_succ m)) (hT (m + 1) le_rfl)
      left; left
      simp only [Prod.mk_add_mk, Prod.mk.injEq, add_zero, and_true]
      push_cast; ring
    exact SlabCriticality.openConnIn_trans h1 h2

/-- Vertical lattice paths in the full configuration. [folklore] -/
theorem edgeSet_openConnIn_vertical {T : Set (ℤ × ℤ)} (a b : ℤ) (m : ℕ)
    (hT : ∀ j : ℕ, j ≤ m → (a, b + j) ∈ T) :
    (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k T) (baseVertex k (a, b))
      (baseVertex k (a, b + m)) := by
  induction m with
  | zero =>
    rw [mem_openConnIn_iff_pathIn]
    simpa using PathIn.refl (G := openGraph (slabGraph 3 k).edgeSet)
      (A := slabLift k T) (u := baseVertex k (a, b)) (by simpa using hT 0 le_rfl)
  | succ m ih =>
    have h1 := ih fun j hj => hT j (hj.trans (Nat.le_succ m))
    have h2 : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k T) (baseVertex k (a, b + m))
        (baseVertex k (a, b + (m + 1 : ℕ))) := by
      refine edgeSet_openConnIn_of_planarAdj k ?_ (hT m (Nat.le_succ m)) (hT (m + 1) le_rfl)
      right; left
      simp only [Prod.mk_add_mk, Prod.mk.injEq, add_zero, true_and]
      push_cast; ring
    exact SlabCriticality.openConnIn_trans h1 h2

/-- In the full configuration, `E_n(s, t)` holds as soon as the segment `{n} × [s, t]` meets
`B_n` (a lattice path along the axis and then up or down the right side). [folklore] -/
theorem edgeSet_mem_sideEvent (n u : ℕ) {s t m : ℤ} (hsm : s ≤ m) (hmt : m ≤ t) (hm : |m| ≤ n) :
    (slabGraph 3 k).edgeSet ∈ sideEvent k n u s t := by
  refine ⟨baseVertex k 0, ?_, baseVertex k ((n : ℤ), m), ?_, ?_⟩
  · simp [sqBox]
  · show planar k (baseVertex k ((n : ℤ), m)) ∈ sideSeg (n : ℤ) s t
    rw [planar_baseVertex]
    exact ⟨rfl, hsm, hmt⟩
  · have hh : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 n)) (baseVertex k ((0 : ℤ), (0 : ℤ)))
        (baseVertex k ((0 : ℤ) + (n : ℕ), (0 : ℤ))) := by
      refine edgeSet_openConnIn_horizontal k 0 0 n fun j hj => ?_
      simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]
      omega
    rw [abs_le] at hm
    rcases le_or_gt 0 m with h0m | h0m
    · have hv : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 n)) (baseVertex k ((n : ℤ), (0 : ℤ)))
          (baseVertex k ((n : ℤ), (0 : ℤ) + (m.toNat : ℕ))) := by
        refine edgeSet_openConnIn_vertical k n 0 m.toNat fun j hj => ?_
        simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]
        omega
      have e1 : ((0 : ℤ) + (n : ℕ), (0 : ℤ)) = ((n : ℤ), (0 : ℤ)) := by simp
      have e2 : ((n : ℤ), (0 : ℤ) + (m.toNat : ℕ)) = ((n : ℤ), m) := by
        simp only [Prod.mk.injEq, true_and]; omega
      rw [e1] at hh
      rw [e2] at hv
      exact SlabCriticality.openConnIn_trans hh hv
    · -- `m < 0`: go down, i.e. reverse an upward path from `(n, m)`
      have hv : (slabGraph 3 k).edgeSet ∈ openConnIn (slabLift k (sqBox 0 n)) (baseVertex k ((n : ℤ), m))
          (baseVertex k ((n : ℤ), m + ((-m).toNat : ℕ))) := by
        refine edgeSet_openConnIn_vertical k n m (-m).toNat fun j hj => ?_
        simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]
        omega
      have e1 : ((0 : ℤ) + (n : ℕ), (0 : ℤ)) = ((n : ℤ), (0 : ℤ)) := by simp
      have e2 : ((n : ℤ), m + ((-m).toNat : ℕ)) = ((n : ℤ), (0 : ℤ)) := by
        simp only [Prod.mk.injEq, true_and]; omega
      rw [e1] at hh
      rw [e2] at hv
      exact SlabCriticality.openConnIn_trans hh (openConnIn_reverse hv)

/-- At `p = 1` every event containing the full configuration has probability one. [folklore] -/
theorem real_eq_one_of_edgeSet_mem {A : Set (BondConfig (slab 3 k))}
    (h : (slabGraph 3 k).edgeSet ∈ A) : (bondPercolation (slabGraph 3 k) 1).real A = 1 := by
  rw [show bondPercolation (slabGraph 3 k) 1 = ProbabilityTheory.setBernoulli (slabGraph 3 k).edgeSet 1
    from rfl, ProbabilityTheory.setBernoulli_one, measureReal_def, Measure.dirac_apply_of_mem h]
  simp

end Lemma4Proof

/-! ## The proof of Lemma 4, III: assembly -/

section Lemma4Final

/-- **DST 2016, Lemma 4** (lattice form `DuminilCopinSidoraviciusTassion2016_lemma4`), following the printed proof
(p. 4): `P[E_n(0,n)] → 1` by the square-root trick and the symmetries of the box
(`tendsto_real_sideEvent_zero`); the local bound `P[E_n(s,s)] ≤ c < 1`
(`real_sideEvent_point_le`) gives (7) `P[E_n(0,0)] < P[E_n(1,n)]` and (8)
`P[E_n(0,n-1)] > P[E_n(n,n)]` for `n` large; `α_n = max{α ≤ n-1 : P[E_n(0,α-1)] < P[E_n(α,n)]}`
(`Nat.findGreatest`) satisfies (9), whence `P[E_n(α_n,n)] → 1` and `P[E_n(0,α_n)] → 1` by two
more square-root tricks, and a last one on `E_n(0,α_n) = E_n(0,⌊α_n/2⌋) ∪ E_n(⌊α_n/2⌋+1,α_n)`
gives the half `[a_n, b_n]`. The degenerate parameter `p = 1` (where `P_1` is the point mass at
the full configuration) is treated separately by exhibiting lattice paths.
[cite: DuminilCopinSidoraviciusTassion2016, Lemma 4] -/
theorem DuminilCopinSidoraviciusTassion2016_lemma4_holds : DuminilCopinSidoraviciusTassion2016_lemma4 := by
  classical
  intro k hk p hθ u hu3 hlim
  set P := bondPercolation (slabGraph 3 k) p with hP
  set f : ℕ → ℤ → ℤ → ℝ := fun n s t => P.real (sideEvent k n (u n) s t) with hf
  have hf1 : ∀ n s t, f n s t ≤ 1 := fun n s t => measureReal_le_one
  have hf0 : ∀ n s t, 0 ≤ f n s t := fun n s t => measureReal_nonneg
  have hfm : ∀ (n : ℕ) (s t : ℤ), MeasurableSet (sideEvent k n (u n) s t) :=
    fun n s t => measurableSet_slabConn k 0 n _ _
  have hfu : ∀ (n : ℕ) (s t : ℤ), IsUpperSet (sideEvent k n (u n) s t) :=
    fun n s t => isUpperSet_openCrossing _ _ _
  have hsplit : ∀ (n : ℕ) (s m t : ℤ),
      sideEvent k n (u n) s t ⊆ sideEvent k n (u n) s m ∪ sideEvent k n (u n) (m + 1) t := by
    intro n s m t
    unfold sideEvent
    rw [← slabConn_union_right]
    refine openCrossing_mono subset_rfl subset_rfl (slabLift_mono k ?_)
    intro w hw
    simp only [sideSeg, Set.mem_setOf_eq, Set.mem_union] at hw ⊢
    omega
  -- the two-event square-root trick in the form used below
  have hsq : ∀ (n : ℕ) (s m t : ℤ),
      1 - (1 - f n s t) ^ ((2 : ℝ)⁻¹) ≤ max (f n s m) (f n (m + 1) t) := fun n s m t =>
    sqrt_trick_two k p (hfu n s m) (hfu n (m + 1) t) (hfm n s m) (hfm n (m + 1) t) (hsplit n s m t)
  ------------------------------------------------------------------
  -- the case `p = 1`
  ------------------------------------------------------------------
  rcases eq_or_lt_of_le p.2.2 with hp1 | hp1
  · have hp : p = 1 := Subtype.ext hp1
    refine ⟨fun _ => 1, fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro n hn
      show 1 ≤ 1 ∧ 1 ≤ n ∧ 0 ≤ 0 ∧ 0 ≤ 1 ∧ 2 * (0 - 0) ≤ 1 + 1
      omega
    · exact (Filter.eventually_ge_atTop 2).mono fun n hn => by
        show 1 + 1 ≤ n
        omega
    · refine tendsto_const_nhds.congr' ?_
      refine (Filter.eventually_ge_atTop 1).mono fun n hn => ?_
      show (1 : ℝ) = (bondPercolation (slabGraph 3 k) p).real (sideEvent k n (u n) ((1 : ℕ) : ℤ) n)
      rw [hp]
      symm
      refine real_eq_one_of_edgeSet_mem k (edgeSet_mem_sideEvent k n (u n) (m := 1) ?_ ?_ ?_)
      · norm_num
      · exact_mod_cast hn
      · rw [abs_one]; exact_mod_cast hn
    · refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => ?_)
      show (1 : ℝ) = (bondPercolation (slabGraph 3 k) p).real (sideEvent k n (u n) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ))
      rw [hp]
      symm
      refine real_eq_one_of_edgeSet_mem k (edgeSet_mem_sideEvent k n (u n) (m := 0) ?_ ?_ ?_)
      · norm_num
      · norm_num
      · simp
  ------------------------------------------------------------------
  -- the case `p < 1`
  ------------------------------------------------------------------
  -- (0) `P[S_n ⟷ ∂B_n] → 1`, hence `f_n(0, n) → 1`
  have hD : Tendsto (fun n => P.real (slabConn k (sqBox 0 n) (sqBox 0 (u n)) (sqSphere 0 n)))
      atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
      (Filter.Eventually.of_forall fun n =>
        measureReal_mono (slabUniqueConn_subset_slabConn k _ _ _))
      (Filter.Eventually.of_forall fun n => measureReal_le_one)
  have h0n : Tendsto (fun n => f n 0 n) atTop (nhds 1) := tendsto_real_sideEvent_zero k p u hD
  -- the local bound `f_n(s, s) ≤ c < 1`
  set c : ℝ := 1 - P.real (allClosed k (sqBox 0 1)) with hc
  have hc1 : c < 1 := by
    have := real_allClosed_pos k p hp1 (sqBox_finite 0 1)
    linarith
  have hloc : ∀ n, 1 ≤ n → ∀ s : ℤ, f n s s ≤ c := fun n hn s =>
    real_sideEvent_point_le k p (by have := hu3 n; omega) s
  -- eventually `c < 1 - (1 - f_n(0,n))^{1/2}`
  have hevc : ∀ᶠ n in atTop, c < 1 - (1 - f n 0 n) ^ ((2 : ℝ)⁻¹) := by
    have hε : 0 < (1 - c) ^ 2 := by nlinarith
    have hev := h0n.eventually (Ioi_mem_nhds (show 1 - (1 - c) ^ 2 < 1 by linarith))
    refine hev.mono fun n hn => ?_
    have hn' : 1 - (1 - c) ^ 2 < f n 0 n := hn
    have h1 : 1 - f n 0 n < (1 - c) ^ 2 := by linarith
    have h2 : (1 - f n 0 n) ^ ((2 : ℝ)⁻¹) < ((1 - c) ^ 2) ^ ((2 : ℝ)⁻¹) :=
      Real.rpow_lt_rpow (by linarith [hf1 n 0 n]) h1 (by norm_num)
    have h3 : ((1 - c) ^ 2) ^ ((2 : ℝ)⁻¹) = 1 - c := by
      have := Real.pow_rpow_inv_natCast (show 0 ≤ 1 - c by linarith) two_ne_zero
      exact_mod_cast this
    linarith
  -- (7) and (8), eventually
  set Good : ℕ → Prop := fun n =>
    2 ≤ n ∧ f n 0 0 < f n 1 n ∧ f n n n < f n 0 ((n : ℤ) - 1) with hGood
  have hGoodev : ∀ᶠ n in atTop, Good n := by
    refine ((Filter.eventually_ge_atTop 2).and hevc).mono fun n hn => ⟨hn.1, ?_, ?_⟩
    · have hst := hsq n 0 0 n
      rw [zero_add] at hst
      have hmax : c < max (f n 0 0) (f n 1 n) := lt_of_lt_of_le hn.2 hst
      have h00 : f n 0 0 ≤ c := hloc n (by omega) 0
      rcases le_or_gt (f n 1 n) (f n 0 0) with h | h
      · rw [max_eq_left h] at hmax
        linarith
      · exact h
    · have hst := hsq n 0 ((n : ℤ) - 1) n
      rw [sub_add_cancel] at hst
      have hmax : c < max (f n 0 ((n : ℤ) - 1)) (f n n n) := lt_of_lt_of_le hn.2 hst
      have hnn : f n n n ≤ c := hloc n (by omega) n
      rcases le_or_gt (f n 0 ((n : ℤ) - 1)) (f n n n) with h | h
      · rw [max_eq_right h] at hmax
        linarith
      · exact h
  -- `α_n`
  set pr : ℕ → ℕ → Prop := fun n m => f n 0 ((m : ℤ) - 1) < f n m n with hpr
  set α : ℕ → ℕ := fun n => if Good n then Nat.findGreatest (pr n) (n - 1) else 1 with hα
  have hαG : ∀ n, Good n → 1 ≤ α n ∧ α n ≤ n - 1 ∧ pr n (α n) ∧
      f n ((α n : ℤ) + 1) n ≤ f n 0 (α n) := by
    intro n hG
    have hαn : α n = Nat.findGreatest (pr n) (n - 1) := if_pos hG
    have hp1' : pr n 1 := by
      simp only [hpr]
      push_cast
      simpa using hG.2.1
    have h1 : 1 ≤ Nat.findGreatest (pr n) (n - 1) := Nat.le_findGreatest (by omega) hp1'
    have h2 : Nat.findGreatest (pr n) (n - 1) ≤ n - 1 := Nat.findGreatest_le _
    have h3 : pr n (Nat.findGreatest (pr n) (n - 1)) := Nat.findGreatest_spec (m := 1) (by omega) hp1'
    rw [hαn]
    refine ⟨h1, h2, h3, ?_⟩
    rcases lt_or_eq_of_le h2 with hlt | heq
    · have hng := Nat.findGreatest_is_greatest (Nat.lt_succ_self (Nat.findGreatest (pr n) (n - 1)))
        (Nat.succ_le_of_lt hlt)
      simp only [hpr, not_lt] at hng
      push_cast at hng
      simpa using hng
    · rw [heq]
      have h8 := hG.2.2
      have e : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        have : 1 ≤ n := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [e, sub_add_cancel]
      exact h8.le
  -- `[a_n, b_n]`: the better half of `[0, α_n]`
  set cond : ℕ → Prop := fun n => f n ((α n / 2 : ℕ) + 1 : ℤ) (α n) ≤ f n 0 (α n / 2 : ℕ)
    with hcond
  set a : ℕ → ℕ := fun n => if Good n then (if cond n then 0 else α n / 2 + 1) else 0 with ha
  set b : ℕ → ℕ := fun n => if Good n then (if cond n then α n / 2 else α n) else 0 with hb
  refine ⟨α, a, b, ?_, ?_, ?_, ?_⟩
  · -- bounds
    intro n hn
    by_cases hG : Good n
    · obtain ⟨h1, h2, -, -⟩ := hαG n hG
      have hαn : 1 ≤ α n ∧ α n ≤ n := ⟨h1, by omega⟩
      simp only [ha, hb, if_pos hG]
      split_ifs <;> omega
    · simp only [hα, ha, hb, if_neg hG]
      omega
  · -- eventually `α_n + 1 ≤ n`
    refine hGoodev.mono fun n hG => ?_
    obtain ⟨-, h2, -, -⟩ := hαG n hG
    have := hG.1
    omega
  · -- (4): `f_n(α_n, n) → 1`
    refine tendsto_one_of_sqrt_trick (r := (2 : ℝ)⁻¹) (by norm_num) h0n (fun n => hf1 n _ _)
      (hGoodev.mono fun n hG => ?_)
    obtain ⟨-, -, h3, -⟩ := hαG n hG
    have hst := hsq n 0 ((α n : ℤ) - 1) n
    rw [sub_add_cancel] at hst
    have hlt : f n 0 ((α n : ℤ) - 1) < f n (α n) n := h3
    rw [max_eq_right hlt.le] at hst
    exact hst
  · -- (5): `f_n(a_n, b_n) → 1`, via `f_n(0, α_n) → 1`
    have h0α : Tendsto (fun n => f n 0 (α n)) atTop (nhds 1) := by
      refine tendsto_one_of_sqrt_trick (r := (2 : ℝ)⁻¹) (by norm_num) h0n (fun n => hf1 n _ _)
        (hGoodev.mono fun n hG => ?_)
      obtain ⟨-, -, -, h4⟩ := hαG n hG
      have hst := hsq n 0 (α n) n
      rw [max_eq_left h4] at hst
      exact hst
    refine tendsto_one_of_sqrt_trick (r := (2 : ℝ)⁻¹) (by norm_num) h0α (fun n => hf1 n _ _)
      (hGoodev.mono fun n hG => ?_)
    have hst := hsq n 0 (α n / 2 : ℕ) (α n)
    show 1 - (1 - f n 0 (α n)) ^ ((2 : ℝ)⁻¹) ≤ f n (a n) (b n)
    have hab : f n (a n) (b n) = max (f n 0 (α n / 2 : ℕ)) (f n ((α n / 2 : ℕ) + 1 : ℤ) (α n)) := by
      by_cases hc' : cond n
      · have ha' : a n = 0 := by simp only [ha, if_pos hG, if_pos hc']
        have hb' : b n = α n / 2 := by simp only [hb, if_pos hG, if_pos hc']
        rw [ha', hb', max_eq_left hc']
        push_cast
        rfl
      · have ha' : a n = α n / 2 + 1 := by simp only [ha, if_pos hG, if_neg hc']
        have hb' : b n = α n := by simp only [hb, if_pos hG, if_neg hc']
        rw [ha', hb', max_eq_right (le_of_not_ge hc')]
        push_cast
        rfl
    rw [hab]
    exact hst

end Lemma4Final

end Percolation.Literature

end
