import Mathlib.Analysis.SpecificLimits.Basic
import Percolation.Literature.InequalitiesProofs
import Percolation.Literature.RSWLemma
import Percolation.Util.Linter

/-!
# Harris' theorem `θ(1/2) = 0` on `ℤ²`: proof of `harris_theta_half`

This file proves the statement
`Percolation.Literature.harris_theta_half : theta (zdGraph 2) 0 half = 0` (`BernoulliPercolation.lean`;
Harris, *Proc. Camb. Phil. Soc.* **56** (1960) 13–20, main theorem; Bollobás–Riordan,
*Percolation* (2006), Ch. 3, Thm. 6; Grimmett, *Percolation* (1999), §11.3, Lemma (11.12)) as
`harris_theta_half_holds`, by reducing it (`harris_theta_half_of_rsw_lowerBound`) to the
Russo–Seymour–Welsh lower bound `Percolation.Literature.rsw_lowerBound` of `RSW.lean`, which is proved
in `RSWLemma.lean` (`rsw_lowerBound_holds`, from Bollobás–Riordan 2006, Ch. 3, Lemma 4 and
Cor. 5, the RSW step proper). Everything in this file is proved.

## The printed proof (Bollobás–Riordan 2006, Ch. 3, §3.2, Thm. 6)

(Bollobás–Riordan 2006, pp. 55–56.)

"At `p = 1/2`, the bonds of the dual lattice `Λ*` are open independently with probability `1/2`,
so, from (4), the probability that a `6n` by `2n` rectangle in `Λ*` has an open crossing is at
least `2⁻²⁵`. Consider two `6n` by `2n` and two `2n` by `6n` rectangles in `Λ*`, arranged to form a
'square annulus' as in Figure 8. By Harris's Lemma, with probability at least `ε = 2⁻¹⁰⁰ > 0` each
rectangle is crossed the long way by an open (dual) path. If this happens, then the union of these
paths contains an open dual cycle surrounding the centre of the annulus ... For `k ≥ 1`, let `A_k`
be the square annulus centred on the origin made up of two `3 × 4^k` by `4^k` and two `4^k` by
`3 × 4^k` dual rectangles ..., and let `E_k` be the event that `A_k` contains an open dual cycle
surrounding the interior of `A_k`, and hence the origin. Then `P(E_k) ≥ ε` for every `k`. As the
`A_k` are disjoint, the events `E_k` are independent. If `E_k` holds, then no point inside `A_k`
can be joined to a point outside `A_k` by an open path in `ℤ²`, so `r(C_0) < 4^{k+1}`. Thus
`P_{1/2}(r(C_0) ≥ 4^{ℓ+1}) ≤ P_{1/2}(⋂_{k=1}^{ℓ} E_kᶜ) = ∏_{k=1}^{ℓ} P_{1/2}(E_kᶜ) ≤ (1 - ε)^ℓ`
... so `θ(1/2) = 0`."

## The formalisation (purely primal bookkeeping of the same argument)

By the rectangle duality lemma (Bollobás–Riordan 2006, Ch. 3, Lemma 1; here
`Percolation.Literature.lrCrossing_xor_dualTBCrossing_holds`), "the dual rectangle is crossed the long way by
an open dual path" is, configuration by configuration, the same event as "the primal rectangle it
is dual to is *not* crossed the short way by an open path". We therefore work with the four
primal rectangles `T_n = [-3n, 3n] × [n, 3n]`, `B_n = [-3n, 3n] × [-3n, -n]`,
`L_n = [-3n, -n] × [-3n, 3n]`, `R_n = [n, 3n] × [-3n, 3n]` (translates of `rectangle (6n) (2n)`
and `rectangle (2n) (6n)`), whose union is the square annulus `{n ≤ ‖z‖_∞ ≤ 3n}`, and with the
decreasing event `annulusBlocked n` that none of them has an open crossing the short way
(`T_n`, `B_n` top–bottom; `L_n`, `R_n` left–right). This is Bollobás–Riordan's `E_k` up to the
exact dimensions of the four rectangles (ours overlap at the corners of the annulus, which the
argument allows), and the dual lattice never has to be mentioned:

* `openConnIn_box_of_annulusBlocked` (deterministic; "no point inside `A_k` can be joined to a
  point outside `A_k` by an open path"): if `annulusBlocked n` holds (`n ≥ 1`, lattice
  configuration), every open path from `B(n)` stays inside the open box `(-3n, 3n)²`. Proof: stop
  the path when it first reaches `‖z‖_∞ = 3n`, say on the top side; after its last visit to the
  row `{z₁ = n}` the stopped path is a bottom–top open crossing of `T_n` (`exists_openConnIn_exit`,
  the first-exit edge of an open path from a set of vertices).
* `pow_four_le_real_annulusBlocked`, `rsw_lowerBound.le_one_sub_crossingProb`
  (probability): each of the four crossing events has probability `crossingProb p (2n) (6n)`
  (translation invariance and transposition symmetry of `P_p`, `LatticeSymmetry.lean`;
  `real_topShortCrossing` etc.), so by Harris's Lemma for the four decreasing complements
  (`harris_fkg_lower`) `P_p(annulusBlocked n) ≥ (1 - crossingProb p (2n) (6n))⁴`; at `p = 1/2`,
  `1 - crossingProb ½ (2n) (6n) = crossingProb ½ (6n + 1) (2n - 1)` (duality of crossing
  probabilities, Bollobás–Riordan Cor. 3(i), `crossingProb_add_crossingProb_symm_holds`) is at
  least the RSW constant `h₄` of `rsw_lowerBound` (Bollobás–Riordan eq. (3), `k = 4`, and
  antitonicity in the width), whence `P_{1/2}(annulusBlocked n) ≥ h₄⁴ =: ε` for all `n ≥ 1`.
* `real_iInter_compl_annulusBlocked` (independence): `annulusBlocked n` is determined by the
  pairs of sites of the annulus `box 2 (3n) \ box 2 (n - 1) = {n ≤ ‖z‖_∞ ≤ 3n}`
  (`determinedBy_annulusBlocked`), and these are pairwise disjoint along the scales `4^(k+1)`
  (`disjoint_sym2_box_sym2_annulus`), so
  `P(⋂_{k<K} (annulusBlocked (4^(k+1)))ᶜ) = ∏_{k<K} (1 - P(annulusBlocked (4^(k+1))))`
  (`bondPercolation_real_inter_of_disjoint`, `FiniteEnergy.lean`, inductively).

`harris_theta_half_holds : harris_theta_half` is then `harris_theta_half_of_rsw_lowerBound` fed with
the proved RSW bound `rsw_lowerBound_holds` of `RSWLemma.lean` (Bollobás–Riordan 2006, Ch. 3,
Lemma 4 and Cor. 5, eq. (3)).

Harris' own proof (1960) is organised differently (Bollobás–Riordan 2006, p. 56: "Although
Harris's proof is very different from that presented here, a key step is similar to a step in the
proof of Lemma 4"); the statement proved is the one printed in all three sources.

Mathlib anchors: `SimpleGraph.Walk` induction, `SimpleGraph.induceUnivIso`, `Finset.sym2`,
`MeasureTheory.measure_mono_ae`, `MeasureTheory.probReal_compl_eq_one_sub`,
`tendsto_pow_atTop_nhds_zero_of_lt_one`; tree anchors as listed above.

## References
* B. Bollobás, O. Riordan, *Percolation*, Cambridge University Press (2006), Ch. 3: Lemma 1,
  Corollary 3, eq. (3)–(4), §3.2 Theorem 6 [BollobasRiordanPercolation2006].
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Cambridge Philos. Soc. 56 (1960) 13–20 [HarrisPCPS1960].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §11.3, Lemma (11.12), and §11.7
  [GrimmettPercolation1999].
-/

namespace Percolation.Literature

open MeasureTheory SimpleGraph

noncomputable section

/-! ### The first exit of an open path from a set of vertices -/

section Exit

variable {V : Type*}

/-- **First-exit edge of an open path.** If `x ∈ T`, `y ∉ T` and `x` is joined to `y` by an open
path inside `S`, then there is an open edge `{u, w}` with `u ∈ T`, `w ∈ S \ T`, such that `x` is
joined to `u` by an open path inside `S ∩ T` (follow the path up to its first vertex outside
`T`). (Kesten 1982, §2.2, first/last intersections of paths with sets; used implicitly in
Bollobás–Riordan 2006, Ch. 3, proof of Thm. 6: a path from inside the annulus to outside must
cross it.) [folklore] -/
theorem exists_openConnIn_exit {ω : BondConfig V} {S T : Set V} {x y : V} (hx : x ∈ T)
    (hy : y ∉ T) (h : ω ∈ openConnIn S x y) :
    ∃ u w, u ∈ T ∧ w ∉ T ∧ w ∈ S ∧ s(u, w) ∈ ω ∧ u ≠ w ∧ ω ∈ openConnIn (S ∩ T) x u := by
  obtain ⟨hxS, hyS, ⟨p⟩⟩ := h
  suffices H : ∀ (a b : S) (p : ((openGraph ω).induce S).Walk a b), (a : V) ∈ T → (b : V) ∉ T →
      ∃ u w, u ∈ T ∧ w ∉ T ∧ w ∈ S ∧ s(u, w) ∈ ω ∧ u ≠ w ∧ ω ∈ openConnIn (S ∩ T) a u from
    H ⟨x, hxS⟩ ⟨y, hyS⟩ p hx hy
  intro a b p
  induction p with
  | nil => intro ha hb; exact absurd ha hb
  | cons hadj p ih =>
    intro ha hb
    rename_i a c b'
    have hadj' : (openGraph ω).Adj a c := hadj
    obtain ⟨hmem, hne⟩ := (openGraph_adj _ _ _).1 hadj'
    by_cases hc : (c : V) ∈ T
    · obtain ⟨u, w, hu, hw, hwS, huw, hne', hr⟩ := ih hc hb
      exact ⟨u, w, hu, hw, hwS, huw, hne',
        PlanarDuality.openConnIn_trans (openConnIn_of_adj ⟨a.2, ha⟩ ⟨c.2, hc⟩ hmem hne) hr⟩
    · exact ⟨a, c, ha, hc, c.2, hmem, hne, openConnIn_refl ⟨a.2, ha⟩⟩

/-- Reachability in the open graph is an open connection inside `Set.univ`. [folklore] -/
theorem openConnIn_univ_of_reachable {ω : BondConfig V} {x y : V}
    (h : (openGraph ω).Reachable x y) :
    ω ∈ openConnIn Set.univ x y :=
  ⟨trivial, trivial, h.map (induceUnivIso (openGraph ω)).symm.toHom⟩

end Exit

/-! ### The square annulus `{n ≤ ‖z‖_∞ ≤ 3n}` as four rectangles -/

/-- Lower-left corner `(-3n, n)` of the top rectangle `T_n = [-3n, 3n] × [n, 3n]`. [folklore] -/
def topCorner (n : ℕ) : LatticeModels.Site 2 := ![-(3 * n : ℤ), n]

/-- Lower-left corner `(-3n, -3n)` of the bottom rectangle `B_n = [-3n, 3n] × [-3n, -n]` and of
the left rectangle `L_n = [-3n, -n] × [-3n, 3n]`. [folklore] -/
def bottomCorner (n : ℕ) : LatticeModels.Site 2 := ![-(3 * n : ℤ), -(3 * n : ℤ)]

/-- Lower-left corner `(n, -3n)` of the right rectangle `R_n = [n, 3n] × [-3n, 3n]`. [folklore] -/
def rightCorner (n : ℕ) : LatticeModels.Site 2 := ![(n : ℤ), -(3 * n : ℤ)]

/-- First coordinate of `topCorner`. [folklore] -/
@[simp] theorem topCorner_apply_zero (n : ℕ) : topCorner n 0 = -(3 * n : ℤ) := rfl

/-- Second coordinate of `topCorner`. [folklore] -/
@[simp] theorem topCorner_apply_one (n : ℕ) : topCorner n 1 = n := rfl

/-- First coordinate of `bottomCorner`. [folklore] -/
@[simp] theorem bottomCorner_apply_zero (n : ℕ) : bottomCorner n 0 = -(3 * n : ℤ) := rfl

/-- Second coordinate of `bottomCorner`. [folklore] -/
@[simp] theorem bottomCorner_apply_one (n : ℕ) : bottomCorner n 1 = -(3 * n : ℤ) := rfl

/-- First coordinate of `rightCorner`. [folklore] -/
@[simp] theorem rightCorner_apply_zero (n : ℕ) : rightCorner n 0 = n := rfl

/-- Second coordinate of `rightCorner`. [folklore] -/
@[simp] theorem rightCorner_apply_one (n : ℕ) : rightCorner n 1 = -(3 * n : ℤ) := rfl

/-- The event that the top rectangle `T_n = [-3n, 3n] × [n, 3n]` of the square annulus
`{n ≤ ‖z‖_∞ ≤ 3n}` has an open **top–bottom** (short-way) crossing; a translate of
`tbCrossing (6n) (2n)`. By rectangle duality (Bollobás–Riordan 2006, Ch. 3, Lemma 1) its
complement is the event that the dual rectangle `T_nᵛ` is crossed the long way by an open dual
path, one of the four events of Bollobás–Riordan's Figure 8. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6 (Figure 8)] -/
def topShortCrossing (n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing ((· + topCorner n) '' ↑(rectangle (6 * n) (2 * n)))
    ((· + topCorner n) '' ↑(bottomSide (6 * n) (2 * n)))
    ((· + topCorner n) '' ↑(topSide (6 * n) (2 * n)))

/-- The event that the bottom rectangle `B_n = [-3n, 3n] × [-3n, -n]` has an open top–bottom
(short-way) crossing. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6 (Figure 8)] -/
def bottomShortCrossing (n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing ((· + bottomCorner n) '' ↑(rectangle (6 * n) (2 * n)))
    ((· + bottomCorner n) '' ↑(bottomSide (6 * n) (2 * n)))
    ((· + bottomCorner n) '' ↑(topSide (6 * n) (2 * n)))

/-- The event that the left rectangle `L_n = [-3n, -n] × [-3n, 3n]` has an open left–right
(short-way) crossing. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6 (Figure 8)] -/
def leftShortCrossing (n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing ((· + bottomCorner n) '' ↑(rectangle (2 * n) (6 * n)))
    ((· + bottomCorner n) '' ↑(leftSide (2 * n) (6 * n)))
    ((· + bottomCorner n) '' ↑(rightSide (2 * n) (6 * n)))

/-- The event that the right rectangle `R_n = [n, 3n] × [-3n, 3n]` has an open left–right
(short-way) crossing. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6 (Figure 8)] -/
def rightShortCrossing (n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  openCrossing ((· + rightCorner n) '' ↑(rectangle (2 * n) (6 * n)))
    ((· + rightCorner n) '' ↑(leftSide (2 * n) (6 * n)))
    ((· + rightCorner n) '' ↑(rightSide (2 * n) (6 * n)))

/-- **The annulus is blocked** (Bollobás–Riordan 2006, Ch. 3, proof of Thm. 6, the event `E_k`
in primal form): none of the four rectangles forming the square annulus `{n ≤ ‖z‖_∞ ≤ 3n}` has
an open crossing the short way. By rectangle duality (Ch. 3, Lemma 1) this says that each of the
four dual rectangles is crossed the long way by an open dual path, whence "the union of these
paths contains an open dual cycle surrounding the centre of the annulus". A decreasing event. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6 (event E_k)] -/
def annulusBlocked (n : ℕ) : Set (BondConfig (LatticeModels.Site 2)) :=
  (topShortCrossing n)ᶜ ∩ (bottomShortCrossing n)ᶜ ∩ (leftShortCrossing n)ᶜ ∩
    (rightShortCrossing n)ᶜ

/-! ### Deterministic step: a blocked annulus confines open paths from its inside -/

/-- The first vertex of an open path from `B(n)` (or from anywhere in the open box `(-3n, 3n)²`)
outside the open box `(-3n, 3n)²` lies on the boundary of `B(3n)`, and the path up to it runs
inside `B(3n)` (the exit step of the printed proof: "no point inside `A_k` can be joined to a point
outside `A_k` by an open path" without crossing the annulus).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (exit step)] -/
theorem exists_exit_box {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) {n : ℕ}
    {x y : LatticeModels.Site 2} (hx : ∀ i, -(3 * n : ℤ) < x i ∧ x i < 3 * n)
    (hy : ¬ ∀ i, -(3 * n : ℤ) < y i ∧ y i < 3 * n) (h : ω ∈ openConnIn Set.univ x y) :
    ∃ w : LatticeModels.Site 2, (w 0 = 3 * n ∨ w 0 = -(3 * n : ℤ) ∨ w 1 = 3 * n ∨ w 1 = -(3 * n : ℤ)) ∧
      ω ∈ openConnIn (↑(LatticeModels.box 2 (3 * n))) x w := by
  obtain ⟨u, w, hu, hw, -, huw, hne, hr⟩ :=
    exists_openConnIn_exit (T := {z : LatticeModels.Site 2 | ∀ i, -(3 * n : ℤ) < z i ∧ z i < 3 * n}) hx hy h
  have hadj : (LatticeModels.zdGraph 2).Adj u w := by
    have := hω huw
    rwa [SimpleGraph.mem_edgeSet] at this
  simp only [Set.mem_setOf_eq, Fin.forall_fin_two, not_and_or, not_lt] at hu hw
  rw [zdGraph_two_adj_iff] at hadj
  have hwbox : w ∈ (↑(LatticeModels.box 2 (3 * n)) : Set (LatticeModels.Site 2)) := by
    rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two]
    omega
  refine ⟨w, by omega, ?_⟩
  have hsub : (Set.univ ∩ {z : LatticeModels.Site 2 | ∀ i, -(3 * n : ℤ) < z i ∧ z i < 3 * n}) ⊆
      (↑(LatticeModels.box 2 (3 * n)) : Set (LatticeModels.Site 2)) := by
    intro z hz
    rw [Finset.mem_coe, LatticeModels.mem_box]
    exact fun i => ⟨(hz.2 i).1.le, (hz.2 i).2.le⟩
  have hubox : u ∈ (↑(LatticeModels.box 2 (3 * n)) : Set (LatticeModels.Site 2)) := by
    rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two]
    omega
  exact PlanarDuality.openConnIn_trans (openConnIn_mono hsub x u hr) (openConnIn_of_adj hubox hwbox huw hne)

/-- One side of the annulus argument: if an open path inside `Box` runs from `w ∈ T` to `x ∉ T`,
where `Box ∩ T` is contained in the rectangle `Rect`, `w` lies on the side `A` of `Rect`, and
every lattice edge from `Box ∩ T` to `Box \ T` ends on the opposite side `B` of `Rect`, then
`Rect` has an open crossing from `A` to `B` (the path up to its first exit from `T`).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (Figure 8: a path leaving the inside of the annulus crosses one of its four rectangles)] -/
theorem openCrossing_of_exit {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet)
    {Box T Rect A B : Set (LatticeModels.Site 2)} {w x : LatticeModels.Site 2} (hw : w ∈ T) (hx : x ∉ T)
    (hr : ω ∈ openConnIn Box w x) (hsub : Box ∩ T ⊆ Rect) (hwA : w ∈ A)
    (hexit : ∀ a b, a ∈ Box → a ∈ T → b ∈ Box → b ∉ T → (LatticeModels.zdGraph 2).Adj a b → b ∈ Rect ∧ b ∈ B) :
    ω ∈ openCrossing Rect A B := by
  obtain ⟨a, b, ha, hb, hbBox, hab, hne, hr2⟩ := exists_openConnIn_exit hw hx hr
  have hadj : (LatticeModels.zdGraph 2).Adj a b := by
    have := hω hab
    rwa [SimpleGraph.mem_edgeSet] at this
  have hr3 := hr2
  obtain ⟨-, ⟨haBox, haT⟩, -⟩ := hr3
  obtain ⟨hbRect, hbB⟩ := hexit a b haBox haT hbBox hb hadj
  exact ⟨w, hwA, b, hbB, PlanarDuality.openConnIn_trans (openConnIn_mono hsub w a hr2)
    (openConnIn_of_adj (hsub ⟨haBox, haT⟩) hbRect hab hne)⟩

/-- **A blocked annulus confines open paths** (Bollobás–Riordan 2006, Ch. 3, proof of Thm. 6:
"If `E_k` holds, then no point inside `A_k` can be joined to a point outside `A_k` by an open path
in `ℤ²`"). For a lattice configuration in `annulusBlocked n`, `n ≥ 1`, every open path starting
in `B(n)` stays in the open box `(-3n, 3n)²`. Proof: otherwise stop the path at its first vertex
`w` with `‖w‖_∞ = 3n` (`exists_exit_box`); if, say, `w₁ = 3n`, the part of the stopped path after
its last visit to the row `{z₁ = n}` is an open bottom–top crossing of `T_n = [-3n, 3n] × [n, 3n]`
(`openCrossing_of_exit`), contradicting `annulusBlocked n`; the other three sides are symmetric. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6] -/
theorem openConnIn_box_of_annulusBlocked {ω : BondConfig (LatticeModels.Site 2)} (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet)
    {n : ℕ} (hn : 1 ≤ n) (hB : ω ∈ annulusBlocked n) {x y : LatticeModels.Site 2} (hx : x ∈ LatticeModels.box 2 n)
    (h : ω ∈ openConnIn Set.univ x y) : ∀ i, -(3 * n : ℤ) < y i ∧ y i < 3 * n := by
  by_contra hy
  rw [LatticeModels.mem_box, Fin.forall_fin_two] at hx
  have hx' : ∀ i, -(3 * n : ℤ) < x i ∧ x i < 3 * n := by
    rw [Fin.forall_fin_two]; omega
  obtain ⟨w, hw, hr⟩ := exists_exit_box hω hx' hy h
  have hr' := hr
  obtain ⟨-, hwbox, -⟩ := hr'
  rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at hwbox
  rw [openConnIn_comm] at hr
  obtain ⟨⟨⟨hT, hBo⟩, hL⟩, hR⟩ := hB
  rcases hw with hw0 | hw0 | hw1 | hw1
  · -- right side: `w₀ = 3n`
    refine hR ?_
    unfold rightShortCrossing
    rw [openCrossing_comm]
    refine openCrossing_of_exit hω (T := {z : LatticeModels.Site 2 | (n : ℤ) < z 0})
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) hr ?_ ?_ ?_
    · rintro z ⟨hz, hzT⟩
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at hz
      simp only [Set.mem_setOf_eq] at hzT
      rw [mem_image_add_rectangle, rightCorner_apply_zero, rightCorner_apply_one]
      omega
    · rw [mem_image_add_rightSide, rightCorner_apply_zero, rightCorner_apply_one]
      omega
    · intro a b ha haT hb hbT hadj
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at ha hb
      simp only [Set.mem_setOf_eq, not_lt] at haT hbT
      rw [zdGraph_two_adj_iff] at hadj
      rw [mem_image_add_rectangle, mem_image_add_leftSide, rightCorner_apply_zero,
        rightCorner_apply_one]
      omega
  · -- left side: `w₀ = -3n`
    refine hL ?_
    unfold leftShortCrossing
    refine openCrossing_of_exit hω (T := {z : LatticeModels.Site 2 | z 0 < -(n : ℤ)})
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) hr ?_ ?_ ?_
    · rintro z ⟨hz, hzT⟩
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at hz
      simp only [Set.mem_setOf_eq] at hzT
      rw [mem_image_add_rectangle, bottomCorner_apply_zero, bottomCorner_apply_one]
      omega
    · rw [mem_image_add_leftSide, bottomCorner_apply_zero, bottomCorner_apply_one]
      omega
    · intro a b ha haT hb hbT hadj
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at ha hb
      simp only [Set.mem_setOf_eq, not_lt] at haT hbT
      rw [zdGraph_two_adj_iff] at hadj
      rw [mem_image_add_rectangle, mem_image_add_rightSide, bottomCorner_apply_zero,
        bottomCorner_apply_one]
      omega
  · -- top side: `w₁ = 3n`
    refine hT ?_
    unfold topShortCrossing
    rw [openCrossing_comm]
    refine openCrossing_of_exit hω (T := {z : LatticeModels.Site 2 | (n : ℤ) < z 1})
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) hr ?_ ?_ ?_
    · rintro z ⟨hz, hzT⟩
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at hz
      simp only [Set.mem_setOf_eq] at hzT
      rw [mem_image_add_rectangle, topCorner_apply_zero, topCorner_apply_one]
      omega
    · rw [mem_image_add_topSide, topCorner_apply_zero, topCorner_apply_one]
      omega
    · intro a b ha haT hb hbT hadj
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at ha hb
      simp only [Set.mem_setOf_eq, not_lt] at haT hbT
      rw [zdGraph_two_adj_iff] at hadj
      rw [mem_image_add_rectangle, mem_image_add_bottomSide, topCorner_apply_zero,
        topCorner_apply_one]
      omega
  · -- bottom side: `w₁ = -3n`
    refine hBo ?_
    unfold bottomShortCrossing
    refine openCrossing_of_exit hω (T := {z : LatticeModels.Site 2 | z 1 < -(n : ℤ)})
      (by simp only [Set.mem_setOf_eq]; omega) (by simp only [Set.mem_setOf_eq]; omega) hr ?_ ?_ ?_
    · rintro z ⟨hz, hzT⟩
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at hz
      simp only [Set.mem_setOf_eq] at hzT
      rw [mem_image_add_rectangle, bottomCorner_apply_zero, bottomCorner_apply_one]
      omega
    · rw [mem_image_add_bottomSide, bottomCorner_apply_zero, bottomCorner_apply_one]
      omega
    · intro a b ha haT hb hbT hadj
      rw [Finset.mem_coe, LatticeModels.mem_box, Fin.forall_fin_two] at ha hb
      simp only [Set.mem_setOf_eq, not_lt] at haT hbT
      rw [zdGraph_two_adj_iff] at hadj
      rw [mem_image_add_rectangle, mem_image_add_topSide, bottomCorner_apply_zero,
        bottomCorner_apply_one]
      omega

/-- **Consequence for the cluster of the origin** (Bollobás–Riordan 2006, Ch. 3, proof of Thm. 6:
"so `r(C_0) < 4^{k+1}`"): for a lattice configuration in `annulusBlocked n`, `n ≥ 1`, the open
cluster of the origin lies in the box `B(3n)`; in particular it is finite. [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6] -/
theorem openCluster_subset_box_of_annulusBlocked {ω : BondConfig (LatticeModels.Site 2)}
    (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) {n : ℕ} (hn : 1 ≤ n) (hB : ω ∈ annulusBlocked n) :
    openCluster ω 0 ⊆ ↑(LatticeModels.box 2 (3 * n)) := by
  intro y hy
  have h0 : (0 : LatticeModels.Site 2) ∈ LatticeModels.box 2 n := by simp [LatticeModels.mem_box]
  have := openConnIn_box_of_annulusBlocked hω hn hB h0 (openConnIn_univ_of_reachable hy)
  rw [Finset.mem_coe, LatticeModels.mem_box]
  exact fun i => ⟨(this i).1.le, (this i).2.le⟩

/-- A blocked annulus at any scale `n ≥ 1` makes the open cluster of the origin finite (lattice
configurations). (Bollobás–Riordan 2006, Ch. 3, proof of Thm. 6.) [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6] -/
theorem not_mem_percolatesAt_of_annulusBlocked {ω : BondConfig (LatticeModels.Site 2)}
    (hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet) {n : ℕ} (hn : 1 ≤ n) (hB : ω ∈ annulusBlocked n) :
    ω ∉ percolatesAt (0 : LatticeModels.Site 2) := fun h =>
  h ((LatticeModels.box 2 (3 * n)).finite_toSet.subset (openCluster_subset_box_of_annulusBlocked hω hn hB))

/-! ### Locality and measurability of the annulus events -/

/-- Open crossing events of translated finite regions are measurable (locality of the annulus events in
the printed proof: "As the `A_k` are disjoint, the events `E_k` are independent").
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (locality of the events E_k)] -/
theorem measurableSet_openCrossing_image (F : Finset (LatticeModels.Site 2)) (v : LatticeModels.Site 2) (A B : Set (LatticeModels.Site 2)) :
    MeasurableSet (openCrossing ((· + v) '' (↑F : Set (LatticeModels.Site 2))) A B) := by
  rw [← Finset.coe_image]
  exact measurableSet_openCrossing _ _ _

/-- Open crossing events of translated finite regions depend only on the pairs of sites of the
translated region (locality of the annulus events: "As the `A_k` are disjoint, the events `E_k` are
independent"). [cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (locality of the events E_k)] -/
theorem determinedBy_openCrossing_image (F : Finset (LatticeModels.Site 2)) (v : LatticeModels.Site 2) (A B : Set (LatticeModels.Site 2)) :
    DeterminedBy (openCrossing ((· + v) '' (↑F : Set (LatticeModels.Site 2))) A B) ↑(F.image (· + v)).sym2 := by
  rw [← Finset.coe_image]
  exact PlanarDuality.determinedBy_openCrossing _ _ _

/-- `annulusBlocked n` is measurable. [folklore] -/
theorem measurableSet_annulusBlocked (n : ℕ) : MeasurableSet (annulusBlocked n) :=
  ((((measurableSet_openCrossing_image _ _ _ _).compl.inter
    (measurableSet_openCrossing_image _ _ _ _).compl).inter
    (measurableSet_openCrossing_image _ _ _ _).compl).inter
    (measurableSet_openCrossing_image _ _ _ _).compl)

/-- The complement of the open crossing event of a translated rectangle lying in the annulus
`A = box(3n) \ box(n - 1) = {n ≤ ‖z‖_∞ ≤ 3n}` depends only on the pairs of sites of `A` (locality of the
annulus events `E_k`). [cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (locality of the events E_k)] -/
theorem determinedBy_compl_openCrossing_image_of_subset {n : ℕ} {F : Finset (LatticeModels.Site 2)} {v : LatticeModels.Site 2}
    (A B : Set (LatticeModels.Site 2)) (hF : ∀ z ∈ F, z + v ∈ LatticeModels.annulus 2 (n - 1) (3 * n)) :
    DeterminedBy (openCrossing ((· + v) '' (↑F : Set (LatticeModels.Site 2))) A B)ᶜ
      ↑((LatticeModels.annulus 2 (n - 1) (3 * n)).sym2) := by
  have hsub : (↑(F.image (· + v)).sym2 : Set (Sym2 (LatticeModels.Site 2))) ⊆
      ↑((LatticeModels.annulus 2 (n - 1) (3 * n)).sym2) := by
    refine Finset.coe_subset.2 (Finset.sym2_mono fun z hz => ?_)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
    exact hF w hw
  have h := (determinedBy_openCrossing_image F v A B).mono hsub
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  rw [Set.mem_compl_iff, Set.mem_compl_iff, h ω ω' hω]

/-- **`annulusBlocked n` depends only on the bonds of the annulus** `{n ≤ ‖z‖_∞ ≤ 3n}`
(`= box 2 (3n) \ box 2 (n - 1)`), `n ≥ 1`: the four rectangles lie in it. (Bollobás–Riordan
2006, Ch. 3, proof of Thm. 6: "As the `A_k` are disjoint, the events `E_k` are independent.") [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6] -/
theorem determinedBy_annulusBlocked {n : ℕ} (hn : 1 ≤ n) :
    DeterminedBy (annulusBlocked n) ↑((LatticeModels.annulus 2 (n - 1) (3 * n)).sym2) := by
  unfold annulusBlocked topShortCrossing bottomShortCrossing leftShortCrossing rightShortCrossing
  refine (((determinedBy_compl_openCrossing_image_of_subset _ _ ?_).inter
    (determinedBy_compl_openCrossing_image_of_subset _ _ ?_)).inter
    (determinedBy_compl_openCrossing_image_of_subset _ _ ?_)).inter
    (determinedBy_compl_openCrossing_image_of_subset _ _ ?_)
  all_goals
    intro z hz
    rw [mem_rectangle_iff] at hz
    simp only [LatticeModels.mem_annulus, LatticeModels.mem_box, Fin.forall_fin_two, Pi.add_apply, topCorner_apply_zero,
      topCorner_apply_one, bottomCorner_apply_zero, bottomCorner_apply_one,
      rightCorner_apply_zero, rightCorner_apply_one]
    omega

/-- The complement of `annulusBlocked n` depends only on the bonds of the annulus ("As the `A_k` are
disjoint, the events `E_k` are independent").
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (locality of the events E_k)] -/
theorem determinedBy_compl_annulusBlocked {n : ℕ} (hn : 1 ≤ n) :
    DeterminedBy (annulusBlocked n)ᶜ ↑((LatticeModels.annulus 2 (n - 1) (3 * n)).sym2) := by
  have h := determinedBy_annulusBlocked hn
  rw [determinedBy_iff] at h ⊢
  intro ω ω' hω
  rw [Set.mem_compl_iff, Set.mem_compl_iff, h ω ω' hω]

/-- Pairs of sites of `box 2 m` and pairs of sites of the annulus `box 2 (3n) \ box 2 (n - 1)`
are disjoint when `m < n` ("As the `A_k` are disjoint, the events `E_k` are independent": the bond sets
of the nested annuli `A_k`, `k < K`, and of `A_K` are disjoint).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (disjointness of the annuli A_k)] -/
theorem disjoint_sym2_box_sym2_annulus {m n : ℕ} (h : m < n) :
    Disjoint (↑((LatticeModels.box 2 m).sym2) : Set (Sym2 (LatticeModels.Site 2))) ↑((LatticeModels.annulus 2 (n - 1) (3 * n)).sym2) := by
  rw [Finset.disjoint_coe, Finset.disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | h x y =>
    rw [Finset.mk_mem_sym2_iff] at he he'
    obtain ⟨hx, -⟩ := he
    obtain ⟨hx', -⟩ := he'
    rw [LatticeModels.mem_annulus] at hx'
    refine hx'.2 ?_
    rw [LatticeModels.mem_box] at hx ⊢
    intro i
    have := hx i
    omega

/-- The events `(annulusBlocked (4^(k+1)))ᶜ`, `k < K`, together depend only on the pairs of
sites of `box 2 (3 · 4^K)` (locality behind "the events `E_k` are independent", used for
`P(⋂_{k ≤ ℓ} E_kᶜ) = ∏ P(E_kᶜ)`). [cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (independence of the E_k)] -/
theorem determinedBy_iInter_compl_annulusBlocked (K : ℕ) :
    DeterminedBy (⋂ k ∈ Finset.range K, (annulusBlocked (4 ^ (k + 1)))ᶜ)
      ↑((LatticeModels.box 2 (3 * 4 ^ K)).sym2) := by
  induction K with
  | zero => simpa using determinedBy_univ _
  | succ K ih =>
    rw [Finset.range_add_one, Finset.set_biInter_insert]
    refine DeterminedBy.inter
      ((determinedBy_compl_annulusBlocked (Nat.one_le_pow _ _ (by norm_num))).mono ?_) (ih.mono ?_)
    · refine Finset.coe_subset.2 (Finset.sym2_mono fun z hz => (LatticeModels.mem_annulus.1 hz).1)
    · refine Finset.coe_subset.2 (Finset.sym2_mono fun z hz => ?_)
      rw [LatticeModels.mem_box] at hz ⊢
      intro i
      have := hz i
      have h4 : (4 : ℤ) ^ K ≤ 4 ^ (K + 1) := by
        rw [pow_succ]; have := pow_pos (show (0 : ℤ) < 4 by norm_num) K; nlinarith
      push_cast at this ⊢
      constructor <;> nlinarith

/-- The events `(annulusBlocked (4^(k+1)))ᶜ`, `k < K`, form a measurable event. [folklore] -/
theorem measurableSet_iInter_compl_annulusBlocked (K : ℕ) :
    MeasurableSet (⋂ k ∈ Finset.range K, (annulusBlocked (4 ^ (k + 1)))ᶜ) :=
  Finset.measurableSet_biInter _ fun k _ => (measurableSet_annulusBlocked (4 ^ (k + 1))).compl

/-! ### Probabilities of the four crossing events -/

/-- `P_p(T_n is crossed top–bottom) = crossingProb p (2n) (6n)` (translation invariance and
transposition symmetry of `P_p`: each of the four `6n` by `2n` / `2n` by `6n` rectangles of the square
annulus is crossed the long way with probability `h(6n, 2n)`).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (the four rectangles of Figure 8)] -/
theorem real_topShortCrossing (p : unitInterval) (n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (topShortCrossing n) = crossingProb p (2 * n) (6 * n) := by
  rw [topShortCrossing, real_openCrossing_shift, ← tbCrossing, real_tbCrossing]

/-- `P_p(B_n is crossed top–bottom) = crossingProb p (2n) (6n)` (the bottom rectangle of the square
annulus, by translation invariance and transposition symmetry).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (the four rectangles of Figure 8)] -/
theorem real_bottomShortCrossing (p : unitInterval) (n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (bottomShortCrossing n) =
      crossingProb p (2 * n) (6 * n) := by
  rw [bottomShortCrossing, real_openCrossing_shift, ← tbCrossing, real_tbCrossing]

/-- `P_p(L_n is crossed left–right) = crossingProb p (2n) (6n)` (the left rectangle of the square
annulus, by translation invariance).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (the four rectangles of Figure 8)] -/
theorem real_leftShortCrossing (p : unitInterval) (n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (leftShortCrossing n) =
      crossingProb p (2 * n) (6 * n) := by
  rw [leftShortCrossing, real_openCrossing_shift]
  rfl

/-- `P_p(R_n is crossed left–right) = crossingProb p (2n) (6n)` (the right rectangle of the square
annulus, by translation invariance).
[cite: BollobasRiordanPercolation2006, Ch. 3 §3.2, proof of Thm. 6 (the four rectangles of Figure 8)] -/
theorem real_rightShortCrossing (p : unitInterval) (n : ℕ) :
    (bondPercolation (LatticeModels.zdGraph 2) p).real (rightShortCrossing n) =
      crossingProb p (2 * n) (6 * n) := by
  rw [rightShortCrossing, real_openCrossing_shift]
  rfl

end

end Percolation.Literature

namespace Percolation.Literature

open MeasureTheory Filter LatticeModels PlanarDuality
open scoped Topology

noncomputable section

/-! ### Harris's Lemma: a blocked annulus has probability at least `(1 - h)^4` -/

/-- **Harris's Lemma applied to the four rectangles** (Bollobás–Riordan 2006, Ch. 3, proof of
Thm. 6: "By Harris's Lemma, with probability at least `ε = 2⁻¹⁰⁰ > 0` each rectangle is crossed
the long way by an open path"; in primal form): the four events "no short-way open crossing" are
decreasing, each of probability `1 - crossingProb p (2n) (6n)`, so
`P_p(annulusBlocked n) ≥ (1 - crossingProb p (2n) (6n))⁴` (`harris_fkg_lower`, three times). [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6] -/
theorem pow_four_le_real_annulusBlocked (p : unitInterval) (n : ℕ) :
    (1 - crossingProb p (2 * n) (6 * n)) ^ 4 ≤
      (bondPercolation (zdGraph 2) p).real (annulusBlocked n) := by
  set μ := bondPercolation (zdGraph 2) p with hμ
  have mT : MeasurableSet (topShortCrossing n) := measurableSet_openCrossing_image _ _ _ _
  have mB : MeasurableSet (bottomShortCrossing n) := measurableSet_openCrossing_image _ _ _ _
  have mL : MeasurableSet (leftShortCrossing n) := measurableSet_openCrossing_image _ _ _ _
  have mR : MeasurableSet (rightShortCrossing n) := measurableSet_openCrossing_image _ _ _ _
  have hT : μ.real (topShortCrossing n)ᶜ = 1 - crossingProb p (2 * n) (6 * n) := by
    rw [probReal_compl_eq_one_sub mT, real_topShortCrossing]
  have hB : μ.real (bottomShortCrossing n)ᶜ = 1 - crossingProb p (2 * n) (6 * n) := by
    rw [probReal_compl_eq_one_sub mB, real_bottomShortCrossing]
  have hL : μ.real (leftShortCrossing n)ᶜ = 1 - crossingProb p (2 * n) (6 * n) := by
    rw [probReal_compl_eq_one_sub mL, real_leftShortCrossing]
  have hR : μ.real (rightShortCrossing n)ᶜ = 1 - crossingProb p (2 * n) (6 * n) := by
    rw [probReal_compl_eq_one_sub mR, real_rightShortCrossing]
  have lT : IsLowerSet (topShortCrossing n)ᶜ := (isUpperSet_openCrossing _ _ _).compl
  have lB : IsLowerSet (bottomShortCrossing n)ᶜ := (isUpperSet_openCrossing _ _ _).compl
  have lL : IsLowerSet (leftShortCrossing n)ᶜ := (isUpperSet_openCrossing _ _ _).compl
  have lR : IsLowerSet (rightShortCrossing n)ᶜ := (isUpperSet_openCrossing _ _ _).compl
  have h1 := harris_fkg_lower (zdGraph 2) p lT lB mT.compl mB.compl
  have h2 := harris_fkg_lower (zdGraph 2) p (lT.inter lB) lL (mT.compl.inter mB.compl) mL.compl
  have h3 := harris_fkg_lower (zdGraph 2) p ((lT.inter lB).inter lL) lR
    ((mT.compl.inter mB.compl).inter mL.compl) mR.compl
  calc (1 - crossingProb p (2 * n) (6 * n)) ^ 4
      = μ.real (topShortCrossing n)ᶜ * μ.real (bottomShortCrossing n)ᶜ *
          μ.real (leftShortCrossing n)ᶜ * μ.real (rightShortCrossing n)ᶜ := by
        rw [hT, hB, hL, hR]; ring
    _ ≤ μ.real ((topShortCrossing n)ᶜ ∩ (bottomShortCrossing n)ᶜ) *
          μ.real (leftShortCrossing n)ᶜ * μ.real (rightShortCrossing n)ᶜ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 measureReal_nonneg)
          measureReal_nonneg
    _ ≤ μ.real ((topShortCrossing n)ᶜ ∩ (bottomShortCrossing n)ᶜ ∩ (leftShortCrossing n)ᶜ) *
          μ.real (rightShortCrossing n)ᶜ :=
        mul_le_mul_of_nonneg_right h2 measureReal_nonneg
    _ ≤ μ.real (annulusBlocked n) := h3

/-! ### Independence of the annuli -/

/-- **Independence of disjoint annuli** (Bollobás–Riordan 2006, Ch. 3, proof of Thm. 6: "As the
`A_k` are disjoint, the events `E_k` are independent ... `P(⋂ E_kᶜ) = ∏ P(E_kᶜ)`"): the events
`annulusBlocked (4^(k+1))`, `k < K`, are determined by the bonds of the pairwise disjoint annuli
`{4^(k+1) ≤ ‖z‖_∞ ≤ 3 · 4^(k+1)}`, so the probability that none of them occurs is the product
`∏_{k<K} (1 - P_p(annulusBlocked (4^(k+1))))` (`bondPercolation_real_inter_of_disjoint`,
inductively). [cite: BollobasRiordanPercolation2006, Ch. 3, proof of Thm. 6] -/
theorem real_iInter_compl_annulusBlocked (p : unitInterval) (K : ℕ) :
    (bondPercolation (zdGraph 2) p).real (⋂ k ∈ Finset.range K, (annulusBlocked (4 ^ (k + 1)))ᶜ) =
      ∏ k ∈ Finset.range K,
        (1 - (bondPercolation (zdGraph 2) p).real (annulusBlocked (4 ^ (k + 1)))) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.prod_range_succ, Finset.range_add_one, Finset.set_biInter_insert, ← ih,
      ← probReal_compl_eq_one_sub (measurableSet_annulusBlocked _), Set.inter_comm]
    have hlt : 3 * 4 ^ K < 4 ^ (K + 1) := by
      rw [pow_succ]; have := Nat.one_le_pow K 4 (by norm_num); omega
    exact bondPercolation_real_inter_of_disjoint (zdGraph 2) p (disjoint_sym2_box_sym2_annulus hlt)
      (determinedBy_iInter_compl_annulusBlocked K)
      (determinedBy_compl_annulusBlocked (Nat.one_le_pow _ _ (by norm_num)))
      (measurableSet_iInter_compl_annulusBlocked K) (measurableSet_annulusBlocked _).compl

/-! ### Conclusion -/

/-- The RSW input in the form used by Harris' theorem: at `p = 1/2` the probability that a
`6n` by `2n` rectangle (`6n + 1` by `2n + 1` sites) is *not* crossed the short way,
`1 - crossingProb ½ (2n) (6n) = crossingProb ½ (6n + 1) (2n - 1)` (duality,
`crossingProb_add_crossingProb_symm`, Bollobás–Riordan 2006, Ch. 3, Cor. 3(i)), is at least the
RSW constant `h₄` of `rsw_lowerBound` (Ch. 3, eq. (3) with `k = 4`: `h(8n, 2n) ≥ h₄` and
`h(6n + 2, 2n) ≥ h(8n, 2n)`), uniformly in `n ≥ 1`. (This is the role of eq. (4),
`h(m₁, 2n) ≥ 2⁻²⁵` for `m₁ ≤ 6n`, in the proof of Thm. 6.) [cite: BollobasRiordanPercolation2006, Ch. 3, eq. (3)–(4)] -/
theorem rsw_lowerBound.le_one_sub_crossingProb (hlow : rsw_lowerBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c ≤ 1 - crossingProb half (2 * n) (6 * n) := by
  obtain ⟨c, hc, hcn⟩ := hlow 4 (by norm_num)
  refine ⟨c, hc, fun n hn => ?_⟩
  have h := crossingProb_add_crossingProb_symm_holds half (2 * n - 1) (6 * n)
  rw [symm_half, Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] at h
  have h' : 1 - crossingProb half (2 * n) (6 * n) = crossingProb half (6 * n + 1) (2 * n - 1) := by
    linarith
  rw [h']
  exact (hcn (2 * n) (by omega)).trans (crossingProb_anti_left half (by omega) _)

/-- **Harris' theorem from a uniform bound on short-way crossings** (Harris 1960, main theorem;
Bollobás–Riordan, *Percolation* (2006), Ch. 3, Thm. 6; Grimmett 1999, §11.3, Lemma (11.12),
proved there after Zhang 1988 by a different argument): if, at `p = 1/2`, the `6n` by `2n`
rectangles fail to be crossed the short way with probability at least `c > 0` for all `n ≥ 1`
(the RSW input, Bollobás–Riordan eq. (4) in dual form), then `θ(1/2) = 0`. With `ε = c⁴ > 0`:
`P_{1/2}(annulusBlocked n) ≥ ε` for all `n ≥ 1` (`pow_four_le_real_annulusBlocked`); a
percolating lattice configuration lies in no `annulusBlocked (4^(k+1))`
(`not_mem_percolatesAt_of_annulusBlocked`), so
`θ(1/2) ≤ P(⋂_{k<K} (annulusBlocked (4^(k+1)))ᶜ) = ∏_{k<K} (1 - P(annulusBlocked (4^(k+1)))) ≤ (1 - ε)^K`
(`real_iInter_compl_annulusBlocked`) for every `K`, and `(1 - ε)^K → 0`. [cite: BollobasRiordanPercolation2006, Ch. 3, Thm. 6] [cite: HarrisPCPS1960, main theorem] -/
theorem harris_theta_half_of_le_one_sub_crossingProb {c : ℝ} (hc : 0 < c)
    (hcn : ∀ n : ℕ, 1 ≤ n → c ≤ 1 - crossingProb half (2 * n) (6 * n)) : harris_theta_half := by
  set μ := bondPercolation (zdGraph 2) half with hμ
  have hε : ∀ n, 1 ≤ n → c ^ 4 ≤ μ.real (annulusBlocked n) := fun n hn =>
    (pow_le_pow_left₀ hc.le (hcn n hn) 4).trans (pow_four_le_real_annulusBlocked half n)
  have hε1 : c ^ 4 ≤ 1 := (hε 1 le_rfl).trans measureReal_le_one
  have hε0 : 0 < c ^ 4 := pow_pos hc 4
  have hbound : ∀ K : ℕ, theta (zdGraph 2) (0 : Site 2) half ≤ (1 - c ^ 4) ^ K := by
    intro K
    calc theta (zdGraph 2) (0 : Site 2) half = μ.real (percolatesAt 0) := rfl
      _ ≤ μ.real (⋂ k ∈ Finset.range K, (annulusBlocked (4 ^ (k + 1)))ᶜ) := by
          refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
          filter_upwards [ae_subset_edgeSet (zdGraph 2) half] with ω hω hperc
          change ω ∈ ⋂ k ∈ Finset.range K, (annulusBlocked (4 ^ (k + 1)))ᶜ
          simp only [Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
          intro k _ hB
          exact not_mem_percolatesAt_of_annulusBlocked hω (Nat.one_le_pow _ _ (by norm_num)) hB
            hperc
      _ = ∏ k ∈ Finset.range K, (1 - μ.real (annulusBlocked (4 ^ (k + 1)))) :=
          real_iInter_compl_annulusBlocked half K
      _ ≤ ∏ _k ∈ Finset.range K, (1 - c ^ 4) :=
          Finset.prod_le_prod (fun k _ => sub_nonneg.2 measureReal_le_one)
            (fun k _ => by linarith [hε (4 ^ (k + 1)) (Nat.one_le_pow _ _ (by norm_num))])
      _ = (1 - c ^ 4) ^ K := by rw [Finset.prod_const, Finset.card_range]
  have hlim : Tendsto (fun K : ℕ => (1 - c ^ 4) ^ K) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.2 hε1) (sub_lt_self 1 hε0)
  exact le_antisymm (ge_of_tendsto' hlim hbound) measureReal_nonneg

/-- **Harris' theorem from the RSW lower bound** (Bollobás–Riordan 2006, Ch. 3, Thm. 6 from
eq. (3)): `θ(1/2) = 0` given `rsw_lowerBound`. [cite: BollobasRiordanPercolation2006, Ch. 3, Thm. 6] -/
theorem harris_theta_half_of_rsw_lowerBound (hlow : rsw_lowerBound) : harris_theta_half := by
  obtain ⟨c, hc, hcn⟩ := rsw_lowerBound.le_one_sub_crossingProb hlow
  exact harris_theta_half_of_le_one_sub_crossingProb hc hcn

/-- **Harris' theorem** `θ(1/2) = 0` for bond percolation on `ℤ²`: the proof of the statement
`harris_theta_half`. Sources: Harris, *Proc. Camb. Phil. Soc.* **56** (1960) 13–20 (the
original; Bollobás–Riordan 2006, Ch. 3, p. 48: "The first major result on this topic was due to
Harris [1960], who proved that `p_H ≥ 1/2`"; Grimmett 1999, notes to §11.3: "Lemma (11.12) was
first proved using quite different techniques by Harris (1960)"); Grimmett, *Percolation*
(2nd ed., 1999), §11.3, Lemma (11.12): "It is the case that `θ(½) = 0`, and therefore the critical
probability `p_c ≥ ½`" (the first half of Thm. (11.11), `p_c = ½`); Bollobás–Riordan,
*Percolation* (2006), Ch. 3, §3.2, Thm. 6: "For bond percolation in `ℤ²`, `θ(1/2) = 0`." The
proof is Bollobás–Riordan's: the Russo–Seymour–Welsh lower bound `rsw_lowerBound`
(Bollobás–Riordan 2006, Ch. 3, eq. (3); proved as `rsw_lowerBound_holds` in `RSWLemma.lean`)
fed into the square-annulus argument above. [cite: HarrisPCPS1960, main theorem] [cite: GrimmettPercolation1999, §11.3 Lemma (11.12)] [cite: BollobasRiordanPercolation2006, Ch. 3 Thm. 6] -/
theorem harris_theta_half_holds : harris_theta_half :=
  harris_theta_half_of_rsw_lowerBound rsw_lowerBound_holds

end

end Percolation.Literature
