import Mathlib.Combinatorics.SetFamily.FourFunctions
import Percolation.Literature.ConditionalPositiveAssociation
import Percolation.Literature.DecisionTreeBK
import Percolation.Util.Linter

/-!
# Proof of van den Berg–Häggström–Kahn (2006), Theorem 1.3

Proves the statement
`Percolation.Literature.BHK2006_clusterConditionalPositiveAssociation`
(file `ConditionalPositiveAssociation.lean`): the open edge cluster `C_s` of Bernoulli bond
percolation on a finite vertex set is conditionally positively associated given `{s ↮ X}`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), via Thm. 1.1 (pp. 3–5) and Thm. 1.2 (p. 5)]

## The printed proof and how it is mirrored here

BHK prove **Theorem 1.1**: for `A, B` increasing events determined by `C_s` and
`X, Y ⊆ V ∖ {s}`, `Pr(A R_X) Pr(B R_Y) ≤ Pr(A B R_{X∩Y}) Pr(R_{X∪Y})` (`R_W = {s ↮ W}`), by
induction on the number of vertices: if `Z := X ∩ Y = ∅` this is two applications of the
Harris–FKG inequality (their display (4)); otherwise one conditions on the random set `S` of
vertices outside `Z` joined to `Z` by an open edge, observes (their (6)) that given `S` the
event `D R_W` (`W ⊇ Z`) becomes the event `D R_{(W∖Z)∪S}` of percolation on `G − Z`, and
concludes with the Ahlswede–Daykin four functions theorem plus the induction hypothesis on
`G − Z`.  Theorem 1.2 is `Y = X`; Theorem 1.3 is its "functional extension" by "a standard (and
easy) reduction".

We formalize exactly this, with two simplifications that avoid the events-to-functions reduction
and all conditional probabilities:

* we prove Theorem 1.1 directly in functional form (`BHK2006.core`): for `F, G ≥ 0` increasing
  functions of the cluster,
  `E[F(C) 1_{R_X}] E[G(C) 1_{R_Y}] ≤ E[F(C) G(C) 1_{R_{X∩Y}}] P(R_{X∪Y})`; the printed argument goes
  through verbatim (Harris for functions; four functions theorem with the same four functions),
  and BHK's preliminary replacement of `A` by an `Ã` not depending on the edges at `X` is not
  needed: on `R_W ⊇ R_Z` the cluster of `s` in `G[U]` *is* its cluster in `G[U ∖ Z]`
  (`BHK2006.rC_restrict`);
* percolation "on `G − Z`" is realised inside the fixed configuration space `Set (Sym2 V)` with
  the fixed product weight, by computing connectivity through `ω ∩ edgesIn U` only
  (`BHK2006.rC`, `BHK2006.rD`, `U` the current vertex set); the conditioning on `S` is the exact
  finite-sum identity `BHK2006.step_sum` (BHK's (6)), proved from a "block Fubini" identity for
  product weights (`BHK2006.blockFubini`), and the four functions theorem is applied on the
  lattice of full configurations with `fᵢ(ω) = weight(ω) · (block expectation at S(ω))`, whose
  Ahlswede–Daykin hypothesis is the product-weight lattice identity times the induction
  hypothesis (BHK's display after (6)).

Harris–FKG and Ahlswede–Daykin are Mathlib's `fkg` and `four_functions_theorem_univ`; the real
`0/1`-indicator `ind` is reused from `DecisionTreeBK.lean` (`DecisionTree.ind`).
Finally `prodBernoulli w` on the finite type `Set (Sym2 V)` is a finite weighted sum
(`BHK2006.integral_prodBernoulli_eq_sum`), which turns the integral statement of the fact into
the finite-sum statement (`Y = X`, and `F, G` shifted by `F ∅, G ∅` to be nonnegative — on a
finite edge set an increasing `F` is bounded below by `F ∅`).
-/

noncomputable section

open MeasureTheory unitInterval
open Percolation.Literature.LatticeModels (prodBernoulli prodBernoulli_eq_map)

namespace Percolation.Literature

namespace BHK2006

open scoped Classical
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)

/-! ### Product weights on `Set ι` and their algebra -/

section Weights

variable {ι : Type*} [Fintype ι]

/-- The weight of the configuration `ω` under the product Bernoulli law with parameters `w`:
`∏ e, (w e if e ∈ ω else 1 - w e)`. [folklore] -/
def weight (w : ι → ℝ) (ω : Set ι) : ℝ := ∏ e, if e ∈ ω then w e else 1 - w e

/-- `1_D ≤ 1` (for the real indicator `DecisionTree.ind` of `DecisionTreeBK.lean`). [folklore] -/
theorem ind_le_one {α : Type*} (D : Set α) (a : α) : ind D a ≤ 1 := by
  by_cases ha : a ∈ D
  · rw [ind_of_mem ha]
  · rw [ind_of_not_mem ha]; norm_num

/-- `1_D ≤ 1_{D'}` for `D ⊆ D'`. [folklore] -/
theorem ind_mono {α : Type*} {D D' : Set α} (h : D ⊆ D') (a : α) : ind D a ≤ ind D' a := by
  by_cases ha : a ∈ D
  · rw [ind_of_mem ha, ind_of_mem (h ha)]
  · rw [ind_of_not_mem ha]; exact ind_nonneg D' a

/-- `1_{D ∩ D'} = 1_D · 1_{D'}`. [folklore] -/
theorem ind_inter {α : Type*} (D D' : Set α) (a : α) : ind (D ∩ D') a = ind D a * ind D' a := by
  by_cases ha : a ∈ D <;> by_cases ha' : a ∈ D' <;>
    simp [ind_of_mem, ind_of_not_mem, ha, ha', Set.mem_inter_iff]

/-- Product weights with parameters in `[0, 1]` are nonnegative. [folklore] -/
theorem weight_nonneg {w : ι → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (ω : Set ι) :
    0 ≤ weight w ω :=
  Finset.prod_nonneg fun e _ => by
    split_ifs
    · exact hw0 e
    · linarith [hw1 e]

/-- The product weight satisfies the FKG lattice condition with equality. [folklore] -/
theorem weight_inter_mul_union (w : ι → ℝ) (a b : Set ι) :
    weight w a * weight w b = weight w (a ∩ b) * weight w (a ∪ b) := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;> simp [ha, hb, mul_comm]

/-- Swapping the coordinates outside `A` between two configurations preserves the product of
their weights. [folklore] -/
theorem weight_swap (w : ι → ℝ) (A a b : Set ι) :
    weight w a * weight w b = weight w (A.ite a b) * weight w (A.ite b a) := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  by_cases hA : e ∈ A <;> by_cases ha : e ∈ a <;> by_cases hb : e ∈ b <;>
    simp [Set.ite, hA, ha, hb, mul_comm]

omit [Fintype ι] in
/-- The `A`-block of `A.ite a b` is that of `a`. [folklore] -/
theorem ite_inter_eq (A a b : Set ι) : A.ite a b ∩ A = a ∩ A := by
  ext e; by_cases hA : e ∈ A <;> simp [Set.ite, hA]

omit [Fintype ι] in
/-- The `Aᶜ`-block of `A.ite a b` is that of `b`. [folklore] -/
theorem ite_diff_eq (A a b : Set ι) : A.ite a b \ A = b \ A := by
  ext e; by_cases hA : e ∈ A <;> simp [Set.ite, hA]

omit [Fintype ι] in
/-- Swapping the `Aᶜ`-blocks twice is the identity. [folklore] -/
theorem ite_ite_ite (A a b : Set ι) : A.ite (A.ite a b) (A.ite b a) = a := by
  ext e; by_cases hA : e ∈ A <;> simp [Set.ite, hA]

omit [Fintype ι] in
/-- The swap of the coordinates outside `A` is an involution of pairs of configurations. [folklore]
-/
theorem swap_involutive (A : Set ι) :
    Function.Involutive (fun p : Set ι × Set ι => (A.ite p.2 p.1, A.ite p.1 p.2)) := by
  intro p
  ext1
  · exact ite_ite_ite A p.1 p.2
  · exact ite_ite_ite A p.2 p.1

/-- **Block Fubini for product weights.** The expectation of a function of the two blocks
`(ω ∩ A, ω ∖ A)` is the iterated expectation over two independent configurations. [folklore] -/
theorem blockFubini (w : ι → ℝ) (A : Set ι) (Φ : Set ι → Set ι → ℝ) :
    (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) =
      ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type' fun ω ω' =>
    weight w ω * (weight w ω' * Φ (ω' ∩ A) (ω' \ A))]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type' fun ω ω' => weight w ω * (weight w ω' * Φ (ω ∩ A) (ω' \ A))]
  refine Fintype.sum_bijective _ (swap_involutive A).bijective _ _ fun p => ?_
  simp only [ite_inter_eq, ite_diff_eq]
  rw [← mul_assoc, ← mul_assoc, mul_comm (weight w p.1), weight_swap w A p.2 p.1]

/-- Sum of the weights. [folklore] -/
theorem sum_affine (w : ι → ℝ) (h f g p q : Set ι → ℝ) (a b c d : ℝ)
    (hh : ∀ ω, h ω = a * f ω + b * g ω + c * p ω + d * q ω) :
    ∑ ω, weight w ω * h ω = a * ∑ ω, weight w ω * f ω + b * ∑ ω, weight w ω * g ω +
      c * ∑ ω, weight w ω * p ω + d * ∑ ω, weight w ω * q ω := by
  have : ∀ ω, weight w ω * h ω = a * (weight w ω * f ω) + b * (weight w ω * g ω) +
      c * (weight w ω * p ω) + d * (weight w ω * q ω) := fun ω => by rw [hh]; ring
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]

variable {w : ι → ℝ}

/-- **Harris–FKG** for the product weight, both functions increasing (Mathlib's `fkg`).
[cite: VandenbergHaggstromKahn2005, §1 p. 6 ("Harris' inequality"); Mathlib `fkg`] -/
theorem harris (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) {f g : Set ι → ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ a, 0 ≤ g a) (hf : Monotone f) (hg : Monotone g) :
    (∑ ω, weight w ω * f ω) * ∑ ω, weight w ω * g ω ≤
      (∑ ω, weight w ω) * ∑ ω, weight w ω * (f ω * g ω) :=
  fkg (μ := weight w) (f := f) (g := g) (fun ω => weight_nonneg hw0 hw1 ω) (fun a => hf0 a)
    (fun a => hg0 a) hf hg fun a b => (weight_inter_mul_union w a b).le

/-- Harris for one increasing and one decreasing (bounded) function.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, display (4)] -/
theorem harris_mono_anti (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) {f g : Set ι → ℝ}
    (hf0 : ∀ a, 0 ≤ f a) (hf : Monotone f) (hg : Antitone g) {M : ℝ}
    (hgM : ∀ a, g a ≤ M) :
    ∑ ω, weight w ω * (f ω * g ω) ≤ (∑ ω, weight w ω * f ω) * ∑ ω, weight w ω * g ω := by
  have h := harris hw0 hw1 hf0 (g := fun a => M - g a) (fun a => sub_nonneg.2 (hgM a)) hf
    (fun a b hab => sub_le_sub_left (hg hab) M)
  rw [hm, one_mul] at h
  have e1 : ∑ ω, weight w ω * (M - g ω) = M - ∑ ω, weight w ω * g ω := by
    have := sum_affine w (fun ω => M - g ω) (fun _ => 1) g g g M (-1) 0 0 (fun ω => by ring)
    rw [this]; simp [hm]; ring
  have e2 : ∑ ω, weight w ω * (f ω * (M - g ω)) =
      M * ∑ ω, weight w ω * f ω - ∑ ω, weight w ω * (f ω * g ω) := by
    have := sum_affine w (fun ω => f ω * (M - g ω)) f (fun ω => f ω * g ω) g g M (-1) 0 0
      (fun ω => by ring)
    rw [this]; ring
  rw [e1, e2] at h
  nlinarith [h]

/-- Harris for two decreasing (bounded) functions.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, display (4)] -/
theorem harris_anti_anti (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) {f g : Set ι → ℝ}
    (hf : Antitone f) (hg : Antitone g) {M N : ℝ}
    (hfM : ∀ a, f a ≤ M) (hgN : ∀ a, g a ≤ N) :
    (∑ ω, weight w ω * f ω) * ∑ ω, weight w ω * g ω ≤ ∑ ω, weight w ω * (f ω * g ω) := by
  have h := harris hw0 hw1 (f := fun a => M - f a) (g := fun a => N - g a)
    (fun a => sub_nonneg.2 (hfM a)) (fun a => sub_nonneg.2 (hgN a))
    (fun a b hab => sub_le_sub_left (hf hab) M) (fun a b hab => sub_le_sub_left (hg hab) N)
  rw [hm, one_mul] at h
  have e1 : ∑ ω, weight w ω * (M - f ω) = M - ∑ ω, weight w ω * f ω := by
    have := sum_affine w (fun ω => M - f ω) (fun _ => 1) f f f M (-1) 0 0 (fun ω => by ring)
    rw [this]; simp [hm]; ring
  have e2 : ∑ ω, weight w ω * (N - g ω) = N - ∑ ω, weight w ω * g ω := by
    have := sum_affine w (fun ω => N - g ω) (fun _ => 1) g g g N (-1) 0 0 (fun ω => by ring)
    rw [this]; simp [hm]; ring
  have e3 : ∑ ω, weight w ω * ((M - f ω) * (N - g ω)) =
      M * N - M * ∑ ω, weight w ω * g ω - N * ∑ ω, weight w ω * f ω +
        ∑ ω, weight w ω * (f ω * g ω) := by
    have := sum_affine w (fun ω => (M - f ω) * (N - g ω)) (fun _ => 1) g f
      (fun ω => f ω * g ω) (M * N) (-M) (-N) 1 (fun ω => by ring)
    rw [this]; simp [hm]; ring
  rw [e1, e2, e3] at h
  nlinarith [h]

/-- Monotonicity of `E[h · 1_D]` in the event `D` for `h ≥ 0`. [folklore] -/
theorem sum_ind_mono (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) {h : Set ι → ℝ}
    (hh : ∀ a, 0 ≤ h a) {D D' : Set (Set ι)} (hDD : D ⊆ D') :
    ∑ ω, weight w ω * (h ω * ind D ω) ≤ ∑ ω, weight w ω * (h ω * ind D' ω) :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (ind_mono hDD ω) (hh ω)) (weight_nonneg hw0 hw1 ω)

/-- `0 ≤ E[h · 1_D]` for `h ≥ 0`. [folklore] -/
theorem sum_ind_nonneg (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) {h : Set ι → ℝ}
    (hh : ∀ a, 0 ≤ h a) (D : Set (Set ι)) :
    0 ≤ ∑ ω, weight w ω * (h ω * ind D ω) :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω)
    (mul_nonneg (hh ω) (ind_nonneg D ω))

/-- `prodBernoulli w` on a finite type is the finite sum of point masses with the product
weights. [folklore] -/
theorem integral_prodBernoulli_eq_sum (w : ι → unitInterval) (h : Set ι → ℝ) :
    ∫ ω, h ω ∂(prodBernoulli w) = ∑ ω : Set ι, weight (fun e => (w e : ℝ)) ω * h ω := by
  set κ : ι → Measure Prop := fun i =>
    toNNReal (w i) • Measure.dirac True + toNNReal (σ (w i)) • Measure.dirac False with hκ
  have hmap : prodBernoulli w = Measure.map MeasurableEquiv.setOf (Measure.infinitePi κ) :=
    prodBernoulli_eq_map w
  rw [hmap, integral_map_equiv, integral_fintype (.of_finite),
    ← Equiv.sum_comp (MeasurableEquiv.setOf (α := ι)).toEquiv]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq : (Measure.infinitePi κ).real {q} = weight (fun e => (w e : ℝ)) (setOf q) := by
    rw [measureReal_def, Measure.infinitePi_singleton_of_fintype, ENNReal.toReal_prod]
    unfold weight
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hqi : q i
    · have : q i = True := by simp [hqi]
      simp [hκ, this]
    · have : q i = False := by simp [hqi]
      simp [hκ, this]
  rw [hq]
  rfl

end Weights

/-! ### Percolation restricted to a vertex set `U` -/

section Graph

variable {V : Type*}

/-- The unordered pairs with both entries in `U` (the edges of the complete graph on `U`,
loops included). [folklore] -/
def edgesIn (U : Finset V) : Set (Sym2 V) := {e | ∀ v ∈ e, v ∈ U}

/-- The unordered pairs meeting `Z`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (`E_X := {e ∈ E : e ∩ X ≠ ∅}`)] -/
def meeting (Z : Finset V) : Set (Sym2 V) := {e | ∃ z ∈ Z, z ∈ e}

/-- BHK's `C_s` for percolation restricted to the vertex set `U`: the open cluster of `s`
computed with the open edges inside `U` only (BHK p. 3; p. 4: the induced model on `G` minus `Z`).
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (definition of `C_s`), p. 4] -/
def rC (U : Finset V) (s : V) (ω : Set (Sym2 V)) : Set (Sym2 V) :=
  openEdgeCluster (ω ∩ edgesIn U) s

/-- BHK's event `R_X = {s ↮ X}` for percolation restricted to the vertex set `U`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3 (definition of `R_X`)] -/
def rD (U : Finset V) (s : V) (X : Set V) : Set (Set (Sym2 V)) :=
  {ω | ∀ x ∈ X, ¬ (openGraph (ω ∩ edgesIn U)).Reachable s x}

/-- BHK's random set `S`: the vertices of `U ∖ Z` joined to `Z` by an open edge.
[cite: VandenbergHaggstromKahn2005, §1 p. 4 (definition of `S`)] -/
def rS (U Z : Finset V) (ω : Set (Sym2 V)) : Set V :=
  {n | n ∈ U \ Z ∧ ∃ z ∈ Z, s(n, z) ∈ ω}

/-- `s(x, y)` lies inside `U` iff both `x, y ∈ U`. [folklore] -/
theorem mem_edgesIn_mk {U : Finset V} {x y : V} : s(x, y) ∈ edgesIn U ↔ x ∈ U ∧ y ∈ U := by
  simp only [edgesIn, Set.mem_setOf_eq, Sym2.mem_iff, or_imp, forall_and, forall_eq]

/-- `edgesIn` is monotone in the vertex set. [folklore] -/
theorem edgesIn_mono {U U' : Finset V} (h : U' ⊆ U) : edgesIn U' ⊆ edgesIn U :=
  fun _ he v hv => h (he v hv)

/-- Adjacency in the open graph restricted to `U`: the edge is open, inside `U`, and not a loop
(Grimmett 1999, §1.3). [folklore] -/
theorem adj_iff {U : Finset V} {ω : Set (Sym2 V)} {x y : V} :
    (openGraph (ω ∩ edgesIn U)).Adj x y ↔ s(x, y) ∈ ω ∧ (x ∈ U ∧ y ∈ U) ∧ x ≠ y := by
  rw [openGraph_adj, Set.mem_inter_iff, mem_edgesIn_mk, and_assoc]

/-- More open edges give a larger open graph. [folklore] -/
theorem openGraph_le {ω ω' : Set (Sym2 V)} (h : ω ⊆ ω') : openGraph ω ≤ openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono h

/-- BHK's `C_s` is increasing in the configuration ("such an event is increasing in the sense
above", p. 3). [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem openEdgeCluster_mono {ω ω' : Set (Sym2 V)} (h : ω ⊆ ω') (s : V) :
    openEdgeCluster ω s ⊆ openEdgeCluster ω' s := fun _ he =>
  ⟨h he.1, he.2.1, fun v hv => (he.2.2 v hv).mono (openGraph_le h)⟩

/-- The restricted cluster `C_s^U` is increasing in the configuration.
[cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem rC_mono (U : Finset V) (s : V) : Monotone (rC U s) := fun _ _ h =>
  openEdgeCluster_mono (Set.inter_subset_inter_left _ h) s

/-- `R_X = {s ↮ X}` is a decreasing event. [cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem rD_decreasing {U : Finset V} {s : V} {X : Set V} {ω ω' : Set (Sym2 V)} (h : ω ⊆ ω')
    (h' : ω' ∈ rD U s X) : ω ∈ rD U s X := fun x hx hr =>
  h' x hx (hr.mono (openGraph_le (Set.inter_subset_inter_left _ h)))

/-- The indicator of the decreasing event `R_X` is antitone.
[cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem ind_rD_antitone (U : Finset V) (s : V) (X : Set V) : Antitone (ind (rD U s X)) := by
  intro ω ω' h
  by_cases h' : ω' ∈ rD U s X
  · rw [ind_of_mem h', ind_of_mem (rD_decreasing h h')]
  · rw [ind_of_not_mem h']; exact ind_nonneg _ _

/-- `R_X` is antitone in `X`: `X ⊆ X' → R_{X'} ⊆ R_X`. [cite: VandenbergHaggstromKahn2005, §1 p. 3]
-/
theorem rD_antitone {U : Finset V} {s : V} {X X' : Set V} (h : X ⊆ X') : rD U s X' ⊆ rD U s X :=
  fun _ hω x hx => hω x (h hx)

/-- `R_{X ∪ Y} = R_X R_Y` (BHK p. 4, "note `R_{X∪Y} = R_X R_Y`").
[cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
theorem rD_union (U : Finset V) (s : V) (X Y : Set V) : rD U s (X ∪ Y) = rD U s X ∩ rD U s Y := by
  ext ω
  simp only [rD, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union, or_imp, forall_and]

/-- `R_X = ∅` when `s ∈ X` (`s ↔ s` always). [folklore] -/
theorem rD_eq_empty {U : Finset V} {s : V} {X : Set V} (hs : s ∈ X) : rD U s X = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hω => hω s hs (SimpleGraph.Reachable.refl s)

/-- `S ⊆ U ∖ Z` (BHK: `S ⊆ N`, the vertices outside `Z`).
[cite: VandenbergHaggstromKahn2005, §1 p. 4] -/
theorem rS_subset (U Z : Finset V) (ω : Set (Sym2 V)) : rS U Z ω ⊆ ↑(U \ Z) := fun _ hn => hn.1

/-- `S(a ∩ b) ⊆ S(a) ∩ S(b)`. [folklore] -/
theorem rS_inter_subset (U Z : Finset V) (a b : Set (Sym2 V)) :
    rS U Z (a ∩ b) ⊆ rS U Z a ∩ rS U Z b := fun _ ⟨hn, z, hz, hza, hzb⟩ =>
  ⟨⟨hn, z, hz, hza⟩, ⟨hn, z, hz, hzb⟩⟩

/-- `S(a ∪ b) = S(a) ∪ S(b)`. [folklore] -/
theorem rS_union (U Z : Finset V) (a b : Set (Sym2 V)) :
    rS U Z (a ∪ b) = rS U Z a ∪ rS U Z b := by
  ext n
  constructor
  · rintro ⟨hn, z, hz, h | h⟩
    · exact Or.inl ⟨hn, z, hz, h⟩
    · exact Or.inr ⟨hn, z, hz, h⟩
  · rintro (⟨hn, z, hz, h⟩ | ⟨hn, z, hz, h⟩)
    · exact ⟨hn, z, hz, Or.inl h⟩
    · exact ⟨hn, z, hz, Or.inr h⟩

/-- `S` only depends on the edges meeting `Z`. [folklore] -/
theorem rS_inter_meeting (U Z : Finset V) (ω : Set (Sym2 V)) :
    rS U Z (ω ∩ meeting Z) = rS U Z ω := by
  ext n
  constructor
  · rintro ⟨hn, z, hz, h⟩
    exact ⟨hn, z, hz, h.1⟩
  · rintro ⟨hn, z, hz, h⟩
    exact ⟨hn, z, hz, h, z, hz, Sym2.mem_mk_right n z⟩

/-- Edges inside `U ∖ Z` do not meet `Z`: deleting the edges meeting `Z` does not change the
configuration inside `U ∖ Z`. [folklore] -/
theorem diff_meeting_inter_edgesIn (U Z : Finset V) (ω : Set (Sym2 V)) :
    (ω \ meeting Z) ∩ edgesIn (U \ Z) = ω ∩ edgesIn (U \ Z) := by
  ext e
  constructor
  · rintro ⟨⟨hω, -⟩, hU⟩
    exact ⟨hω, hU⟩
  · rintro ⟨hω, hU⟩
    exact ⟨⟨hω, fun ⟨z, hz, hze⟩ => (Finset.mem_sdiff.1 (hU z hze)).2 hz⟩, hU⟩

/-- The cluster in `G[U ∖ Z]` does not depend on the edges meeting `Z`. [folklore] -/
theorem rC_diff_meeting (U Z : Finset V) (s : V) (ω : Set (Sym2 V)) :
    rC (U \ Z) s (ω \ meeting Z) = rC (U \ Z) s ω := by
  simp only [rC, diff_meeting_inter_edgesIn]

/-- The events `R_T` of `G[U ∖ Z]` do not depend on the edges meeting `Z`. [folklore] -/
theorem mem_rD_diff_meeting (U Z : Finset V) (s : V) (T : Set V) (ω : Set (Sym2 V)) :
    ω \ meeting Z ∈ rD (U \ Z) s T ↔ ω ∈ rD (U \ Z) s T := by
  simp only [rD, Set.mem_setOf_eq, diff_meeting_inter_edgesIn]

/-- The heart of BHK's identity (6): if, in `G − Z`, `s` is joined to no vertex having an open
edge to `Z`, then every vertex joined to `s` in `G[U]` is outside `Z` and joined to `s` in
`G[U ∖ Z]`. [cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem reach_restrict {U Z : Finset V} {s : V} (hs : s ∉ Z) {ω : Set (Sym2 V)}
    (hS : ∀ n ∈ rS U Z ω, ¬ (openGraph (ω ∩ edgesIn (U \ Z))).Reachable s n) {v : V}
    (hv : (openGraph (ω ∩ edgesIn U)).Reachable s v) :
    v ∉ Z ∧ (openGraph (ω ∩ edgesIn (U \ Z))).Reachable s v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact ⟨hs, SimpleGraph.Reachable.refl s⟩
  | tail _ hbc ih =>
    obtain ⟨hbZ, hb⟩ := ih
    obtain ⟨hω, ⟨hbU, hcU⟩, hne⟩ := adj_iff.1 hbc
    have hcZ : _ ∉ Z := fun hcZ =>
      hS _ ⟨Finset.mem_sdiff.2 ⟨hbU, hbZ⟩, _, hcZ, hω⟩ hb
    refine ⟨hcZ, hb.trans (SimpleGraph.Adj.reachable ?_)⟩
    exact adj_iff.2 ⟨hω, ⟨Finset.mem_sdiff.2 ⟨hbU, hbZ⟩, Finset.mem_sdiff.2 ⟨hcU, hcZ⟩⟩, hne⟩

/-- **BHK's identity (6)**, pointwise: for `W ⊇ Z`, `{s ↮ W in G[U]}` is the event
`{s ↮ (W ∖ Z) ∪ S(ω) in G[U ∖ Z]}`. [cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6)] -/
theorem mem_rD_iff_restrict {U Z : Finset V} (hZU : Z ⊆ U) {s : V} (hs : s ∉ Z) {W : Set V}
    (hZW : (↑Z : Set V) ⊆ W) (ω : Set (Sym2 V)) :
    ω ∈ rD U s W ↔ ω ∈ rD (U \ Z) s ((W \ ↑Z) ∪ rS U Z ω) := by
  constructor
  · intro h x hx hreach
    rcases hx with ⟨hxW, -⟩ | ⟨hxUZ, z, hzZ, hxz⟩
    · exact h x hxW (hreach.mono (openGraph_le
        (Set.inter_subset_inter_right _ (edgesIn_mono Finset.sdiff_subset))))
    · obtain ⟨hxU, hxZ⟩ := Finset.mem_sdiff.1 hxUZ
      refine h z (hZW hzZ) ((hreach.mono (openGraph_le
        (Set.inter_subset_inter_right _ (edgesIn_mono Finset.sdiff_subset)))).trans
        (SimpleGraph.Adj.reachable (adj_iff.2 ⟨hxz, ⟨hxU, hZU hzZ⟩, ?_⟩)))
      rintro rfl
      exact hxZ hzZ
  · intro h x hxW hreach
    have hS : ∀ n ∈ rS U Z ω, ¬ (openGraph (ω ∩ edgesIn (U \ Z))).Reachable s n :=
      fun n hn => h n (Or.inr hn)
    obtain ⟨hxZ, hreach'⟩ := reach_restrict hs hS hreach
    exact h x (Or.inl ⟨hxW, hxZ⟩) hreach'

/-- On the event of `mem_rD_iff_restrict`, the cluster of `s` in `G[U]` is its cluster in
`G[U ∖ Z]`. [cite: VandenbergHaggstromKahn2005, §1 p. 4, identity (6) and the remark following it]
-/
theorem rC_restrict {U Z : Finset V} {s : V} (hs : s ∉ Z) {ω : Set (Sym2 V)}
    (hS : ∀ n ∈ rS U Z ω, ¬ (openGraph (ω ∩ edgesIn (U \ Z))).Reachable s n) :
    rC U s ω = rC (U \ Z) s ω := by
  ext e
  simp only [rC, mem_openEdgeCluster_iff, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨heω, heU⟩, hd, hr⟩
    exact ⟨⟨heω, fun v hv => Finset.mem_sdiff.2 ⟨heU v hv, (reach_restrict hs hS (hr v hv)).1⟩⟩,
      hd, fun v hv => (reach_restrict hs hS (hr v hv)).2⟩
  · rintro ⟨⟨heω, heU⟩, hd, hr⟩
    exact ⟨⟨heω, fun v hv => (Finset.mem_sdiff.1 (heU v hv)).1⟩, hd, fun v hv =>
      (hr v hv).mono (openGraph_le
        (Set.inter_subset_inter_right _ (edgesIn_mono Finset.sdiff_subset)))⟩

/-! ### Conditioning on `S` (BHK's (6), summed) -/

variable [Fintype V]

/-- The block expectation `T ↦ E[H(C_s^{U'}) · 1{s ↮ B ∪ T in G[U']}]`.
[cite: VandenbergHaggstromKahn2005, §1 p. 4 (`Pr(· | S)`)] -/
def blockE (w : Sym2 V → ℝ) (U' : Finset V) (s : V) (H : Set (Sym2 V) → ℝ) (B T : Set V) : ℝ :=
  ∑ ω, weight w ω * (H (rC U' s ω) * ind (rD U' s (B ∪ T)) ω)

/-- Block expectations of nonnegative functions are nonnegative. [folklore] -/
theorem blockE_nonneg {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (U' : Finset V) (s : V) {H : Set (Sym2 V) → ℝ} (hH : ∀ a, 0 ≤ H a) (B T : Set V) :
    0 ≤ blockE w U' s H B T :=
  sum_ind_nonneg hw0 hw1 (fun _ => hH _) _

/-- **BHK's (6)**: `E[H(C_s^U) 1{s ↮ W in G[U]}] = Σ_ω weight(ω) · E'[H(C_s^{U∖Z}) 1{s ↮ (W∖Z) ∪
S(ω)}]`
for `Z ⊆ W`, the conditioning on the set `S` of vertices joined to `Z` by an open edge.
[cite: VandenbergHaggstromKahn2005, §1 p. 4, the display before (5) and identity (6)] -/
theorem step_sum {U Z : Finset V} (hZU : Z ⊆ U) {s : V} (hs : s ∉ Z) {W : Set V}
    (hZW : (↑Z : Set V) ⊆ W) (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1)
    (H : Set (Sym2 V) → ℝ) :
    ∑ ω, weight w ω * (H (rC U s ω) * ind (rD U s W) ω) =
      ∑ ω, weight w ω * blockE w (U \ Z) s H (W \ ↑Z) (rS U Z ω) := by
  set A := meeting Z with hA
  set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
    H (rC (U \ Z) s η) * ind (rD (U \ Z) s ((W \ ↑Z) ∪ rS U Z ζ)) η with hΦ
  have h1 : ∀ ω, H (rC U s ω) * ind (rD U s W) ω = Φ (ω ∩ A) (ω \ A) := by
    intro ω
    simp only [hΦ, hA, rS_inter_meeting, rC_diff_meeting]
    by_cases hω : ω ∈ rD U s W
    · have hω' := (mem_rD_iff_restrict hZU hs hZW ω).1 hω
      rw [ind_of_mem hω, ind_of_mem ((mem_rD_diff_meeting U Z s _ ω).2 hω'),
        rC_restrict hs fun n hn => hω' n (Or.inr hn)]
    · have hω' : ω \ meeting Z ∉ rD (U \ Z) s ((W \ ↑Z) ∪ rS U Z ω) := fun h =>
        hω ((mem_rD_iff_restrict hZU hs hZW ω).2 ((mem_rD_diff_meeting U Z s _ ω).1 h))
      rw [ind_of_not_mem hω, ind_of_not_mem hω', mul_zero, mul_zero]
  have h2 : ∀ ω ω', Φ (ω ∩ A) (ω' \ A) =
      H (rC (U \ Z) s ω') * ind (rD (U \ Z) s ((W \ ↑Z) ∪ rS U Z ω)) ω' := by
    intro ω ω'
    simp only [hΦ, hA, rS_inter_meeting, rC_diff_meeting]
    by_cases hω' : ω' ∈ rD (U \ Z) s ((W \ ↑Z) ∪ rS U Z ω)
    · rw [ind_of_mem hω', ind_of_mem ((mem_rD_diff_meeting U Z s _ ω').2 hω')]
    · rw [ind_of_not_mem hω', ind_of_not_mem (fun h => hω' ((mem_rD_diff_meeting U Z s _ ω').1 h))]
  calc ∑ ω, weight w ω * (H (rC U s ω) * ind (rD U s W) ω)
      = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
        rw [hm, one_mul]; simp_rw [h1]
    _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
    _ = ∑ ω, weight w ω * blockE w (U \ Z) s H (W \ ↑Z) (rS U Z ω) := by
        simp_rw [h2]; rfl

/-! ### Theorem 1.1 (functional form) by induction on the vertex set -/

/-- **BHK Theorem 1.1, functional form, for percolation restricted to `U`.** For `s ∈ U`,
`X, Y ⊆ U`, and `F, G ≥ 0` increasing,
`E[F(C) 1{s↮X}] · E[G(C) 1{s↮Y}] ≤ E[F(C) G(C) 1{s ↮ X∩Y}] · P(s ↮ X∪Y)`.
Proof by strong induction on `U` following BHK pp. 3–5.
[cite: VandenbergHaggstromKahn2005, Thm. 1.1 (pp. 3–5)] -/
theorem core (w : Sym2 V → ℝ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (U : Finset V) :
    ∀ (s : V), s ∈ U → ∀ (X Y : Set V), X ⊆ ↑U → Y ⊆ ↑U →
    ∀ (F G : Set (Sym2 V) → ℝ), Monotone F → Monotone G → (∀ a, 0 ≤ F a) → (∀ a, 0 ≤ G a) →
    (∑ ω, weight w ω * (F (rC U s ω) * ind (rD U s X) ω)) *
      (∑ ω, weight w ω * (G (rC U s ω) * ind (rD U s Y) ω)) ≤
    (∑ ω, weight w ω * (F (rC U s ω) * G (rC U s ω) * ind (rD U s (X ∩ Y)) ω)) *
      (∑ ω, weight w ω * ind (rD U s (X ∪ Y)) ω) := by
  induction U using Finset.strongInduction with
  | H U ih =>
  intro s hsU X Y hXU hYU F G hF hG hF0 hG0
  -- nonnegativity of the right-hand side
  have hRHS : 0 ≤ (∑ ω, weight w ω * (F (rC U s ω) * G (rC U s ω) * ind (rD U s (X ∩ Y)) ω)) *
      (∑ ω, weight w ω * ind (rD U s (X ∪ Y)) ω) :=
    mul_nonneg (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω)
      (mul_nonneg (mul_nonneg (hF0 _) (hG0 _)) (ind_nonneg _ _)))
      (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _))
  -- trivial cases `s ∈ X`, `s ∈ Y`
  by_cases hsX : s ∈ X
  · have h0 : ∑ ω, weight w ω * (F (rC U s ω) * ind (rD U s X) ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => by
        rw [rD_eq_empty hsX, ind_of_not_mem (Set.notMem_empty ω)]; ring
    rw [h0, zero_mul]; exact hRHS
  by_cases hsY : s ∈ Y
  · have h0 : ∑ ω, weight w ω * (G (rC U s ω) * ind (rD U s Y) ω) = 0 :=
      Finset.sum_eq_zero fun ω _ => by
        rw [rD_eq_empty hsY, ind_of_not_mem (Set.notMem_empty ω)]; ring
    rw [h0, mul_zero]; exact hRHS
  -- `Z := X ∩ Y`
  set Z : Finset V := U.filter fun v => v ∈ X ∧ v ∈ Y with hZ
  have hZU : Z ⊆ U := Finset.filter_subset _ _
  have hmemZ : ∀ v, v ∈ Z ↔ v ∈ X ∧ v ∈ Y := fun v => by
    simp only [hZ, Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hXU h.1
  have hsZ : s ∉ Z := fun h => hsX ((hmemZ s).1 h).1
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · /- `X ∩ Y = ∅`: two applications of Harris (BHK display (4)). -/
    have hXY : ∀ ω, ind (rD U s (X ∩ Y)) ω = 1 := fun ω =>
      ind_of_mem fun x hx _ => by
        have : x ∈ Z := (hmemZ x).2 hx
        rw [hZe] at this
        exact absurd this (Finset.notMem_empty x)
    have hXuY : ∀ ω, ind (rD U s (X ∪ Y)) ω = ind (rD U s X) ω * ind (rD U s Y) ω := fun ω => by
      rw [rD_union, ind_inter]
    simp_rw [hXY, mul_one, hXuY]
    have hFm : Monotone fun ω => F (rC U s ω) := fun a b hab => hF (rC_mono U s hab)
    have hGm : Monotone fun ω => G (rC U s ω) := fun a b hab => hG (rC_mono U s hab)
    have h1 : ∑ ω, weight w ω * (F (rC U s ω) * ind (rD U s X) ω) ≤
        (∑ ω, weight w ω * F (rC U s ω)) * ∑ ω, weight w ω * ind (rD U s X) ω :=
      harris_mono_anti hw0 hw1 hm (fun _ => hF0 _) hFm
        (ind_rD_antitone U s X) (fun _ => ind_le_one _ _)
    have h2 : ∑ ω, weight w ω * (G (rC U s ω) * ind (rD U s Y) ω) ≤
        (∑ ω, weight w ω * G (rC U s ω)) * ∑ ω, weight w ω * ind (rD U s Y) ω :=
      harris_mono_anti hw0 hw1 hm (fun _ => hG0 _) hGm
        (ind_rD_antitone U s Y) (fun _ => ind_le_one _ _)
    have h3 : (∑ ω, weight w ω * F (rC U s ω)) * (∑ ω, weight w ω * G (rC U s ω)) ≤
        ∑ ω, weight w ω * (F (rC U s ω) * G (rC U s ω)) := by
      have := harris hw0 hw1 (fun _ => hF0 _) (fun _ => hG0 _) hFm hGm
      rwa [hm, one_mul] at this
    have h4 : (∑ ω, weight w ω * ind (rD U s X) ω) * (∑ ω, weight w ω * ind (rD U s Y) ω) ≤
        ∑ ω, weight w ω * (ind (rD U s X) ω * ind (rD U s Y) ω) :=
      harris_anti_anti hw0 hw1 hm
        (ind_rD_antitone U s X) (ind_rD_antitone U s Y) (fun _ => ind_le_one _ _)
        (fun _ => ind_le_one _ _)
    have hFn : 0 ≤ ∑ ω, weight w ω * F (rC U s ω) :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (hF0 _)
    have hGn : 0 ≤ ∑ ω, weight w ω * G (rC U s ω) :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (hG0 _)
    have hXn : 0 ≤ ∑ ω, weight w ω * ind (rD U s X) ω :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
    have hYn : 0 ≤ ∑ ω, weight w ω * ind (rD U s Y) ω :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
    calc (∑ ω, weight w ω * (F (rC U s ω) * ind (rD U s X) ω)) *
          (∑ ω, weight w ω * (G (rC U s ω) * ind (rD U s Y) ω))
        ≤ ((∑ ω, weight w ω * F (rC U s ω)) * ∑ ω, weight w ω * ind (rD U s X) ω) *
          ((∑ ω, weight w ω * G (rC U s ω)) * ∑ ω, weight w ω * ind (rD U s Y) ω) :=
          mul_le_mul h1 h2 (sum_ind_nonneg hw0 hw1 (fun _ => hG0 _) _) (mul_nonneg hFn hXn)
      _ = ((∑ ω, weight w ω * F (rC U s ω)) * ∑ ω, weight w ω * G (rC U s ω)) *
          ((∑ ω, weight w ω * ind (rD U s X) ω) * ∑ ω, weight w ω * ind (rD U s Y) ω) := by
          ring
      _ ≤ (∑ ω, weight w ω * (F (rC U s ω) * G (rC U s ω))) *
          ∑ ω, weight w ω * (ind (rD U s X) ω * ind (rD U s Y) ω) :=
          mul_le_mul h3 h4 (mul_nonneg hXn hYn)
            (Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω)
              (mul_nonneg (hF0 _) (hG0 _)))
  · /- `Z ≠ ∅`: condition on `S` and apply the four functions theorem with the induction
    hypothesis on `U ∖ Z` (BHK pp. 4–5). -/
    have hss : U \ Z ⊂ U := Finset.sdiff_ssubset hZU hZne
    have hsU' : s ∈ U \ Z := Finset.mem_sdiff.2 ⟨hsU, hsZ⟩
    have hZX : (↑Z : Set V) ⊆ X := fun v hv => ((hmemZ v).1 hv).1
    have hZY : (↑Z : Set V) ⊆ Y := fun v hv => ((hmemZ v).1 hv).2
    have hZXY : (↑Z : Set V) ⊆ X ∩ Y := fun v hv => (hmemZ v).1 hv
    have hZXuY : (↑Z : Set V) ⊆ X ∪ Y := fun v hv => Or.inl (((hmemZ v).1 hv).1)
    have hFG : Monotone fun a => F a * G a := fun a b hab =>
      mul_le_mul (hF hab) (hG hab) (hG0 _) (hF0 _)
    -- the four sums, conditioned on `S`
    have e1 := step_sum hZU hsZ hZX w hm F
    have e2 := step_sum hZU hsZ hZY w hm G
    have e3 : ∑ ω, weight w ω * (F (rC U s ω) * G (rC U s ω) * ind (rD U s (X ∩ Y)) ω) =
        ∑ ω, weight w ω * blockE w (U \ Z) s (fun a => F a * G a) ((X ∩ Y) \ ↑Z) (rS U Z ω) :=
      step_sum hZU hsZ hZXY w hm (fun a => F a * G a)
    have e4 : ∑ ω, weight w ω * ind (rD U s (X ∪ Y)) ω =
        ∑ ω, weight w ω * blockE w (U \ Z) s (fun _ => 1) ((X ∪ Y) \ ↑Z) (rS U Z ω) := by
      have := step_sum hZU hsZ hZXuY w hm (fun _ => 1)
      simpa only [one_mul] using this
    rw [e1, e2, e3, e4]
    refine four_functions_theorem_univ
      (fun ω => weight w ω * blockE w (U \ Z) s F (X \ ↑Z) (rS U Z ω))
      (fun ω => weight w ω * blockE w (U \ Z) s G (Y \ ↑Z) (rS U Z ω))
      (fun ω => weight w ω * blockE w (U \ Z) s (fun a => F a * G a) ((X ∩ Y) \ ↑Z) (rS U Z ω))
      (fun ω => weight w ω * blockE w (U \ Z) s (fun _ => 1) ((X ∪ Y) \ ↑Z) (rS U Z ω))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω) (blockE_nonneg hw0 hw1 _ _ hF0 _ _))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω) (blockE_nonneg hw0 hw1 _ _ hG0 _ _))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (blockE_nonneg hw0 hw1 _ _ (fun a => mul_nonneg (hF0 a) (hG0 a)) _ _))
      (fun ω => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (blockE_nonneg hw0 hw1 _ _ (fun _ => zero_le_one) _ _))
      fun a b => ?_
    -- the Ahlswede–Daykin hypothesis: weight lattice identity × induction hypothesis
    set Sa := rS U Z a with hSa
    set Sb := rS U Z b with hSb
    have hSaU : Sa ⊆ ↑(U \ Z) := rS_subset U Z a
    have hSbU : Sb ⊆ ↑(U \ Z) := rS_subset U Z b
    have hX1 : X \ ↑Z ∪ Sa ⊆ ↑(U \ Z) := Set.union_subset
      (fun v hv => by rw [Finset.coe_sdiff]; exact ⟨hXU hv.1, hv.2⟩) hSaU
    have hY1 : Y \ ↑Z ∪ Sb ⊆ ↑(U \ Z) := Set.union_subset
      (fun v hv => by rw [Finset.coe_sdiff]; exact ⟨hYU hv.1, hv.2⟩) hSbU
    have IH := ih (U \ Z) hss s hsU' (X \ ↑Z ∪ Sa) (Y \ ↑Z ∪ Sb) hX1 hY1 F G hF hG hF0 hG0
    -- monotonicity in the conditioning sets
    have hsub3 : (X ∩ Y) \ ↑Z ∪ rS U Z (a ∩ b) ⊆ (X \ ↑Z ∪ Sa) ∩ (Y \ ↑Z ∪ Sb) := by
      refine Set.union_subset (fun v hv => ⟨Or.inl ⟨hv.1.1, hv.2⟩, Or.inl ⟨hv.1.2, hv.2⟩⟩) ?_
      exact fun v hv =>
        ⟨Or.inr (rS_inter_subset U Z a b hv).1, Or.inr (rS_inter_subset U Z a b hv).2⟩
    have hsub4 : (X ∪ Y) \ ↑Z ∪ rS U Z (a ∪ b) ⊆ (X \ ↑Z ∪ Sa) ∪ (Y \ ↑Z ∪ Sb) := by
      rw [rS_union]
      rintro v (⟨hXY | hXY, hvZ⟩ | hS | hS)
      · exact Or.inl (Or.inl ⟨hXY, hvZ⟩)
      · exact Or.inr (Or.inl ⟨hXY, hvZ⟩)
      · exact Or.inl (Or.inr hS)
      · exact Or.inr (Or.inr hS)
    have h3 : ∑ ω, weight w ω * (F (rC (U \ Z) s ω) * G (rC (U \ Z) s ω) *
        ind (rD (U \ Z) s ((X \ ↑Z ∪ Sa) ∩ (Y \ ↑Z ∪ Sb))) ω) ≤
        blockE w (U \ Z) s (fun a => F a * G a) ((X ∩ Y) \ ↑Z) (rS U Z (a ∩ b)) :=
      sum_ind_mono hw0 hw1 (fun ω => mul_nonneg (hF0 _) (hG0 _)) (rD_antitone hsub3)
    have h4 : ∑ ω, weight w ω * ind (rD (U \ Z) s ((X \ ↑Z ∪ Sa) ∪ (Y \ ↑Z ∪ Sb))) ω ≤
        blockE w (U \ Z) s (fun _ => 1) ((X ∪ Y) \ ↑Z) (rS U Z (a ∪ b)) := by
      have := sum_ind_mono hw0 hw1 (h := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
        (rD_antitone (U := U \ Z) (s := s) hsub4) (w := w)
      simp only [one_mul] at this
      simpa only [blockE, one_mul] using this
    have hn3 : 0 ≤ ∑ ω, weight w ω * (F (rC (U \ Z) s ω) * G (rC (U \ Z) s ω) *
        ind (rD (U \ Z) s ((X \ ↑Z ∪ Sa) ∩ (Y \ ↑Z ∪ Sb))) ω) :=
      Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω)
        (mul_nonneg (mul_nonneg (hF0 _) (hG0 _)) (ind_nonneg _ _))
    have hIH' : blockE w (U \ Z) s F (X \ ↑Z) Sa * blockE w (U \ Z) s G (Y \ ↑Z) Sb ≤
        blockE w (U \ Z) s (fun a => F a * G a) ((X ∩ Y) \ ↑Z) (rS U Z (a ∩ b)) *
          blockE w (U \ Z) s (fun _ => 1) ((X ∪ Y) \ ↑Z) (rS U Z (a ∪ b)) :=
      IH.trans (mul_le_mul h3 h4 (Finset.sum_nonneg fun ω _ =>
        mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _))
        (blockE_nonneg hw0 hw1 _ _ (fun a => mul_nonneg (hF0 a) (hG0 a)) _ _))
    have hwab := weight_inter_mul_union w a b
    show weight w a * blockE w (U \ Z) s F (X \ ↑Z) Sa *
        (weight w b * blockE w (U \ Z) s G (Y \ ↑Z) Sb) ≤
      weight w (a ∩ b) * blockE w (U \ Z) s (fun a => F a * G a) ((X ∩ Y) \ ↑Z) (rS U Z (a ∩ b)) *
        (weight w (a ∪ b) * blockE w (U \ Z) s (fun _ => 1) ((X ∪ Y) \ ↑Z) (rS U Z (a ∪ b)))
    calc weight w a * blockE w (U \ Z) s F (X \ ↑Z) Sa *
          (weight w b * blockE w (U \ Z) s G (Y \ ↑Z) Sb)
        = (weight w a * weight w b) *
          (blockE w (U \ Z) s F (X \ ↑Z) Sa * blockE w (U \ Z) s G (Y \ ↑Z) Sb) := by ring
      _ ≤ (weight w (a ∩ b) * weight w (a ∪ b)) *
          (blockE w (U \ Z) s (fun a => F a * G a) ((X ∩ Y) \ ↑Z) (rS U Z (a ∩ b)) *
            blockE w (U \ Z) s (fun _ => 1) ((X ∪ Y) \ ↑Z) (rS U Z (a ∪ b))) := by
          rw [hwab]
          exact mul_le_mul_of_nonneg_left hIH'
            (mul_nonneg (weight_nonneg hw0 hw1 _) (weight_nonneg hw0 hw1 _))
      _ = _ := by ring

end Graph

end BHK2006

open BHK2006 DecisionTree in
/-- **van den Berg–Häggström–Kahn (2006), Theorem 1.3** — proof of the statement
`BHK2006_clusterConditionalPositiveAssociation`: the open cluster of `s` is conditionally
positively associated given `{s ↮ X}`.  Obtained from the functional Theorem 1.1
(`BHK2006.core`) with `Y = X` (BHK's Theorem 1.2) and `F, G` shifted to be nonnegative, after
identifying `prodBernoulli w` on the finite type `Set (Sym2 V)` with the finite weighted sum.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6), Thm. 1.2 (p. 5), Thm. 1.1 (pp. 3–5)] -/
theorem BHK2006_clusterConditionalPositiveAssociation_holds :
    BHK2006_clusterConditionalPositiveAssociation := by
  intro V _ w s X F G hF hG hs
  classical
  set D : Set (BondConfig V) := {ω | ∀ x ∈ X, ¬ (openGraph ω).Reachable s x} with hD
  have hDm : MeasurableSet D := MeasurableSet.of_discrete
  set w' : Sym2 V → ℝ := fun e => (w e : ℝ) with hw'
  have hw0 : ∀ e, 0 ≤ w' e := fun e => (w e).2.1
  have hw1 : ∀ e, w' e ≤ 1 := fun e => (w e).2.2
  -- the integrals as finite sums
  have hint : ∀ h : Set (Sym2 V) → ℝ,
      ∫ ω in D, h ω ∂(prodBernoulli w) = ∑ ω, weight w' ω * (h ω * ind D ω) := by
    intro h
    rw [← integral_indicator hDm, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, mul_one]
    · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω]; ring
  have hreal : (prodBernoulli w).real D = ∑ ω, weight w' ω * ind D ω := by
    rw [← integral_indicator_one hDm, integral_prodBernoulli_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    by_cases hω : ω ∈ D
    · rw [Set.indicator_of_mem hω, ind_of_mem hω, Pi.one_apply]
    · rw [Set.indicator_of_notMem hω, ind_of_not_mem hω, mul_zero]
  have hm : ∑ ω, weight w' ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  -- `U = univ`: the restricted quantities are the original ones
  have hE : ∀ ω : Set (Sym2 V), ω ∩ edgesIn (Finset.univ : Finset V) = ω := fun ω => by
    ext e
    simp only [Set.mem_inter_iff, edgesIn, Set.mem_setOf_eq, Finset.mem_univ, imp_true_iff,
      and_true]
  have hC : ∀ ω, rC Finset.univ s ω = openEdgeCluster ω s := fun ω => by
    simp only [rC, hE]
  have hDD : rD Finset.univ s X = D := by
    ext ω
    simp only [rD, hE, hD, Set.mem_setOf_eq]
  -- Theorem 1.1 with `Y = X` for the shifted (nonnegative) functions
  have hXU : X ⊆ ↑(Finset.univ : Finset V) := by simp
  have key := core w' hw0 hw1 hm Finset.univ s (Finset.mem_univ s) X X hXU hXU
    (fun a => F a - F ∅) (fun a => G a - G ∅)
    (fun a b hab => sub_le_sub_right (hF hab) _) (fun a b hab => sub_le_sub_right (hG hab) _)
    (fun a => sub_nonneg.2 (hF (Set.empty_subset a)))
    (fun a => sub_nonneg.2 (hG (Set.empty_subset a)))
  rw [Set.inter_self, Set.union_self] at key
  simp only [hC, hDD] at key
  -- expand the shifted sums
  set P := ∑ ω, weight w' ω * ind D ω with hP
  set Ef := ∑ ω, weight w' ω * (F (openEdgeCluster ω s) * ind D ω) with hEf
  set Eg := ∑ ω, weight w' ω * (G (openEdgeCluster ω s) * ind D ω) with hEg
  set Efg := ∑ ω, weight w' ω * (F (openEdgeCluster ω s) * G (openEdgeCluster ω s) * ind D ω)
    with hEfg
  have x1 : ∑ ω, weight w' ω * ((F (openEdgeCluster ω s) - F ∅) * ind D ω) = Ef - F ∅ * P := by
    have := sum_affine w' (fun ω => (F (openEdgeCluster ω s) - F ∅) * ind D ω)
      (fun ω => F (openEdgeCluster ω s) * ind D ω) (ind D) (ind D) (ind D) 1 (-F ∅) 0 0
      (fun ω => by ring)
    rw [this]; ring
  have x2 : ∑ ω, weight w' ω * ((G (openEdgeCluster ω s) - G ∅) * ind D ω) = Eg - G ∅ * P := by
    have := sum_affine w' (fun ω => (G (openEdgeCluster ω s) - G ∅) * ind D ω)
      (fun ω => G (openEdgeCluster ω s) * ind D ω) (ind D) (ind D) (ind D) 1 (-G ∅) 0 0
      (fun ω => by ring)
    rw [this]; ring
  have x3 : ∑ ω, weight w' ω * ((F (openEdgeCluster ω s) - F ∅) * (G (openEdgeCluster ω s) - G ∅)
      * ind D ω) = Efg - F ∅ * Eg - G ∅ * Ef + F ∅ * G ∅ * P := by
    have := sum_affine w'
      (fun ω => (F (openEdgeCluster ω s) - F ∅) * (G (openEdgeCluster ω s) - G ∅) * ind D ω)
      (fun ω => F (openEdgeCluster ω s) * G (openEdgeCluster ω s) * ind D ω)
      (fun ω => G (openEdgeCluster ω s) * ind D ω) (fun ω => F (openEdgeCluster ω s) * ind D ω)
      (ind D) 1 (-F ∅) (-G ∅) (F ∅ * G ∅) (fun ω => by ring)
    rw [this]; ring
  rw [x1, x2, x3] at key
  -- conclude
  rw [hint, hint, hint (fun ω => F (openEdgeCluster ω s) * G (openEdgeCluster ω s)), hreal]
  show Ef * Eg ≤ P * Efg
  nlinarith [key]

end Percolation.Literature
