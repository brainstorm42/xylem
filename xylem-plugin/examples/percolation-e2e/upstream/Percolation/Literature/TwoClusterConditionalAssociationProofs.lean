import Percolation.Literature.ConditionalPositiveAssociationProofs
import Percolation.Literature.TwoClusterConditionalAssociation
import Percolation.Util.Linter

/-!
# Proof of van den Berg–Häggström–Kahn (2006), Theorem 1.5

Proves the statement
`Percolation.Literature.BHK2006_twoClusterConditionalAssociation`
(file `TwoClusterConditionalAssociation.lean`): given `{s ↮ t}`, functions of `(C_s, C_t)` that
are increasing in the open edge cluster `C_s` and decreasing in `C_t` are positively associated
(Bernoulli bond percolation with arbitrary edge probabilities on a finite vertex set, in the
denominator-free form `(∫_D f)(∫_D g) ≤ μ(D) ∫_D f g`, `D = {s ↮ t}`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9)), proof pp. 7–8]

## The printed proof (pp. 7–8) and how it is mirrored here

BHK: "it is enough to prove this for finite `G`.  We have
**(10)** `E[f g | s ↮ t] = Σ_W Pr(C_s = W | s ↮ t) E[f g | C_s = W]`, where we may restrict to
`W` containing no `(s, t)`-path.  Write `W̄` for the union of `W` and its boundary … When we
condition on `{C_s = W}`, `f` and `g` become decreasing functions of `C_t`, and the (conditional)
distribution of `C_t` is the same as that for the restriction of our percolation model to the
graph obtained from `G` by deleting all edges in `W̄`.  Thus (on `{C_s = W}`) `f, g` are
decreasing functions of the independent r.v.'s `(ω_e : e ∈ E ∖ W̄)`, and by Harris' inequality
`E[f g | C_s = W] ≥ E[f | C_s = W] E[g | C_s = W]`.  On the other hand, the conditional
distribution of `C_t` given `{C_s = W}` is stochastically decreasing in `W` (to couple these
distributions, choose all `ω_e`'s independently according to their `p_e`'s and then for
conditioning on `{C_s = W}` simply ignore those `ω_e`'s with `e ∈ W̄`); so in particular
`E[f | C_s = W]` and `E[g | C_s = W]` are increasing functions of `W`, and it then follows from
Theorem 1.3 that the right hand side of (10) is not less than
`[Σ_W Pr(C_s = W | s ↮ t) E[f | C_s = W]] [Σ_W Pr(C_s = W | s ↮ t) E[g | C_s = W]]`
`= E[f | s ↮ t] E[g | s ↮ t]`."

Lean, in the finite-sum language of `ConditionalPositiveAssociationProofs.lean`
(`BHK2006.weight`, `BHK2006.blockFubini`, `BHK2006.harris_anti_anti`,
`BHK2006.integral_prodBernoulli_eq_sum`) and with Theorem 1.3 =
`BHK2006_clusterConditionalPositiveAssociation_holds`:

* `W̄` is written out as the set of pairs meeting the vertex set `{s} ∪ V(W)`,
  `W̄ = {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}` (this also contains the pairs at `s`, which
  BHK's `W̄` omits for `W = ∅`; with them `{C_s = W}` is determined by the coordinates in `W̄`
  for every `W`, `BHK2006.openEdgeCluster_eq_of_agree`); no auxiliary definitions are
  introduced, the set is spelled out in each statement;
* BHK's coupling is the map `η ↦ C_t(η ∖ W̄) = openEdgeCluster (η \ W̄) t`: on
  `{C_s = W} ∩ {s ↮ t}` it computes `C_t` (`BHK2006.openEdgeCluster_eq_sdiff_bar`), it is
  increasing in `η` and decreasing in `W` (`openEdgeCluster_mono`, `BHK2006.bar_mono`), so that
  `E[H(W, C_t) | C_s = W] = Σ_η weight(η) H(W, C_t(η ∖ W̄))` is increasing in `W` for `H`
  increasing in its first and decreasing in its second argument (`BHK2006.condAvg_mono`), and
  Harris gives `E[F | C_s = W] E[G | C_s = W] ≤ E[F G | C_s = W]` (`BHK2006.condAvg_mul_le`);
* display (10) together with the domain Markov property is the exact identity
  `BHK2006.sum_cond_cluster` (`E[H(C_s, C_t) 1_D] = E[E[H | C_s] 1_D]`), proved from
  `blockFubini` with the block `A = W̄`, one `W` at a time;
* the final chain is Theorem 1.3 with `X = {t}` applied to `W ↦ E[f | C_s = W]`,
  `W ↦ E[g | C_s = W]`, followed by Harris termwise.
-/

noncomputable section

open MeasureTheory unitInterval
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

namespace BHK2006

open scoped Classical
open DecisionTree (ind ind_of_mem ind_of_not_mem ind_nonneg)

/-! ### `W̄` and the coupling of `C_t` given `C_s = W` -/

section Graph

variable {V : Type*}

/-- `W̄ = {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}` (the pairs meeting `{s} ∪ V(W)`; BHK: "all edges
having at least one vertex in common with some edge of `W`") is increasing in `W`.
[cite: VandenbergHaggstromKahn2005, §1 p. 8 (definition of `W̄`)] -/
theorem bar_mono (s : V) :
    Monotone fun W : Set (Sym2 V) => {e : Sym2 V | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'} := by
  rintro W W' h e ⟨v, hv, hvK⟩
  exact ⟨v, hv, hvK.imp id fun ⟨e', he', hve'⟩ => ⟨e', h he', hve'⟩⟩

/-- Deleting the pairs of `B` twice is deleting them once: the cluster of `t` off `B` only depends
on the coordinates off `B`. [folklore] -/
theorem openEdgeCluster_sdiff_sdiff (t : V) (B η : Set (Sym2 V)) :
    openEdgeCluster ((η \ B) \ B) t = openEdgeCluster (η \ B) t := by
  rw [Set.sdiff_sdiff, Set.union_self]

/-- **Locality of `{C_s = W}`**: the event `{C_s = W}` is determined by the coordinates in `W̄`
(two configurations agreeing on `W̄` lie in it together).
[cite: VandenbergHaggstromKahn2005, §1 p. 8 (conditioning on `{C_s = W}`)] -/
theorem openEdgeCluster_eq_of_agree {s : V} {W ω ω' : Set (Sym2 V)}
    (hag : ∀ e : Sym2 V, (∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e') → (e ∈ ω ↔ e ∈ ω'))
    (hW : openEdgeCluster ω s = W) : openEdgeCluster ω' s = W := by
  have hK : ∀ v, (openGraph ω).Reachable s v ↔ v = s ∨ ∃ e ∈ W, v ∈ e := fun v => by
    rw [reachable_iff_exists_mem_openEdgeCluster, hW]
  -- reachability from `s` agrees in `ω` and `ω'`
  have h1 : ∀ v, (openGraph ω').Reachable s v → (openGraph ω).Reachable s v := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl s
    | @tail b c _ hbc ih =>
      obtain ⟨hω', hne⟩ := (openGraph_adj ω' b c).1 hbc
      exact ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj ω b c).2
        ⟨(hag _ ⟨b, Sym2.mem_mk_left b c, (hK b).1 ih⟩).2 hω', hne⟩))
  have h2 : ∀ v, (openGraph ω).Reachable s v → (openGraph ω').Reachable s v := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl s
    | @tail b c hab hbc ih =>
      obtain ⟨hω, hne⟩ := (openGraph_adj ω b c).1 hbc
      have hb : (openGraph ω).Reachable s b := (SimpleGraph.reachable_iff_reflTransGen s b).2 hab
      exact ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj ω' b c).2
        ⟨(hag _ ⟨b, Sym2.mem_mk_left b c, (hK b).1 hb⟩).1 hω, hne⟩))
  rw [← hW]
  ext e
  rw [mem_openEdgeCluster_iff, mem_openEdgeCluster_iff]
  constructor
  · rintro ⟨he', hd, hr⟩
    have hr' : ∀ v ∈ e, (openGraph ω).Reachable s v := fun v hv => h1 v (hr v hv)
    exact ⟨(hag e ⟨e.out.1, Sym2.out_fst_mem e, (hK _).1 (hr' _ (Sym2.out_fst_mem e))⟩).2 he',
      hd, hr'⟩
  · rintro ⟨he, hd, hr⟩
    exact ⟨(hag e ⟨e.out.1, Sym2.out_fst_mem e, (hK _).1 (hr _ (Sym2.out_fst_mem e))⟩).1 he,
      hd, fun v hv => h2 v (hr v hv)⟩

/-- `{C_s = W}` is a cylinder event on `W̄`: `C_s(ω ∩ W̄) = W ↔ C_s(ω) = W`. [folklore] -/
theorem openEdgeCluster_inter_bar_eq_iff (s : V) (W ω : Set (Sym2 V)) :
    openEdgeCluster (ω ∩ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) s = W ↔
      openEdgeCluster ω s = W :=
  ⟨fun h => openEdgeCluster_eq_of_agree (ω := ω ∩ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})
      (ω' := ω) (fun _ he => ⟨fun h' => h'.1, fun h' => ⟨h', he⟩⟩) h,
    fun h => openEdgeCluster_eq_of_agree (ω := ω)
      (ω' := ω ∩ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})
      (fun _ he => ⟨fun h' => ⟨h', he⟩, fun h' => h'.1⟩) h⟩

/-- **`C_t` given `C_s = W`**: on `{C_s = W}` with `t ∉ {s} ∪ V(W)` (i.e. `s ↮ t`), the open
cluster of `t` is the open cluster of `t` in the configuration with the pairs of `W̄` deleted
("the (conditional) distribution of `C_t` is the same as that for the restriction of our
percolation model to the graph obtained from `G` by deleting all edges in `W̄`").
[cite: VandenbergHaggstromKahn2005, §1 p. 8 (proof of Thm. 1.5)] -/
theorem openEdgeCluster_eq_sdiff_bar {s t : V} {W ω : Set (Sym2 V)}
    (hW : openEdgeCluster ω s = W) (ht : ¬ (t = s ∨ ∃ e ∈ W, t ∈ e)) :
    openEdgeCluster ω t = openEdgeCluster (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t := by
  have hK : ∀ v, (openGraph ω).Reachable s v ↔ v = s ∨ ∃ e ∈ W, v ∈ e := fun v => by
    rw [reachable_iff_exists_mem_openEdgeCluster, hW]
  -- a vertex joined to `t` is not in `{s} ∪ V(W)`
  have hnot : ∀ v, (openGraph ω).Reachable t v → ¬ (v = s ∨ ∃ e ∈ W, v ∈ e) := fun v hv hvK =>
    ht ((hK t).1 (((hK v).2 hvK).trans hv.symm))
  have hreach : ∀ v, (openGraph ω).Reachable t v →
      (openGraph (ω \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'})).Reachable t v := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact SimpleGraph.Reachable.refl t
    | @tail b c hab hbc ih =>
      obtain ⟨hω, hne⟩ := (openGraph_adj ω b c).1 hbc
      have hb : (openGraph ω).Reachable t b := (SimpleGraph.reachable_iff_reflTransGen t b).2 hab
      have hbK := hnot b hb
      have hcK := hnot c (hb.trans hbc.reachable)
      refine ih.trans (SimpleGraph.Adj.reachable ((openGraph_adj _ b c).2 ⟨⟨hω, ?_⟩, hne⟩))
      rintro ⟨v, hv, hvK⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact hbK hvK
      · exact hcK hvK
  apply Set.Subset.antisymm
  · intro e he
    rw [mem_openEdgeCluster_iff] at he
    obtain ⟨he, hd, hr⟩ := he
    refine (mem_openEdgeCluster_iff _ _ _).2 ⟨⟨he, ?_⟩, hd, fun v hv => hreach v (hr v hv)⟩
    rintro ⟨v, hv, hvK⟩
    exact hnot v (hr v hv) hvK
  · exact openEdgeCluster_mono Set.sdiff_subset t

end Graph

/-! ### Conditional expectations given `C_s = W` as finite sums -/

section Sums

variable {V : Type*} [Fintype V]

/-- "`E[f | C_s = W]` and `E[g | C_s = W]` are increasing functions of `W`": for `H` increasing in
its first and decreasing in its second argument and an increasing family of deleted sets `B W`
(here `B W = W̄`), `W ↦ Σ_η weight(η) H(W, C_t(η ∖ B W))` is increasing.
[cite: VandenbergHaggstromKahn2005, §1 p. 8] -/
theorem condAvg_mono {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1) (t : V)
    {B : Set (Sym2 V) → Set (Sym2 V)} (hB : Monotone B) {H : Set (Sym2 V) → Set (Sym2 V) → ℝ}
    (hH1 : ∀ D, Monotone fun C => H C D) (hH2 : ∀ C, Antitone fun D => H C D) :
    Monotone fun W => ∑ η, weight w η * H W (openEdgeCluster (η \ B W) t) := by
  intro W W' hWW'
  refine Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hw0 hw1 η)
  exact (hH1 _ hWW').trans
    (hH2 W' (openEdgeCluster_mono (Set.sdiff_subset_sdiff_right (hB hWW')) t))

/-- "by Harris' inequality we have `E[f g | C_s = W] ≥ E[f | C_s = W] E[g | C_s = W]`": given
`C_s = W`, `f, g` are decreasing functions of the fresh variables `η` off the deleted set `B`
(here `B = W̄`). [cite: VandenbergHaggstromKahn2005, §1 p. 8] -/
theorem condAvg_mul_le {w : Sym2 V → ℝ} (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (hm : ∑ ω, weight w ω = 1) (t : V) (B : Set (Sym2 V))
    {F G : Set (Sym2 V) → Set (Sym2 V) → ℝ}
    (hF2 : ∀ C, Antitone fun D => F C D) (hG2 : ∀ C, Antitone fun D => G C D)
    (W : Set (Sym2 V)) :
    (∑ η, weight w η * F W (openEdgeCluster (η \ B) t)) *
        ∑ η, weight w η * G W (openEdgeCluster (η \ B) t) ≤
      ∑ η, weight w η * (F W (openEdgeCluster (η \ B) t) * G W (openEdgeCluster (η \ B) t)) :=
  harris_anti_anti hw0 hw1 hm (f := fun η => F W (openEdgeCluster (η \ B) t))
    (g := fun η => G W (openEdgeCluster (η \ B) t))
    (fun _ _ hab => hF2 W (openEdgeCluster_mono (Set.sdiff_subset_sdiff_left hab) t))
    (fun _ _ hab => hG2 W (openEdgeCluster_mono (Set.sdiff_subset_sdiff_left hab) t))
    (M := F W ∅) (N := G W ∅)
    (fun _ => hF2 W (Set.empty_subset _)) (fun _ => hG2 W (Set.empty_subset _))

/-- **BHK's display (10) with the domain Markov property**: for any `H`,
`E[H(C_s, C_t) 1{s ↮ t}] = Σ_W P(C_s = W, s ↮ t) E[H(W, C_t) | C_s = W]`, with
`E[H(W, C_t) | C_s = W] = Σ_η weight(η) H(W, C_t(η ∖ W̄))` computed in fresh variables off `W̄`.
[cite: VandenbergHaggstromKahn2005, §1 pp. 7–8, display (10) and the paragraph following it] -/
theorem sum_cond_cluster (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (s t : V)
    (H : Set (Sym2 V) → Set (Sym2 V) → ℝ) {D : Set (Set (Sym2 V))}
    (hD : ∀ ω, ω ∈ D ↔ ¬ (openGraph ω).Reachable s t) :
    ∑ ω, weight w ω * (H (openEdgeCluster ω s) (openEdgeCluster ω t) * ind D ω) =
      ∑ ω, weight w ω * ((∑ η, weight w η * H (openEdgeCluster ω s) (openEdgeCluster
        (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t)) * ind D ω) := by
  -- the identity on each event `{C_s = W}`
  have key : ∀ W : Set (Sym2 V),
      ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * (H W (openEdgeCluster ω t) * ind D ω) else 0) =
      ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * ((∑ η, weight w η * H W (openEdgeCluster
            (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t)) * ind D ω) else 0) := by
    intro W
    by_cases ht : t = s ∨ ∃ e ∈ W, t ∈ e
    · -- on `{C_s = W}`, `s ↔ t`: both sides vanish termwise
      refine Finset.sum_congr rfl fun ω _ => ?_
      split_ifs with hW
      · have hr : (openGraph ω).Reachable s t := by
          rw [reachable_iff_exists_mem_openEdgeCluster, hW]; exact ht
        simp only [ind_of_not_mem (fun h => (hD ω).1 h hr), mul_zero]
      · rfl
    · -- block Fubini with the block `A = W̄`
      set A : Set (Sym2 V) := {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'} with hA
      set Φ : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun ζ η =>
        if openEdgeCluster ζ s = W then H W (openEdgeCluster (η \ A) t) else 0 with hΦ
      have hind : ∀ ω, openEdgeCluster ω s = W → ind D ω = 1 := fun ω hW =>
        ind_of_mem ((hD ω).2 (by rw [reachable_iff_exists_mem_openEdgeCluster, hW]; exact ht))
      have h1 : ∀ ω, (if openEdgeCluster ω s = W then
          weight w ω * (H W (openEdgeCluster ω t) * ind D ω) else 0) =
          weight w ω * Φ (ω ∩ A) (ω \ A) := by
        intro ω
        simp only [hΦ, hA, openEdgeCluster_inter_bar_eq_iff, openEdgeCluster_sdiff_sdiff]
        split_ifs with hW
        · rw [hind ω hW, mul_one, openEdgeCluster_eq_sdiff_bar hW ht]
        · rw [mul_zero]
      have h2 : ∀ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) =
          (if openEdgeCluster ω s = W then
            weight w ω * ((∑ η, weight w η * H W (openEdgeCluster (η \ A) t)) * ind D ω)
          else 0) := by
        intro ω
        simp only [hΦ, hA, openEdgeCluster_inter_bar_eq_iff, openEdgeCluster_sdiff_sdiff]
        split_ifs with hW
        · rw [hind ω hW, mul_one]
        · simp
      calc ∑ ω, (if openEdgeCluster ω s = W then
              weight w ω * (H W (openEdgeCluster ω t) * ind D ω) else 0)
          = (∑ ω, weight w ω) * ∑ ω, weight w ω * Φ (ω ∩ A) (ω \ A) := by
            rw [hm, one_mul]; exact Finset.sum_congr rfl fun ω _ => h1 ω
        _ = ∑ ω, weight w ω * ∑ ω', weight w ω' * Φ (ω ∩ A) (ω' \ A) := blockFubini w A Φ
        _ = _ := Finset.sum_congr rfl fun ω _ => h2 ω
  -- sum over `W`
  calc ∑ ω, weight w ω * (H (openEdgeCluster ω s) (openEdgeCluster ω t) * ind D ω)
      = ∑ ω, ∑ W, (if openEdgeCluster ω s = W then
          weight w ω * (H W (openEdgeCluster ω t) * ind D ω) else 0) :=
        Finset.sum_congr rfl fun ω _ => (Fintype.sum_ite_eq (openEdgeCluster ω s)
          fun W => weight w ω * (H W (openEdgeCluster ω t) * ind D ω)).symm
    _ = ∑ W, ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * (H W (openEdgeCluster ω t) * ind D ω) else 0) := Finset.sum_comm
    _ = ∑ W, ∑ ω, (if openEdgeCluster ω s = W then
          weight w ω * ((∑ η, weight w η * H W (openEdgeCluster
            (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t)) * ind D ω) else 0) :=
        Finset.sum_congr rfl fun W _ => key W
    _ = ∑ ω, ∑ W, (if openEdgeCluster ω s = W then
          weight w ω * ((∑ η, weight w η * H W (openEdgeCluster
            (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t)) * ind D ω) else 0) :=
        Finset.sum_comm
    _ = _ :=
        Finset.sum_congr rfl fun ω _ => Fintype.sum_ite_eq (openEdgeCluster ω s)
          fun W => weight w ω * ((∑ η, weight w η * H W (openEdgeCluster
            (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t)) * ind D ω)

end Sums

end BHK2006

open BHK2006 DecisionTree in
/-- **van den Berg–Häggström–Kahn (2006), Theorem 1.5** — proof of the statement
`BHK2006_twoClusterConditionalAssociation`: given `{s ↮ t}`, functions of `(C_s, C_t)` increasing
in `C_s` and decreasing in `C_t` are positively associated.  Printed proof (pp. 7–8): condition
on `C_s = W` (display (10)); given `C_s = W` the cluster `C_t` is that of the model with `W̄`
deleted, so Harris applies in the fresh variables; `E[f | C_s = W]` is increasing in `W` by the
"ignore `ω_e`, `e ∈ W̄`" coupling; conclude with Theorem 1.3 (`X = {t}`), here the proved
`BHK2006_clusterConditionalPositiveAssociation_holds`.
[cite: VandenbergHaggstromKahn2005, Thm. 1.5 (p. 7, eq. (9)), proof pp. 7–8] -/
theorem BHK2006_twoClusterConditionalAssociation_holds :
    BHK2006_twoClusterConditionalAssociation := by
  intro V _ w s t F G hF1 hF2 hG1 hG2 hst
  classical
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable s t} with hD
  have hDmem : ∀ ω, ω ∈ D ↔ ¬ (openGraph ω).Reachable s t := fun ω => by rw [hD]; rfl
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
  -- `E[f | C_s = W]`, `E[g | C_s = W]` are increasing in `W`: Theorem 1.3 with `X = {t}`
  have hf₁ : Monotone fun W => ∑ η, weight w' η *
      F W (openEdgeCluster (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t) :=
    condAvg_mono hw0 hw1 t (bar_mono s) hF1 hF2
  have hg₁ : Monotone fun W => ∑ η, weight w' η *
      G W (openEdgeCluster (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t) :=
    condAvg_mono hw0 hw1 t (bar_mono s) hG1 hG2
  have h13 := BHK2006_clusterConditionalPositiveAssociation_holds V w s ({t} : Set V)
    (fun W => ∑ η, weight w' η *
      F W (openEdgeCluster (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t))
    (fun W => ∑ η, weight w' η *
      G W (openEdgeCluster (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ W, v ∈ e'}) t))
    hf₁ hg₁ (by simpa using hst)
  have hDt : {ω : BondConfig V | ∀ x ∈ ({t} : Set V), ¬ (openGraph ω).Reachable s x} = D := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, forall_eq, hDmem]
  rw [hDt] at h13
  rw [hint, hint, hint (fun ω =>
    (∑ η, weight w' η * F (openEdgeCluster ω s) (openEdgeCluster
      (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t)) *
    ∑ η, weight w' η * G (openEdgeCluster ω s) (openEdgeCluster
      (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t)), hreal] at h13
  -- the three integrals of the goal, conditioned on `C_s` (display (10))
  rw [hint (fun ω => F (openEdgeCluster ω s) (openEdgeCluster ω t)),
    hint (fun ω => G (openEdgeCluster ω s) (openEdgeCluster ω t)),
    hint (fun ω => F (openEdgeCluster ω s) (openEdgeCluster ω t) *
      G (openEdgeCluster ω s) (openEdgeCluster ω t)), hreal]
  have e1 := sum_cond_cluster w' hm s t F hDmem
  have e2 := sum_cond_cluster w' hm s t G hDmem
  have e3 := sum_cond_cluster w' hm s t (fun C C' => F C C' * G C C') hDmem
  -- Harris on each `{C_s = W}`
  have hH : ∑ ω, weight w' ω *
      ((∑ η, weight w' η * F (openEdgeCluster ω s) (openEdgeCluster
        (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t)) *
      (∑ η, weight w' η * G (openEdgeCluster ω s) (openEdgeCluster
        (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t)) * ind D ω) ≤
      ∑ ω, weight w' ω * ((∑ η, weight w' η *
        (F (openEdgeCluster ω s) (openEdgeCluster
          (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t) *
        G (openEdgeCluster ω s) (openEdgeCluster
          (η \ {e | ∃ v ∈ e, v = s ∨ ∃ e' ∈ openEdgeCluster ω s, v ∈ e'}) t))) * ind D ω) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (condAvg_mul_le hw0 hw1 hm t _ hF2 hG2 _) (ind_nonneg _ _))
      (weight_nonneg hw0 hw1 ω)
  have hP : 0 ≤ ∑ ω, weight w' ω * ind D ω :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (weight_nonneg hw0 hw1 ω) (ind_nonneg _ _)
  show (∑ ω, weight w' ω * (F (openEdgeCluster ω s) (openEdgeCluster ω t) * ind D ω)) *
      (∑ ω, weight w' ω * (G (openEdgeCluster ω s) (openEdgeCluster ω t) * ind D ω)) ≤
    (∑ ω, weight w' ω * ind D ω) *
      ∑ ω, weight w' ω * (F (openEdgeCluster ω s) (openEdgeCluster ω t) *
        G (openEdgeCluster ω s) (openEdgeCluster ω t) * ind D ω)
  rw [e1, e2, e3]
  exact h13.trans (mul_le_mul_of_nonneg_left hH hP)

end Percolation.Literature
