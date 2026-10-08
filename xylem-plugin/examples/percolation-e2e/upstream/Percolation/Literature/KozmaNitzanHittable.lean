import Percolation.Literature.KozmaNitzanTargetLemma
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — toolkit III: restricted weightings, wired sources, quarter faces

Fourth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a
conjectured inequality*, arXiv:2401.12397, §4), on the way from the target lemma (Lemma 10,
`KozmaNitzanTargetLemma.lean`) to Lemmas 11–12 and the exploration process of pp. 25–31.

The printed proof constantly passes to sub- and quotient graphs ("the graph `Ω` which one gets by
taking `[-r, Kr] × [-r, r]^{d-1}` and identifying the cube `[-n, n]^d` to a point", p. 22; "we
apply lemma 10 … in the subgraph `A`", p. 24; "our conditioned percolation is equivalent to usual
percolation on an auxiliary graph", p. 28). As in `KozmaNitzanPinning.lean` these operations are
realised as changes of WEIGHTS on the fixed configuration space `Set (Sym2 (Site d))`:

* `restrW S w` — the weighting `w` restricted to the pairs inside `S` (all other pairs get weight
  `0`): `prodBernoulli (restrW S w)` is percolation on the subgraph induced by `S`, and
  `prodBernoulli_restrW_real_biUnion_openConn` identifies its connection events with the
  "`o ↔ T` in `S`" events (`openConnIn`) of `prodBernoulli w`; `finSupp_restrW`,
  `IsSubbox.restrW`, `IsSubbox.pinW`, `isSubbox_lattW` feed the hypotheses of the target lemma;
* `prodBernoulli_wireW_real_biUnion_openConn` — the wiring identity of `KozmaNitzanPinning.lean`
  (`P_{wire C}(c₀ ↔ t) = P(C ↔ t)`) for a target SET;
* `qfGeom a τ` — the quarter-face geometry (`Q = [-1,1]^d`, `F` = the face orthant of direction
  `a`, signs `τ`), and `isHittable_qfGeom` — KN's Lemma 9 ("the basic example of a hittable
  geometry", p. 16) in the form `IsHittable` consumed by `targetLemma`, read off this library's
  `exists_forall_lt_real_linked_orthantFace` (Grimmett (7.14)–(7.16): FKG square-root trick and
  symmetry).

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 p. 16 (hittable geometries, Lemma 9), p. 22,
  p. 24, p. 28.
* G. Grimmett, *Percolation*, 2nd ed. (1999), §7.2 (7.14)–(7.16).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature

open LatticeModels SimpleGraph

/-! ## Unions of connection events: determination, measurability, monotonicity -/

section Unions

variable {V : Type*}

/-- A union of events each determined by `K` is determined by `K`. [folklore] -/
theorem determinedBy_biUnion {ι : Type*} {K : Set (Sym2 V)} {I : Set ι} {A : ι → Set (BondConfig V)}
    (h : ∀ i ∈ I, DeterminedBy (A i) K) : DeterminedBy (⋃ i ∈ I, A i) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  simp only [Set.mem_iUnion, exists_prop]
  refine exists_congr fun i => and_congr_right fun hi => ?_
  exact (determinedBy_iff _ _).1 (h i hi) ω ω' hω

/-- `{o ↔ T in S}` is determined by the off-diagonal pairs inside `S`. [cite: GrimmettPercolation1999, §2.2] -/
theorem determinedBy_biUnion_openConnIn (S : Set V) (o : V) (T : Set V) {K : Set (Sym2 V)}
    (hK : wireSet S ⊆ K) : DeterminedBy (⋃ t ∈ T, openConnIn S o t) K :=
  determinedBy_biUnion fun t _ => KozmaNitzan.determinedBy_openConnIn_wireSet S o t hK

/-- `{o ↔ T in S}` is measurable (`V` countable). [folklore] -/
theorem measurableSet_biUnion_openConnIn [Countable V] (S : Set V) (o : V) (T : Set V) :
    MeasurableSet (⋃ t ∈ T, openConnIn S o t : Set (BondConfig V)) :=
  MeasurableSet.biUnion (Set.to_countable T) fun t _ => measurableSet_openConnIn_of_countable S o t

/-- `{o ↔ T in S}` is monotone in `S` and `T`. [folklore] -/
theorem biUnion_openConnIn_mono {S S' : Set V} (hS : S ⊆ S') (o : V) {T T' : Set V} (hT : T ⊆ T') :
    (⋃ t ∈ T, openConnIn S o t : Set (BondConfig V)) ⊆ ⋃ t ∈ T', openConnIn S' o t := by
  intro ω hω
  simp only [Set.mem_iUnion, exists_prop] at hω ⊢
  obtain ⟨t, ht, h⟩ := hω
  refine ⟨t, hT ht, ?_⟩
  rw [DCT16.mem_openConnIn_iff_pathIn] at h ⊢
  exact h.mono hS

/-- `{o ↔ T in S} ⊆ {o ↔ T}`. [folklore] -/
theorem biUnion_openConnIn_subset_biUnion_openConn (S : Set V) (o : V) (T : Set V) :
    (⋃ t ∈ T, openConnIn S o t : Set (BondConfig V)) ⊆ ⋃ t ∈ T, openConn o t := by
  intro ω hω
  simp only [Set.mem_iUnion, exists_prop] at hω ⊢
  obtain ⟨t, ht, h⟩ := hω
  refine ⟨t, ht, ?_⟩
  rw [DCT16.mem_openConnIn_iff_pathIn] at h
  exact reachable_of_pathIn h

/-- `{x ↔ y} = {y ↔ x}`. [folklore] -/
theorem openConn_comm (x y : V) : (openConn x y : Set (BondConfig V)) = openConn y x := by
  ext ω
  exact ⟨fun h => SimpleGraph.Reachable.symm h, fun h => SimpleGraph.Reachable.symm h⟩

end Unions

/-! ## Restricted weightings: percolation on an induced subgraph -/

section Restrict

variable {V : Type*}

open Classical in
/-- **Restricted weights**: the pairs inside `S` keep their weight, all other pairs get weight `0`
(Kozma–Nitzan 2024, p. 24: "we apply lemma 10 … in the subgraph `A`"; p. 22: the graph `Ω`
obtained from a box of `ℤ^d`). [cite: KozmaNitzan2024, §4 p. 24 (the subgraph A)] -/
def restrW (S : Set V) (w : Sym2 V → unitInterval) : Sym2 V → unitInterval :=
  fun e => if e ∈ wireSet S then w e else 0

/-- Pairs inside `S` keep their weight. [folklore] -/
theorem restrW_apply_of_mem {S : Set V} (w : Sym2 V → unitInterval) {e : Sym2 V} (he : e ∈ wireSet S) :
    restrW S w e = w e := by
  classical
  simp [restrW, he]

/-- Other pairs get weight `0`. [folklore] -/
theorem restrW_apply_of_not_mem {S : Set V} (w : Sym2 V → unitInterval) {e : Sym2 V} (he : e ∉ wireSet S) :
    restrW S w e = 0 := by
  classical
  simp [restrW, he]

/-- Restriction only lowers weights. [folklore] -/
theorem restrW_le (S : Set V) (w : Sym2 V → unitInterval) : restrW S w ≤ w := by
  intro e
  by_cases he : e ∈ wireSet S
  · rw [restrW_apply_of_mem w he]
  · rw [restrW_apply_of_not_mem w he]; exact bot_le

/-- **Restriction and pinning commute** when the pinned pairs lie inside `S`. [folklore] -/
theorem restrW_pinW_comm {S : Set V} (w : Sym2 V → unitInterval) {F : Set (Sym2 V)} (ξ : Set (Sym2 V))
    (hF : F ⊆ wireSet S) : restrW S (pinW w F ξ) = pinW (restrW S w) F ξ := by
  classical
  funext e
  by_cases he : e ∈ wireSet S
  · rw [restrW_apply_of_mem _ he]
    by_cases heF : e ∈ F
    · by_cases heξ : e ∈ ξ
      · rw [pinW_apply_of_mem_of_mem _ heF heξ, pinW_apply_of_mem_of_mem _ heF heξ]
      · rw [pinW_apply_of_mem_of_not_mem _ heF heξ, pinW_apply_of_mem_of_not_mem _ heF heξ]
    · rw [pinW_apply_of_not_mem _ _ heF, pinW_apply_of_not_mem _ _ heF, restrW_apply_of_mem _ he]
  · have heF : e ∉ F := fun h => he (hF h)
    rw [restrW_apply_of_not_mem _ he, pinW_apply_of_not_mem _ _ heF, restrW_apply_of_not_mem _ he]

/-- **The restricted weighting is finitely supported** on `S` (KN's graphs are finite).
[cite: KozmaNitzan2024, Conjecture 1 (p. 3)] -/
theorem finSupp_restrW {d : ℕ} (S : Finset (Site d)) (w : Sym2 (Site d) → unitInterval) :
    KozmaNitzan.FinSupp (restrW (↑S : Set (Site d)) w) S := by
  refine ⟨fun e he => restrW_apply_of_not_mem w fun h => ?_⟩
  obtain ⟨x, hx, hxS⟩ := he
  exact hxS (Finset.mem_coe.1 (h.1 x hx))

/-- An open path all of whose edges lie inside `S`, from a vertex of `S`, is a path inside `S`.
[folklore] -/
theorem pathIn_of_reachable_of_forall_mem_wireSet {ω : BondConfig V} {S : Set V}
    (hω : ∀ e ∈ ω, e ∈ wireSet S) {o t : V} (ho : o ∈ S) (h : (openGraph ω).Reachable o t) :
    PathIn (openGraph ω) S o t := by
  obtain ⟨-, hp⟩ := DCT16.pathIn_univ_of_reachable h
  clear h
  refine ⟨ho, ?_⟩
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine ih.tail ⟨hbc.1, ?_⟩
    have h1 := hbc.1
    rw [openGraph_adj] at h1
    exact (mk_mem_wireSet_iff.1 (hω _ h1.1)).2.1

/-- **Percolation with restricted weights = percolation "in `S`"**: for `o ∈ S`,
`P_{restrW S w}(o ↔ T) = P_w(o ↔ T in S)` (under the restricted law all open pairs lie inside
`S` almost surely, and the "in `S`" event is determined by the pairs inside `S`, where the two
weightings agree). [cite: KozmaNitzan2024, §4 p. 24 (P(o ↔^A ·))] -/
theorem prodBernoulli_restrW_real_biUnion_openConn [Countable V] (w : Sym2 V → unitInterval) (S : Set V)
    {o : V} (ho : o ∈ S) (T : Set V) :
    (prodBernoulli (restrW S w)).real (⋃ t ∈ T, openConn o t) =
      (prodBernoulli w).real (⋃ t ∈ T, openConnIn S o t) := by
  have hae : ∀ᵐ ω ∂prodBernoulli (restrW S w), ∀ e ∈ (wireSet S)ᶜ, e ∉ ω :=
    prodBernoulli_ae_forall_notMem _ (Set.to_countable _) fun e he => restrW_apply_of_not_mem w he
  calc (prodBernoulli (restrW S w)).real (⋃ t ∈ T, openConn o t)
      = (prodBernoulli (restrW S w)).real (⋃ t ∈ T, openConnIn S o t) := by
        refine measureReal_congr ?_
        filter_upwards [hae] with ω hω
        have hω' : ∀ e ∈ ω, e ∈ wireSet S := fun e he => by
          by_contra h; exact hω e h he
        refine propext ?_
        change (ω ∈ ⋃ t ∈ T, openConn o t) ↔ (ω ∈ ⋃ t ∈ T, openConnIn S o t)
        simp only [Set.mem_iUnion, exists_prop]
        refine exists_congr fun t => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
        · rw [DCT16.mem_openConnIn_iff_pathIn]
          exact pathIn_of_reachable_of_forall_mem_wireSet hω' ho h
        · rw [DCT16.mem_openConnIn_iff_pathIn] at h
          exact reachable_of_pathIn h
    _ = (prodBernoulli w).real (⋃ t ∈ T, openConnIn S o t) :=
        prodBernoulli_real_eq_of_determinedBy _ _ (fun _ he => restrW_apply_of_mem w he)
          (determinedBy_biUnion_openConnIn S o T subset_rfl) (measurableSet_biUnion_openConnIn S o T)

/-- Events determined by the pairs inside `S` have the same probability before and after
restriction. [folklore] -/
theorem prodBernoulli_restrW_real_eq_of_determinedBy [Countable V] (w : Sym2 V → unitInterval) (S : Set V)
    {A : Set (BondConfig V)} (hA : DeterminedBy A (wireSet S)) (hAm : MeasurableSet A) :
    (prodBernoulli (restrW S w)).real A = (prodBernoulli w).real A :=
  prodBernoulli_real_eq_of_determinedBy _ _ (fun _ he => restrW_apply_of_mem w he) hA hAm

/-- **Restriction with a source SET**: for `C ⊆ S`,
`P_{restrW S w}(C ↔ T) = P_w(C ↔ T in S)` (as `prodBernoulli_restrW_real_biUnion_openConn`, for the
union over the sources in `C`). [cite: KozmaNitzan2024, §4 p. 22 (Ω), p. 24] -/
theorem prodBernoulli_restrW_real_biUnion₂_openConn [Countable V] (w : Sym2 V → unitInterval) (S : Set V)
    {C : Set V} (hC : C ⊆ S) (T : Set V) :
    (prodBernoulli (restrW S w)).real (⋃ t ∈ T, ⋃ s ∈ C, openConn s t) =
      (prodBernoulli w).real (⋃ t ∈ T, ⋃ s ∈ C, openConnIn S s t) := by
  have hae : ∀ᵐ ω ∂prodBernoulli (restrW S w), ∀ e ∈ (wireSet S)ᶜ, e ∉ ω :=
    prodBernoulli_ae_forall_notMem _ (Set.to_countable _) fun e he => restrW_apply_of_not_mem w he
  have hdet : DeterminedBy (⋃ t ∈ T, ⋃ s ∈ C, openConnIn S s t) (wireSet S) :=
    determinedBy_biUnion fun t _ => determinedBy_biUnion fun s _ =>
      KozmaNitzan.determinedBy_openConnIn_wireSet S s t subset_rfl
  have hmeas : MeasurableSet (⋃ t ∈ T, ⋃ s ∈ C, openConnIn S s t : Set (BondConfig V)) :=
    MeasurableSet.biUnion (Set.to_countable T) fun t _ =>
      MeasurableSet.biUnion (Set.to_countable C) fun s _ => measurableSet_openConnIn_of_countable S s t
  calc (prodBernoulli (restrW S w)).real (⋃ t ∈ T, ⋃ s ∈ C, openConn s t)
      = (prodBernoulli (restrW S w)).real (⋃ t ∈ T, ⋃ s ∈ C, openConnIn S s t) := by
        refine measureReal_congr ?_
        filter_upwards [hae] with ω hω
        have hω' : ∀ e ∈ ω, e ∈ wireSet S := fun e he => by
          by_contra h; exact hω e h he
        refine propext ?_
        change (ω ∈ ⋃ t ∈ T, ⋃ s ∈ C, openConn s t) ↔ (ω ∈ ⋃ t ∈ T, ⋃ s ∈ C, openConnIn S s t)
        simp only [Set.mem_iUnion, exists_prop]
        refine exists_congr fun t => and_congr_right fun _ => exists_congr fun s =>
          and_congr_right fun hs => ⟨fun h => ?_, fun h => ?_⟩
        · rw [DCT16.mem_openConnIn_iff_pathIn]
          exact pathIn_of_reachable_of_forall_mem_wireSet hω' (hC hs) h
        · rw [DCT16.mem_openConnIn_iff_pathIn] at h
          exact reachable_of_pathIn h
    _ = (prodBernoulli w).real (⋃ t ∈ T, ⋃ s ∈ C, openConnIn S s t) :=
        prodBernoulli_real_eq_of_determinedBy _ _ (fun _ he => restrW_apply_of_mem w he) hdet hmeas

/-- Wiring inside `C ⊆ S` and restricting to `S` commute. [folklore] -/
theorem restrW_wireW_comm {S C : Set V} (hC : C ⊆ S) (w : Sym2 V → unitInterval) :
    restrW S (wireW C w) = wireW C (restrW S w) := by
  funext e
  by_cases heC : e ∈ wireSet C
  · have heS : e ∈ wireSet S := ⟨fun x hx => hC (heC.1 x hx), heC.2⟩
    rw [restrW_apply_of_mem _ heS, wireW_apply_of_mem _ heC, wireW_apply_of_mem _ heC]
  · rw [wireW_apply_of_not_mem _ heC]
    by_cases heS : e ∈ wireSet S
    · rw [restrW_apply_of_mem _ heS, restrW_apply_of_mem _ heS, wireW_apply_of_not_mem _ heC]
    · rw [restrW_apply_of_not_mem _ heS, restrW_apply_of_not_mem _ heS]

end Restrict

/-! ## Subboxes of restricted and pinned weightings -/

namespace KozmaNitzan

variable {d : ℕ}

/-- **Every box of `ℤ^d` is a subbox of the lattice weighting.** [cite: KozmaNitzan2024, §4 p. 17 (subbox)] -/
theorem isSubbox_lattW (p : unitInterval) (D : Finset (Site d)) : IsSubbox (lattW d p) p D := by
  refine ⟨fun u _ v _ _ => lattW_mk p u v, fun v hvD hv x hx => ?_⟩
  rw [lattW_mk]
  rw [if_neg]
  intro hadj
  refine hv (mem_innerBoundary_iff.2 ⟨hvD, x, hx, hadj.symm⟩)

/-- Restriction to a set containing `D` preserves subboxes. [cite: KozmaNitzan2024, §4 p. 17 (subbox), p. 24] -/
theorem IsSubbox.restrW {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)}
    (h : IsSubbox W p D) {S : Set (Site d)} (hDS : (↑D : Set (Site d)) ⊆ S) :
    IsSubbox (Percolation.Literature.restrW S W) p D := by
  refine ⟨fun u hu v hv huv => ?_, fun v hvD hv x hx => ?_⟩
  · rw [restrW_apply_of_mem W (mk_mem_wireSet_iff.2 ⟨hDS (Finset.mem_coe.2 hu), hDS (Finset.mem_coe.2 hv), huv⟩)]
    exact h.inside u hu v hv huv
  · have := h.outside v hvD hv x hx
    have hle := restrW_le S W s(x, v)
    rw [this] at hle
    exact le_antisymm hle bot_le

/-- Pinning pairs none of whose endpoints lies in `D` preserves subboxes (KN p. 28: conditioning on
`ω|_{E_i}` away from the subbox). [cite: KozmaNitzan2024, §4 p. 17 (subbox), p. 28] -/
theorem IsSubbox.pinW {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)}
    (h : IsSubbox W p D) {F : Set (Sym2 (Site d))} (ξ : Set (Sym2 (Site d)))
    (hF : ∀ e ∈ F, ∀ x ∈ e, x ∉ D) : IsSubbox (Percolation.Literature.pinW W F ξ) p D := by
  refine ⟨fun u hu v hv huv => ?_, fun v hvD hv x hx => ?_⟩
  · rw [pinW_apply_of_not_mem _ _ (fun he => hF _ he u (Sym2.mem_mk_left u v) hu)]
    exact h.inside u hu v hv huv
  · rw [pinW_apply_of_not_mem _ _ (fun he => hF _ he v (Sym2.mem_mk_right x v) hvD)]
    exact h.outside v hvD hv x hx

/-- Wiring a set of vertices disjoint from `D` preserves subboxes (KN p. 22: the cube identified to
a point lies outside the subbox `D`). [cite: KozmaNitzan2024, §4 p. 17 (subbox), p. 22] -/
theorem IsSubbox.wireW {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)}
    (h : IsSubbox W p D) {C : Set (Site d)} (hCD : ∀ x ∈ C, x ∉ D) :
    IsSubbox (Percolation.Literature.wireW C W) p D := by
  refine ⟨fun u hu v hv huv => ?_, fun v hvD hv x hx => ?_⟩
  · rw [wireW_apply_of_not_mem _ (fun he => hCD u ((mk_mem_wireSet_iff.1 he).1) hu)]
    exact h.inside u hu v hv huv
  · rw [wireW_apply_of_not_mem _ (fun he => hCD v ((mk_mem_wireSet_iff.1 he).2.1) hvD)]
    exact h.outside v hvD hv x hx

/-- A wired, restricted weighting is finitely supported on the restriction set when the wired set
lies inside it. [folklore] -/
theorem finSupp_wireW_restrW (S : Finset (Site d)) {C : Set (Site d)} (hC : C ⊆ ↑S)
    (w : Sym2 (Site d) → unitInterval) :
    FinSupp (Percolation.Literature.wireW C (Percolation.Literature.restrW (↑S : Set (Site d)) w)) S := by
  rw [← restrW_wireW_comm hC]
  exact finSupp_restrW S _

end KozmaNitzan

/-! ## Wiring with a target set -/

section Wire

variable {V : Type*}

/-- The wiring identity for a target SET: `c₀ ∈ C` is joined to `T` in `ω ∪ wireSet C` iff some
vertex of `C` is joined to `T` in `ω`. [cite: KozmaNitzan2024, §4 p. 22] -/
theorem preimage_union_wireSet_biUnion_openConn (C : Set V) {c₀ : V} (hc₀ : c₀ ∈ C) (T : Set V) :
    (fun ω : Set (Sym2 V) => ω ∪ wireSet C) ⁻¹' (⋃ t ∈ T, openConn c₀ t) = ⋃ t ∈ T, ⋃ s ∈ C, openConn s t := by
  ext ω
  simp only [Set.preimage_iUnion, Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨t, ht, h⟩
    have h' : ω ∪ wireSet C ∈ openConn t c₀ := by rw [openConn_comm]; exact h
    have h2 : ω ∈ (fun ω : Set (Sym2 V) => ω ∪ wireSet C) ⁻¹' openConn t c₀ := h'
    rw [preimage_union_wireSet_openConn C hc₀ t] at h2
    simp only [Set.mem_iUnion, exists_prop] at h2
    obtain ⟨s, hs, hts⟩ := h2
    exact ⟨t, ht, s, hs, by rw [openConn_comm]; exact hts⟩
  · rintro ⟨t, ht, s, hs, h⟩
    refine ⟨t, ht, ?_⟩
    have h2 : ω ∈ (fun ω : Set (Sym2 V) => ω ∪ wireSet C) ⁻¹' openConn t c₀ := by
      rw [preimage_union_wireSet_openConn C hc₀ t]
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨s, hs, by rw [openConn_comm]; exact h⟩
    have h3 : ω ∪ wireSet C ∈ openConn t c₀ := h2
    rw [openConn_comm] at h3
    exact h3

/-- **Wiring = contraction, for a target set**: for `c₀ ∈ C`,
`P_{wireW C w}(c₀ ↔ T) = P_w(C ↔ T)` (Kozma–Nitzan 2024, p. 22: "identifying the cube `[-n,n]^d`
to a point (which will be `o`)"). [cite: KozmaNitzan2024, §4 p. 22] -/
theorem prodBernoulli_wireW_real_biUnion_openConn [Countable V] (w : Sym2 V → unitInterval) (C : Set V)
    {c₀ : V} (hc₀ : c₀ ∈ C) (T : Set V) :
    (prodBernoulli (wireW C w)).real (⋃ t ∈ T, openConn c₀ t) =
      (prodBernoulli w).real (⋃ t ∈ T, ⋃ s ∈ C, openConn s t) := by
  set E := wireSet C with hE
  have hEc : E.Countable := Set.to_countable E
  have hUm : MeasurableSet (⋃ t ∈ T, openConn c₀ t : Set (BondConfig V)) :=
    MeasurableSet.biUnion (Set.to_countable T) fun t _ => measurableSet_openConn_holds c₀ t
  have hA'm : MeasurableSet ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' ⋃ t ∈ T, openConn c₀ t) :=
    measurable_union_right_const E hUm
  have hae : ∀ᵐ ω ∂prodBernoulli (wireW C w), ∀ e ∈ E, e ∈ ω := by
    have : Countable E := hEc.to_subtype
    have h : ∀ e : E, ∀ᵐ ω ∂prodBernoulli (wireW C w), (e : Sym2 V) ∈ ω := fun e =>
      prodBernoulli_ae_mem_of_eq_one _ (wireW_apply_of_mem w e.2)
    filter_upwards [ae_all_iff.2 h] with ω hω e he using hω ⟨e, he⟩
  calc (prodBernoulli (wireW C w)).real (⋃ t ∈ T, openConn c₀ t)
      = (prodBernoulli (wireW C w)).real ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' ⋃ t ∈ T, openConn c₀ t) := by
        refine measureReal_congr ?_
        filter_upwards [hae] with ω hω
        have : ω ∪ E = ω := Set.union_eq_self_of_subset_right fun e he => hω e he
        refine propext ?_
        change ω ∈ (⋃ t ∈ T, openConn c₀ t) ↔ ω ∪ E ∈ ⋃ t ∈ T, openConn c₀ t
        rw [this]
    _ = (prodBernoulli w).real ((fun ω : Set (Sym2 V) => ω ∪ E) ⁻¹' ⋃ t ∈ T, openConn c₀ t) := by
        refine prodBernoulli_real_eq_of_determinedBy _ _ (F := Eᶜ) (fun e he => ?_)
          (determinedBy_preimage_union_const E _) hA'm
        exact wireW_apply_of_not_mem w he
    _ = (prodBernoulli w).real (⋃ t ∈ T, ⋃ s ∈ C, openConn s t) := by
        rw [hE, preimage_union_wireSet_biUnion_openConn C hc₀ T]

end Wire

/-! ## The quarter-face geometry is hittable (KN Lemma 9) -/

namespace KozmaNitzan

variable {d : ℕ}

/-- **The quarter-face geometry** of direction `a` and signs `τ` (KN p. 16, Lemma 9: `Q = [-1,1]^d`,
`F = {1} × [0,1]^{d-1}` "and all maps of `F` under lattice symmetries"): `F` is the face orthant
`{x_a = τ_a, 0 ≤ τ_j x_j ≤ 1 (j ≠ a)}`. [cite: KozmaNitzan2024, §4 Lemma 9 (p. 16)] -/
def qfGeom (a : Fin d) (τ : Fin d → ℤˣ) : Geom d where
  loQ := fun _ => -1
  hiQ := fun _ => 1
  loF := fun j => if j = a then (τ a : ℤ) else min 0 (τ j : ℤ)
  hiF := fun j => if j = a then (τ a : ℤ) else max 0 (τ j : ℤ)
  far := ⟨a, by
    rcases Int.units_eq_one_or (τ a) with h | h
    · left; simp [h]
    · right; simp [h]⟩

/-- `ℓQ = Λ_ℓ` for the quarter-face geometry. [folklore] -/
theorem qfGeom_Qset (a : Fin d) (τ : Fin d → ℤˣ) (ℓ : ℕ) : (qfGeom a τ).Qset ℓ 0 = box d ℓ := by
  rw [Geom.Qset, box_eq_Icc]
  congr 1
  · funext i; simp [qfGeom]
  · funext i; simp [qfGeom]

/-- `ℓF` is the face orthant `orthantFace a τ ℓ` for the quarter-face geometry. [folklore] -/
theorem mem_qfGeom_Fset_iff (a : Fin d) (τ : Fin d → ℤˣ) (ℓ : ℕ) (x : Site d) :
    x ∈ (qfGeom a τ).Fset ℓ 0 ↔ x ∈ orthantFace a τ ℓ := by
  rw [Geom.Fset, mem_Icc_iff, mem_orthantFace, mem_box]
  simp only [zero_add, Pi.smul_apply, smul_eq_mul, qfGeom]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_, fun j hj => ?_⟩
    · have := h i
      by_cases hi : i = a
      · subst hi
        simp only [if_true] at this
        rcases Int.units_eq_one_or (τ i) with h1 | h1 <;> simp [h1] at this <;> omega
      · simp only [if_neg hi] at this
        rcases Int.units_eq_one_or (τ i) with h1 | h1 <;> simp [h1] at this <;> omega
    · have := h a
      simp only [if_true] at this
      rcases Int.units_eq_one_or (τ a) with h1 | h1 <;> simp [h1] at this ⊢ <;> omega
    · have := h j
      simp only [if_neg hj] at this
      rcases Int.units_eq_one_or (τ j) with h1 | h1 <;> simp [h1] at this ⊢ <;> omega
  · rintro ⟨hb, ha, hj⟩ i
    by_cases hi : i = a
    · subst hi
      simp only [if_true]
      rcases Int.units_eq_one_or (τ i) with h1 | h1 <;> simp [h1] at ha ⊢ <;> omega
    · simp only [if_neg hi]
      have h2 := hj i hi
      have h3 := hb i
      rcases Int.units_eq_one_or (τ i) with h1 | h1 <;> simp [h1] at h2 ⊢ <;> omega

/-- **KN Lemma 9: the quarter-face geometry is hittable** for every direction and signs, at any
`p < 1` with `θ(p) > 0` (Kozma–Nitzan 2024, p. 16, via Lemma 6, lattice symmetry and "FKG for the
complement events"; here read off this library's `exists_forall_lt_real_linked_orthantFace`).
[cite: KozmaNitzan2024, §4 Lemma 9 (p. 16)] -/
theorem isHittable_qfGeom [NeZero d] (p : unitInterval) (hθ : 0 < theta (zdGraph d) (0 : Site d) p)
    (hp1 : (p : ℝ) < 1) (a : Fin d) (τ : Fin d → ℤˣ) : IsHittable p (qfGeom a τ) := by
  refine ⟨fun ε hε => ?_⟩
  obtain ⟨k, -, n₁, -, h⟩ := exists_forall_lt_real_linked_orthantFace p hθ hp1 hε 0
  refine ⟨k, n₁, fun m hm ℓ hℓ => ?_⟩
  refine (h ℓ hℓ a τ).trans_le (measureReal_mono ?_)
  rintro ω ⟨y, hy, x, hx, hω⟩
  refine ⟨y, box_mono d hm hy, x, (mem_qfGeom_Fset_iff a τ ℓ x).2 hx, ?_⟩
  rw [qfGeom_Qset]
  exact hω

end KozmaNitzan

end Percolation.Literature

end
