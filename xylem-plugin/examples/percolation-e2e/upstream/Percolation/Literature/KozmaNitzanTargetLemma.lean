import Percolation.Literature.HalfSpacePinnedPairs
import Percolation.Literature.KozmaNitzanBoxes
import Percolation.Literature.KozmaNitzanPinning
import Percolation.Literature.LatticeModels.ProdBernoulliProofs
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — the target lemma (Lemma 10)

Third proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4): the main lemma of the
proof of Theorem 6, Lemma 10 (pp. 17–22), for weightings of `ℤ^d` with a lattice subbox
(`IsSubbox`; KN p. 17 "subbox"), hittable geometries (`Geom`, `IsHittable`; KN p. 16) and
targets (`IsTarget`; KN p. 16), proved along the printed Steps I–V with the modifications
recorded in the module docstrings of `KozmaNitzanPinning.lean` (conditioning = pinning,
contraction = wiring) and `KozmaNitzanBoxes.lean` (one plaquette per far-apart contact vertex
instead of a tiling of `∂B⟨j⟩`).

The printed proof uses Conjecture 3 at one place only (Step V, p. 22), for a source `o` lying
OUTSIDE the subbox `D` that contains the relays, the target and — by the definition of a target (p.
16) and of the scale `m` in (16) (p. 17) — every open path certifying the relays' reliability to the
target.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4, Lemma 10 and its proof, pp. 17–22; the
  inputs Lemma 7 (p. 15; here `exists_forall_le_lt_real_uniqZone`) and Lemma 9 (p. 16; here
  `exists_forall_lt_real_linked_orthantFace`).
* G. Grimmett, *Percolation*, 2nd ed. (1999), §7.2.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature

open LatticeModels SimpleGraph

namespace KozmaNitzan

variable {d : ℕ}

/-! ## The lattice weighting and subboxes -/

open Classical in
/-- The lattice weighting of `ℤ^d` at parameter `p`: `p` on nearest-neighbour edges, `0` on all
other pairs; `prodBernoulli (lattW p) = P_p` (`prodBernoulli_lattW`). [cite: KozmaNitzan2024, §2.1 p. 4 (P_p)] -/
def lattW (d : ℕ) (p : unitInterval) : Sym2 (Site d) → unitInterval :=
  fun e => if e ∈ (zdGraph d).edgeSet then p else 0

/-- Unfolding of `lattW`. [folklore] -/
theorem lattW_apply (p : unitInterval) (e : Sym2 (Site d)) [Decidable (e ∈ (zdGraph d).edgeSet)] :
    lattW d p e = if e ∈ (zdGraph d).edgeSet then p else 0 := by
  unfold lattW; congr

/-- The lattice weight of a pair of vertices. [folklore] -/
theorem lattW_mk (p : unitInterval) (u v : Site d) :
    lattW d p s(u, v) = if (zdGraph d).Adj u v then p else 0 := by
  classical
  rw [lattW_apply]; simp only [SimpleGraph.mem_edgeSet]

/-- `prodBernoulli (lattW p)` is bond percolation `P_p` on `ℤ^d`. [cite: GrimmettPercolation1999, §1.3] -/
theorem prodBernoulli_lattW (p : unitInterval) :
    prodBernoulli (lattW d p) = bondPercolation (zdGraph d) p := by
  classical
  unfold bondPercolation
  have h : lattW d p = fun e => if e ∈ (zdGraph d).edgeSet then p else 0 := funext fun e => lattW_apply p e
  rw [h]
  exact prodBernoulli_indicator_holds _ _

/-- **Subbox** (KN p. 17): inside the finite vertex set `D` the weighting `W` is the lattice
weighting at parameter `p`, and pairs from outside `D` carry weight `0` unless they end on the
inner vertex boundary of `D` ("the induced graph on `D` is isomorphic to `∏ [-s_i, s_i]` … any
edge that connects some vertex of `G \ D` to some vertex `v ∈ D` must have `v ∈ ∂_iv`").
[cite: KozmaNitzan2024, §4 p. 17 (Definition of a subbox)] -/
structure IsSubbox (W : Sym2 (Site d) → unitInterval) (p : unitInterval) (D : Finset (Site d)) : Prop where
  inside : ∀ u ∈ D, ∀ v ∈ D, u ≠ v → W s(u, v) = if (zdGraph d).Adj u v then p else 0
  outside : ∀ v ∈ D, v ∉ innerBoundary (zdGraph d) D → ∀ x ∉ D, W s(x, v) = 0

/-- **Finitely supported weighting**: pairs not inside the finite set `Sfin` carry weight `0`
(KN's graphs are finite, p. 3: "Let `G` be a finite graph"). [cite: KozmaNitzan2024, Conjecture 1 (p. 3)] -/
structure FinSupp (W : Sym2 (Site d) → unitInterval) (Sfin : Finset (Site d)) : Prop where
  zero : ∀ e : Sym2 (Site d), (∃ x ∈ e, x ∉ Sfin) → W e = 0

/-- On the off-diagonal pairs inside a subbox the weighting is the lattice weighting. [cite: KozmaNitzan2024, §4 p. 17] -/
theorem IsSubbox.eq_lattW {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)}
    (h : IsSubbox W p D) {e : Sym2 (Site d)} (he : e ∈ wireSet (↑D : Set (Site d))) :
    W e = lattW d p e := by
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨hu, hv, huv⟩ := mk_mem_wireSet_iff.1 he
    rw [h.inside u (Finset.mem_coe.1 hu) v (Finset.mem_coe.1 hv) huv, lattW_mk]

/-! ## Events determined by the off-diagonal pairs inside a set -/

/-- Two configurations with the same off-diagonal pairs inside `S` have the same open paths inside
`S`. [folklore] -/
theorem pathIn_openGraph_congr {V : Type*} {ω ω' : BondConfig V} {S : Set V}
    (h : ∀ e ∈ wireSet S, e ∈ ω ↔ e ∈ ω') {a b : V} (hp : PathIn (openGraph ω) S a b) :
    PathIn (openGraph ω') S a b := by
  obtain ⟨ha, hp⟩ := hp
  refine ⟨ha, ?_⟩
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v huv hv ih =>
    have hu : u ∈ S := (show PathIn (openGraph ω) S a u from ⟨ha, huv⟩).right_mem
    refine ih.tail ⟨?_, hv.2⟩
    have h1 := hv.1
    rw [openGraph_adj] at h1 ⊢
    exact ⟨(h _ (mk_mem_wireSet_iff.2 ⟨hu, hv.2, h1.2⟩)).1 h1.1, h1.2⟩

/-- `{a ↔ b in S}` is determined by the off-diagonal pairs inside `S`. [cite: GrimmettPercolation1999, §2.2] -/
theorem determinedBy_openConnIn_wireSet {V : Type*} (S : Set V) (a b : V) {K : Set (Sym2 V)}
    (hK : wireSet S ⊆ K) : DeterminedBy (openConnIn S a b) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  have h1 : ∀ e ∈ wireSet S, e ∈ ω ↔ e ∈ ω' := fun e he => by
    have := Set.ext_iff.1 hω e
    simp only [Set.mem_inter_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', hK he⟩).1, fun h' => (this.2 ⟨h', hK he⟩).1⟩
  simp only [DCT16.mem_openConnIn_iff_pathIn]
  exact ⟨pathIn_openGraph_congr h1, pathIn_openGraph_congr fun e he => (h1 e he).symm⟩

/-- `wireSet` is monotone. [folklore] -/
theorem wireSet_mono {V : Type*} {S S' : Set V} (h : S ⊆ S') : wireSet S ⊆ wireSet S' := by
  intro e he
  exact ⟨fun x hx => h (he.1 x hx), he.2⟩

/-- **Transfer to `P_p`**: an event determined by the off-diagonal pairs inside a subbox `D` has
the same probability under `prodBernoulli W` as under `P_p` ("the induced graph on `D` is
isomorphic to [a box of] `ℤ^d`"). [cite: KozmaNitzan2024, §4 p. 17 (subbox), p. 20 ((22)–(23))] -/
theorem IsSubbox.real_eq_bondPercolation {W : Sym2 (Site d) → unitInterval} {p : unitInterval}
    {D : Finset (Site d)} (h : IsSubbox W p D) {A : Set (BondConfig (Site d))}
    (hA : DeterminedBy A (wireSet (↑D : Set (Site d)))) (hAm : MeasurableSet A) :
    (prodBernoulli W).real A = (bondPercolation (zdGraph d) p).real A := by
  rw [← prodBernoulli_lattW]
  exact prodBernoulli_real_eq_of_determinedBy W (lattW d p) (fun e he => h.eq_lattW he) hA hAm

/-! ## The link events and their translates -/

/-- `{S ↔ T in U}`: some vertex of `S` is joined to some vertex of `T` by an open path inside `U`
(KN: "`[-m,m]^d ↔^{ℓQ} ℓF`", p. 16). [cite: KozmaNitzan2024, §4 p. 16 (Definition of a hittable geometry)] -/
def linkIn (U : Set (Site d)) (S T : Finset (Site d)) : Set (BondConfig (Site d)) :=
  {ω | ∃ s ∈ S, ∃ t ∈ T, ω ∈ openConnIn U s t}

/-- Membership in `linkIn`. [folklore] -/
theorem mem_linkIn_iff {U : Set (Site d)} {S T : Finset (Site d)} {ω : BondConfig (Site d)} :
    ω ∈ linkIn U S T ↔ ∃ s ∈ S, ∃ t ∈ T, ω ∈ openConnIn U s t := Iff.rfl

/-- `linkIn` as a finite union. [folklore] -/
theorem linkIn_eq_biUnion (U : Set (Site d)) (S T : Finset (Site d)) :
    linkIn U S T = ⋃ s ∈ S, ⋃ t ∈ T, openConnIn U s t := by
  ext ω; simp [linkIn]

/-- `linkIn` is measurable for finite `U`. [folklore] -/
theorem measurableSet_linkIn (U S T : Finset (Site d)) : MeasurableSet (linkIn (↑U : Set (Site d)) S T) := by
  rw [linkIn_eq_biUnion]
  exact Finset.measurableSet_biUnion _ fun s _ => Finset.measurableSet_biUnion _ fun t _ =>
    DCT16.measurableSet_openConnIn U s t

/-- `linkIn` is determined by the off-diagonal pairs inside `U`. [folklore] -/
theorem determinedBy_linkIn (U : Set (Site d)) (S T : Finset (Site d)) {K : Set (Sym2 (Site d))}
    (hK : wireSet U ⊆ K) : DeterminedBy (linkIn U S T) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  simp only [mem_linkIn_iff]
  refine exists_congr fun s => and_congr_right fun _ => exists_congr fun t => and_congr_right fun _ => ?_
  exact (determinedBy_iff _ _).1 (determinedBy_openConnIn_wireSet U s t hK) ω ω' hω

/-- `linkIn` is monotone in all three arguments. [folklore] -/
theorem linkIn_mono {U U' : Set (Site d)} {S S' T T' : Finset (Site d)} (hU : U ⊆ U') (hS : S ⊆ S')
    (hT : T ⊆ T') : linkIn U S T ⊆ linkIn U' S' T' := by
  rintro ω ⟨s, hs, t, ht, h⟩
  refine ⟨s, hS hs, t, hT ht, ?_⟩
  rw [DCT16.mem_openConnIn_iff_pathIn] at h ⊢
  exact h.mono hU

/-- **Translation invariance of the link events under `P_p`**:
`P_p(S + v ↔ T + v in U + v) = P_p(S ↔ T in U)`. [cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem real_linkIn_image_add (p : unitInterval) (U S T : Finset (Site d)) (v : Site d) :
    (bondPercolation (zdGraph d) p).real
        (linkIn (↑(U.image (· + v)) : Set (Site d)) (S.image (· + v)) (T.image (· + v))) =
      (bondPercolation (zdGraph d) p).real (linkIn (↑U : Set (Site d)) S T) := by
  have hpre : BondConfig.relabel (sym2Equiv (Site.shift v)) ⁻¹'
      linkIn (↑(U.image (· + v)) : Set (Site d)) (S.image (· + v)) (T.image (· + v)) =
        linkIn (↑U : Set (Site d)) S T := by
    ext ω
    simp only [Set.mem_preimage, mem_linkIn_iff, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, _, ⟨t, ht, rfl⟩, h⟩
      refine ⟨s, hs, t, ht, ?_⟩
      have h' := (GM.relabel_mem_openConnIn_iff (Site.shift v) (↑(U.image (· + v)) : Set (Site d)) s t ω).1
        (by simpa only [Site.shift_apply] using h)
      have hset : Site.shift v ⁻¹' (↑(U.image (· + v)) : Set (Site d)) = ↑U := by
        ext z; simp [Site.shift_apply]
      rwa [hset] at h'
    · rintro ⟨s, hs, t, ht, h⟩
      refine ⟨s + v, ⟨s, hs, rfl⟩, t + v, ⟨t, ht, rfl⟩, ?_⟩
      have hset : Site.shift v ⁻¹' (↑(U.image (· + v)) : Set (Site d)) = ↑U := by
        ext z; simp [Site.shift_apply]
      have h' := (GM.relabel_mem_openConnIn_iff (Site.shift v) (↑(U.image (· + v)) : Set (Site d)) s t ω).2
        (by rwa [hset])
      simpa only [Site.shift_apply] using h'
  rw [← hpre, bondPercolation_real_preimage_shift]

/-! ## The uniqueness zone around an arbitrary vertex -/

/-- `x ↔ ∂(v + Λ_n)` inside `v + Λ_n`. [cite: GrimmettPercolation1999, §1.4 (A_n)] -/
def toBdryAt (v : Site d) (n : ℕ) (x : Site d) : Set (BondConfig (Site d)) :=
  {ω | ∃ w ∈ innerBoundary (zdGraph d) (GM.ball v n), ω ∈ openConnIn (↑(GM.ball v n) : Set (Site d)) x w}

/-- **The uniqueness zone around `v`**: any two vertices of `v + Λ_k` joined inside `v + Λ_n` to
its boundary are joined to each other inside `v + Λ_n` (translate of `uniqZone k n`).
[cite: KozmaNitzan2024, §4 p. 15 (Lemma 7)] -/
def uniqZoneAt (v : Site d) (k n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∀ x ∈ GM.ball v k, ∀ y ∈ GM.ball v k, ω ∈ toBdryAt v n x → ω ∈ toBdryAt v n y →
    ω ∈ openConnIn (↑(GM.ball v n) : Set (Site d)) x y}

/-- `v + Λ_n` as a preimage under translation. [folklore] -/
theorem shift_preimage_ball (v : Site d) (n : ℕ) :
    Site.shift v ⁻¹' (↑(GM.ball v n) : Set (Site d)) = ↑(box d n) := by
  ext z
  simp only [Set.mem_preimage, Finset.mem_coe, Site.shift_apply, GM.mem_ball, mem_box,
    Pi.add_apply, add_sub_cancel_right]

/-- Membership in `v + Λ_n`. [folklore] -/
theorem mem_ball_iff_sub {v : Site d} {n : ℕ} {z : Site d} : z ∈ GM.ball v n ↔ z - v ∈ box d n := by
  rw [GM.mem_ball, mem_box]; rfl

/-- The inner boundary of `v + Λ_n` is the translate of that of `Λ_n`. [folklore] -/
theorem mem_innerBoundary_ball_iff {v : Site d} {n : ℕ} {w : Site d} :
    w ∈ innerBoundary (zdGraph d) (GM.ball v n) ↔ w - v ∈ innerBoundary (zdGraph d) (box d n) := by
  rw [mem_innerBoundary_iff, mem_innerBoundary_iff, mem_ball_iff_sub]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨y, hy, hwy⟩
    refine ⟨y - v, fun h' => hy (mem_ball_iff_sub.2 h'), ?_⟩
    have := (zdGraph_adj_shift_iff (-v) w y).2 hwy
    simpa only [Site.shift_apply, ← sub_eq_add_neg] using this
  · rintro ⟨y, hy, hwy⟩
    refine ⟨y + v, fun h' => hy (by have := mem_ball_iff_sub.1 h'; rwa [add_sub_cancel_right] at this), ?_⟩
    have := (zdGraph_adj_shift_iff v (w - v) y).2 hwy
    simpa only [Site.shift_apply, sub_add_cancel] using this

/-- **Translation invariance of the uniqueness zone**: `P_p(uniqZoneAt v k n) = P_p(uniqZone k n)`.
[cite: GrimmettPercolation1999, §1.6 p. 16] -/
theorem real_uniqZoneAt_eq (p : unitInterval) (v : Site d) (k n : ℕ) :
    (bondPercolation (zdGraph d) p).real (uniqZoneAt v k n) =
      (bondPercolation (zdGraph d) p).real (uniqZone k n) := by
  have key : ∀ (ω : BondConfig (Site d)) (a b : Site d),
      BondConfig.relabel (sym2Equiv (Site.shift v)) ω ∈ openConnIn (↑(GM.ball v n) : Set (Site d)) (a + v) (b + v) ↔
        ω ∈ openConnIn (↑(box d n) : Set (Site d)) a b := by
    intro ω a b
    have h := GM.relabel_mem_openConnIn_iff (Site.shift v) (↑(GM.ball v n) : Set (Site d)) a b ω
    rw [Site.shift_apply, Site.shift_apply, shift_preimage_ball] at h
    exact h
  have keyB : ∀ (ω : BondConfig (Site d)) (a : Site d),
      BondConfig.relabel (sym2Equiv (Site.shift v)) ω ∈ toBdryAt v n (a + v) ↔ ω ∈ toBdry n a := by
    intro ω a
    simp only [toBdryAt, Set.mem_setOf_eq, DCT16.BdryConn]
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨w - v, mem_innerBoundary_ball_iff.1 hw, ?_⟩
      rw [← key ω a (w - v), sub_add_cancel]; exact h
    · rintro ⟨w, hw, h⟩
      refine ⟨w + v, ?_, (key ω a w).2 h⟩
      rw [mem_innerBoundary_ball_iff, add_sub_cancel_right]; exact hw
  have hpre : BondConfig.relabel (sym2Equiv (Site.shift v)) ⁻¹' uniqZoneAt v k n = uniqZone k n := by
    ext ω
    simp only [Set.mem_preimage, uniqZoneAt, uniqZone, Set.mem_setOf_eq]
    constructor
    · intro h x hx y hy hbx hby
      have hx' : x + v ∈ GM.ball v k := by rw [mem_ball_iff_sub, add_sub_cancel_right]; exact hx
      have hy' : y + v ∈ GM.ball v k := by rw [mem_ball_iff_sub, add_sub_cancel_right]; exact hy
      exact (key ω x y).1 (h _ hx' _ hy' ((keyB ω x).2 hbx) ((keyB ω y).2 hby))
    · intro h x hx y hy hbx hby
      obtain ⟨x, rfl⟩ : ∃ x', x = x' + v := ⟨x - v, (sub_add_cancel x v).symm⟩
      obtain ⟨y, rfl⟩ : ∃ y', y = y' + v := ⟨y - v, (sub_add_cancel y v).symm⟩
      rw [keyB] at hbx hby
      rw [key]
      rw [mem_ball_iff_sub, add_sub_cancel_right] at hx hy
      exact h _ hx _ hy hbx hby
  rw [← hpre, bondPercolation_real_preimage_shift]

/-! ## Measurability and locality of the events around a cube -/

/-- The off-diagonal pairs inside a finite set, as a finite set. [folklore] -/
def pairsF (S : Finset (Site d)) : Finset (Sym2 (Site d)) := S.sym2.filter fun e => ¬ e.IsDiag

/-- `pairsF S` is `wireSet S`. [folklore] -/
theorem coe_pairsF (S : Finset (Site d)) : (↑(pairsF S) : Set (Sym2 (Site d))) = wireSet (↑S : Set (Site d)) := by
  ext e
  simp only [pairsF, Finset.coe_filter, Finset.mem_sym2_iff, Set.mem_setOf_eq, wireSet, Finset.mem_coe]

/-- `toBdryAt` is determined by the off-diagonal pairs inside the ball. [folklore] -/
theorem determinedBy_toBdryAt (v : Site d) (n : ℕ) (x : Site d) {K : Set (Sym2 (Site d))}
    (hK : wireSet (↑(GM.ball v n) : Set (Site d)) ⊆ K) : DeterminedBy (toBdryAt v n x) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  simp only [toBdryAt, Set.mem_setOf_eq]
  refine exists_congr fun w => and_congr_right fun _ => ?_
  exact (determinedBy_iff _ _).1 (determinedBy_openConnIn_wireSet _ x w hK) ω ω' hω

/-- `uniqZoneAt` is determined by the off-diagonal pairs inside the ball. [folklore] -/
theorem determinedBy_uniqZoneAt (v : Site d) (k n : ℕ) {K : Set (Sym2 (Site d))}
    (hK : wireSet (↑(GM.ball v n) : Set (Site d)) ⊆ K) : DeterminedBy (uniqZoneAt v k n) K := by
  rw [determinedBy_iff]
  intro ω ω' hω
  simp only [uniqZoneAt, Set.mem_setOf_eq]
  refine forall₂_congr fun x _ => forall₂_congr fun y _ => ?_
  rw [(determinedBy_iff _ _).1 (determinedBy_toBdryAt v n x hK) ω ω' hω,
    (determinedBy_iff _ _).1 (determinedBy_toBdryAt v n y hK) ω ω' hω,
    (determinedBy_iff _ _).1 (determinedBy_openConnIn_wireSet _ x y hK) ω ω' hω]

/-- `uniqZoneAt` is measurable. [folklore] -/
theorem measurableSet_uniqZoneAt (v : Site d) (k n : ℕ) : MeasurableSet (uniqZoneAt v k n) :=
  (determinedBy_uniqZoneAt v k n (K := ↑(pairsF (GM.ball v n))) (by rw [coe_pairsF])).measurableSet_of_finset

/-- The event that every open pair inside `D` is a lattice edge (sure under `P_p`, almost sure
under any weighting with a subbox `D`). [folklore] -/
def lattOnly (D : Finset (Site d)) : Set (BondConfig (Site d)) :=
  {ω | ∀ e ∈ pairsF D, e ∈ ω → e ∈ (zdGraph d).edgeSet}

/-- `lattOnly D` fails with probability `0` under a weighting with subbox `D`. [folklore] -/
theorem IsSubbox.real_compl_lattOnly {W : Sym2 (Site d) → unitInterval} {p : unitInterval}
    {D : Finset (Site d)} (h : IsSubbox W p D) : (prodBernoulli W).real (lattOnly D)ᶜ = 0 := by
  classical
  set bad := (pairsF D).filter fun e => e ∉ (zdGraph d).edgeSet with hbad
  have hsub : (lattOnly D)ᶜ ⊆ {ω | ∃ e ∈ bad, e ∈ ω} := by
    intro ω hω
    simp only [Set.mem_compl_iff, lattOnly, Set.mem_setOf_eq, not_forall, exists_prop] at hω
    obtain ⟨e, he, heω, hel⟩ := hω
    exact ⟨e, Finset.mem_filter.2 ⟨he, hel⟩, heω⟩
  refine le_antisymm ((measureReal_mono hsub).trans ?_) measureReal_nonneg
  refine (prodBernoulli_real_exists_mem_le_sum W bad).trans (le_of_eq ?_)
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
  have he1' : e ∈ wireSet (↑D : Set (Site d)) := by rw [← coe_pairsF]; exact Finset.mem_coe.2 he1
  rw [h.eq_lattW he1']
  induction e using Sym2.ind with
  | h a b =>
    rw [lattW_mk, if_neg (by rwa [SimpleGraph.mem_edgeSet] at he2)]
    rfl

/-! ## Step IV of the proof of Lemma 10: behind every contact there is a vertex of `A_ξ` -/

/-- In Lemma 10 one takes `Rg = D`, the subbox, which does not contain the source `o` (KN p. 17: "for
 every vertex `o ∈ G \ D`"), so the relays of Step V are reliable to the target by paths avoiding
 `o`. [cite: KozmaNitzan2024, §4 pp. 19–21 (Step IV, (21)–(25)); p. 16 (definition of a target: v +
 l(v)Q(v) ⊆ D)]
-/
theorem stepIV_in {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D S T U Qt Ft : Finset (Site d)}
    (hW : IsSubbox W p D) (hT : Ft ⊆ T) (hQt : Qt ⊆ D) {v : Site d} {m M : ℕ} (hmM : m ≤ M)
    (hQS : GM.ball v M ⊆ S) (hU : U ⊆ innerBoundary (zdGraph d) (GM.ball v M))
    (hfar : Disjoint Ft (GM.ball v M)) {δ : ℝ} (hδ : 0 < δ) {Rg : Set (Site d)}
    (hRb : (↑(GM.ball v M) : Set (Site d)) ⊆ Rg) (hRQ : (↑Qt : Set (Site d)) ⊆ Rg)
    (h1 : 1 - δ ^ 2 < (prodBernoulli W).real (uniqZoneAt v m M))
    (h2 : 1 - δ ^ 2 < (prodBernoulli W).real (linkIn (↑(GM.ball v M)) (GM.ball v m) U))
    (h3 : 1 - δ ^ 2 < (prodBernoulli W).real (linkIn (↑Qt) (GM.ball v m) Ft)) :
    1 - 3 * δ ≤ (prodBernoulli W).real {ω | ∃ u ∈ U,
      1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real
        (⋃ t ∈ T, openConnIn Rg u t)} := by
  classical
  -- trivial when `δ > 1`
  rcases le_or_gt δ 1 with hδ1 | hδ1
  swap
  · exact le_trans (by linarith) measureReal_nonneg
  have hballmono : GM.ball v m ⊆ GM.ball v M := fun z hz => by
    rw [mem_ball_iff_sub] at hz ⊢; exact box_mono d hmM hz
  set μ := prodBernoulli W with hμ
  -- the good event `𝒢`
  set G : Set (BondConfig (Site d)) := uniqZoneAt v m M ∩ linkIn (↑(GM.ball v M)) (GM.ball v m) U ∩
    linkIn (↑Qt) (GM.ball v m) Ft ∩ lattOnly D with hG
  have hGm : MeasurableSet G := by
    refine (((measurableSet_uniqZoneAt v m M).inter (measurableSet_linkIn _ _ _)).inter
      (measurableSet_linkIn _ _ _)).inter ?_
    refine (DeterminedBy.measurableSet_of_finset (F := pairsF D) ?_)
    rw [determinedBy_iff]
    intro ω ω' hω
    simp only [lattOnly, Set.mem_setOf_eq]
    refine forall₂_congr fun e he => ?_
    have := Set.ext_iff.1 hω e
    simp only [Set.mem_inter_iff, Finset.mem_coe] at this
    rw [show (e ∈ ω ↔ e ∈ ω') from ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩]
  -- `μ G > 1 - 3 δ²`
  have hGprob : 1 - 3 * δ ^ 2 < μ.real G := by
    have hL : μ.real (lattOnly D)ᶜ = 0 := hW.real_compl_lattOnly
    have hcov : Gᶜ ⊆ (uniqZoneAt v m M)ᶜ ∪ (linkIn (↑(GM.ball v M)) (GM.ball v m) U)ᶜ ∪
        (linkIn (↑Qt) (GM.ball v m) Ft)ᶜ ∪ (lattOnly D)ᶜ := by
      intro ω hω
      simp only [hG, Set.mem_compl_iff, Set.mem_inter_iff, not_and, Set.mem_union] at hω ⊢
      tauto
    have hb := (measureReal_mono hcov (μ := μ)).trans ((measureReal_union_le _ _).trans
      (add_le_add ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)) le_rfl))
    rw [measureReal_compl (measurableSet_uniqZoneAt v m M), measureReal_compl (measurableSet_linkIn _ _ _),
      measureReal_compl (measurableSet_linkIn _ _ _), hL, probReal_univ, measureReal_compl hGm,
      probReal_univ] at hb
    linarith
  -- Markov: the low-conditional-probability event has mass `< 3δ`
  set F := pairsF S with hF
  have hFS : (↑F : Set (Sym2 (Site d))) = wireSet (↑S : Set (Site d)) := coe_pairsF S
  have hMarkov := prodBernoulli_real_pinLow_le' W F hGm δ
  have hLlt : μ.real (pinLow W ↑F G δ) < 3 * δ := by
    by_contra hge
    push Not at hge
    have : δ * (3 * δ) ≤ δ * μ.real (pinLow W ↑F G δ) := mul_le_mul_of_nonneg_left hge hδ.le
    nlinarith
  -- outside it, some `u ∈ U` is a good vertex (reliable to `T` inside `Rg`)
  have hincl : (pinLow W ↑F G δ)ᶜ ⊆ {ω | ∃ u ∈ U,
      1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real
        (⋃ t ∈ T, openConnIn Rg u t)} := by
    intro ω hω
    simp only [Set.mem_compl_iff, mem_pinLow_iff, not_le] at hω
    -- a configuration of `G` in the cylinder of `ω`
    have hpos : 0 < (prodBernoulli (pinW W ↑F ω)).real (G ∩ localCylinder ↑F ω) := by
      rw [prodBernoulli_pinW_real_inter_localCylinder W (F.finite_toSet.countable) ω G]
      exact lt_of_le_of_lt (sub_nonneg.2 hδ1) hω
    obtain ⟨ω₁, hω₁G, hω₁c⟩ := nonempty_of_measureReal_ne_zero (ne_of_gt hpos)
    -- the arm to `U` and the uniqueness zone, valid throughout the cylinder
    obtain ⟨⟨⟨hUZ₁, hlinkU₁⟩, -⟩, -⟩ := hω₁G
    obtain ⟨x₀, hx₀, u₀, hu₀, harm₁⟩ := hlinkU₁
    have hKball : wireSet (↑(GM.ball v M) : Set (Site d)) ⊆ ↑F := by
      rw [hFS]; exact wireSet_mono (by exact_mod_cast hQS)
    have cyl_iff : ∀ ω' ∈ localCylinder (↑F : Set (Sym2 (Site d))) ω, ∀ e ∈ wireSet (↑(GM.ball v M) : Set (Site d)),
        e ∈ ω₁ ↔ e ∈ ω' := by
      intro ω' hω' e he
      exact (hω₁c e (hKball he)).trans (hω' e (hKball he)).symm
    refine ⟨u₀, hu₀, ?_⟩
    -- `G ∩ [ω]_F ⊆ {u₀ ↔ T inside Rg}`
    have key : G ∩ localCylinder ↑F ω ⊆ ⋃ t ∈ T, openConnIn Rg u₀ t := by
      rintro ω' ⟨⟨⟨⟨hUZ', -⟩, hlinkT'⟩, hlatt'⟩, hω'c⟩
      have hc := cyl_iff ω' hω'c
      -- the arm from `x₀` to `u₀` inside the ball, in `ω'`
      have harm' : ω' ∈ openConnIn (↑(GM.ball v M)) x₀ u₀ := by
        rw [DCT16.mem_openConnIn_iff_pathIn] at harm₁ ⊢
        exact pathIn_openGraph_congr hc harm₁
      -- the route to `Ft`, exiting the ball through a lattice edge
      obtain ⟨x', hx', t', ht', hpath⟩ := hlinkT'
      have ht'ball : t' ∉ (↑(GM.ball v M) : Set (Site d)) := fun h' =>
        Finset.disjoint_left.1 hfar ht' (Finset.mem_coe.1 h')
      have hx'ball : x' ∈ (↑(GM.ball v M) : Set (Site d)) :=
        Finset.mem_coe.2 (hballmono hx')
      have hpathIn : ω' ∈ openConnIn (↑Qt) x' t' := hpath
      rw [DCT16.mem_openConnIn_iff_pathIn] at hpath
      obtain ⟨a, b, ha, hb, hbQt, hab, hpa⟩ := hpath.exit hx'ball ht'ball
      have haQt : a ∈ (↑Qt : Set (Site d)) := hpa.right_mem.2
      -- `s(a,b)` is open inside `D`, hence a lattice edge
      have hadj : (zdGraph d).Adj a b := by
        rw [openGraph_adj] at hab
        have hmem : s(a, b) ∈ pairsF D := by
          simp only [pairsF, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
          exact ⟨⟨hQt (Finset.mem_coe.1 haQt), hQt (Finset.mem_coe.1 hbQt)⟩, hab.2⟩
        have := hlatt' _ hmem hab.1
        rwa [SimpleGraph.mem_edgeSet] at this
      have habdry : a ∈ innerBoundary (zdGraph d) (GM.ball v M) := by
        rw [mem_innerBoundary_iff]
        exact ⟨Finset.mem_coe.1 ha, b, fun h' => hb (Finset.mem_coe.2 h'), hadj⟩
      have hx'bd : ω' ∈ toBdryAt v M x' := ⟨a, habdry, by
        rw [DCT16.mem_openConnIn_iff_pathIn]; exact hpa.mono Set.inter_subset_left⟩
      have hx₀bd : ω' ∈ toBdryAt v M x₀ := ⟨u₀, hU hu₀, harm'⟩
      have hconn : ω' ∈ openConnIn (↑(GM.ball v M)) x₀ x' := hUZ' x₀ hx₀ x' hx' hx₀bd hx'bd
      -- chain `u₀ ↔ x₀ ↔ x' ↔ t'`, all inside `Rg`
      have hmono : ∀ {A : Set (Site d)} {x y : Site d}, A ⊆ Rg → ω' ∈ openConnIn A x y →
          ω' ∈ openConnIn Rg x y := fun hA h => by
        rw [DCT16.mem_openConnIn_iff_pathIn] at h ⊢
        exact h.mono hA
      simp only [Set.mem_iUnion, exists_prop]
      refine ⟨t', hT ht', ?_⟩
      exact GM.openConnIn_trans (GM.openConnIn_trans (GM.openConnIn_comm.1 (hmono hRb harm'))
        (hmono hRb hconn)) (hmono hRQ hpathIn)
    have hge := measureReal_mono (μ := prodBernoulli (pinW W ↑F ω)) key (measure_ne_top _ _)
    rw [prodBernoulli_pinW_real_inter_localCylinder W (F.finite_toSet.countable) ω G] at hge
    rw [← hFS]
    exact hω.trans_le hge
  -- conclusion
  have hLm : MeasurableSet (pinLow W (↑F : Set (Sym2 (Site d))) G δ) :=
    (determinedBy_pinLow W (↑F) G δ).measurableSet_of_finset
  calc 1 - 3 * δ ≤ μ.real (pinLow W ↑F G δ)ᶜ := by
        rw [measureReal_compl hLm, probReal_univ]; linarith
    _ ≤ μ.real {ω | ∃ u ∈ U,
          1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real
            (⋃ t ∈ T, openConnIn Rg u t)} := measureReal_mono hincl

/-! ## Step II of the proof of Lemma 10: a level with many contacts

The data the level events depend on: the box `B = Icc lo hi`, the source `o`, and the finite
support `Sfin` of the weighting. -/

/-- The data of Lemma 10 on which the level events depend: the box `B = Icc lo hi`, the source
vertex `o`, and the finite set `Sfin` carrying the weighting. [cite: KozmaNitzan2024, §4 Lemma 10 (p. 17)] -/
structure LData (d : ℕ) where
  /-- lower corner of `B` -/
  lo : Site d
  /-- upper corner of `B` -/
  hi : Site d
  /-- the source vertex `o ∉ D` -/
  o : Site d
  /-- the finite support of the weighting -/
  Sfin : Finset (Site d)

namespace LData

variable (L : LData d)

/-- The enlarged box `B⟨j⟩`. [cite: KozmaNitzan2024, §4 p. 15 (B⟨R⟩)] -/
def X (j : ℕ) : Finset (Site d) := Finset.Icc (L.lo - (j : Site d)) (L.hi + (j : Site d))

/-- The region outside `B⟨j⟩` (inside the support). [cite: KozmaNitzan2024, §4 p. 18 (G \ B⟨j⟩)] -/
def region (j : ℕ) : Set (Site d) := (↑(L.X j) : Set (Site d))ᶜ ∩ ↑L.Sfin

open Classical in
/-- **The contact vertices at level `j`**: the vertices of the outer boundary of `B⟨j⟩` joined to
`o` outside `B⟨j⟩`, i.e. `C(o; G \ B⟨j⟩) ∩ ∂_ev B⟨j⟩` (KN p. 18, the events `E_j`).
[cite: KozmaNitzan2024, §4 p. 18 (Step II, E_j)] -/
def Kont (j : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  (outerBoundary (zdGraph d) (L.X j)).filter fun x => ω ∈ openConnIn (L.region j) L.o x

/-- The lattice edges from a set `κ` of vertices into `B⟨j⟩` ("each such vertex has exactly one
edge connecting it to `B⟨j⟩`", p. 18 — we do not use uniqueness). [cite: KozmaNitzan2024, §4 p. 18] -/
def cEdges (j : ℕ) (κ : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  κ.biUnion fun x => ((L.X j).filter fun y => (zdGraph d).Adj x y).image fun y => s(x, y)

/-- `D_j`: some contact edge at level `j` is open (the event `{o ↔ B⟨j⟩}` of (18), up to a null
set). [cite: KozmaNitzan2024, §4 p. 18 (the events G_i)] -/
def Djo (j : ℕ) : Set (BondConfig (Site d)) := {ω | ∃ e ∈ L.cEdges j (L.Kont j ω), e ∈ ω}

/-- `¬E_j`: fewer than `N` contact vertices at level `j`. [cite: KozmaNitzan2024, §4 p. 18 (E_j)] -/
def Fail (N j : ℕ) : Set (BondConfig (Site d)) := {ω | (L.Kont j ω).card < N}

/-- `{o ↔ B}`. [cite: KozmaNitzan2024, §4 Lemma 10 (p. 17)] -/
def reachB : Set (BondConfig (Site d)) := ⋃ b ∈ Finset.Icc L.lo L.hi, openConn L.o b

/-- The enlarged boxes increase. [folklore] -/
theorem X_mono {j j' : ℕ} (h : j ≤ j') : L.X j ⊆ L.X j' := Icc_enlarge_mono h

/-- The regions decrease, and so do their pair sets. [folklore] -/
theorem wireSet_region_anti {j j' : ℕ} (h : j ≤ j') : wireSet (L.region j') ⊆ wireSet (L.region j) := by
  refine wireSet_mono fun z hz => ⟨fun hz' => hz.1 (Finset.mem_coe.2 (L.X_mono h (Finset.mem_coe.1 hz'))), hz.2⟩

/-- The pair sets of the regions are finite: inside `pairsF Sfin`. [folklore] -/
theorem wireSet_region_subset (j : ℕ) : wireSet (L.region j) ⊆ ↑(pairsF L.Sfin) := by
  rw [coe_pairsF]
  exact wireSet_mono fun z hz => hz.2

variable {L}

/-- **Locality of the contact set**: configurations agreeing on the pairs of the region outside
`B⟨j⟩` have the same contact vertices at level `j`. [cite: KozmaNitzan2024, §4 p. 18] -/
theorem Kont_congr {j : ℕ} {ω ω' : BondConfig (Site d)} (h : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω') :
    L.Kont j ω = L.Kont j ω' := by
  classical
  unfold Kont
  refine Finset.filter_congr fun x _ => ?_
  simp only [DCT16.mem_openConnIn_iff_pathIn]
  exact ⟨pathIn_openGraph_congr h, pathIn_openGraph_congr fun e he => (h e he).symm⟩

/-- A contact vertex at level `j`: outside `B⟨j⟩`, in `B⟨j+1⟩`, in the support, and joined to `o`
outside `B⟨j⟩`. [folklore] -/
theorem mem_Kont_iff {j : ℕ} {ω : BondConfig (Site d)} {x : Site d} :
    x ∈ L.Kont j ω ↔ x ∈ outerBoundary (zdGraph d) (L.X j) ∧ ω ∈ openConnIn (L.region j) L.o x := by
  classical
  exact Finset.mem_filter

/-- Contact vertices lie in the support. [folklore] -/
theorem mem_Sfin_of_mem_Kont {j : ℕ} {ω : BondConfig (Site d)} {x : Site d} (hx : x ∈ L.Kont j ω) :
    x ∈ L.Sfin := by
  obtain ⟨-, h⟩ := mem_Kont_iff.1 hx
  rw [DCT16.mem_openConnIn_iff_pathIn] at h
  exact Finset.mem_coe.1 h.right_mem.2

/-- Membership in `cEdges`. [folklore] -/
theorem mem_cEdges_iff {j : ℕ} {κ : Finset (Site d)} {e : Sym2 (Site d)} :
    e ∈ L.cEdges j κ ↔ ∃ x ∈ κ, ∃ y ∈ L.X j, (zdGraph d).Adj x y ∧ e = s(x, y) := by
  simp only [cEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, y, ⟨hy, hxy⟩, rfl⟩; exact ⟨x, hx, y, hy, hxy, rfl⟩
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩; exact ⟨x, hx, y, ⟨hy, hxy⟩, rfl⟩

/-- At most `2d` contact edges per contact vertex. [cite: KozmaNitzan2024, §4 p. 18] -/
theorem card_cEdges_le (j : ℕ) (κ : Finset (Site d)) : (L.cEdges j κ).card ≤ 2 * d * κ.card := by
  unfold cEdges
  calc _ ≤ ∑ x ∈ κ, (((L.X j).filter fun y => (zdGraph d).Adj x y).image fun y => s(x, y)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ κ, 2 * d := Finset.sum_le_sum fun x _ => ?_
    _ = 2 * d * κ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  refine Finset.card_image_le.trans ?_
  calc ((L.X j).filter fun y => (zdGraph d).Adj x y).card ≤ ((zdGraph d).neighborFinset x).card :=
        Finset.card_le_card fun y hy => by
          rw [SimpleGraph.mem_neighborFinset]; exact (Finset.mem_filter.1 hy).2
    _ ≤ 2 * d := card_neighborFinset_zdGraph_le x

/-- Contact edges at level `j` are NOT pairs of the region outside `B⟨j⟩` (one endpoint lies in
`B⟨j⟩`). [folklore] -/
theorem cEdges_disjoint_wireSet_region {j : ℕ} {κ : Finset (Site d)} {e : Sym2 (Site d)}
    (he : e ∈ L.cEdges j κ) : e ∉ wireSet (L.region j) := by
  obtain ⟨x, -, y, hy, -, rfl⟩ := mem_cEdges_iff.1 he
  intro h
  exact ((mk_mem_wireSet_iff.1 h).2.1).1 (Finset.mem_coe.2 hy)

/-- Contact edges at a level `j' > j`, from vertices in the support, ARE pairs of the region outside
`B⟨j⟩` (provided `B⟨j'⟩ ⊆ Sfin`). [folklore] -/
theorem cEdges_subset_wireSet_region {j j' : ℕ} (hjj' : j < j') (hX : L.X j' ⊆ L.Sfin)
    {κ : Finset (Site d)} (hκ : κ ⊆ outerBoundary (zdGraph d) (L.X j')) (hκS : κ ⊆ L.Sfin)
    {e : Sym2 (Site d)} (he : e ∈ L.cEdges j' κ) : e ∈ wireSet (L.region j) := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := mem_cEdges_iff.1 he
  have hxout : x ∉ L.X j' := (mem_outerBoundary_iff.1 (hκ hx)).1
  rw [mk_mem_wireSet_iff]
  refine ⟨⟨fun h' => hxout (L.X_mono hjj'.le (Finset.mem_coe.1 h')), Finset.mem_coe.2 (hκS hx)⟩,
    ⟨fun h' => ?_, Finset.mem_coe.2 (hX hy)⟩, hxy.ne⟩
  -- `y ∈ B⟨j⟩` is impossible: `y` is an inner-boundary vertex of `B⟨j'⟩`
  have hyb : y ∈ innerBoundary (zdGraph d) (L.X j') := by
    rw [mem_innerBoundary_iff]; exact ⟨hy, x, hxout, hxy.symm⟩
  obtain ⟨j'', rfl⟩ : ∃ t, j' = j + 1 + t := ⟨j' - (j + 1), by omega⟩
  have hsub : Finset.Icc (L.lo - ((j + 1 : ℕ) : Site d)) (L.hi + ((j + 1 : ℕ) : Site d)) ⊆ L.X (j + 1 + j'') :=
    Icc_enlarge_mono (by omega)
  exact not_mem_innerBoundary_of_enlarge_succ_subset hsub (Finset.mem_coe.1 h') hyb

/-- **Locality of `D_{j'}` and `Fail j'` seen from a lower level `j`.** [folklore] -/
theorem Fail_congr {N j j' : ℕ} (hjj' : j ≤ j') {ω ω' : BondConfig (Site d)}
    (h : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω') : ω ∈ L.Fail N j' ↔ ω' ∈ L.Fail N j' := by
  simp only [Fail, Set.mem_setOf_eq, Kont_congr fun e he => h e (L.wireSet_region_anti hjj' he)]

/-- Locality of `D_{j'}` seen from a lower level. [folklore] -/
theorem Djo_congr {j j' : ℕ} (hjj' : j < j') (hX : L.X j' ⊆ L.Sfin) {ω ω' : BondConfig (Site d)}
    (h : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω') : ω ∈ L.Djo j' ↔ ω' ∈ L.Djo j' := by
  classical
  simp only [Djo, Set.mem_setOf_eq]
  have hK : L.Kont j' ω = L.Kont j' ω' := Kont_congr fun e he => h e (L.wireSet_region_anti hjj'.le he)
  rw [hK]
  refine exists_congr fun e => and_congr_right fun he => h e ?_
  refine cEdges_subset_wireSet_region hjj' hX (Finset.filter_subset _ _) (fun x hx => ?_) he
  exact mem_Sfin_of_mem_Kont hx

/-- The event "all open pairs have positive weight" — almost sure. [folklore] -/
def PosOnly (W : Sym2 (Site d) → unitInterval) : Set (BondConfig (Site d)) := {ω | ∀ e ∈ ω, W e ≠ 0}

/-- `PosOnly` fails with probability `0`. [folklore] -/
theorem real_compl_posOnly (W : Sym2 (Site d) → unitInterval) : (prodBernoulli W).real (PosOnly W)ᶜ = 0 := by
  have hZ : ({e : Sym2 (Site d) | W e = 0}).Countable := Set.to_countable _
  have hae := prodBernoulli_ae_forall_notMem W hZ fun e he => he
  have h0 : prodBernoulli W {ω | ¬ ∀ e ∈ {e : Sym2 (Site d) | W e = 0}, e ∉ ω} = 0 := ae_iff.1 hae
  have hsub : (PosOnly W)ᶜ ⊆ {ω | ¬ ∀ e ∈ {e : Sym2 (Site d) | W e = 0}, e ∉ ω} := by
    intro ω hω
    simp only [PosOnly, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not, exists_prop] at hω ⊢
    obtain ⟨e, he, hW⟩ := hω
    exact ⟨e, hW, he⟩
  rw [measureReal_eq_zero_iff]
  exact measure_mono_null hsub h0

/-- On `PosOnly`, open paths of a weighting supported in `Sfin` stay in `Sfin`. [folklore] -/
theorem pathIn_of_posOnly {W : Sym2 (Site d) → unitInterval} {Sfin : Finset (Site d)} (hfin : FinSupp W Sfin)
    {ω : BondConfig (Site d)} (hpos : ω ∈ PosOnly W) {o b : Site d} (ho : o ∈ Sfin)
    (hob : (openGraph ω).Reachable o b) : PathIn (openGraph ω) (↑Sfin : Set (Site d)) o b := by
  obtain ⟨-, hp⟩ := DCT16.pathIn_univ_of_reachable hob
  refine ⟨Finset.mem_coe.2 ho, ?_⟩
  clear hob
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v _ huv ih =>
    refine ih.tail ⟨huv.1, ?_⟩
    have h1 := huv.1
    rw [openGraph_adj] at h1
    by_contra hv
    exact hpos _ h1.1 (hfin.zero _ ⟨v, Sym2.mem_mk_right u v, fun h' => hv (Finset.mem_coe.2 h')⟩)

end LData

/-- The hypotheses of Lemma 10 on the weighting, relative to the level data. [cite: KozmaNitzan2024, §4 Lemma 10 (p. 17)] -/
structure LHyp (L : LData d) (W : Sym2 (Site d) → unitInterval) (p : unitInterval)
    (D : Finset (Site d)) (R : ℕ) : Prop where
  sub : IsSubbox W p D
  fin : FinSupp W L.Sfin
  DS : D ⊆ L.Sfin
  encl : Finset.Icc (L.lo - ((R + 1 : ℕ) : Site d)) (L.hi + ((R + 1 : ℕ) : Site d)) ⊆ D
  o_not : L.o ∉ D
  o_mem : L.o ∈ L.Sfin

namespace LHyp

variable {L : LData d} {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)} {R : ℕ}
variable (hL : LHyp L W p D R)
include hL

/-- `B⟨j⟩ ⊆ D` for `j ≤ R + 1`. [folklore] -/
theorem X_subset_D {j : ℕ} (hj : j ≤ R + 1) : L.X j ⊆ D := (L.X_mono hj).trans hL.encl

/-- The outer boundary of `B⟨j⟩` lies in `D` for `j ≤ R`. [folklore] -/
theorem outerBoundary_X_subset_D {j : ℕ} (hj : j ≤ R) : outerBoundary (zdGraph d) (L.X j) ⊆ D :=
  (outerBoundary_enlarge_subset L.lo L.hi j).trans ((Icc_enlarge_mono (by omega)).trans hL.encl)

/-- No vertex of `B⟨j⟩`, `j ≤ R`, is an inner-boundary vertex of `D`. [folklore] -/
theorem not_mem_innerBoundary_D {j : ℕ} (hj : j ≤ R) {y : Site d} (hy : y ∈ L.X j) :
    y ∉ innerBoundary (zdGraph d) D :=
  not_mem_innerBoundary_of_enlarge_succ_subset hL.encl (Icc_enlarge_mono hj hy)

/-- **Contact edges carry weight `p`.** [cite: KozmaNitzan2024, §4 p. 18] -/
theorem W_cEdge {j : ℕ} (hj : j ≤ R) {κ : Finset (Site d)} (hκ : κ ⊆ outerBoundary (zdGraph d) (L.X j))
    {e : Sym2 (Site d)} (he : e ∈ L.cEdges j κ) : W e = p := by
  obtain ⟨x, hx, y, hy, hxy, rfl⟩ := LData.mem_cEdges_iff.1 he
  rw [hL.sub.inside x (hL.outerBoundary_X_subset_D hj (hκ hx)) y (hL.X_subset_D (by omega) hy) hxy.ne,
    if_pos hxy]

/-- **`{o ↔ B}` forces an open contact edge at every level** (up to the null event `PosOnlyᶜ`):
an open path from `o ∉ D` to `B ⊆ B⟨j⟩` enters `B⟨j⟩` through an open pair of positive weight,
which by the subbox property is a lattice edge from an outer-boundary vertex.
[cite: KozmaNitzan2024, §4 p. 18 ("X > k₂ implies G_1 ∩ ⋯ ∩ G_{k₂}")] -/
theorem reachB_subset_Djo {j : ℕ} (hj : j ≤ R) :
    L.reachB ∩ LData.PosOnly W ⊆ L.Djo j := by
  rintro ω ⟨hreach, hpos⟩
  simp only [LData.reachB, Set.mem_iUnion, exists_prop] at hreach
  obtain ⟨b, hb, hob⟩ := hreach
  -- an open path from `o` to `b`, inside `Sfin`
  have hpath : PathIn (openGraph ω) (↑L.Sfin : Set (Site d)) L.o b :=
    LData.pathIn_of_posOnly hL.fin hpos hL.o_mem hob
  have hoX : L.o ∈ (↑(L.X j) : Set (Site d))ᶜ := fun h' => hL.o_not (hL.X_subset_D (by omega) (Finset.mem_coe.1 h'))
  have hbX : b ∉ (↑(L.X j) : Set (Site d))ᶜ := fun h' => h' (Finset.mem_coe.2 (Icc_subset_enlarge L.lo L.hi j hb))
  obtain ⟨a, b', ha, hb', hb'S, hab, hpa⟩ := hpath.exit hoX hbX
  simp only [Set.mem_compl_iff, not_not, Finset.mem_coe] at hb'
  rw [openGraph_adj] at hab
  have hWpos : W s(a, b') ≠ 0 := hpos _ hab.1
  -- `a ∈ D` (else the weight would vanish by the subbox property)
  have haD : a ∈ D := by
    by_contra haD
    exact hWpos (hL.sub.outside b' (hL.X_subset_D (by omega) hb') (hL.not_mem_innerBoundary_D hj hb') a haD)
  -- hence `a ∼ b'` in the lattice
  have hadj : (zdGraph d).Adj a b' := by
    have := hL.sub.inside a haD b' (hL.X_subset_D (by omega) hb') hab.2
    by_contra hna
    rw [if_neg hna] at this
    exact hWpos this
  have haout : a ∈ outerBoundary (zdGraph d) (L.X j) := by
    rw [mem_outerBoundary_iff]; exact ⟨fun h' => ha (Finset.mem_coe.2 h'), b', hb', hadj⟩
  have haK : a ∈ L.Kont j ω := by
    rw [LData.mem_Kont_iff]
    refine ⟨haout, ?_⟩
    rw [DCT16.mem_openConnIn_iff_pathIn]
    exact hpa
  exact ⟨s(a, b'), LData.mem_cEdges_iff.2 ⟨a, haK, b', hb', hadj, rfl⟩, hab.1⟩

end LHyp

namespace LData

variable (L : LData d)

open Classical in
/-- The failure levels of `J` strictly above `j`. [cite: KozmaNitzan2024, §4 p. 18 (the levels j_i)] -/
def failAbove (N : ℕ) (J : Finset ℕ) (j : ℕ) (ω : BondConfig (Site d)) : Finset ℕ :=
  J.filter fun j' => j < j' ∧ ω ∈ L.Fail N j'

/-- `H_{t,j}`: level `j` is the `(t+1)`-st outermost failure level of `J`, and at the `t` failure
levels above it a contact edge is open. [cite: KozmaNitzan2024, §4 p. 18 (the events G_i)] -/
def Hev (N : ℕ) (J : Finset ℕ) (t j : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ω ∈ L.Fail N j ∧ (L.failAbove N J j ω).card = t ∧ ∀ j' ∈ J, j < j' → ω ∈ L.Fail N j' → ω ∈ L.Djo j'}

/-- `A_t`: the `t` outermost failure levels of `J` exist and at each of them a contact edge is open
(`G_1 ∩ ⋯ ∩ G_t` of (18)). [cite: KozmaNitzan2024, §4 p. 18 ((17)–(18))] -/
def Aev (N : ℕ) (J : Finset ℕ) : ℕ → Set (BondConfig (Site d))
  | 0 => Set.univ
  | t + 1 => ⋃ j ∈ J, (L.Hev N J t j ∩ L.Djo j)

variable {L}

/-- Membership in `failAbove`. [folklore] -/
theorem mem_failAbove_iff {N : ℕ} {J : Finset ℕ} {j j' : ℕ} {ω : BondConfig (Site d)} :
    j' ∈ L.failAbove N J j ω ↔ j' ∈ J ∧ j < j' ∧ ω ∈ L.Fail N j' := by
  classical
  rw [failAbove, Finset.mem_filter]

/-- Passing from a level to the lowest failure level above it removes exactly that level from the
failure levels above. [folklore] -/
theorem failAbove_min' {N : ℕ} {J : Finset ℕ} {j : ℕ} {ω : BondConfig (Site d)}
    (hne : (L.failAbove N J j ω).Nonempty) :
    L.failAbove N J ((L.failAbove N J j ω).min' hne) ω = (L.failAbove N J j ω).erase ((L.failAbove N J j ω).min' hne) := by
  classical
  set s := L.failAbove N J j ω with hs
  set m := s.min' hne with hm
  have hm_mem : m ∈ s := Finset.min'_mem s hne
  ext j''
  rw [Finset.mem_erase, mem_failAbove_iff, mem_failAbove_iff]
  have hjm : j < m := (mem_failAbove_iff.1 (hs ▸ hm_mem)).2.1
  constructor
  · rintro ⟨hJ, hmj, hF⟩
    exact ⟨ne_of_gt hmj, hJ, hjm.trans hmj, hF⟩
  · rintro ⟨hne', hJ, hjj, hF⟩
    refine ⟨hJ, lt_of_le_of_ne (Finset.min'_le s j'' ?_) (Ne.symm hne'), hF⟩
    rw [hs, mem_failAbove_iff]; exact ⟨hJ, hjj, hF⟩

/-- `H_{t,j} ⊆ A_t` (the `t` outermost failure levels above `j` carry open contact edges).
[folklore] -/
theorem Hev_subset_Aev {N : ℕ} {J : Finset ℕ} (t j : ℕ) : L.Hev N J t j ⊆ L.Aev N J t := by
  classical
  cases t with
  | zero => intro ω _; exact Set.mem_univ ω
  | succ t =>
    rintro ω ⟨-, hcard, hD⟩
    have hne : (L.failAbove N J j ω).Nonempty := by
      rw [← Finset.card_pos, hcard]; exact Nat.succ_pos t
    set m := (L.failAbove N J j ω).min' hne with hm
    have hm_mem := Finset.min'_mem _ hne
    rw [← hm] at hm_mem
    obtain ⟨hmJ, hjm, hmF⟩ := mem_failAbove_iff.1 hm_mem
    simp only [Aev, Set.mem_iUnion, exists_prop]
    refine ⟨m, hmJ, ⟨hmF, ?_, fun j' hj' hmj' hF' => hD j' hj' (hjm.trans hmj') hF'⟩, hD m hmJ hjm hmF⟩
    rw [hm, failAbove_min' hne, Finset.card_erase_of_mem (hm ▸ hm_mem), hcard]
    rfl

/-- The events `H_{t,j}`, `j ∈ J`, are pairwise disjoint. [folklore] -/
theorem Hev_disjoint {N : ℕ} {J : Finset ℕ} (t : ℕ) {j j' : ℕ} (hjj' : j ≠ j') (hj' : j' ∈ J) (hj : j ∈ J) :
    Disjoint (L.Hev N J t j) (L.Hev N J t j') := by
  classical
  wlog hlt : j < j' generalizing j j'
  · exact (this hjj'.symm hj hj' (lt_of_le_of_ne (not_lt.1 hlt) hjj'.symm)).symm
  rw [Set.disjoint_left]
  rintro ω ⟨hF, hcard, -⟩ ⟨hF', hcard', -⟩
  -- `failAbove j' ⊆ (failAbove j).erase j'` and `j' ∈ failAbove j`
  have hmem : j' ∈ L.failAbove N J j ω := mem_failAbove_iff.2 ⟨hj', hlt, hF'⟩
  have hsub : L.failAbove N J j' ω ⊆ (L.failAbove N J j ω).erase j' := by
    intro j'' hj''
    obtain ⟨hJ, hlt', hF''⟩ := mem_failAbove_iff.1 hj''
    exact Finset.mem_erase.2 ⟨ne_of_gt hlt', mem_failAbove_iff.2 ⟨hJ, hlt.trans hlt', hF''⟩⟩
  have h1 : 0 < (L.failAbove N J j ω).card := Finset.card_pos.2 ⟨_, hmem⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at h2
  rw [hcard] at h1 h2
  rw [hcard'] at h2
  omega

/-- **Locality of `H_{t,j}`**: it is determined by the pairs of the region outside `B⟨j⟩`.
[folklore] -/
theorem Hev_congr {N : ℕ} {J : Finset ℕ} (hXS : ∀ j' ∈ J, L.X j' ⊆ L.Sfin) {t j : ℕ}
    {ω ω' : BondConfig (Site d)} (h : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω') :
    ω ∈ L.Hev N J t j ↔ ω' ∈ L.Hev N J t j := by
  classical
  have hfa : L.failAbove N J j ω = L.failAbove N J j ω' := by
    unfold failAbove
    refine Finset.filter_congr fun j' _ => ?_
    constructor
    · rintro ⟨hlt, hF⟩; exact ⟨hlt, (Fail_congr hlt.le h).1 hF⟩
    · rintro ⟨hlt, hF⟩; exact ⟨hlt, (Fail_congr hlt.le h).2 hF⟩
  simp only [Hev, Set.mem_setOf_eq, hfa, Fail_congr le_rfl h]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun j' hj' => ?_
  refine forall_congr' fun hlt => ?_
  rw [Fail_congr hlt.le h, Djo_congr hlt (hXS j' hj') h]

end LData

namespace LHyp

variable {L : LData d} {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)} {R : ℕ}
variable (hL : LHyp L W p D R)
include hL

/-- `B⟨j⟩ ⊆ Sfin` for `j ≤ R + 1`. [folklore] -/
theorem X_subset_Sfin {j : ℕ} (hj : j ≤ R + 1) : L.X j ⊆ L.Sfin := (hL.X_subset_D hj).trans hL.DS

/-- **The one-level estimate** `P(H_{t,j} ∩ D_j) ≤ (1 - (1-p)^{2dN}) · P(H_{t,j})` (eq. (18)):
condition on the contact set `κ` (fewer than `N` vertices on `H_{t,j} ⊆ Fail_j`); `H_{t,j} ∩ {Kont = κ}`
is determined by the pairs outside `B⟨j⟩`, the contact edges of `κ` are at most `2dN` fresh lattice
edges of weight `p`. [cite: KozmaNitzan2024, §4 p. 18 ((18))] -/
theorem real_Hev_inter_Djo_le {N : ℕ} {J : Finset ℕ} (hJ : ∀ j' ∈ J, j' ≤ R) {t j : ℕ} (hj : j ∈ J) :
    (prodBernoulli W).real (L.Hev N J t j ∩ L.Djo j) ≤
      (1 - (1 - (p : ℝ)) ^ (2 * d * N)) * (prodBernoulli W).real (L.Hev N J t j) := by
  classical
  set μ := prodBernoulli W with hμ
  set r : ℝ := 1 - (1 - (p : ℝ)) ^ (2 * d * N) with hr
  have hXS : ∀ j' ∈ J, L.X j' ⊆ L.Sfin := fun j' hj' => hL.X_subset_Sfin (by have := hJ j' hj'; omega)
  have hjR : j ≤ R := hJ j hj
  set OB := outerBoundary (zdGraph d) (L.X j) with hOB
  -- the pieces
  set B : Finset (Site d) → Set (BondConfig (Site d)) := fun κ => L.Hev N J t j ∩ {ω | L.Kont j ω = κ} with hB
  set Op : Finset (Site d) → Set (BondConfig (Site d)) := fun κ => {ω | ∃ e ∈ L.cEdges j κ, e ∈ ω} with hOp
  have hBdet : ∀ κ, DeterminedBy (B κ) (wireSet (L.region j)) := by
    intro κ
    rw [determinedBy_iff]
    intro ω ω' hω
    have h1 : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω' := fun e he => by
      have := Set.ext_iff.1 hω e
      simp only [Set.mem_inter_iff] at this
      exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
    simp only [hB, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [LData.Hev_congr hXS h1, LData.Kont_congr h1]
  have hBm : ∀ κ, MeasurableSet (B κ) := fun κ =>
    ((hBdet κ).mono (L.wireSet_region_subset j)).measurableSet_of_finset
  have hOpdet : ∀ κ, DeterminedBy (Op κ) (↑(L.cEdges j κ) : Set (Sym2 (Site d))) := by
    intro κ
    rw [determinedBy_iff]
    intro ω ω' hω
    simp only [hOp, Set.mem_setOf_eq]
    refine exists_congr fun e => and_congr_right fun he => ?_
    have := Set.ext_iff.1 hω e
    simp only [Set.mem_inter_iff, Finset.mem_coe] at this
    exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
  have hOpm : ∀ κ, MeasurableSet (Op κ) := fun κ => (hOpdet κ).measurableSet_of_finset
  -- `P(Op κ) ≤ r` when `κ ⊆ ∂B⟨j⟩` has fewer than `N` vertices
  have hOp_le : ∀ κ, κ ⊆ OB → κ.card < N → μ.real (Op κ) ≤ r := by
    intro κ hκ hcard
    have hcompl : Op κ = {ω | ∀ e ∈ L.cEdges j κ, e ∉ ω}ᶜ := by
      ext ω; simp [hOp]
    have hclosed : μ.real {ω | ∀ e ∈ L.cEdges j κ, e ∉ ω} = (1 - (p : ℝ)) ^ (L.cEdges j κ).card := by
      rw [hμ, prodBernoulli_real_forall_notMem W (L.cEdges j κ)]
      rw [Finset.prod_congr rfl fun e he => by rw [hL.W_cEdge hjR hκ he], Finset.prod_const]
    have hmeas : MeasurableSet {ω : BondConfig (Site d) | ∀ e ∈ L.cEdges j κ, e ∉ ω} :=
      measurableSet_forall_notMem_of_countable (L.cEdges j κ).countable_toSet
    rw [hcompl, measureReal_compl hmeas, probReal_univ, hclosed, hr]
    have hp0 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.2.2
    have hp1' : 1 - (p : ℝ) ≤ 1 := sub_le_self _ p.2.1
    have hle : (L.cEdges j κ).card ≤ 2 * d * N :=
      (L.card_cEdges_le j κ).trans (Nat.mul_le_mul_left _ hcard.le)
    linarith [pow_le_pow_of_le_one hp0 hp1' hle]
  -- decompositions over `κ`
  have hdecH : L.Hev N J t j = ⋃ κ ∈ OB.powerset, B κ := by
    ext ω
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_powerset, hB, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hω; exact ⟨L.Kont j ω, Finset.filter_subset _ _, hω, rfl⟩
    · rintro ⟨κ, -, hω, -⟩; exact hω
  have hdecHD : L.Hev N J t j ∩ L.Djo j = ⋃ κ ∈ OB.powerset, (Op κ ∩ B κ) := by
    ext ω
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_powerset, hB, hOp, Set.mem_inter_iff,
      Set.mem_setOf_eq, LData.Djo]
    constructor
    · rintro ⟨hω, hD⟩; exact ⟨L.Kont j ω, Finset.filter_subset _ _, hD, hω, rfl⟩
    · rintro ⟨κ, -, hD, hω, rfl⟩; exact ⟨hω, hD⟩
  have hdisjB : (↑OB.powerset : Set (Finset (Site d))).PairwiseDisjoint B := by
    intro κ _ κ' _ hne
    rw [Function.onFun, Set.disjoint_left]
    rintro ω ⟨-, h1⟩ ⟨-, h2⟩
    exact hne (h1.symm.trans h2)
  have hdisjOB : (↑OB.powerset : Set (Finset (Site d))).PairwiseDisjoint fun κ => Op κ ∩ B κ := by
    intro κ hκ κ' hκ' hne
    exact (hdisjB hκ hκ' hne).mono Set.inter_subset_right Set.inter_subset_right
  rw [hdecHD, measureReal_biUnion_finset hdisjOB (fun κ _ => (hOpm κ).inter (hBm κ)),
    hdecH, measureReal_biUnion_finset hdisjB (fun κ _ => hBm κ), Finset.mul_sum]
  refine Finset.sum_le_sum fun κ hκ => ?_
  rw [Finset.mem_powerset] at hκ
  -- independence of `Op κ` (fresh contact edges) from `B κ`
  have hind : μ.real (Op κ ∩ B κ) = μ.real (Op κ) * μ.real (B κ) := by
    rw [hμ]
    refine prodBernoulli_real_inter_of_determinedBy W (L.cEdges j κ) (hOpdet κ) ?_ (hOpm κ) (hBm κ)
    exact (hBdet κ).mono fun e he he' => LData.cEdges_disjoint_wireSet_region (Finset.mem_coe.1 he') he
  rw [hind]
  by_cases hcard : κ.card < N
  · exact mul_le_mul_of_nonneg_right (hOp_le κ hκ hcard) measureReal_nonneg
  · -- `B κ = ∅` since `H ⊆ Fail`
    have hBempty : B κ = ∅ := by
      ext ω
      simp only [hB, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨hF, -, -⟩ hK
      rw [LData.Fail, Set.mem_setOf_eq, hK] at hF
      exact hcard hF
    rw [hBempty, measureReal_empty, mul_zero, mul_zero]

/-- **`P(A_t) ≤ (1 - (1-p)^{2dN})^t`** (eq. (17)–(18) of KN: "`P(G_1 ∩ ⋯ ∩ G_{k₂}) ≤ (1 - (1-p)^{…})^{k₂}`").
[cite: KozmaNitzan2024, §4 p. 18 ((17)–(18))] -/
theorem real_Aev_le {N : ℕ} {J : Finset ℕ} (hJ : ∀ j' ∈ J, j' ≤ R) (t : ℕ) :
    (prodBernoulli W).real (L.Aev N J t) ≤ (1 - (1 - (p : ℝ)) ^ (2 * d * N)) ^ t := by
  classical
  set μ := prodBernoulli W with hμ
  set r : ℝ := 1 - (1 - (p : ℝ)) ^ (2 * d * N) with hr
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg]
    exact pow_le_one₀ (sub_nonneg.2 p.2.2) (sub_le_self _ p.2.1)
  have hXS : ∀ j' ∈ J, L.X j' ⊆ L.Sfin := fun j' hj' => hL.X_subset_Sfin (by have := hJ j' hj'; omega)
  have hHm : ∀ t j, MeasurableSet (L.Hev N J t j) := by
    intro t j
    refine (DeterminedBy.mono (F := wireSet (L.region j)) ?_ (L.wireSet_region_subset j)).measurableSet_of_finset
    rw [determinedBy_iff]
    intro ω ω' hω
    refine LData.Hev_congr hXS fun e he => ?_
    have := Set.ext_iff.1 hω e
    simp only [Set.mem_inter_iff] at this
    exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
  induction t with
  | zero => rw [pow_zero]; exact measureReal_le_one
  | succ t ih =>
    calc μ.real (L.Aev N J (t + 1)) ≤ ∑ j ∈ J, μ.real (L.Hev N J t j ∩ L.Djo j) := by
          simp only [LData.Aev]; exact measureReal_biUnion_finset_le (μ := μ) J _
      _ ≤ ∑ j ∈ J, r * μ.real (L.Hev N J t j) :=
          Finset.sum_le_sum fun j hj => hL.real_Hev_inter_Djo_le hJ hj
      _ = r * μ.real (⋃ j ∈ J, L.Hev N J t j) := by
          rw [← Finset.mul_sum, measureReal_biUnion_finset (fun j hj j' hj' hne =>
            LData.Hev_disjoint t hne (Finset.mem_coe.1 hj') (Finset.mem_coe.1 hj)) (fun j _ => hHm t j)]
      _ ≤ r * μ.real (L.Aev N J t) := by
          refine mul_le_mul_of_nonneg_left (measureReal_mono ?_) hr0
          exact Set.iUnion₂_subset fun j _ => LData.Hev_subset_Aev t j
      _ ≤ r * r ^ t := mul_le_mul_of_nonneg_left ih hr0
      _ = r ^ (t + 1) := by ring

open Classical in
/-- **On `{o ↔ B}`, `t` failure levels in `J` give `A_t`** (almost surely): all levels carry open
contact edges (`reachB_subset_Djo`), so the `t` outermost failure levels do.
[cite: KozmaNitzan2024, §4 p. 18 ("X > k₂ implies G_1 ∩ ⋯ ∩ G_{k₂}")] -/
theorem reachB_inter_subset_Aev {N : ℕ} {J : Finset ℕ} (hJ : ∀ j' ∈ J, j' ≤ R) {t : ℕ} (ht : 1 ≤ t) :
    L.reachB ∩ LData.PosOnly W ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card} ⊆ L.Aev N J t := by
  classical
  rintro ω ⟨hω, hcard⟩
  simp only [Set.mem_setOf_eq] at hcard
  have hD : ∀ j ∈ J, ω ∈ L.Djo j := fun j hj => hL.reachB_subset_Djo (hJ j hj) hω
  -- strong induction on the number of failure levels above a failure level
  have key : ∀ n j, j ∈ J → ω ∈ L.Fail N j → (L.failAbove N J j ω).card = n →
      ∀ t, 1 ≤ t → t ≤ n + 1 → ω ∈ L.Aev N J t := by
    intro n
    induction n with
    | zero =>
      intro j hj hF hc t ht1 htn
      obtain rfl : t = 1 := by omega
      simp only [LData.Aev, Set.mem_iUnion, exists_prop]
      exact ⟨j, hj, ⟨hF, hc, fun j' hj' _ _ => hD j' hj'⟩, hD j hj⟩
    | succ n ih =>
      intro j hj hF hc t ht1 htn
      rcases Nat.lt_or_ge t (n + 2) with hlt | hge
      · rcases Nat.lt_or_ge t (n + 1 + 1) with hlt' | hge'
        · -- descend to the lowest failure level above `j`
          have hne : (L.failAbove N J j ω).Nonempty := by rw [← Finset.card_pos, hc]; omega
          set m := (L.failAbove N J j ω).min' hne with hm
          have hm_mem := Finset.min'_mem _ hne
          rw [← hm] at hm_mem
          obtain ⟨hmJ, -, hmF⟩ := LData.mem_failAbove_iff.1 hm_mem
          have hcm : (L.failAbove N J m ω).card = n := by
            rw [hm, LData.failAbove_min' hne, Finset.card_erase_of_mem (hm ▸ hm_mem), hc]; rfl
          exact ih m hmJ hmF hcm t ht1 (by omega)
        · obtain rfl : t = n + 2 := by omega
          simp only [LData.Aev, Set.mem_iUnion, exists_prop]
          exact ⟨j, hj, ⟨hF, hc, fun j' hj' _ _ => hD j' hj'⟩, hD j hj⟩
      · obtain rfl : t = n + 2 := by omega
        simp only [LData.Aev, Set.mem_iUnion, exists_prop]
        exact ⟨j, hj, ⟨hF, hc, fun j' hj' _ _ => hD j' hj'⟩, hD j hj⟩
  set FS := J.filter fun j => ω ∈ L.Fail N j with hFS
  have hne : FS.Nonempty := by rw [← Finset.card_pos]; omega
  set m := FS.min' hne with hm
  have hm_mem := Finset.min'_mem _ hne
  rw [← hm] at hm_mem
  obtain ⟨hmJ, hmF⟩ := Finset.mem_filter.1 hm_mem
  have hfa : L.failAbove N J m ω = FS.erase m := by
    ext j''
    rw [LData.mem_failAbove_iff, Finset.mem_erase, hFS, Finset.mem_filter]
    constructor
    · rintro ⟨hJ'', hlt, hF''⟩; exact ⟨ne_of_gt hlt, hJ'', hF''⟩
    · rintro ⟨hne', hJ'', hF''⟩
      refine ⟨hJ'', lt_of_le_of_ne (hm ▸ Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hJ'', hF''⟩)) (Ne.symm hne'), hF''⟩
  have hc : (L.failAbove N J m ω).card = FS.card - 1 := by
    rw [hfa, Finset.card_erase_of_mem (hm ▸ hm_mem)]
  exact key _ m hmJ hmF hc t ht (by omega)

end LHyp

namespace LHyp

variable {L : LData d} {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)} {R : ℕ}
variable (hL : LHyp L W p D R)
include hL

omit hL in
/-- `Fail N j` is measurable. [folklore] -/
theorem measurableSet_Fail (N j : ℕ) : MeasurableSet (L.Fail N j) := by
  refine (DeterminedBy.mono (F := wireSet (L.region j)) ?_ (L.wireSet_region_subset j)).measurableSet_of_finset
  rw [determinedBy_iff]
  intro ω ω' hω
  refine LData.Fail_congr le_rfl fun e he => ?_
  have := Set.ext_iff.1 hω e
  simp only [Set.mem_inter_iff] at this
  exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩

omit hL in
/-- `{o ↔ B}` is measurable. [folklore] -/
theorem measurableSet_reachB : MeasurableSet L.reachB :=
  Finset.measurableSet_biUnion _ fun _ _ => measurableSet_openConn_holds _ _

omit hL in
open Classical in
/-- **Counting the failure levels on an event**:
`Σ_{j ∈ J} P(C ∩ Fail_j) = Σ_{t=1}^{|J|} P(C ∩ {t ≤ #failure levels})` (both are `E[#failures; C]`;
KN p. 18: "`E(X) ≥ δ(R - 5M)`" versus "`P(X > k₂) < ½δ`"). [cite: KozmaNitzan2024, §4 p. 18 (the variable X)] -/
theorem sum_real_inter_Fail_eq (N : ℕ) (J : Finset ℕ) {C : Set (BondConfig (Site d))} (hC : MeasurableSet C) :
    ∑ j ∈ J, (prodBernoulli W).real (C ∩ L.Fail N j) =
      ∑ t ∈ Finset.Icc 1 J.card, (prodBernoulli W).real (C ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card}) := by
  set μ := prodBernoulli W with hμ
  have hcount : ∀ t, MeasurableSet {ω : BondConfig (Site d) | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card} := by
    intro t
    have : {ω : BondConfig (Site d) | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card} =
        ⋃ K ∈ J.powerset.filter (fun K => t ≤ K.card), ⋂ j ∈ J, {ω | ω ∈ L.Fail N j ↔ j ∈ K} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Finset.mem_filter, Finset.mem_powerset,
        exists_prop]
      constructor
      · intro h
        refine ⟨J.filter fun j => ω ∈ L.Fail N j, ⟨Finset.filter_subset _ _, h⟩, fun j hj => ?_⟩
        simp [Finset.mem_filter, hj]
      · rintro ⟨K, ⟨hKJ, hK⟩, hiff⟩
        have : J.filter (fun j => ω ∈ L.Fail N j) = K := by
          ext j
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hj, hF⟩; exact (hiff j hj).1 hF
          · intro hjK; exact ⟨hKJ hjK, (hiff j (hKJ hjK)).2 hjK⟩
        rwa [this]
    rw [this]
    refine Finset.measurableSet_biUnion _ fun K _ => Finset.measurableSet_biInter _ fun j _ => ?_
    have h1 := measurableSet_Fail (L := L) N j
    by_cases hjK : j ∈ K
    · have : {ω : BondConfig (Site d) | ω ∈ L.Fail N j ↔ j ∈ K} = L.Fail N j := by
        ext ω; simp [hjK]
      rw [this]; exact h1
    · have : {ω : BondConfig (Site d) | ω ∈ L.Fail N j ↔ j ∈ K} = (L.Fail N j)ᶜ := by
        ext ω; simp [hjK]
      rw [this]; exact h1.compl
  -- both sides are integrals of the same simple function
  have hL1 : ∀ j ∈ J, μ.real (C ∩ L.Fail N j) = ∫ ω, (C ∩ L.Fail N j).indicator (1 : BondConfig (Site d) → ℝ) ω ∂μ :=
    fun j _ => (integral_indicator_one (hC.inter (measurableSet_Fail (L := L) N j))).symm
  have hR1 : ∀ t ∈ Finset.Icc 1 J.card, μ.real (C ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card}) =
      ∫ ω, (C ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card}).indicator (1 : BondConfig (Site d) → ℝ) ω ∂μ :=
    fun t _ => (integral_indicator_one (hC.inter (hcount t))).symm
  rw [Finset.sum_congr rfl hL1, Finset.sum_congr rfl hR1, ← integral_finsetSum, ← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show (∑ i ∈ J, (C ∩ L.Fail N i).indicator 1 ω) =
      ∑ i ∈ Finset.Icc 1 J.card, (C ∩ {ω | i ≤ (J.filter fun j => ω ∈ L.Fail N j).card}).indicator 1 ω
    by_cases hω : ω ∈ C
    · have e1 : ∀ j ∈ J, (C ∩ L.Fail N j).indicator (1 : BondConfig (Site d) → ℝ) ω =
          if ω ∈ L.Fail N j then 1 else 0 := by
        intro j _
        simp only [Set.indicator_apply, Set.mem_inter_iff, hω, true_and, Pi.one_apply]
      have e2 : ∀ t ∈ Finset.Icc 1 J.card,
          (C ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card}).indicator (1 : BondConfig (Site d) → ℝ) ω =
            if t ≤ (J.filter fun j => ω ∈ L.Fail N j).card then 1 else 0 := by
        intro t _
        simp only [Set.indicator_apply, Set.mem_inter_iff, hω, true_and, Pi.one_apply, Set.mem_setOf_eq]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_boole, Finset.sum_boole]
      congr 1
      set k := (J.filter fun j => ω ∈ L.Fail N j).card with hk
      have hkJ : k ≤ J.card := Finset.card_filter_le _ _
      have : (Finset.Icc 1 J.card).filter (fun t => t ≤ k) = Finset.Icc 1 k := by
        ext t; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [this, Nat.card_Icc]
      omega
    · have e1 : ∀ j ∈ J, (C ∩ L.Fail N j).indicator (1 : BondConfig (Site d) → ℝ) ω = 0 := by
        intro j _
        simp only [Set.indicator_apply, Set.mem_inter_iff, hω, false_and, if_false]
      have e2 : ∀ t ∈ Finset.Icc 1 J.card,
          (C ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card}).indicator (1 : BondConfig (Site d) → ℝ) ω = 0 := by
        intro t _
        simp only [Set.indicator_apply, Set.mem_inter_iff, hω, false_and, if_false]
      rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const_zero, Finset.sum_const_zero]
  · intro t _
    exact (integrable_const (1 : ℝ)).indicator (hC.inter (hcount t))
  · intro j _
    exact (integrable_const (1 : ℝ)).indicator (hC.inter (measurableSet_Fail (L := L) N j))

open Classical in
/-- **Step II** (KN p. 18): if `P(o ↔ B) > 1 - δ` and the level range `J = [j₀, j₁]`, `j₁ ≤ R`, has
at least `(1-p)^{-2dN} / δ` levels, then at some level `j ∈ J` there are at least `N` contact
vertices with probability `> 1 - 2δ`. [cite: KozmaNitzan2024, §4 p. 18 (Step II)] -/
theorem stepII (hp1 : (p : ℝ) < 1) {N j₀ j₁ : ℕ} (hj₁ : j₁ ≤ R) {δ : ℝ}
    (hJ : 1 / (1 - (p : ℝ)) ^ (2 * d * N) ≤ δ * ((Finset.Icc j₀ j₁).card : ℝ))
    (hreach : 1 - δ < (prodBernoulli W).real L.reachB) :
    ∃ j ∈ Finset.Icc j₀ j₁, 1 - 2 * δ < (prodBernoulli W).real (L.Fail N j)ᶜ := by
  set μ := prodBernoulli W with hμ
  set J := Finset.Icc j₀ j₁ with hJdef
  have hJle : ∀ j ∈ J, j ≤ R := fun j hj => (Finset.mem_Icc.1 hj).2.trans hj₁
  set q : ℝ := (1 - (p : ℝ)) ^ (2 * d * N) with hq
  have hq0 : 0 < q := pow_pos (by linarith) _
  have hq1 : q ≤ 1 := pow_le_one₀ (sub_nonneg.2 p.2.2) (sub_le_self _ p.2.1)
  set r : ℝ := 1 - q with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  -- `J` is nonempty
  have hJne : J.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    push Not at h0
    have : (J.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.1 h0
    rw [this, mul_zero] at hJ
    have : 0 < 1 / q := by positivity
    linarith
  -- tails: `P(o ↔ B, t ≤ #fails) ≤ r^t`
  have htail : ∀ t ∈ Finset.Icc 1 J.card,
      μ.real (L.reachB ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card}) ≤ r ^ t := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    have hcov : L.reachB ∩ {ω | t ≤ (J.filter fun j => ω ∈ L.Fail N j).card} ⊆
        L.Aev N J t ∪ (LData.PosOnly W)ᶜ := by
      intro ω hω
      by_cases hpos : ω ∈ LData.PosOnly W
      · exact Or.inl (hL.reachB_inter_subset_Aev hJle ht1 ⟨⟨hω.1, hpos⟩, hω.2⟩)
      · exact Or.inr hpos
    calc _ ≤ μ.real (L.Aev N J t ∪ (LData.PosOnly W)ᶜ) := measureReal_mono hcov
      _ ≤ μ.real (L.Aev N J t) + μ.real (LData.PosOnly W)ᶜ := measureReal_union_le _ _
      _ ≤ r ^ t := by rw [hμ, LData.real_compl_posOnly W, add_zero]; exact hL.real_Aev_le hJle t
  -- the sum over levels is at most `1/q`
  have hsum : ∑ j ∈ J, μ.real (L.reachB ∩ L.Fail N j) ≤ 1 / q := by
    rw [hμ, sum_real_inter_Fail_eq (L := L) N J measurableSet_reachB]
    calc _ ≤ ∑ t ∈ Finset.Icc 1 J.card, r ^ t := Finset.sum_le_sum htail
      _ ≤ ∑ t ∈ Finset.range (J.card + 1), r ^ t := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => pow_nonneg hr0 t)
          rw [Finset.mem_range]; rw [Finset.mem_Icc] at ht; omega
      _ = (r ^ (J.card + 1) - 1) / (r - 1) := geom_sum_eq hr1.ne _
      _ ≤ 1 / q := by
          have e1 : (r ^ (J.card + 1) - 1) / (r - 1) = (1 - r ^ (J.card + 1)) / q := by
            have hq' : r - 1 = -q := by rw [hr]; ring
            rw [hq', div_neg, ← neg_div, neg_sub]
          rw [e1]
          exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 (J.card + 1)]) hq0.le
  -- some level has `P(o ↔ B, Fail_j) ≤ δ`
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le hJne
    (f := fun j => μ.real (L.reachB ∩ L.Fail N j)) (g := fun _ => (1 / q) / J.card) (by
      rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hJne.card_pos.ne')]
      exact hsum)
  refine ⟨j, hj, ?_⟩
  have hjδ : μ.real (L.reachB ∩ L.Fail N j) ≤ δ := by
    refine hjle.trans ?_
    rw [div_le_iff₀ (by exact_mod_cast hJne.card_pos)]
    exact hJ
  -- `P(Fail_jᶜ) ≥ P(o ↔ B) - P(o ↔ B, Fail_j)`
  have hsplit : μ.real L.reachB ≤ μ.real (L.reachB ∩ L.Fail N j) + μ.real (L.Fail N j)ᶜ := by
    rw [← measureReal_inter_add_sdiff (s := L.reachB) (measurableSet_Fail (L := L) N j)]
    refine add_le_add le_rfl (measureReal_mono fun ω hω => hω.2)
  linarith

end LHyp

/-! ## Step III of the proof of Lemma 10: seeds behind far-apart contact vertices -/

namespace LData

variable (L : LData d)

/-- Lower corner of `B⟨j⟩`. [folklore] -/
def Lo (j : ℕ) : Site d := L.lo - (j : Site d)

/-- Upper corner of `B⟨j⟩`. [folklore] -/
def Hi (j : ℕ) : Site d := L.hi + (j : Site d)

/-- `B⟨j⟩` as an order interval of its corners. [folklore] -/
theorem X_eq (j : ℕ) : L.X j = Finset.Icc (L.Lo j) (L.Hi j) := rfl

/-- The window data `(i, σ, y)` of a vertex `x` of the outer boundary of `B⟨j⟩` (a choice;
`KozmaNitzanBoxes.exists_winHyp_of_mem_outerBoundary`). [cite: KozmaNitzan2024, §4 pp. 19–21] -/
def winData [NeZero d] (j M : ℕ) (x : Site d) : Fin d × ℤ × Site d :=
  Classical.epsilon fun q : Fin d × ℤ × Site d =>
    WinHyp (L.Lo j) (L.Hi j) M q.1 q.2.1 q.2.2 ∧ x = q.2.2 + q.2.1 • unitVec q.1

/-- The seed edges of the contact vertex `x` at level `j`. [cite: KozmaNitzan2024, §4 p. 19 (seeds)] -/
def seedE [NeZero d] (j M : ℕ) (x : Site d) : Finset (Sym2 (Site d)) :=
  seedEdges (L.Lo j) (L.Hi j) M (L.winData j M x).1 (L.winData j M x).2.1 (L.winData j M x).2.2

/-- The face `U(P)` behind the contact vertex `x`. [cite: KozmaNitzan2024, §4 p. 21 (U(P))] -/
def ufaceX [NeZero d] (j M : ℕ) (x : Site d) : Finset (Site d) :=
  uface (L.Lo j) (L.Hi j) M (L.winData j M x).1 (L.winData j M x).2.1 (L.winData j M x).2.2

/-- The cube centre `v(P)` behind the contact vertex `x`. [cite: KozmaNitzan2024, §4 p. 21 (v(P))] -/
def vX [NeZero d] (j M : ℕ) (x : Site d) : Site d :=
  vctr (L.Lo j) (L.Hi j) M (L.winData j M x).1 (L.winData j M x).2.1 (L.winData j M x).2.2

/-- The separation radius between selected contacts. [folklore] -/
def Rsep (M : ℕ) : ℕ := 2 * M + 4

/-- The number of contacts needed to extract `k` separated ones. [folklore] -/
def Ncont (d M k : ℕ) : ℕ := k * (box d (2 * Rsep M)).card

/-- A choice of `k` pairwise `Rsep`-separated vertices of `κ`, when `κ` is large (else `∅`).
[cite: KozmaNitzan2024, §4 p. 19 ("faces at least k different plaquettes")] -/
def selOf (M k : ℕ) (κ : Finset (Site d)) : Finset (Site d) :=
  if h : Ncont d M k ≤ κ.card then Classical.choose (exists_subset_card_eq_separated (Rsep M) k κ h) else ∅

/-- The selected contact vertices at level `j`. [cite: KozmaNitzan2024, §4 p. 19 (P_1, …, P_k)] -/
def sel (j M k : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) := selOf M k (L.Kont j ω)

/-- All seed edges of `x` are open. [cite: KozmaNitzan2024, §4 p. 19 (seed)] -/
def SeedOpen [NeZero d] (j M : ℕ) (x : Site d) : Set (BondConfig (Site d)) := {ω | ↑(L.seedE j M x) ⊆ ω}

/-- `x` is a selected contact vertex whose seed is open ("`P` is a seed in the cluster of `o`").
[cite: KozmaNitzan2024, §4 p. 19 (the events F_P)] -/
def oSeed [NeZero d] (j M k : ℕ) (x : Site d) : Set (BondConfig (Site d)) :=
  {ω | x ∈ L.sel j M k ω} ∩ L.SeedOpen j M x

/-- `𝒢`: some selected contact vertex has an open seed. [cite: KozmaNitzan2024, §4 p. 19 (the event 𝒢, (19))] -/
def Gev [NeZero d] (j M k : ℕ) : Set (BondConfig (Site d)) :=
  ⋃ x ∈ outerBoundary (zdGraph d) (L.X j), L.oSeed j M k x

open Classical in
/-- `F_x`: `x` is the FIRST (in a fixed enumeration of `ℤ^d`) selected contact vertex with an open
seed. [cite: KozmaNitzan2024, §4 p. 19 ("P is the first such seed in this order")] -/
def Fx [NeZero d] (j M k : ℕ) (x : Site d) : Set (BondConfig (Site d)) :=
  L.oSeed j M k x ∩ ⋂ x' ∈ (outerBoundary (zdGraph d) (L.X j)).filter
    (fun x' => Encodable.encode x' < Encodable.encode x), (L.oSeed j M k x')ᶜ

variable {L}

/-- Specification of the window data of an outer-boundary vertex of a wide `B⟨j⟩`. [folklore] -/
theorem winData_spec [NeZero d] {j M : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k) {x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    WinHyp (L.Lo j) (L.Hi j) M (L.winData j M x).1 (L.winData j M x).2.1 (L.winData j M x).2.2 ∧
      x = (L.winData j M x).2.2 + (L.winData j M x).2.1 • unitVec (L.winData j M x).1 := by
  obtain ⟨i, σ, y, h, hxy⟩ := exists_winHyp_of_mem_outerBoundary hwide (by rw [X_eq] at hx; exact hx)
  exact Classical.epsilon_spec (p := fun q : Fin d × ℤ × Site d =>
    WinHyp (L.Lo j) (L.Hi j) M q.1 q.2.1 q.2.2 ∧ x = q.2.2 + q.2.1 • unitVec q.1) ⟨(i, σ, y), h, hxy⟩

/-- Specification of the selection. [folklore] -/
theorem selOf_spec {M k : ℕ} {κ : Finset (Site d)} (h : Ncont d M k ≤ κ.card) :
    selOf M k κ ⊆ κ ∧ (selOf M k κ).card = k ∧
      ∀ x ∈ selOf M k κ, ∀ y ∈ selOf M k κ, x ≠ y → y - x ∉ box d (2 * Rsep M) := by
  rw [selOf, dif_pos h]
  exact Classical.choose_spec (exists_subset_card_eq_separated (Rsep M) k κ h)

/-- The selection is a subset. [folklore] -/
theorem selOf_subset {M k : ℕ} (κ : Finset (Site d)) : selOf M k κ ⊆ κ := by
  by_cases h : Ncont d M k ≤ κ.card
  · exact (selOf_spec h).1
  · rw [selOf, dif_neg h]; exact Finset.empty_subset _

/-- Selected contacts are contacts. [folklore] -/
theorem sel_subset_Kont {j M k : ℕ} (ω : BondConfig (Site d)) : L.sel j M k ω ⊆ L.Kont j ω := selOf_subset _

/-- Seed edges of a contact vertex: lattice edges, with an endpoint in `B⟨j⟩`, not inside `B⟨j-1⟩`, and local. [cite: KozmaNitzan2024, §4 p. 19 (seeds)] -/
theorem mem_seedE [NeZero d] {j M : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k) {x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) {e : Sym2 (Site d)} (he : e ∈ L.seedE j M x) :
    e ∈ (zdGraph d).edgeSet ∧ (∃ z ∈ e, z ∈ L.X j) ∧ (∃ z ∈ e, z ∉ Finset.Icc (L.Lo j + 1) (L.Hi j - 1)) ∧
      ∀ z ∈ e, z - x ∈ box d (Rsep M) := by
  obtain ⟨h, hxy⟩ := winData_spec hwide hx
  refine ⟨seedEdges_subset_edgeSet h (Finset.mem_coe.2 he), ?_, exists_not_mem_shrink_of_mem_seedEdges h he,
    fun z hz => ?_⟩
  · rw [X_eq]; exact exists_mem_Icc_of_mem_seedEdges h he
  · rw [hxy]; exact sub_mem_box_of_mem_seedEdges h he hz

end LData

namespace LHyp

variable {L : LData d} {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)} {R : ℕ}
variable (hL : LHyp L W p D R)
include hL

/-- Both endpoints of a seed edge lie in `D`, so it carries weight `p`. [cite: KozmaNitzan2024, §4 p. 19] -/
theorem W_seedE [NeZero d] {j M : ℕ} (hj : j ≤ R) (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) {e : Sym2 (Site d)} (he : e ∈ L.seedE j M x) :
    W e = p := by
  obtain ⟨hedge, -, -, -⟩ := LData.mem_seedE hwide hx he
  obtain ⟨h, hxy⟩ := LData.winData_spec hwide hx
  -- endpoints: in `X j` or equal to `x`
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet] at hedge
    have hmem : ∀ z ∈ s(a, b), z ∈ D := by
      intro z hz
      rcases (mem_seedEdges_iff).1 he with h1 | ⟨w, hw, hab⟩ | hab
      · exact hL.X_subset_D (j := j) (by omega) (by rw [LData.X_eq]; exact wreg_subset_Icc h ((mem_edgesIn_iff.1 h1).2 z hz))
      · rw [hab] at hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hL.X_subset_D (j := j) (by omega) (by rw [LData.X_eq]; exact wreg_subset_Icc h (plaq_subset_wreg hw))
        · refine hL.X_subset_D (show j ≤ R + 1 by omega) ?_
          rw [LData.X_eq]
          refine Finset.mem_of_subset ?_ (uface_subset_shrink h ((mem_uface_iff).2 (by rwa [sub_add_cancel])))
          intro u hu; rw [mem_Icc_iff] at hu ⊢; intro k; have := hu k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at this; omega
      · rw [hab] at hz
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · rw [← hxy]; exact hL.outerBoundary_X_subset_D hj hx
        · exact hL.X_subset_D (j := j) (by omega) (by rw [LData.X_eq]; exact wreg_subset_Icc h (self_mem_wreg h))
    rw [hL.sub.inside a (hmem a (Sym2.mem_mk_left a b)) b (hmem b (Sym2.mem_mk_right a b)) hedge.ne, if_pos hedge]

/-- **A seed is open with probability at least `p^{seedBound d M}`.** [cite: KozmaNitzan2024, §4 p. 19 ("at least p^{(d+1)(4M)^{d-1}}")] -/
theorem le_real_seedOpen [NeZero d] {j M : ℕ} (hj : j ≤ R) (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    (p : ℝ) ^ seedBound d M ≤ (prodBernoulli W).real (L.SeedOpen j M x) := by
  unfold LData.SeedOpen
  rw [prodBernoulli_real_subset W (L.seedE j M x),
    Finset.prod_congr rfl fun e he => by rw [hL.W_seedE hj hwide hx he], Finset.prod_const]
  exact pow_le_pow_of_le_one p.2.1 p.2.2 card_seedEdges_le

open Classical in
/-- **Step III, (19)**: with `≥ Ncont d M k` contact vertices at level `j`, with probability at most
`(1 - p^{seedBound d M})^k` no selected contact vertex has an open seed: conditionally on the
contact set, the `k` selected seeds live on disjoint sets of fresh edges.
[cite: KozmaNitzan2024, §4 p. 19 ((19))] -/
theorem real_manyContacts_diff_Gev_le [NeZero d] {j M k : ℕ} (hj : j ≤ R)
    (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k) :
    (prodBernoulli W).real ((L.Fail (LData.Ncont d M k) j)ᶜ \ L.Gev j M k) ≤
      (1 - (p : ℝ) ^ seedBound d M) ^ k := by
  set μ := prodBernoulli W with hμ
  set N := LData.Ncont d M k with hN
  set OB := outerBoundary (zdGraph d) (L.X j) with hOB
  set Bκ : Finset (Site d) → Set (BondConfig (Site d)) := fun κ => {ω | L.Kont j ω = κ} with hBκ
  set Cx : Site d → Set (BondConfig (Site d)) := fun x => (L.SeedOpen j M x)ᶜ with hCx
  set q : ℝ := 1 - (p : ℝ) ^ seedBound d M with hq
  have hq0 : 0 ≤ q := by rw [hq, sub_nonneg]; exact pow_le_one₀ p.2.1 p.2.2
  -- covering
  have hcov : (L.Fail N j)ᶜ \ L.Gev j M k ⊆
      ⋃ κ ∈ OB.powerset.filter (fun κ => N ≤ κ.card), (Bκ κ ∩ ⋂ x ∈ LData.selOf M k κ, Cx x) := by
    rintro ω ⟨hE, hG⟩
    simp only [LData.Fail, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hE
    simp only [Set.mem_iUnion, Set.mem_iInter, Set.mem_inter_iff, Finset.mem_filter, Finset.mem_powerset,
      exists_prop, hBκ, hCx, Set.mem_setOf_eq, Set.mem_compl_iff]
    refine ⟨L.Kont j ω, ⟨Finset.filter_subset _ _, hE⟩, rfl, fun x hx hseed => hG ?_⟩
    simp only [LData.Gev, Set.mem_iUnion, exists_prop]
    exact ⟨x, Finset.filter_subset _ _ (LData.selOf_subset _ hx), ⟨hx, hseed⟩⟩
  -- each piece
  have hBdet : ∀ κ, DeterminedBy (Bκ κ) (wireSet (L.region j)) := by
    intro κ; rw [determinedBy_iff]; intro ω ω' hω
    have h1 : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω' := fun e he => by
      have := Set.ext_iff.1 hω e
      simp only [Set.mem_inter_iff] at this
      exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
    simp only [hBκ, Set.mem_setOf_eq, LData.Kont_congr h1]
  have hBm : ∀ κ, MeasurableSet (Bκ κ) := fun κ =>
    ((hBdet κ).mono (L.wireSet_region_subset j)).measurableSet_of_finset
  have hCdet : ∀ x, DeterminedBy (Cx x) (↑(L.seedE j M x) : Set (Sym2 (Site d))) := by
    intro x; rw [determinedBy_iff]; intro ω ω' hω
    simp only [hCx, Set.mem_compl_iff, LData.SeedOpen, Set.mem_setOf_eq]
    rw [show ((↑(L.seedE j M x) : Set (Sym2 (Site d))) ⊆ ω ↔ (↑(L.seedE j M x) : Set (Sym2 (Site d))) ⊆ ω') from ?_]
    constructor
    · intro h e he; have := Set.ext_iff.1 hω e; simp only [Set.mem_inter_iff] at this
      exact (this.1 ⟨h he, he⟩).1
    · intro h e he; have := Set.ext_iff.1 hω e; simp only [Set.mem_inter_iff] at this
      exact (this.2 ⟨h he, he⟩).1
  have hCm : ∀ x, MeasurableSet (Cx x) := fun x => (hCdet x).measurableSet_of_finset
  have hCle : ∀ x ∈ OB, μ.real (Cx x) ≤ q := by
    intro x hx
    have hSm : MeasurableSet (L.SeedOpen j M x) := by
      have := hCm x; rw [hCx] at this; simpa using this.compl
    simp only [hCx]
    rw [measureReal_compl hSm, probReal_univ, hq]
    linarith [hL.le_real_seedOpen hj hwide hx]
  have hpiece : ∀ κ ∈ OB.powerset.filter (fun κ => N ≤ κ.card),
      μ.real (Bκ κ ∩ ⋂ x ∈ LData.selOf M k κ, Cx x) ≤ q ^ k * μ.real (Bκ κ) := by
    intro κ hκ
    obtain ⟨hκOB, hκN⟩ := Finset.mem_filter.1 hκ
    rw [Finset.mem_powerset] at hκOB
    obtain ⟨hselκ, hcard, hsep⟩ := LData.selOf_spec (M := M) (k := k) hκN
    have hselOB : LData.selOf M k κ ⊆ OB := hselκ.trans hκOB
    -- disjoint supports
    have hdisj : (↑(LData.selOf M k κ) : Set (Site d)).PairwiseDisjoint (fun x => L.seedE j M x) := by
      intro x hx x' hx' hne
      have hxO := hselOB (Finset.mem_coe.1 hx); have hx'O := hselOB (Finset.mem_coe.1 hx')
      obtain ⟨h, hxy⟩ := LData.winData_spec hwide hxO
      obtain ⟨h', hxy'⟩ := LData.winData_spec hwide hx'O
      have hfar := hsep x (Finset.mem_coe.1 hx) x' (Finset.mem_coe.1 hx') hne
      rw [Function.onFun]
      unfold LData.seedE
      refine seedEdges_disjoint h h' ?_
      rw [← hxy, ← hxy']; exact hfar
    have hA : DeterminedBy (Bκ κ) (⋃ x ∈ LData.selOf M k κ, (↑(L.seedE j M x) : Set (Sym2 (Site d))))ᶜ := by
      refine (hBdet κ).mono fun e he hmem => ?_
      simp only [Set.mem_iUnion, exists_prop, Finset.mem_coe] at hmem
      obtain ⟨x, hx, hex⟩ := hmem
      obtain ⟨-, ⟨z, hz, hzX⟩, -⟩ := LData.mem_seedE hwide (hselOB hx) hex
      exact ((mk_mem_wireSet_iff.1 (show s(z, Sym2.Mem.other hz) ∈ wireSet (L.region j) by
        rwa [Sym2.other_spec hz])).1).1 (Finset.mem_coe.2 hzX)
    rw [hμ, prodBernoulli_real_inter_biInter_of_determinedBy W (LData.selOf M k κ) (fun x => L.seedE j M x) hdisj
      (fun x _ => hCdet x) (fun x _ => hCm x) hA (hBm κ), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ measureReal_nonneg
    calc ∏ x ∈ LData.selOf M k κ, (prodBernoulli W).real (Cx x) ≤ ∏ _x ∈ LData.selOf M k κ, q :=
          Finset.prod_le_prod (fun x _ => measureReal_nonneg) fun x hx => hCle x (hselOB hx)
      _ = q ^ k := by rw [Finset.prod_const, hcard]
  -- sum up
  have hdisjB : (↑(OB.powerset.filter (fun κ => N ≤ κ.card)) : Set (Finset (Site d))).PairwiseDisjoint Bκ := by
    intro κ _ κ' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    exact hne (h1.symm.trans h2)
  calc μ.real ((L.Fail N j)ᶜ \ L.Gev j M k)
      ≤ μ.real (⋃ κ ∈ OB.powerset.filter (fun κ => N ≤ κ.card), (Bκ κ ∩ ⋂ x ∈ LData.selOf M k κ, Cx x)) :=
        measureReal_mono hcov (measure_ne_top _ _)
    _ ≤ ∑ κ ∈ OB.powerset.filter (fun κ => N ≤ κ.card), μ.real (Bκ κ ∩ ⋂ x ∈ LData.selOf M k κ, Cx x) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ κ ∈ OB.powerset.filter (fun κ => N ≤ κ.card), q ^ k * μ.real (Bκ κ) := Finset.sum_le_sum hpiece
    _ = q ^ k * μ.real (⋃ κ ∈ OB.powerset.filter (fun κ => N ≤ κ.card), Bκ κ) := by
        rw [← Finset.mul_sum, measureReal_biUnion_finset hdisjB (fun κ _ => hBm κ)]
    _ ≤ q ^ k * 1 := mul_le_mul_of_nonneg_left measureReal_le_one (pow_nonneg hq0 k)
    _ = q ^ k := mul_one _

end LHyp

namespace LData

variable {L : LData d}

/-- `F_x ⊆ oSeed x`. [folklore] -/
theorem Fx_subset_oSeed [NeZero d] {j M k : ℕ} (x : Site d) : L.Fx j M k x ⊆ L.oSeed j M k x :=
  Set.inter_subset_left

/-- The events `F_x` are pairwise disjoint. [cite: KozmaNitzan2024, §4 p. 19 ("These events are disjoint")] -/
theorem Fx_disjoint [NeZero d] {j M k : ℕ} {x x' : Site d} (hne : x ≠ x')
    (hx' : x' ∈ outerBoundary (zdGraph d) (L.X j)) (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    Disjoint (L.Fx j M k x) (L.Fx j M k x') := by
  classical
  have hne' : Encodable.encode x ≠ Encodable.encode x' := fun h => hne (Encodable.encode_injective h)
  rw [Set.disjoint_left]
  rintro ω ⟨hωx, hIx⟩ ⟨hωx', hIx'⟩
  simp only [Set.mem_iInter, Finset.mem_filter, Set.mem_compl_iff] at hIx hIx'
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact hIx' x ⟨hx, hlt⟩ hωx
  · exact hIx x' ⟨hx', hlt⟩ hωx'

/-- `⋃_x F_x = 𝒢` (first-index decomposition). [cite: KozmaNitzan2024, §4 p. 19 ((20))] -/
theorem biUnion_Fx_eq_Gev [NeZero d] (j M k : ℕ) :
    ⋃ x ∈ outerBoundary (zdGraph d) (L.X j), L.Fx j M k x = L.Gev j M k := by
  classical
  ext ω
  simp only [Gev, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨x, hx, hF⟩; exact ⟨x, hx, Fx_subset_oSeed x hF⟩
  · rintro ⟨x, hx, hωx⟩
    -- the first contact vertex (in the enumeration) with an open selected seed
    obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image
      ((outerBoundary (zdGraph d) (L.X j)).filter fun x' => ω ∈ L.oSeed j M k x') Encodable.encode
      ⟨x, Finset.mem_filter.2 ⟨hx, hωx⟩⟩
    obtain ⟨hx₀O, hωx₀⟩ := Finset.mem_filter.1 hx₀
    refine ⟨x₀, hx₀O, hωx₀, ?_⟩
    simp only [Set.mem_iInter, Finset.mem_filter, Set.mem_compl_iff]
    rintro x' ⟨hx'O, hlt⟩ hωx'
    exact absurd (hmin x' (Finset.mem_filter.2 ⟨hx'O, hωx'⟩)) (not_le.2 hlt)

/-- `oSeed x` only depends on the pairs of the region outside `B⟨j⟩` and on the seed edges of `x`,
none of which is a pair inside the shrunken box `Icc (Lo + 1) (Hi - 1)`: so `oSeed x` is not affected
by the states of the pairs inside any `S ⊆ Icc (Lo + 1) (Hi - 1)`. [cite: KozmaNitzan2024, §4 p. 21 ("P_{K_ξ}(F_P) = P_G(F_P)")] -/
theorem oSeed_congr [NeZero d] {j M k : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {S : Finset (Site d)} (hS : S ⊆ Finset.Icc (L.Lo j + 1) (L.Hi j - 1)) {x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) {ω ω' : BondConfig (Site d)}
    (h : ∀ e ∉ wireSet (↑S : Set (Site d)), e ∈ ω ↔ e ∈ ω') : ω ∈ L.oSeed j M k x ↔ ω' ∈ L.oSeed j M k x := by
  have hSX : S ⊆ L.X j := hS.trans (by
    intro u hu; rw [X_eq, mem_Icc_iff]; rw [mem_Icc_iff] at hu; intro k'; have := hu k'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply] at this; omega)
  -- pairs of the region are not pairs inside `S`
  have hreg : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω' := by
    intro e he
    refine h e fun heS => ?_
    induction e using Sym2.ind with
    | h a b =>
      have h1 := (mk_mem_wireSet_iff.1 he).1
      have h2 := (mk_mem_wireSet_iff.1 heS).1
      exact h1.1 (Finset.mem_coe.2 (hSX (Finset.mem_coe.1 h2)))
  -- seed edges are not pairs inside `S`
  have hseed : ∀ e ∈ L.seedE j M x, e ∈ ω ↔ e ∈ ω' := by
    intro e he
    refine h e fun heS => ?_
    obtain ⟨-, -, ⟨z, hz, hzS⟩, -⟩ := mem_seedE hwide hx he
    exact hzS (hS (Finset.mem_coe.1 (heS.1 z hz)))
  simp only [oSeed, Set.mem_inter_iff, Set.mem_setOf_eq, sel, Kont_congr hreg, SeedOpen]
  refine and_congr_right fun _ => ⟨fun h' e he => (hseed e he).1 (h' he), fun h' e he => (hseed e he).2 (h' he)⟩

open Classical in
/-- Same for `F_x`. [cite: KozmaNitzan2024, §4 p. 21] -/
theorem Fx_congr [NeZero d] {j M k : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {S : Finset (Site d)} (hS : S ⊆ Finset.Icc (L.Lo j + 1) (L.Hi j - 1)) {x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) {ω ω' : BondConfig (Site d)}
    (h : ∀ e ∉ wireSet (↑S : Set (Site d)), e ∈ ω ↔ e ∈ ω') : ω ∈ L.Fx j M k x ↔ ω' ∈ L.Fx j M k x := by
  simp only [Fx, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_filter]
  rw [oSeed_congr hwide hS hx h]
  refine and_congr_right fun _ => forall₂_congr fun x' hx' => ?_
  rw [oSeed_congr hwide hS hx'.1 h]

/-- `F_x` is determined by the complement of the pairs inside `S`. [cite: KozmaNitzan2024, §4 p. 21] -/
theorem determinedBy_Fx [NeZero d] {j M k : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {S : Finset (Site d)} (hS : S ⊆ Finset.Icc (L.Lo j + 1) (L.Hi j - 1)) {x : Site d}
    (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    DeterminedBy (L.Fx j M k x) (wireSet (↑S : Set (Site d)))ᶜ := by
  rw [determinedBy_iff]
  intro ω ω' hω
  refine Fx_congr hwide hS hx fun e he => ?_
  have := Set.ext_iff.1 hω e
  simp only [Set.mem_inter_iff, Set.mem_compl_iff] at this
  exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩

/-- `F_x` is measurable (determined by the finite set of pairs of `Sfin ∪` seed edges). [folklore] -/
theorem measurableSet_Fx [NeZero d] {j M k : ℕ}
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) : MeasurableSet (L.Fx j M k x) := by
  classical
  -- all the events involved are determined by `pairsF Sfin ∪ ⋃ seed edges`
  set K : Finset (Sym2 (Site d)) := pairsF L.Sfin ∪ (outerBoundary (zdGraph d) (L.X j)).biUnion
    fun x' => L.seedE j M x' with hK
  have hos : ∀ x' ∈ outerBoundary (zdGraph d) (L.X j), DeterminedBy (L.oSeed j M k x') ↑K := by
    intro x' hx'
    rw [determinedBy_iff]
    intro ω ω' hω
    have hag : ∀ e ∈ K, e ∈ ω ↔ e ∈ ω' := fun e he => by
      have := Set.ext_iff.1 hω e
      simp only [Set.mem_inter_iff, Finset.mem_coe] at this
      exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
    have hreg : ∀ e ∈ wireSet (L.region j), e ∈ ω ↔ e ∈ ω' := fun e he =>
      hag e (Finset.mem_union_left _ (by have := L.wireSet_region_subset j he; exact_mod_cast this))
    simp only [oSeed, Set.mem_inter_iff, Set.mem_setOf_eq, sel, Kont_congr hreg, SeedOpen]
    refine and_congr_right fun _ => ⟨fun h' e he => ?_, fun h' e he => ?_⟩
    · exact (hag e (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x', hx', he⟩))).1 (h' he)
    · exact (hag e (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x', hx', he⟩))).2 (h' he)
  have hF : DeterminedBy (L.Fx j M k x) ↑K := by
    rw [determinedBy_iff]
    intro ω ω' hω
    simp only [Fx, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_filter]
    rw [(determinedBy_iff _ _).1 (hos x hx) ω ω' hω]
    refine and_congr_right fun _ => forall₂_congr fun x' hx' => ?_
    rw [(determinedBy_iff _ _).1 (hos x' hx'.1) ω ω' hω]
  exact hF.measurableSet_of_finset

/-- **On `oSeed x`, `o` is joined to every vertex of the face behind `x`** (through `x`, which is
a contact vertex, and the open seed). [cite: KozmaNitzan2024, §4 p. 21 ("hence o connects to A_ξ")] -/
theorem openConn_of_mem_oSeed [NeZero d] {j M k : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) {ω : BondConfig (Site d)}
    (hω : ω ∈ L.oSeed j M k x) {u : Site d} (hu : u ∈ L.ufaceX j M x) : ω ∈ openConn L.o u := by
  obtain ⟨hsel, hseed⟩ := hω
  have hxK : x ∈ L.Kont j ω := sel_subset_Kont ω hsel
  obtain ⟨-, hox⟩ := mem_Kont_iff.1 hxK
  rw [DCT16.mem_openConnIn_iff_pathIn] at hox
  obtain ⟨h, hxy⟩ := winData_spec hwide hx
  have hxu : ω ∈ openConn ((L.winData j M x).2.2 + (L.winData j M x).2.1 • unitVec (L.winData j M x).1) u :=
    openConn_of_seedEdges_subset h hseed hu
  rw [← hxy] at hxu
  exact (reachable_of_pathIn hox).trans hxu

end LData

/-! ## Step V of the proof of Lemma 10: Conjecture 3 in the pinned weightings -/

namespace LHyp

variable {L : LData d} {W : Sym2 (Site d) → unitInterval} {p : unitInterval} {D : Finset (Site d)} {R : ℕ}
variable (hL : LHyp L W p D R)
include hL

/-- Pinning on pairs inside `Sfin` keeps the weighting supported in `Sfin`. [folklore] -/
theorem finSupp_pinW {S : Finset (Site d)} (hS : S ⊆ L.Sfin) (ξ : Set (Sym2 (Site d))) :
    FinSupp (pinW W (wireSet (↑S : Set (Site d))) ξ) L.Sfin := by
  refine ⟨fun e he => ?_⟩
  rw [pinW_apply_of_not_mem W ξ ?_, hL.fin.zero e he]
  intro heS
  obtain ⟨x, hx, hxS⟩ := he
  exact hxS (hS (Finset.mem_coe.1 (heS.1 x hx)))

open Classical in
/-- **Step V with region-internal relay reliability** (KN pp. 21–22, read as in `stepIV_in`): the
averaged estimate (26) ⟹ `Σ_ξ p_ξ φ_ξ > (1-3δ)²`, the set `W` of good patterns, the gluing
hypothesis in each `K_ξ`, `ξ ∈ W`, and the final summation — with the relay set
`A_ξ := {u ∈ S : P(u ↔ T inside Rg | ξ) > 1 - δ}` for an arbitrary region `Rg`, so that the gluing
hypothesis `hC3` is only needed for relays reliable to `T` INSIDE `Rg` (for `Rg = D ∌ o`: by paths
avoiding the source). Inputs: a level `j` with many contacts w.h.p. (Step II), the seed bound (19)
(Step III), the face estimate of `stepIV_in` for every potential contact, and the gluing hypothesis
for finitely supported weightings, source `o`, target set `T` and `Rg`-reliable relays.
[cite: KozmaNitzan2024, §4 pp. 21–22 (Step V)] -/
theorem stepV_in [NeZero d] {Rg : Set (Site d)} {j M k : ℕ} (hj : j ≤ R) (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {S T : Finset (Site d)} (hS : S ⊆ Finset.Icc (L.Lo j + 1) (L.Hi j - 1)) (hSD : S ⊆ D)
    {ε δ δc : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδc : δ ≤ δc)
    (h3δ : 3 * δ ≤ 1) (h12 : 12 * δ ≤ ε * δc)
    (hII : 1 - 2 * δ < (prodBernoulli W).real (L.Fail (LData.Ncont d M k) j)ᶜ)
    (hIII : (1 - (p : ℝ) ^ seedBound d M) ^ k ≤ δ)
    (hUS : ∀ x ∈ outerBoundary (zdGraph d) (L.X j), L.ufaceX j M x ⊆ S)
    (hIV : ∀ x ∈ outerBoundary (zdGraph d) (L.X j),
      1 - 3 * δ ≤ (prodBernoulli W).real {ω | ∃ u ∈ L.ufaceX j M x,
        1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real (⋃ t ∈ T, openConnIn Rg u t)})
    (hC3 : ∀ (w : Sym2 (Site d) → unitInterval), FinSupp w L.Sfin → ∀ (A : Finset (Site d)), A ⊆ L.Sfin →
      1 - δc < (prodBernoulli w).real (⋃ a ∈ A, openConn L.o a) →
      (∀ a ∈ A, 1 - δc < (prodBernoulli w).real (⋃ t ∈ T, openConnIn Rg a t)) →
      1 - ε / 2 < (prodBernoulli w).real (⋃ t ∈ T, openConn L.o t)) :
    1 - ε < (prodBernoulli W).real (⋃ t ∈ T, openConn L.o t) := by
  set μ := prodBernoulli W with hμ
  set OB := outerBoundary (zdGraph d) (L.X j) with hOB
  set F := pairsF S with hF
  have hFS : (↑F : Set (Sym2 (Site d))) = wireSet (↑S : Set (Site d)) := coe_pairsF S
  have hSfin : S ⊆ L.Sfin := hSD.trans hL.DS
  -- the good sets `A_ξ` and the quantities `φ_ξ`
  set Aof : Finset (Sym2 (Site d)) → Finset (Site d) := fun P => S.filter fun u =>
    1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ↑P)).real (⋃ t ∈ T, openConnIn Rg u t) with hAof
  set φ : Finset (Sym2 (Site d)) → ℝ := fun P =>
    (prodBernoulli (pinW W ↑F ↑P)).real (⋃ a ∈ Aof P, openConn L.o a) with hφ
  set cyl : Finset (Sym2 (Site d)) → Set (BondConfig (Site d)) := fun P => localCylinder ↑F ↑P with hcyl
  -- `μ(𝒢) > 1 - 3δ`
  have hG : 1 - 3 * δ < μ.real (L.Gev j M k) := by
    have hmG : MeasurableSet (L.Gev j M k) := by
      rw [← LData.biUnion_Fx_eq_Gev]
      exact Finset.measurableSet_biUnion _ fun x hx => LData.measurableSet_Fx hx
    have hmE : MeasurableSet (L.Fail (LData.Ncont d M k) j)ᶜ := (measurableSet_Fail (L := L) _ _).compl
    have h1 := hL.real_manyContacts_diff_Gev_le (j := j) (M := M) (k := k) hj hwide
    have h2 : μ.real (L.Fail (LData.Ncont d M k) j)ᶜ ≤
        μ.real ((L.Fail (LData.Ncont d M k) j)ᶜ \ L.Gev j M k) + μ.real (L.Gev j M k) := by
      rw [← measureReal_inter_add_sdiff (s := (L.Fail (LData.Ncont d M k) j)ᶜ) hmG, add_comm]
      exact add_le_add le_rfl (measureReal_mono Set.inter_subset_right)
    linarith
  -- Claim D: `Σ_P μ(cyl P) φ(P) ≥ (1 - 3δ) μ(𝒢)`
  have hGood_det : ∀ x, DeterminedBy {ω | ∃ u ∈ L.ufaceX j M x,
      1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real (⋃ t ∈ T, openConnIn Rg u t)} ↑F := by
    intro x
    rw [determinedBy_iff]
    intro ω ω' hω
    simp only [Set.mem_setOf_eq]
    have hag : ∀ e ∈ wireSet (↑S : Set (Site d)), e ∈ ω ↔ e ∈ ω' := by
      intro e he
      rw [← hFS] at he
      have := Set.ext_iff.1 hω e
      simp only [Set.mem_inter_iff] at this
      exact ⟨fun h' => (this.1 ⟨h', he⟩).1, fun h' => (this.2 ⟨h', he⟩).1⟩
    refine exists_congr fun u => and_congr_right fun _ => ?_
    rw [pinW_congr W hag]
  have hFx_pin : ∀ P, ∀ x ∈ OB, (prodBernoulli (pinW W ↑F ↑P)).real (L.Fx j M k x) = μ.real (L.Fx j M k x) := by
    intro P x hx
    rw [hμ]
    refine (prodBernoulli_real_eq_of_determinedBy W _ (F := (↑F : Set (Sym2 (Site d)))ᶜ)
      (fun e he => (pinW_apply_of_not_mem W ↑P he).symm) ?_ (LData.measurableSet_Fx hx)).symm
    rw [hFS]
    exact LData.determinedBy_Fx hwide hS hx
  have hφ_ge : ∀ P, P ⊆ F →
      ∑ x ∈ OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P), μ.real (L.Fx j M k x) ≤ φ P := by
    intro P hP
    have hsub : (⋃ x ∈ OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P), L.Fx j M k x) ⊆
        ⋃ a ∈ Aof P, openConn L.o a := by
      intro ω hω
      simp only [Set.mem_iUnion, exists_prop, Finset.mem_filter] at hω ⊢
      obtain ⟨x, ⟨hxO, u, hu, huA⟩, hFx⟩ := hω
      exact ⟨u, huA, LData.openConn_of_mem_oSeed hwide hxO (LData.Fx_subset_oSeed x hFx) hu⟩
    calc _ = ∑ x ∈ OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P),
            (prodBernoulli (pinW W ↑F ↑P)).real (L.Fx j M k x) :=
          Finset.sum_congr rfl fun x hx => (hFx_pin P x (Finset.mem_filter.1 hx).1).symm
      _ = (prodBernoulli (pinW W ↑F ↑P)).real
            (⋃ x ∈ OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P), L.Fx j M k x) := by
          rw [measureReal_biUnion_finset]
          · intro x hx x' hx' hne
            exact LData.Fx_disjoint hne (Finset.mem_filter.1 hx').1 (Finset.mem_filter.1 hx).1
          · intro x hx; exact LData.measurableSet_Fx (Finset.mem_filter.1 hx).1
      _ ≤ φ P := measureReal_mono hsub (measure_ne_top _ _)
  have hD : (1 - 3 * δ) * μ.real (L.Gev j M k) ≤ ∑ P ∈ F.powerset, μ.real (cyl P) * φ P := by
    -- `Σ_x μ(F_x) μ(Good_x) = Σ_P μ(cyl P) Σ_{x good for P} μ(F_x)`
    have hGx : ∀ x ∈ OB, μ.real {ω | ∃ u ∈ L.ufaceX j M x,
        1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real (⋃ t ∈ T, openConnIn Rg u t)} =
        ∑ P ∈ F.powerset.filter (fun P => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P), μ.real (cyl P) := by
      intro x hx
      rw [hμ, prodBernoulli_real_eq_sum_localCylinder W F (hGood_det x)]
      refine Finset.sum_congr ?_ fun P _ => rfl
      ext P
      simp only [Finset.mem_filter, Finset.mem_powerset, Set.mem_setOf_eq, hAof, and_congr_right_iff]
      intro _
      constructor
      · rintro ⟨u, hu, hg⟩; exact ⟨u, hu, hUS x hx hu, hg⟩
      · rintro ⟨u, hu, -, hg⟩; exact ⟨u, hu, hg⟩
    calc (1 - 3 * δ) * μ.real (L.Gev j M k)
        = ∑ x ∈ OB, (1 - 3 * δ) * μ.real (L.Fx j M k x) := by
          rw [← LData.biUnion_Fx_eq_Gev, measureReal_biUnion_finset, Finset.mul_sum]
          · intro x hx x' hx' hne; exact LData.Fx_disjoint hne hx' hx
          · intro x hx; exact LData.measurableSet_Fx hx
      _ ≤ ∑ x ∈ OB, μ.real {ω | ∃ u ∈ L.ufaceX j M x,
            1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real (⋃ t ∈ T, openConnIn Rg u t)} *
            μ.real (L.Fx j M k x) :=
          Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right (hIV x hx) measureReal_nonneg
      _ = ∑ x ∈ OB, ∑ P ∈ F.powerset.filter (fun P => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P),
            μ.real (cyl P) * μ.real (L.Fx j M k x) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [hGx x hx, Finset.sum_mul]
      _ = ∑ P ∈ F.powerset, ∑ x ∈ OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P),
            μ.real (cyl P) * μ.real (L.Fx j M k x) := by
          rw [Finset.sum_comm' (t' := F.powerset)
            (s' := fun P => OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P))]
          intro x P
          simp only [Finset.mem_filter, Finset.mem_powerset]
          tauto
      _ = ∑ P ∈ F.powerset, μ.real (cyl P) *
            ∑ x ∈ OB.filter (fun x => ∃ u ∈ L.ufaceX j M x, u ∈ Aof P), μ.real (L.Fx j M k x) := by
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ P ∈ F.powerset, μ.real (cyl P) * φ P :=
          Finset.sum_le_sum fun P hP => mul_le_mul_of_nonneg_left (hφ_ge P (Finset.mem_powerset.1 hP)) measureReal_nonneg
  -- total mass of the cylinders is `1`
  have hcyl_sum : ∑ P ∈ F.powerset, μ.real (cyl P) = 1 := by
    have := prodBernoulli_real_eq_sum_localCylinder W F (determinedBy_univ (↑F : Set (Sym2 (Site d))))
    rw [probReal_univ] at this
    rw [hμ, this]
    refine (Finset.sum_congr ?_ fun P _ => rfl)
    ext P; simp
  -- Claim E: the bad patterns have mass `≤ ε/2`
  set Bad := F.powerset.filter (fun P => φ P ≤ 1 - δc) with hBad
  have hφ_le : ∀ P, φ P ≤ 1 := fun P => measureReal_le_one
  have hE : ∑ P ∈ Bad, μ.real (cyl P) ≤ ε / 2 := by
    have hδc0 : 0 < δc := hδ.trans_le hδc
    have h1 : δc * ∑ P ∈ Bad, μ.real (cyl P) ≤ ∑ P ∈ F.powerset, μ.real (cyl P) * (1 - φ P) := by
      rw [Finset.mul_sum]
      calc ∑ P ∈ Bad, δc * μ.real (cyl P) ≤ ∑ P ∈ Bad, μ.real (cyl P) * (1 - φ P) :=
            Finset.sum_le_sum fun P hP => by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (by have := (Finset.mem_filter.1 hP).2; linarith) measureReal_nonneg
        _ ≤ ∑ P ∈ F.powerset, μ.real (cyl P) * (1 - φ P) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun P _ _ =>
              mul_nonneg measureReal_nonneg (by linarith [hφ_le P])
    have h2 : ∑ P ∈ F.powerset, μ.real (cyl P) * (1 - φ P) =
        1 - ∑ P ∈ F.powerset, μ.real (cyl P) * φ P := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hcyl_sum]
    have h3 : 1 - ∑ P ∈ F.powerset, μ.real (cyl P) * φ P < 6 * δ := by
      have : (1 - 3 * δ) * (1 - 3 * δ) < (1 - 3 * δ) * μ.real (L.Gev j M k) ∨ 1 - 3 * δ = 0 := by
        rcases eq_or_lt_of_le (sub_nonneg.2 h3δ) with h0 | h0
        · exact Or.inr h0.symm
        · exact Or.inl (mul_lt_mul_of_pos_left hG h0)
      rcases this with h4 | h4
      · nlinarith
      · have : ∑ P ∈ F.powerset, μ.real (cyl P) * φ P ≥ 0 :=
          Finset.sum_nonneg fun P _ => mul_nonneg measureReal_nonneg measureReal_nonneg
        nlinarith
    have h4 : δc * ∑ P ∈ Bad, μ.real (cyl P) ≤ 6 * δ := by linarith
    have h5 : δc * ∑ P ∈ Bad, μ.real (cyl P) ≤ δc * (ε / 2) := by nlinarith
    exact le_of_mul_le_mul_left h5 hδc0
  -- Claim F: on good patterns Conjecture 3 applies
  have hF : ∀ P ∈ F.powerset, P ∉ Bad →
      1 - ε / 2 < (prodBernoulli (pinW W ↑F ↑P)).real (⋃ t ∈ T, openConn L.o t) := by
    intro P hP hPB
    have hgood : 1 - δc < φ P := by
      by_contra hle; exact hPB (Finset.mem_filter.2 ⟨hP, not_lt.1 hle⟩)
    have hsupp : FinSupp (pinW W ↑F ↑P) L.Sfin := by rw [hFS]; exact hL.finSupp_pinW hSfin ↑P
    refine hC3 _ hsupp (Aof P) ((Finset.filter_subset _ _).trans hSfin) hgood fun a ha => ?_
    have hga := (Finset.mem_filter.1 ha).2
    rw [← hFS] at hga
    linarith
  -- conclusion: total probability over the patterns
  have hmT : MeasurableSet (⋃ t ∈ T, openConn L.o t : Set (BondConfig (Site d))) :=
    Finset.measurableSet_biUnion _ fun t _ => measurableSet_openConn_holds _ _
  have htot := prodBernoulli_real_inter_eq_sum_pinW W F hmT (determinedBy_univ (↑F : Set (Sym2 (Site d))))
  rw [Set.inter_univ] at htot
  simp only [Set.mem_univ, Finset.filter_true] at htot
  rw [hμ] at hE hcyl_sum
  rw [htot]
  calc 1 - ε < (1 - ε / 2) * (1 - ε / 2) := by nlinarith
    _ ≤ (1 - ε / 2) * ∑ P ∈ F.powerset \ Bad, (prodBernoulli W).real (cyl P) := by
        have hnonneg : (0 : ℝ) ≤ 1 - ε / 2 := by linarith
        have : ∑ P ∈ F.powerset \ Bad, (prodBernoulli W).real (cyl P) =
            1 - ∑ P ∈ Bad, (prodBernoulli W).real (cyl P) := by
          have hBsub : Bad ⊆ F.powerset := by rw [hBad]; exact Finset.filter_subset _ _
          rw [← hcyl_sum, ← Finset.sum_sdiff hBsub]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_left (by linarith) hnonneg
    _ = ∑ P ∈ F.powerset \ Bad, (prodBernoulli W).real (cyl P) * (1 - ε / 2) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun P _ => mul_comm _ _
    _ ≤ ∑ P ∈ F.powerset \ Bad, (prodBernoulli W).real (cyl P) *
          (prodBernoulli (pinW W ↑F ↑P)).real (⋃ t ∈ T, openConn L.o t) :=
        Finset.sum_le_sum fun P hP => by
          obtain ⟨hP1, hP2⟩ := Finset.mem_sdiff.1 hP
          exact mul_le_mul_of_nonneg_left (hF P hP1 hP2).le measureReal_nonneg
    _ ≤ ∑ P ∈ F.powerset, (prodBernoulli W).real (cyl P) *
          (prodBernoulli (pinW W ↑F ↑P)).real (⋃ t ∈ T, openConn L.o t) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun P _ _ =>
          mul_nonneg measureReal_nonneg measureReal_nonneg

end LHyp

/-! ## Hittable geometries and targets (KN p. 16) -/

/-- **A geometry** `(F, Q)`: two integer boxes `Q = Icc loQ hiQ`, `F = Icc loF hiF` of `ℤ^d`, to be
scaled by `ℓ` and translated; `F` lies in a half-space `{x_i ≥ 1}` or `{x_i ≤ -1}` (all of KN's
geometries — quarter faces `{1} × [0,1]^{d-1}`, faces `{K} × [-1,1]^{d-1}` — do), so that `v + ℓF`
is at sup-distance `≥ ℓ` from `v`. [cite: KozmaNitzan2024, §4 p. 16 (Definition of a hittable geometry)] -/
structure Geom (d : ℕ) where
  /-- lower corner of `Q` -/
  loQ : Site d
  /-- upper corner of `Q` -/
  hiQ : Site d
  /-- lower corner of `F` -/
  loF : Site d
  /-- upper corner of `F` -/
  hiF : Site d
  /-- `F` avoids the open unit cube around the origin in some coordinate direction -/
  far : ∃ i, 1 ≤ loF i ∨ hiF i ≤ -1

namespace Geom

/-- `v + ℓQ`. [cite: KozmaNitzan2024, §4 p. 16 (ℓQ)] -/
def Qset (g : Geom d) (ℓ : ℕ) (v : Site d) : Finset (Site d) :=
  Finset.Icc (v + (ℓ : ℤ) • g.loQ) (v + (ℓ : ℤ) • g.hiQ)

/-- `v + ℓF`. [cite: KozmaNitzan2024, §4 p. 16 (ℓF)] -/
def Fset (g : Geom d) (ℓ : ℕ) (v : Site d) : Finset (Site d) :=
  Finset.Icc (v + (ℓ : ℤ) • g.loF) (v + (ℓ : ℤ) • g.hiF)

/-- `v + ℓQ` is the translate of `ℓQ`. [folklore] -/
theorem Qset_eq_image (g : Geom d) (ℓ : ℕ) (v : Site d) : g.Qset ℓ v = (g.Qset ℓ 0).image (· + v) := by
  ext z
  simp only [Qset, Finset.mem_image, mem_Icc_iff, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h; refine ⟨z - v, fun i => ?_, sub_add_cancel z v⟩; have := h i; simp only [Pi.sub_apply]; omega
  · rintro ⟨w, hw, rfl⟩ i; have := hw i; simp only [Pi.add_apply]; omega

/-- `v + ℓF` is the translate of `ℓF`. [folklore] -/
theorem Fset_eq_image (g : Geom d) (ℓ : ℕ) (v : Site d) : g.Fset ℓ v = (g.Fset ℓ 0).image (· + v) := by
  ext z
  simp only [Fset, Finset.mem_image, mem_Icc_iff, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h; refine ⟨z - v, fun i => ?_, sub_add_cancel z v⟩; have := h i; simp only [Pi.sub_apply]; omega
  · rintro ⟨w, hw, rfl⟩ i; have := hw i; simp only [Pi.add_apply]; omega

/-- **`v + ℓF` is far from `v`**: disjoint from `v + Λ_M` once `ℓ > M`. [folklore] -/
theorem disjoint_Fset_ball (g : Geom d) {ℓ M : ℕ} (hℓ : M < ℓ) (v : Site d) :
    Disjoint (g.Fset ℓ v) (GM.ball v M) := by
  rw [Finset.disjoint_left]
  intro t ht hball
  rw [Fset, mem_Icc_iff] at ht
  rw [mem_ball_iff_sub, mem_box] at hball
  obtain ⟨i, hi | hi⟩ := g.far
  · have h1 := ht i; have h2 := hball i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 h2
    nlinarith
  · have h1 := ht i; have h2 := hball i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 h2
    nlinarith

end Geom

/-- **Hittable geometry** (KN p. 16: "for every `ε > 0` there exists an `m` such that for any integer
`ℓ > m` we have `P_p([-m,m]^d ↔^{ℓQ} ℓF) > 1 - ε`"), in the monotone normal form: from some source
size `k` and some scale `ℓ₀` on, for ALL larger `m` and `ℓ`. (For `m' ≥ m` the event only grows, so
this is the printed notion with `m := max k ℓ₀`.) [cite: KozmaNitzan2024, §4 p. 16 (Definition of a hittable geometry)] -/
structure IsHittable (p : unitInterval) (g : Geom d) : Prop where
  hit : ∀ ε : ℝ, 0 < ε → ∃ k ℓ₀ : ℕ, ∀ m, k ≤ m → ∀ ℓ, ℓ₀ ≤ ℓ →
    1 - ε < (bondPercolation (zdGraph d) p).real (linkIn (↑(g.Qset ℓ 0)) (box d m) (g.Fset ℓ 0))

/-- **Target** (KN p. 16): `T` is a target with respect to `(B = Icc lo hi, D, R, H)` if from every
vertex `v` of `B⟨R⟩` some geometry of `H`, at some scale `ℓ ≥ R`, fits inside `D` and lands in `T`:
`v + ℓQ ⊆ D`, `v + ℓF ⊆ T`. [cite: KozmaNitzan2024, §4 p. 16 (Definition of a target)] -/
structure IsTarget (T : Finset (Site d)) (lo hi : Site d) (D : Finset (Site d)) (R : ℕ) (H : List (Geom d)) : Prop where
  hit : ∀ v ∈ Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)), ∃ ℓ : ℕ, R ≤ ℓ ∧ ∃ g ∈ H,
    g.Qset ℓ v ⊆ D ∧ g.Fset ℓ v ⊆ T

/-! ## The cube and face behind a contact vertex, in the coordinates of Step IV -/

/-- Shrinking `B⟨j⟩` by one gives `B⟨j-1⟩` (lower corner). [folklore] -/
theorem enlarge_lo_add_one {lo : Site d} {j : ℕ} (h : 1 ≤ j) :
    lo - ((j : ℕ) : Site d) + 1 = lo - (((j - 1 : ℕ)) : Site d) := by
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
  push_cast [h]
  ring

/-- Shrinking `B⟨j⟩` by one gives `B⟨j-1⟩` (upper corner). [folklore] -/
theorem enlarge_hi_sub_one {hi : Site d} {j : ℕ} (h : 1 ≤ j) :
    hi + ((j : ℕ) : Site d) - 1 = hi + (((j - 1 : ℕ)) : Site d) := by
  funext k
  simp only [Pi.add_apply, Pi.sub_apply, Pi.natCast_apply, Pi.one_apply]
  push_cast [h]
  ring

namespace LData

variable {L : LData d}

/-- The cube behind the contact vertex `x`. [cite: KozmaNitzan2024, §4 p. 19] -/
def cubeX [NeZero d] (L : LData d) (j M : ℕ) (x : Site d) : Finset (Site d) :=
  cube (L.Lo j) (L.Hi j) M (L.winData j M x).1 (L.winData j M x).2.1 (L.winData j M x).2.2

/-- The cube is the ball of radius `M` around its centre. [folklore] -/
theorem cubeX_eq_ball [NeZero d] (j M : ℕ) (x : Site d) : L.cubeX j M x = GM.ball (L.vX j M x) M := by
  ext z
  rw [cubeX, mem_cube_iff_sub_mem_box, mem_ball_iff_sub]
  rfl

/-- The face behind `x` lies on the inner boundary of the cube. [folklore] -/
theorem ufaceX_subset_innerBoundary [NeZero d] {j M : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    L.ufaceX j M x ⊆ innerBoundary (zdGraph d) (GM.ball (L.vX j M x) M) := by
  obtain ⟨h, -⟩ := winData_spec hwide hx
  intro u hu
  rw [← cubeX_eq_ball]
  unfold cubeX
  rw [cube, mem_innerBoundary_Icc]
  obtain ⟨hcube, hui⟩ := (mem_uface_iff_cube h).1 hu
  refine ⟨hcube, (L.winData j M x).1, ?_⟩
  simp only [Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
  rw [hui]
  rcases h.sign with hs | hs
  · right; rw [hs]; ring
  · left; rw [hs]; ring

/-- **The cube lies in the shell** `S = B⟨j-1⟩ \ B⟨j-2M-2⟩`. [cite: KozmaNitzan2024, §4 p. 19 ("v + [-M,M]^d ⊆ S")] -/
theorem ball_vX_subset_shell [NeZero d] {j M : ℕ} (hj : 2 * M + 2 ≤ j) (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    GM.ball (L.vX j M x) M ⊆ L.X (j - 1) \ L.X (j - (2 * M + 2)) := by
  obtain ⟨h, -⟩ := winData_spec hwide hx
  intro z hz
  rw [← cubeX_eq_ball] at hz
  rw [Finset.mem_sdiff]
  constructor
  · have := cube_subset_shrink h hz
    rw [X]
    rwa [LData.Lo, LData.Hi, enlarge_lo_add_one (by omega), enlarge_hi_sub_one (by omega)] at this
  · have := not_mem_shrink2_of_mem_cube h hz
    rw [X]
    rwa [LData.Lo, LData.Hi, enlarge_lo_add (t := 2 * M + 2) hj, enlarge_hi_sub (t := 2 * M + 2) hj] at this

/-- The shell in the form used by Step V: `B⟨j-1⟩ \ B⟨j-2M-2⟩ ⊆ Icc (Lo j + 1) (Hi j - 1)`. [folklore] -/
theorem shell_subset_shrink {j M : ℕ} (hj : 1 ≤ j) :
    L.X (j - 1) \ L.X (j - (2 * M + 2)) ⊆ Finset.Icc (L.Lo j + 1) (L.Hi j - 1) := by
  intro z hz
  have := (Finset.mem_sdiff.1 hz).1
  rw [X] at this
  rw [LData.Lo, LData.Hi, enlarge_lo_add_one hj, enlarge_hi_sub_one hj]
  exact this

/-- The cube centre lies in `B⟨j-1⟩`. [folklore] -/
theorem vX_mem [NeZero d] {j M : ℕ} (hj : 1 ≤ j) (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) : L.vX j M x ∈ L.X (j - 1) := by
  obtain ⟨h, -⟩ := winData_spec hwide hx
  have := vctr_mem_shrink h
  rw [X]
  rw [LData.Lo, LData.Hi, enlarge_lo_add_one hj, enlarge_hi_sub_one hj] at this
  exact this

/-- **A face orthant of the cube lies in the face `U(P)`**: for the crossing direction `i` and any
transverse signs, the translate of `orthantFace i τ M` (with `τ_i = σ`) lies in `ufaceX`.
[cite: KozmaNitzan2024, §4 p. 20 ((23): lattice symmetries and the full-face geometry)] -/
theorem orthantFace_image_subset_ufaceX [NeZero d] {j M : ℕ} (hwide : ∀ k, L.Lo j k + 2 * M + 2 ≤ L.Hi j k)
    {x : Site d} (hx : x ∈ outerBoundary (zdGraph d) (L.X j)) :
    ∃ (a : Fin d) (τ : Fin d → ℤˣ), (orthantFace a τ M).image (· + L.vX j M x) ⊆ L.ufaceX j M x := by
  obtain ⟨h, -⟩ := winData_spec hwide hx
  set σu : ℤˣ := if (L.winData j M x).2.1 = 1 then 1 else -1 with hσu
  have hσ : (σu : ℤ) = (L.winData j M x).2.1 := by
    rcases h.sign with hs | hs
    · rw [hσu, if_pos hs, hs]; rfl
    · rw [hσu, if_neg (by rw [hs]; norm_num), hs]; rfl
  refine ⟨(L.winData j M x).1, fun _ => σu, ?_⟩
  intro u hu
  rw [Finset.mem_image] at hu
  obtain ⟨z, hz, rfl⟩ := hu
  rw [mem_orthantFace] at hz
  obtain ⟨hzbox, hza, -⟩ := hz
  rw [ufaceX, mem_uface_iff_cube h]
  constructor
  · change z + L.vX j M x ∈ L.cubeX j M x
    rw [cubeX_eq_ball, mem_ball_iff_sub, add_sub_cancel_right]; exact hzbox
  · change (z + L.vX j M x) (L.winData j M x).1 = L.vX j M x (L.winData j M x).1 + (L.winData j M x).2.1 * M
    rw [Pi.add_apply, ← hσ]
    have hsq : (σu : ℤ) * (σu : ℤ) = 1 := by rcases Int.units_eq_one_or σu with h1 | h1 <;> simp [h1]
    have : z (L.winData j M x).1 = (σu : ℤ) * M := by
      calc z (L.winData j M x).1 = ((σu : ℤ) * (σu : ℤ)) * z (L.winData j M x).1 := by rw [hsq, one_mul]
        _ = (σu : ℤ) * ((σu : ℤ) * z (L.winData j M x).1) := by ring
        _ = (σu : ℤ) * M := by rw [hza]
    rw [this]; ring

end LData

/-! ## Lemma 10 -/

/-- **Kozma–Nitzan 2024, Lemma 10 under the AVOIDING gluing hypothesis.** The printed proof of Lemma 10
 (pp. 17–22) invokes Conjecture 3 once (Step V, p. 22), in the auxiliary graph `K_ξ`, for the source
 `o ∉ D`, the target `T ⊆ D` and the relay set `A_ξ ⊆ S ⊆ D`; and the relays are certified reliable
 to `T` by open paths INSIDE the subbox `D` ((22) is a connection inside `v + ℓ(v)Q(v) ⊆ D` by the
 definitions of a target, p. 16, and of `m` in (16), p. 17; (23) and Lemma 7 live inside `v + Λ_M ⊆
 S ⊆ D`) — see `stepIV_in`. Hence Lemma 10 holds under the weaker gluing hypothesis `hC` in which
 the relays are only assumed reliable to the target INSIDE A REGION `Rg` NOT CONTAINING THE SOURCE
 (for `ℤ^d`-indexed finitely supported weightings and a target set; Conjecture 3 implies it,
 `targetLemma`, and so does its `H = G - o` form, KN Question 9's reference graph, p. 36). Assume
 `hC`, `0 < p < 1` and `θ(p) > 0`. For every `ε > 0` there is `δ > 0` such that for every finite
 of hittable geometries there is `R` with: for every finitely supported weighting `W` of
 `ℤ^d` with a lattice subbox `D ⊇ B⟨R⟩` at parameter `p` (`B = Icc lo hi`), every nonempty target `T
 ⊆ D` with respect to `(B, D, R, H)` and every `o ∉ D`, `P_W(o ↔ B) > 1 - δ ⟹ P_W(o ↔ T) > 1 - ε`.
 Proof: Steps I–V of KN pp. 17–22 in their region-internal forms `stepIV_in`, `LHyp.stepV_in` with
 `Rg = D`, with Lemma 7 := `exists_forall_le_lt_real_uniqZone` and the full-face hittability (Lemma
 9) := `exists_forall_lt_real_linked_orthantFace`. [cite: KozmaNitzan2024, §4 Lemma 10 (pp. 17–22);
 p. 16 (targets); p. 36 (Question 9, the graph H)]
-/
theorem targetLemma_avoiding [NeZero d]
    (hC : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (w : Sym2 (Site d) → unitInterval) (Sf : Finset (Site d)),
      (∀ e : Sym2 (Site d), (∃ x ∈ e, x ∉ Sf) → w e = 0) →
      ∀ (A T : Finset (Site d)) (o : Site d) (Rg : Set (Site d)),
        A ⊆ Sf → T ⊆ Sf → o ∈ Sf → T.Nonempty → o ∉ Rg →
        1 - δ < (prodBernoulli w).real (⋃ a ∈ A, openConn o a) →
          (∀ a ∈ A, 1 - δ < (prodBernoulli w).real (⋃ t ∈ T, openConnIn Rg a t)) →
            1 - ε < (prodBernoulli w).real (⋃ t ∈ T, openConn o t))
    (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) 0 p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : List (Geom d), (∀ g ∈ H, IsHittable p g) → ∃ R : ℕ,
      ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
        (T : Finset (Site d)) (o : Site d),
        FinSupp W Sfin → IsSubbox W p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
        Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
        IsTarget T lo hi D R H → T ⊆ D → T.Nonempty →
        1 - δ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
          1 - ε < (prodBernoulli W).real (⋃ t ∈ T, openConn o t) := by
  classical
  -- trivial when `ε > 1`
  rcases le_or_gt ε 1 with hε1 | hε1
  swap
  · refine ⟨1, one_pos, fun H _ => ⟨0, fun W Sfin D lo hi T o _ _ _ _ _ _ _ _ _ _ => ?_⟩⟩
    exact lt_of_lt_of_le (by linarith) measureReal_nonneg
  -- Step I: the constants `δ_{C3}`, `δ`
  obtain ⟨δ₀, hδ₀, hC3⟩ := hC (ε / 2) (half_pos hε)
  set δc : ℝ := min δ₀ 1 with hδc
  have hδc0 : 0 < δc := lt_min hδ₀ one_pos
  have hδc1 : δc ≤ 1 := min_le_right _ _
  set δ : ℝ := ε * δc / 12 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδc' : δ ≤ δc := by rw [hδdef]; nlinarith
  have h3δ : 3 * δ ≤ 1 := by rw [hδdef]; nlinarith
  have h12 : 12 * δ ≤ ε * δc := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by linarith
  refine ⟨δ, hδpos, fun H hH => ?_⟩
  -- the scales `m`, `M`
  have hη : 0 < δ ^ 2 := by positivity
  have hkl : ∀ g ∈ H, ∃ kl : ℕ × ℕ, ∀ m, kl.1 ≤ m → ∀ ℓ, kl.2 ≤ ℓ →
      1 - δ ^ 2 < (bondPercolation (zdGraph d) p).real (linkIn (↑(g.Qset ℓ 0)) (box d m) (g.Fset ℓ 0)) := by
    intro g hg
    obtain ⟨k, ℓ₀, h⟩ := (hH g hg).hit (δ ^ 2) hη
    exact ⟨(k, ℓ₀), h⟩
  choose! kl hklspec using hkl
  -- every element of a list of naturals is at most its `foldr max 0`
  have le_foldr_max_of_mem : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => intro a h; exact absurd h List.not_mem_nil
    | cons b l ih =>
      intro a h
      rw [List.foldr_cons]
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
  set k₀ := (H.map fun g => (kl g).1).foldr max 0 with hk₀
  set ℓmax := (H.map fun g => (kl g).2).foldr max 0 with hℓmax
  have hk₀le : ∀ g ∈ H, (kl g).1 ≤ k₀ := fun g hg => le_foldr_max_of_mem (List.mem_map.2 ⟨g, hg, rfl⟩)
  have hℓle : ∀ g ∈ H, (kl g).2 ≤ ℓmax := fun g hg => le_foldr_max_of_mem (List.mem_map.2 ⟨g, hg, rfl⟩)
  obtain ⟨m, hmk₀, n₁, hmn₁, hface⟩ := exists_forall_lt_real_linked_orthantFace p hθ hp1 hη k₀
  obtain ⟨n₂, huniq⟩ := exists_forall_le_lt_real_uniqZone p m hη
  set M := max n₁ n₂ with hM
  have hmM : m ≤ M := (le_of_lt hmn₁).trans (le_max_left _ _)
  have hmM' : m < M := hmn₁.trans_le (le_max_left _ _)
  -- the number of seeds `k`, of contacts `N`, of levels
  set q : ℝ := 1 - (p : ℝ) ^ seedBound d M with hq
  have hq0 : 0 ≤ q := by rw [hq, sub_nonneg]; exact pow_le_one₀ p.2.1 p.2.2
  have hq1 : q < 1 := by rw [hq]; linarith [pow_pos hp0 (seedBound d M)]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδpos hq1
  set N := LData.Ncont d M k with hN
  set K₀ : ℝ := 1 / (1 - (p : ℝ)) ^ (2 * d * N) with hK₀
  set Lcount : ℕ := ⌈K₀ / δ⌉₊ + 1 with hLcount
  set j₀ : ℕ := 2 * M + 2 with hj₀
  set j₁ : ℕ := j₀ + Lcount - 1 with hj₁
  set R : ℕ := j₁ + M + ℓmax + 2 with hR
  refine ⟨R, fun W Sfin D lo hi T o hfin hsub hDS ho hoD hBR htgt hTD hTne hreach => ?_⟩
  set μ := prodBernoulli W with hμ
  -- `lo ≤ hi`, else `B = ∅`
  have hlohi : lo ≤ hi := by
    by_contra hlt
    have : Finset.Icc lo hi = ∅ := Finset.Icc_eq_empty hlt
    rw [this] at hreach
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, measureReal_empty] at hreach
    linarith
  -- the level data and hypotheses
  set L : LData d := ⟨lo, hi, o, Sfin⟩ with hLdef
  have hL : LHyp L W p D (R - 1) :=
    { sub := hsub
      fin := hfin
      DS := hDS
      encl := by
        have : R - 1 + 1 = R := by omega
        rw [this]; exact hBR
      o_not := hoD
      o_mem := ho }
  -- Step II
  have hj₁R : j₁ ≤ R - 1 := by omega
  have hcard : ((Finset.Icc j₀ j₁).card : ℝ) = Lcount := by
    rw [Nat.card_Icc]; congr 1; omega
  have hJ : 1 / (1 - (p : ℝ)) ^ (2 * d * N) ≤ δ * ((Finset.Icc j₀ j₁).card : ℝ) := by
    rw [hcard, hLcount]
    push_cast
    have h1 : K₀ / δ ≤ ⌈K₀ / δ⌉₊ := Nat.le_ceil _
    have h2 : K₀ = δ * (K₀ / δ) := by field_simp
    rw [← hK₀]
    nlinarith
  obtain ⟨j, hjJ, hII⟩ := hL.stepII hp1 (N := N) hj₁R hJ hreach
  obtain ⟨hj₀j, hjj₁⟩ := Finset.mem_Icc.1 hjJ
  have hjR : j ≤ R - 1 := hjj₁.trans hj₁R
  have hjM : 2 * M + 2 ≤ j := hj₀j
  have hwide : ∀ k', L.Lo j k' + 2 * M + 2 ≤ L.Hi j k' := by
    intro k'
    simp only [LData.Lo, LData.Hi, Pi.sub_apply, Pi.add_apply, Pi.natCast_apply]
    have : L.lo k' ≤ L.hi k' := hlohi k'
    omega
  -- the shell
  set S := L.X (j - 1) \ L.X (j - (2 * M + 2)) with hSdef
  have hS : S ⊆ Finset.Icc (L.Lo j + 1) (L.Hi j - 1) := LData.shell_subset_shrink (by omega)
  have hSD : S ⊆ D := (Finset.sdiff_subset).trans (hL.X_subset_D (by omega))
  -- Step III input
  have hIII : (1 - (p : ℝ) ^ seedBound d M) ^ k ≤ δ := hk.le
  -- the faces lie in the shell
  have hUS : ∀ x ∈ outerBoundary (zdGraph d) (L.X j), L.ufaceX j M x ⊆ S := by
    intro x hx
    obtain ⟨h, -⟩ := LData.winData_spec hwide hx
    refine (uface_subset_cube h).trans ?_
    change L.cubeX j M x ⊆ S
    rw [LData.cubeX_eq_ball]
    exact LData.ball_vX_subset_shell hjM hwide hx
  -- Step IV at every contact vertex: a relay reliable to `T` inside `D`
  have hIV : ∀ x ∈ outerBoundary (zdGraph d) (L.X j),
      1 - 3 * δ ≤ μ.real {ω | ∃ u ∈ L.ufaceX j M x,
        1 - δ < (prodBernoulli (pinW W (wireSet (↑S : Set (Site d))) ω)).real
          (⋃ t ∈ T, openConnIn (↑D : Set (Site d)) u t)} := by
    intro x hx
    set v := L.vX j M x with hv
    have hballS : GM.ball v M ⊆ S := LData.ball_vX_subset_shell hjM hwide hx
    have hballD : (↑(GM.ball v M) : Set (Site d)) ⊆ ↑D := Finset.coe_subset.2 (hballS.trans hSD)
    -- the target route from `v`
    have hvB : v ∈ Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) := by
      have := LData.vX_mem (L := L) (by omega) hwide hx
      exact Icc_enlarge_mono (show j - 1 ≤ R by omega) this
    obtain ⟨ℓ, hRℓ, g, hg, hQ, hF⟩ := htgt.hit v hvB
    have hMℓ : M < ℓ := lt_of_lt_of_le (by omega) hRℓ
    -- (1) uniqueness zone
    have h1 : 1 - δ ^ 2 < μ.real (uniqZoneAt v m M) := by
      rw [hμ, hsub.real_eq_bondPercolation (determinedBy_uniqZoneAt v m M (wireSet_mono hballD))
        (measurableSet_uniqZoneAt v m M), real_uniqZoneAt_eq]
      exact huniq M (le_max_right _ _)
    -- (2) the face
    have h2 : 1 - δ ^ 2 < μ.real (linkIn (↑(GM.ball v M)) (GM.ball v m) (L.ufaceX j M x)) := by
      obtain ⟨a, τ, hsubU⟩ := LData.orthantFace_image_subset_ufaceX hwide hx
      have hmono : linkIn (↑(GM.ball v M)) (GM.ball v m) ((orthantFace a τ M).image (· + v)) ⊆
          linkIn (↑(GM.ball v M)) (GM.ball v m) (L.ufaceX j M x) := linkIn_mono le_rfl le_rfl hsubU
      refine lt_of_lt_of_le ?_ (measureReal_mono hmono)
      rw [hμ, hsub.real_eq_bondPercolation (determinedBy_linkIn _ _ _ (wireSet_mono hballD))]
      · have e1 : GM.ball v M = (box d M).image (· + v) := rfl
        have e2 : GM.ball v m = (box d m).image (· + v) := rfl
        rw [e1, e2, real_linkIn_image_add]
        exact hface M (le_max_left _ _) a τ
      · exact measurableSet_linkIn _ _ _
    -- (3) the target route
    have h3 : 1 - δ ^ 2 < μ.real (linkIn (↑(g.Qset ℓ v)) (GM.ball v m) (g.Fset ℓ v)) := by
      rw [hμ, hsub.real_eq_bondPercolation (determinedBy_linkIn _ _ _ (wireSet_mono (Finset.coe_subset.2 hQ)))
        (measurableSet_linkIn _ _ _)]
      have e2 : GM.ball v m = (box d m).image (· + v) := rfl
      rw [g.Qset_eq_image ℓ v, g.Fset_eq_image ℓ v, e2, real_linkIn_image_add]
      exact hklspec g hg m ((hk₀le g hg).trans hmk₀) ℓ ((hℓle g hg).trans (by omega))
    exact stepIV_in (S := S) hsub hF hQ hmM hballS (LData.ufaceX_subset_innerBoundary hwide hx)
      (g.disjoint_Fset_ball hMℓ v) hδpos (Rg := (↑D : Set (Site d))) hballD (Finset.coe_subset.2 hQ) h1 h2 h3
  -- the gluing hypothesis in the required form: source `o ∉ D`, relays reliable to `T` inside `D`
  have hC3' : ∀ (w : Sym2 (Site d) → unitInterval), FinSupp w L.Sfin → ∀ (A : Finset (Site d)), A ⊆ L.Sfin →
      1 - δc < (prodBernoulli w).real (⋃ a ∈ A, openConn L.o a) →
      (∀ a ∈ A, 1 - δc < (prodBernoulli w).real (⋃ t ∈ T, openConnIn (↑D : Set (Site d)) a t)) →
      1 - ε / 2 < (prodBernoulli w).real (⋃ t ∈ T, openConn L.o t) := by
    intro w hw A hA hoA haT
    have hle : 1 - δ₀ ≤ 1 - δc := by linarith [min_le_left δ₀ 1]
    exact hC3 w L.Sfin hw.zero A T L.o (↑D : Set (Site d)) hA (hTD.trans hDS) ho hTne
      (fun h => hoD (Finset.mem_coe.1 h)) (hle.trans_lt hoA) fun a ha => hle.trans_lt (haT a ha)
  -- Step V
  exact hL.stepV_in (Rg := (↑D : Set (Site d))) hjR hwide hS hSD hε hε1 hδpos hδc' h3δ h12 hII hIII hUS
    hIV hC3'

/-- **Kozma–Nitzan 2024, Lemma 10 (the target lemma).** Assume Conjecture 3, `0 < p < 1` and `θ(p) >
 0`. For every `ε > 0` there is `δ > 0` such that for every finite of hittable geometries
 there is `R` with: for every finitely supported weighting `W` of `ℤ^d` with a lattice subbox `D ⊇
 B⟨R⟩` at parameter `p` (`B = Icc lo hi`), every nonempty target `T ⊆ D` with respect to `(B, D, R,
 H)` and every `o ∉ D`, `P_W(o ↔ B) > 1 - δ ⟹ P_W(o ↔ T) > 1 - ε`. Proof: Steps I–V of KN pp. 17–22,
 with Lemma 7 := `exists_forall_le_lt_real_uniqZone` and the full-face hittability (Lemma 9) :=
 `exists_forall_lt_real_linked_orthantFace`. [cite: KozmaNitzan2024, §4 Lemma 10 (pp. 17–22)]
-/
theorem targetLemma [NeZero d] (hC : KozmaNitzan2024_conjecture3) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) 0 p) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : List (Geom d), (∀ g ∈ H, IsHittable p g) → ∃ R : ℕ,
      ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
        (T : Finset (Site d)) (o : Site d),
        FinSupp W Sfin → IsSubbox W p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
        Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
        IsTarget T lo hi D R H → T ⊆ D → T.Nonempty →
        1 - δ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
          1 - ε < (prodBernoulli W).real (⋃ t ∈ T, openConn o t) := by
  refine targetLemma_avoiding (d := d) (fun ε' hε' => ?_) p hp0 hp1 hθ hε
  obtain ⟨δ, hδ, h⟩ := hC.openConn_set hε'
  refine ⟨δ, hδ, fun w Sf hw A T o Rg hA hT ho hne _ hoA haT => h (Site d) w Sf hw A T o hA hT ho hne hoA ?_⟩
  intro a ha
  refine (haT a ha).trans_le (measureReal_mono (Set.iUnion₂_mono fun t _ ω hω => ?_) (measure_ne_top _ _))
  rw [DCT16.mem_openConnIn_iff_pathIn] at hω
  exact reachable_of_pathIn hω

end KozmaNitzan

end Percolation.Literature

end
