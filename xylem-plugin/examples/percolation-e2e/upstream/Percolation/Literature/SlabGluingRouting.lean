import Percolation.Literature.SlabGluingFact2Core
import Percolation.Util.Linter

/-!
# DST 2016, §2.3, Fact 2 — the routing in the cleared box and the surgery at a point of `U(ω)`

Part of the bottom-up discharge of the Gluing Lemma of
Duminil-Copin–Sidoravicius–Tassion 2016 below Thm. 1 (`DuminilCopinSidoraviciusTassion2016`,
`HalfSpace.lean`). `SlabGluingFact2Core.lean` proves everything about ONE local surgery `ω ↦
ω^{(z)}` of the proof of Fact 2 (pp. 6–7 of arXiv:1401.7130) given its combinatorial data
`GlueGeom.Surgery G k ω`. This file CONSTRUCTS that data at every good point `z ∈ U(ω)`
(`GlueGeom.exists_surgery`), i.e. it supplies the step "there exist three disjoint self-avoiding
paths in `\overline{B_R}(z) ∖ {z}` connecting `u` to `u'`, `v` to `v'` and `w` to `w'` … such an `R`
exists since `k > 0`" (p. 6) in the form the formalisation needs:

* a toolkit of explicit lattice paths: planar straight segments, L-shaped paths, planar routing in
  a rectangle avoiding obstacles on one row/column (`exists_ppath_avoiding_row`, by the obvious
  detours), one obstacle, a domino; vertical slab segments `vcol`/`vline`, lifts `liftH` of
  planar paths to a fixed height, gluing of self-avoiding slab paths (`SPath.trans`);
* `RouteSpec` — what the routing must produce: the rerouted piece `L` from `E₁` (first vertex of
  `γ_min(ω)` in `D̄`) to `E₂` (last one), an attachment vertex `c`, and the branch `Br` to `w'`
  (the last vertex in `D̄` of the (P2)-witness path), with DST's order condition
  "`(z,v) ≺ (z,w)`" as `vKey (successor of c) < vKey (Br.head)`;
* the routing `exists_route` by an explicit case analysis (templates `route_main` — columns of
  `E₁`, `E₂` distinct: descend to the bottom layer, planar path, climb; branch through the top
  layer — and `route_desc/beta/delta1/delta0/micro*` for `E₁`, `E₂` in one column), the order
  condition holding by construction (heights first: the key `vKey` is height-lexicographic);
* the cleared box `GlueGeom.Dbox z = [max(z₁-3,n), min(z₁+3,3n)] × [z₂-3, min(z₂+3, max(3n,y+n))]`
  (the formalisation's `\overline{B_R(z)}`, `R = 3`, clipped to `B_{3n} ∪ B'_n` and to `x ≥ n`),
  the routing rectangle `RPbox` (its part in `B_{3n}`, minus the right column when `Z_n` covers
  it), the bounded excluded sets `zBad` (boxes cut partially by `Z_n`) and `lastBad` (boxes that
  could contain the end of `γ_min`), and `GlueGeom.exists_surgery`: for `ω ∈ 𝒳` a lattice
  configuration, `z ∈ U(ω) ∖ (zBad ∪ lastBad)`, in the RESTRICTED range `u_{3n} + 1 ≤ n` (the case
  `u_{3n} = n` of `GlueGeom.InRange` is not treated, see Design choices), a `Surgery` with
  `D ⊆ z + B_3` exists.

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, CPAM 69 (2016), 1397–1411, arXiv:1401.7130: §2.3, proof of
  Fact 2 (pp. 6–7 of the arXiv text: the choice of `R`, the three disjoint paths `γ_u, γ_v, γ_w`,
  "`(z,v) ≺ (z,w)`").
* C. M. Newman, V. Tassion, W. Wu, *Critical percolation and the minimal spanning tree in slabs*,
  CPAM 70 (2017), §3.2, Definition 3.7 and proof of Thm. 3.9 [NewmanTassionWu2017].

## Design choices

* `R = 3` and a bounded set of excluded points (`zBad ∪ lastBad`, at most `48 + 49` points of any
  `U(ω)`) replace the printed "for any site `z`": Fact 2 only needs the surgery at all but
  boundedly many points of `U(ω)` (see `SlabGluingFact2.lean`).
* The attachment vertex is `c = E₁` whenever possible, the rerouted piece leaving `E₁` downwards
  (or the branch leaving it upwards), which makes the order condition automatic; only the case
  of `E₁` below `E₂` in one column needs the side-column templates.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels SimpleGraph

variable {k : ℕ}

/-! ## Coordinates of slab vertices -/

/-- The height (first coordinate) of a slab vertex, as a natural number. [folklore] -/
def ht (v : slab 3 k) : ℕ := (v.1 0).toNat

/-- The height, cast back to `ℤ`, is the first coordinate. [folklore] -/
theorem ht_coe (v : slab 3 k) : ((ht v : ℕ) : ℤ) = v.1 0 := Int.toNat_of_nonneg v.2.1

/-- Heights are at most `k`. [folklore] -/
theorem ht_le (v : slab 3 k) : ht v ≤ k := by
  have h := v.2.2
  have := ht_coe v
  omega

/-- The planar part of `vtx z h` is `z`. [folklore] -/
theorem planar_vtx (z : ℤ × ℤ) (h : ℕ) : planar k (vtx k z h) = z := by
  simp [vtx, planar]

/-- The first coordinate of `vtx z h` is `h` (for `h ≤ k`). [folklore] -/
theorem vtx_apply_zero {h : ℕ} (hh : h ≤ k) (z : ℤ × ℤ) : (vtx k z h).1 0 = h := by
  simp [vtx, Nat.min_eq_left hh]

/-- The height of `vtx z h` is `h` (for `h ≤ k`). [folklore] -/
theorem ht_vtx {h : ℕ} (hh : h ≤ k) (z : ℤ × ℤ) : ht (vtx k z h) = h := by
  have := ht_coe (vtx k z h)
  rw [vtx_apply_zero hh] at this
  exact_mod_cast this

/-- A vertex is `vtx` of its planar part and its height. [folklore] -/
theorem vtx_planar_ht (v : slab 3 k) : vtx k (planar k v) (ht v) = v :=
  (eq_vtx_of_height k (ht_coe v).symm).symm

/-- Two slab vertices agree iff their planar parts and heights agree. [folklore] -/
theorem slab_ext_iff (v w : slab 3 k) : v = w ↔ planar k v = planar k w ∧ ht v = ht w := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← vtx_planar_ht v, ← vtx_planar_ht w, h1, h2]

/-- Adjacency in the slab in coordinates. [folklore] -/
theorem slab_adj_iff (v w : slab 3 k) :
    (slabGraph 3 k).Adj v w ↔
      (ht v = ht w ∧ planarAdj (planar k v) (planar k w)) ∨
        (planar k v = planar k w ∧ (ht w = ht v + 1 ∨ ht v = ht w + 1)) := by
  have e : (slabGraph 3 k).Adj v w ↔ (zdGraph 3).Adj v.1 w.1 := Iff.rfl
  rw [e, zdGraph_three_adj_iff]
  have hv := ht_coe v
  have hw := ht_coe w
  simp only [planar]
  constructor
  · rintro (⟨h0, hp⟩ | ⟨hp, h0⟩)
    · left; exact ⟨by omega, hp⟩
    · right; exact ⟨hp, by omega⟩
  · rintro (⟨h0, hp⟩ | ⟨hp, h0⟩)
    · left; exact ⟨by omega, hp⟩
    · right; exact ⟨hp, by omega⟩

/-- Planar-adjacent points give adjacent vertices at every height. [folklore] -/
theorem vtx_adj_vtx_planar {z w : ℤ × ℤ} (hzw : planarAdj z w) (h : ℕ) :
    (slabGraph 3 k).Adj (vtx k z h) (vtx k w h) := by
  rw [slab_adj_iff]
  left
  exact ⟨rfl, by rwa [planar_vtx, planar_vtx]⟩

/-- Consecutive heights over a point give adjacent vertices. [folklore] -/
theorem vtx_adj_vtx_succ (z : ℤ × ℤ) {h : ℕ} (hh : h + 1 ≤ k) :
    (slabGraph 3 k).Adj (vtx k z h) (vtx k z (h + 1)) := by
  rw [slab_adj_iff]
  right
  refine ⟨by rw [planar_vtx, planar_vtx], Or.inl ?_⟩
  rw [ht_vtx hh, ht_vtx (by omega)]

/-! ## Vertical and lifted pieces -/

variable (k)

/-- The vertical segment over the planar point `c`, heights `lo, lo+1, …, hi` (empty if `lo > hi`).
[folklore] -/
def vcol (c : ℤ × ℤ) (lo hi : ℕ) : List (slab 3 k) :=
  (List.range (hi + 1 - lo)).map fun i => vtx k c (lo + i)

/-- A planar list lifted to height `h`. [folklore] -/
def liftH (h : ℕ) (l : List (ℤ × ℤ)) : List (slab 3 k) := l.map fun z => vtx k z h

variable {k}

/-- Membership in a vertical segment. [folklore] -/
theorem mem_vcol_iff {c : ℤ × ℤ} {lo hi : ℕ} (hhi : hi ≤ k) (v : slab 3 k) :
    v ∈ vcol k c lo hi ↔ planar k v = c ∧ lo ≤ ht v ∧ ht v ≤ hi := by
  simp only [vcol, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hle : lo + i ≤ k := by omega
    rw [planar_vtx, ht_vtx hle]
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨hp, h1, h2⟩
    refine ⟨ht v - lo, by omega, ?_⟩
    rw [show lo + (ht v - lo) = ht v by omega, ← hp, vtx_planar_ht]

/-- A vertical segment is a lattice chain. [folklore] -/
theorem vcol_isChain (c : ℤ × ℤ) {lo hi : ℕ} (hhi : hi ≤ k) :
    (vcol k c lo hi).IsChain (fun a b => (slabGraph 3 k).Adj a b) := by
  rw [vcol, List.isChain_map]
  rcases Nat.eq_zero_or_eq_succ_pred (hi + 1 - lo) with h0 | hs
  · rw [h0]; simp
  · rw [hs, List.isChain_range_succ]
    intro m hm
    rw [show lo + m.succ = (lo + m) + 1 by omega]
    exact vtx_adj_vtx_succ c (by omega)

/-- A vertical segment has no duplicates. [folklore] -/
theorem vcol_nodup (c : ℤ × ℤ) {lo hi : ℕ} (hhi : hi ≤ k) : (vcol k c lo hi).Nodup := by
  refine (List.nodup_range).map_on fun i hi' j hj' hij => ?_
  rw [List.mem_range] at hi' hj'
  have h1 := congrArg ht hij
  rwa [ht_vtx (by omega), ht_vtx (by omega), Nat.add_left_cancel_iff] at h1

/-- The first vertex of a vertical segment. [folklore] -/
theorem head?_vcol (c : ℤ × ℤ) {lo hi : ℕ} (h : lo ≤ hi) : (vcol k c lo hi).head? = some (vtx k c lo) := by
  rw [vcol, List.head?_map, show hi + 1 - lo = (hi - lo) + 1 by omega, List.range_succ_eq_map]
  simp

/-- The last vertex of a vertical segment. [folklore] -/
theorem getLast?_vcol (c : ℤ × ℤ) {lo hi : ℕ} (h : lo ≤ hi) : (vcol k c lo hi).getLast? = some (vtx k c hi) := by
  rw [vcol, List.getLast?_map, show hi + 1 - lo = (hi - lo) + 1 by omega, List.getLast?_range]
  simp
  congr 1; omega

/-- A non-empty vertical segment. [folklore] -/
theorem vcol_ne_nil {c : ℤ × ℤ} {lo hi : ℕ} (h : lo ≤ hi) : vcol k c lo hi ≠ [] := by
  intro he
  have := head?_vcol (k := k) c h
  rw [he] at this; simp at this

/-- Membership in a lifted list. [folklore] -/
theorem mem_liftH_iff {h : ℕ} (hh : h ≤ k) {l : List (ℤ × ℤ)} (v : slab 3 k) :
    v ∈ liftH k h l ↔ planar k v ∈ l ∧ ht v = h := by
  simp only [liftH, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [planar_vtx, ht_vtx hh]
    exact ⟨hz, rfl⟩
  · rintro ⟨hp, hv⟩
    exact ⟨planar k v, hp, by rw [← hv, vtx_planar_ht]⟩

/-- A lifted planar chain is a lattice chain. [folklore] -/
theorem liftH_isChain (h : ℕ) {l : List (ℤ × ℤ)} (hl : l.IsChain planarAdj) :
    (liftH k h l).IsChain (fun a b => (slabGraph 3 k).Adj a b) := by
  rw [liftH, List.isChain_map]
  exact hl.imp fun a b hab => vtx_adj_vtx_planar hab h

/-- Lifting preserves `Nodup`. [folklore] -/
theorem liftH_nodup {h : ℕ} {l : List (ℤ × ℤ)} (hl : l.Nodup) : (liftH k h l).Nodup :=
  hl.map_on fun a _ b _ hab => by
    have := congrArg (planar k) hab
    rwa [planar_vtx, planar_vtx] at this

/-- The head of a lifted list. [folklore] -/
theorem head?_liftH (h : ℕ) (l : List (ℤ × ℤ)) : (liftH k h l).head? = l.head?.map fun z => vtx k z h := by
  rw [liftH, List.head?_map]

/-- The last element of a lifted list. [folklore] -/
theorem getLast?_liftH (h : ℕ) (l : List (ℤ × ℤ)) :
    (liftH k h l).getLast? = l.getLast?.map fun z => vtx k z h := by
  rw [liftH, List.getLast?_map]

/-- Lifting preserves non-emptiness. [folklore] -/
theorem liftH_ne_nil {h : ℕ} {l : List (ℤ × ℤ)} (hl : l ≠ []) : liftH k h l ≠ [] := by
  simpa [liftH] using hl

/-! ## Planar straight segments -/

/-- The planar points `f 0, f 1, …, f n`. [folklore] -/
def pseg (f : ℕ → ℤ × ℤ) (n : ℕ) : List (ℤ × ℤ) := (List.range (n + 1)).map f

/-- Segments are non-empty. [folklore] -/
theorem pseg_ne_nil (f : ℕ → ℤ × ℤ) (n : ℕ) : pseg f n ≠ [] := by simp [pseg]

/-- The first point of a segment. [folklore] -/
theorem head?_pseg (f : ℕ → ℤ × ℤ) (n : ℕ) : (pseg f n).head? = some (f 0) := by
  rw [pseg, List.head?_map, List.range_succ_eq_map]; simp

/-- The last point of a segment. [folklore] -/
theorem getLast?_pseg (f : ℕ → ℤ × ℤ) (n : ℕ) : (pseg f n).getLast? = some (f n) := by
  rw [pseg, List.getLast?_map, List.getLast?_range]; simp

/-- Membership in a segment. [folklore] -/
theorem mem_pseg_iff (f : ℕ → ℤ × ℤ) (n : ℕ) (z : ℤ × ℤ) : z ∈ pseg f n ↔ ∃ i, i ≤ n ∧ f i = z := by
  simp only [pseg, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩

/-- A segment of consecutive lattice neighbours is a chain. [folklore] -/
theorem pseg_isChain {f : ℕ → ℤ × ℤ} {n : ℕ} (hf : ∀ i < n, planarAdj (f i) (f (i + 1))) :
    (pseg f n).IsChain planarAdj := by
  rw [pseg, List.isChain_map, List.isChain_range_succ]
  exact fun m hm => hf m hm

/-- An injectively parametrised segment has no duplicates. [folklore] -/
theorem pseg_nodup {f : ℕ → ℤ × ℤ} {n : ℕ} (hf : ∀ i ≤ n, ∀ j ≤ n, f i = f j → i = j) : (pseg f n).Nodup := by
  refine (List.nodup_range).map_on fun i hi j hj hij => ?_
  rw [List.mem_range] at hi hj
  exact hf i (by omega) j (by omega) hij

/-- `planarAdj` is symmetric. [folklore] -/
theorem planarAdj_symm {z w : ℤ × ℤ} (h : planarAdj z w) : planarAdj w z := by
  unfold planarAdj at h ⊢; tauto

/-- A planar self-avoiding lattice path from `s` to `t` (as a vertex list). [folklore] -/
structure PPath (l : List (ℤ × ℤ)) (s t : ℤ × ℤ) : Prop where
  ne_nil : l ≠ []
  chain : l.IsChain planarAdj
  nodup : l.Nodup
  head : l.head? = some s
  last : l.getLast? = some t

/-- Reversal of a planar path. [folklore] -/
theorem PPath.reverse {l : List (ℤ × ℤ)} {s t : ℤ × ℤ} (h : PPath l s t) : PPath l.reverse t s where
  ne_nil := by simpa using h.ne_nil
  chain := by
    rw [List.isChain_reverse]
    exact h.chain.imp fun a b hab => planarAdj_symm hab
  nodup := List.nodup_reverse.2 h.nodup
  head := by rw [List.head?_reverse, h.last]
  last := by rw [List.getLast?_reverse, h.head]

/-- A planar path contains its last point. [folklore] -/
theorem PPath.last_mem {l : List (ℤ × ℤ)} {s t : ℤ × ℤ} (h : PPath l s t) : t ∈ l :=
  List.mem_of_getLast? h.last

/-- **Horizontal segment**: a straight planar path along the row `r` from `(a, r)` to `(b, r)`,
visiting exactly the points of the row between them. [folklore] -/
theorem exists_hpath (r a b : ℤ) : ∃ l, PPath l (a, r) (b, r) ∧
    ∀ z : ℤ × ℤ, z ∈ l ↔ z.2 = r ∧ min a b ≤ z.1 ∧ z.1 ≤ max a b := by
  -- ascending version
  have up : ∀ a b : ℤ, a ≤ b → ∃ l, PPath l (a, r) (b, r) ∧
      ∀ z : ℤ × ℤ, z ∈ l ↔ z.2 = r ∧ a ≤ z.1 ∧ z.1 ≤ b := by
    intro a b hab
    refine ⟨pseg (fun i => (a + i, r)) (b - a).toNat, ⟨pseg_ne_nil _ _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact pseg_isChain fun i _ => by left; left; simp; ring
    · exact pseg_nodup fun i _ j _ h => by simpa using h
    · rw [head?_pseg]; simp
    · rw [getLast?_pseg]; simp; omega
    · intro z
      rw [mem_pseg_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩; simp; omega
      · rintro ⟨h2, h1, h3⟩
        refine ⟨(z.1 - a).toNat, by omega, ?_⟩
        ext <;> simp <;> omega
  rcases le_total a b with hab | hab
  · obtain ⟨l, hl, hmem⟩ := up a b hab
    exact ⟨l, hl, fun z => by rw [hmem, min_eq_left hab, max_eq_right hab]⟩
  · obtain ⟨l, hl, hmem⟩ := up b a hab
    refine ⟨l.reverse, hl.reverse, fun z => ?_⟩
    rw [List.mem_reverse, hmem, min_eq_right hab, max_eq_left hab]

/-- **Vertical planar segment** along the column `x` from `(x, a)` to `(x, b)`. [folklore] -/
theorem exists_vpath (x a b : ℤ) : ∃ l, PPath l (x, a) (x, b) ∧
    ∀ z : ℤ × ℤ, z ∈ l ↔ z.1 = x ∧ min a b ≤ z.2 ∧ z.2 ≤ max a b := by
  have up : ∀ a b : ℤ, a ≤ b → ∃ l, PPath l (x, a) (x, b) ∧
      ∀ z : ℤ × ℤ, z ∈ l ↔ z.1 = x ∧ a ≤ z.2 ∧ z.2 ≤ b := by
    intro a b hab
    refine ⟨pseg (fun i => (x, a + i)) (b - a).toNat, ⟨pseg_ne_nil _ _, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact pseg_isChain fun i _ => by right; left; simp; ring
    · exact pseg_nodup fun i _ j _ h => by simpa using h
    · rw [head?_pseg]; simp
    · rw [getLast?_pseg]; simp; omega
    · intro z
      rw [mem_pseg_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩; simp; omega
      · rintro ⟨h2, h1, h3⟩
        refine ⟨(z.2 - a).toNat, by omega, ?_⟩
        ext <;> simp <;> omega
  rcases le_total a b with hab | hab
  · obtain ⟨l, hl, hmem⟩ := up a b hab
    exact ⟨l, hl, fun z => by rw [hmem, min_eq_left hab, max_eq_right hab]⟩
  · obtain ⟨l, hl, hmem⟩ := up b a hab
    refine ⟨l.reverse, hl.reverse, fun z => ?_⟩
    rw [List.mem_reverse, hmem, min_eq_right hab, max_eq_left hab]

/-- **Concatenation of planar paths** at a common vertex: `l₁` from `s` to `m` and `l₂` from `m` to
`t`, meeting only at `m`, give the path `l₁ ++ l₂.tail` from `s` to `t`. [folklore] -/
theorem PPath.trans {l₁ l₂ : List (ℤ × ℤ)} {s m t : ℤ × ℤ} (h₁ : PPath l₁ s m) (h₂ : PPath l₂ m t)
    (hdisj : ∀ z ∈ l₁, z ∈ l₂ → z = m) : PPath (l₁ ++ l₂.tail) s t ∧
      ∀ z, z ∈ l₁ ++ l₂.tail ↔ z ∈ l₁ ∨ z ∈ l₂ := by
  obtain ⟨m', r, rfl⟩ := List.exists_cons_of_ne_nil h₂.ne_nil
  have hm' : m = m' := by have := h₂.head; simp at this; exact this.symm
  subst hm'
  have hmr : m ∉ r := (List.nodup_cons.1 h₂.nodup).1
  refine ⟨⟨by simp [h₁.ne_nil], ?_, ?_, ?_, ?_⟩, fun z => ?_⟩
  · rw [List.isChain_append]
    refine ⟨h₁.chain, h₂.chain.tail, fun x hx y hy => ?_⟩
    rw [h₁.last, Option.mem_def, Option.some.injEq] at hx
    subst hx
    have hc := h₂.chain
    rw [List.isChain_cons] at hc
    exact hc.1 y hy
  · rw [List.nodup_append]
    refine ⟨h₁.nodup, (List.nodup_cons.1 h₂.nodup).2, fun a ha b hb hab => ?_⟩
    subst hab
    rw [List.tail_cons] at hb
    have := hdisj a ha (List.mem_cons_of_mem _ hb)
    subst this
    exact hmr hb
  · rw [List.head?_append, h₁.head]; rfl
  · rw [List.getLast?_append, List.tail_cons]
    cases hr : r with
    | nil =>
      have := h₂.last
      rw [hr] at this
      simp at this
      subst this
      simpa using h₁.last
    | cons y ys =>
      have := h₂.last
      rw [hr, List.getLast?_cons_cons] at this
      rw [this]; rfl
  · rw [List.mem_append, List.tail_cons, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl h
      · exact Or.inl h₁.last_mem
      · exact Or.inr h

/-- **L-shaped path**, vertical leg first: from `s` along its column to the row of `t`, then along
that row to `t`. [folklore] -/
theorem exists_lpath_vh (s t : ℤ × ℤ) : ∃ l, PPath l s t ∧
    ∀ z : ℤ × ℤ, z ∈ l ↔ (z.1 = s.1 ∧ min s.2 t.2 ≤ z.2 ∧ z.2 ≤ max s.2 t.2) ∨
      (z.2 = t.2 ∧ min s.1 t.1 ≤ z.1 ∧ z.1 ≤ max s.1 t.1) := by
  obtain ⟨l₁, h₁, hm₁⟩ := exists_vpath s.1 s.2 t.2
  obtain ⟨l₂, h₂, hm₂⟩ := exists_hpath t.2 s.1 t.1
  obtain ⟨h, hm⟩ := PPath.trans (m := (s.1, t.2)) h₁ h₂ fun z hz1 hz2 => by
    rw [hm₁] at hz1; rw [hm₂] at hz2
    exact Prod.ext hz1.1 hz2.1
  refine ⟨_, h, fun z => ?_⟩
  rw [hm, hm₁, hm₂]

/-- **L-shaped path**, horizontal leg first. [folklore] -/
theorem exists_lpath_hv (s t : ℤ × ℤ) : ∃ l, PPath l s t ∧
    ∀ z : ℤ × ℤ, z ∈ l ↔ (z.2 = s.2 ∧ min s.1 t.1 ≤ z.1 ∧ z.1 ≤ max s.1 t.1) ∨
      (z.1 = t.1 ∧ min s.2 t.2 ≤ z.2 ∧ z.2 ≤ max s.2 t.2) := by
  obtain ⟨l₁, h₁, hm₁⟩ := exists_hpath s.2 s.1 t.1
  obtain ⟨l₂, h₂, hm₂⟩ := exists_vpath t.1 s.2 t.2
  obtain ⟨h, hm⟩ := PPath.trans (m := (t.1, s.2)) h₁ h₂ fun z hz1 hz2 => by
    rw [hm₁] at hz1; rw [hm₂] at hz2
    exact Prod.ext hz2.1 hz1.1
  refine ⟨_, h, fun z => ?_⟩
  rw [hm, hm₁, hm₂]

/-- The discrete rectangle `[xL, xR] × [rB, rT]`. [folklore] -/
def boxR (xL xR rB rT : ℤ) : Set (ℤ × ℤ) := {z | xL ≤ z.1 ∧ z.1 ≤ xR ∧ rB ≤ z.2 ∧ z.2 ≤ rT}

/-- Membership in a discrete rectangle. [folklore] -/
@[simp] theorem mem_boxR_iff {xL xR rB rT : ℤ} (z : ℤ × ℤ) :
    z ∈ boxR xL xR rB rT ↔ xL ≤ z.1 ∧ z.1 ≤ xR ∧ rB ≤ z.2 ∧ z.2 ≤ rT := Iff.rfl

/-- **Planar routing avoiding obstacles on one row.** In a rectangle with at least two rows, two
distinct free points are joined by a self-avoiding lattice path inside the rectangle avoiding a
set `F` of obstacles all lying on one row `ρ`, provided some column `ξ` of the rectangle is free
on that row. [folklore] -/
theorem exists_ppath_avoiding_row {xL xR rB rT : ℤ} (hrow : rB < rT) {s t : ℤ × ℤ}
    (hs : s ∈ boxR xL xR rB rT) (ht : t ∈ boxR xL xR rB rT) (hst : s ≠ t)
    (F : Set (ℤ × ℤ)) (ρ : ℤ) (hF : ∀ f ∈ F, f.2 = ρ) (hsF : s ∉ F) (htF : t ∉ F)
    (ξ : ℤ) (hξ1 : xL ≤ ξ) (hξ2 : ξ ≤ xR) (hξF : (ξ, ρ) ∉ F) :
    ∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT ∧ z ∉ F := by
  rw [mem_boxR_iff] at hs ht
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  simp only at hs ht
  have hne : s1 ≠ t1 ∨ s2 ≠ t2 := by
    by_contra h; push Not at h; exact hst (Prod.ext h.1 h.2)
  -- a point of `F` is `(x, ρ)`
  have hFρ : ∀ z : ℤ × ℤ, z ∈ F → z.2 ≠ ρ → False := fun z hz h => h (hF z hz)
  by_cases hs2 : s2 = ρ
  · by_cases ht2 : t2 = ρ
    · -- (1) both on the obstacle row: detour via an adjacent row
      have hst1 : s1 ≠ t1 := by
        rcases hne with h | h
        · exact h
        · exact absurd (hs2.trans ht2.symm) h
      set ρ' : ℤ := if ρ < rT then ρ + 1 else ρ - 1 with hρ'
      have hρ'1 : rB ≤ ρ' ∧ ρ' ≤ rT ∧ ρ' ≠ ρ := by
        rw [hρ']; split_ifs <;> omega
      obtain ⟨l₁, h₁, hm₁⟩ := exists_lpath_vh (s1, s2) (t1, ρ')
      obtain ⟨l₂, h₂, hm₂⟩ := exists_vpath t1 ρ' t2
      obtain ⟨h, hm⟩ := PPath.trans h₁ h₂ fun z hz1 hz2 => by
        rw [hm₁] at hz1; rw [hm₂] at hz2
        simp only at hz1 hz2
        rcases hz1 with hz1 | hz1
        · exact absurd (hz1.1.symm.trans hz2.1) hst1
        · exact Prod.ext hz2.1 hz1.1
      refine ⟨_, h, fun z hz => ?_⟩
      rw [hm, hm₁, hm₂] at hz
      simp only at hz
      refine ⟨?_, fun hzF => ?_⟩
      · simp only [mem_boxR_iff]
        rcases hz with (hz | hz) | hz <;>
          · rw [min_le_iff, le_max_iff] at hz; omega
      · have h2 := hF z hzF
        rcases hz with (hz | hz) | hz
        · have : z = (s1, s2) := Prod.ext hz.1 (by rw [min_le_iff, le_max_iff] at hz; omega)
          subst this; exact hsF hzF
        · exact hρ'1.2.2 (hz.1.symm.trans h2)
        · have : z = (t1, t2) := Prod.ext hz.1 (by rw [min_le_iff, le_max_iff] at hz; omega)
          subst this; exact htF hzF
    · -- (2) `s` on the row, `t` off it: column of `s`, then row of `t`
      obtain ⟨l, h, hm⟩ := exists_lpath_vh (s1, s2) (t1, t2)
      refine ⟨l, h, fun z hz => ?_⟩
      rw [hm] at hz; simp only at hz
      refine ⟨?_, fun hzF => ?_⟩
      · simp only [mem_boxR_iff]
        rcases hz with hz | hz <;>
          · rw [min_le_iff, le_max_iff] at hz; omega
      · have h2 := hF z hzF
        rcases hz with hz | hz
        · have : z = (s1, s2) := Prod.ext hz.1 (by omega)
          subst this; exact hsF hzF
        · exact ht2 (hz.1.symm.trans h2)
  · by_cases ht2 : t2 = ρ
    · -- (3) `t` on the row, `s` off it: row of `s`, then column of `t`
      obtain ⟨l, h, hm⟩ := exists_lpath_hv (s1, s2) (t1, t2)
      refine ⟨l, h, fun z hz => ?_⟩
      rw [hm] at hz; simp only at hz
      refine ⟨?_, fun hzF => ?_⟩
      · simp only [mem_boxR_iff]
        rcases hz with hz | hz <;>
          · rw [min_le_iff, le_max_iff] at hz; omega
      · have h2 := hF z hzF
        rcases hz with hz | hz
        · exact hs2 (hz.1.symm.trans h2)
        · have : z = (t1, t2) := Prod.ext hz.1 (by omega)
          subst this; exact htF hzF
    · -- (4)/(5) both off the row
      by_cases hA : ((s1, ρ) : ℤ × ℤ) ∉ F ∨ ¬(min s2 t2 ≤ ρ ∧ ρ ≤ max s2 t2)
      · -- column of `s` then row of `t`
        obtain ⟨l, h, hm⟩ := exists_lpath_vh (s1, s2) (t1, t2)
        refine ⟨l, h, fun z hz => ?_⟩
        rw [hm] at hz; simp only at hz
        refine ⟨?_, fun hzF => ?_⟩
        · simp only [mem_boxR_iff]
          rcases hz with hz | hz <;>
            · rw [min_le_iff, le_max_iff] at hz; omega
        · have h2 := hF z hzF
          rcases hz with hz | hz
          · have hz' : z = (s1, ρ) := Prod.ext hz.1 h2
            rcases hA with hA | hA
            · exact hA (hz' ▸ hzF)
            · exact hA ⟨h2 ▸ hz.2.1, h2 ▸ hz.2.2⟩
          · exact ht2 (hz.1.symm.trans h2)
      · by_cases hB : ((t1, ρ) : ℤ × ℤ) ∉ F
        · -- row of `s` then column of `t`
          obtain ⟨l, h, hm⟩ := exists_lpath_hv (s1, s2) (t1, t2)
          refine ⟨l, h, fun z hz => ?_⟩
          rw [hm] at hz; simp only at hz
          refine ⟨?_, fun hzF => ?_⟩
          · simp only [mem_boxR_iff]
            rcases hz with hz | hz <;>
              · rw [min_le_iff, le_max_iff] at hz; omega
          · have h2 := hF z hzF
            rcases hz with hz | hz
            · exact hs2 (hz.1.symm.trans h2)
            · have hz' : z = (t1, ρ) := Prod.ext hz.1 h2
              exact hB (hz' ▸ hzF)
        · -- (5c) through the free column `ξ`
          push Not at hA hB
          obtain ⟨hA, hρs, hρt⟩ := hA
          have hξs : ξ ≠ s1 := fun h => hξF (by rw [h]; exact hA)
          have hξt : ξ ≠ t1 := fun h => hξF (by rw [h]; exact hB)
          have hs2t2 : s2 ≠ t2 := by
            intro h
            rw [← h, min_self] at hρs
            rw [← h, max_self] at hρt
            exact hs2 (le_antisymm hρs hρt)
          obtain ⟨l₁, h₁, hm₁⟩ := exists_lpath_hv (s1, s2) (ξ, t2)
          obtain ⟨l₂, h₂, hm₂⟩ := exists_hpath t2 ξ t1
          obtain ⟨h, hm⟩ := PPath.trans h₁ h₂ fun z hz1 hz2 => by
            rw [hm₁] at hz1; rw [hm₂] at hz2
            simp only at hz1 hz2
            rcases hz1 with hz1 | hz1
            · exact absurd (hz1.1.symm.trans hz2.1) hs2t2
            · exact Prod.ext hz1.1 hz2.1
          refine ⟨_, h, fun z hz => ?_⟩
          rw [hm, hm₁, hm₂] at hz
          simp only at hz
          refine ⟨?_, fun hzF => ?_⟩
          · simp only [mem_boxR_iff]
            rcases hz with (hz | hz) | hz <;>
              · rw [min_le_iff, le_max_iff] at hz; omega
          · have h2 := hF z hzF
            rcases hz with (hz | hz) | hz
            · exact hs2 (hz.1.symm.trans h2)
            · exact hξF (by have : z = (ξ, ρ) := Prod.ext hz.1 h2; exact this ▸ hzF)
            · exact ht2 (hz.1.symm.trans h2)

/-- Planar paths are mapped to planar paths by the coordinate swap. [folklore] -/
theorem PPath.swap {l : List (ℤ × ℤ)} {s t : ℤ × ℤ} (h : PPath l s t) :
    PPath (l.map Prod.swap) s.swap t.swap where
  ne_nil := by simpa using h.ne_nil
  chain := by
    rw [List.isChain_map]
    exact h.chain.imp fun a b hab => (planarAdj_planarSwap a b).2 hab
  nodup := h.nodup.map Prod.swap_injective
  head := by rw [List.head?_map, h.head]; rfl
  last := by rw [List.getLast?_map, h.last]; rfl

/-- **Planar routing avoiding obstacles on one column** (the transpose of
`exists_ppath_avoiding_row`). [folklore] -/
theorem exists_ppath_avoiding_col {xL xR rB rT : ℤ} (hcol : xL < xR) {s t : ℤ × ℤ}
    (hs : s ∈ boxR xL xR rB rT) (ht : t ∈ boxR xL xR rB rT) (hst : s ≠ t)
    (F : Set (ℤ × ℤ)) (κ : ℤ) (hF : ∀ f ∈ F, f.1 = κ) (hsF : s ∉ F) (htF : t ∉ F)
    (ξ : ℤ) (hξ1 : rB ≤ ξ) (hξ2 : ξ ≤ rT) (hξF : (κ, ξ) ∉ F) :
    ∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT ∧ z ∉ F := by
  have hs' : s.swap ∈ boxR rB rT xL xR := by
    rw [mem_boxR_iff] at hs ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; tauto
  have ht' : t.swap ∈ boxR rB rT xL xR := by
    rw [mem_boxR_iff] at ht ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; tauto
  have hξF' : ((ξ, κ) : ℤ × ℤ) ∉ Prod.swap '' F := by
    rintro ⟨g, hg, hgs⟩
    have : g = (κ, ξ) := by rw [← Prod.swap_swap g, hgs]; rfl
    exact hξF (this ▸ hg)
  obtain ⟨l, hl, hmem⟩ := exists_ppath_avoiding_row hcol hs' ht'
    (fun h => hst (Prod.swap_injective h)) (Prod.swap '' F) κ
    (by rintro f ⟨g, hg, rfl⟩; exact hF g hg)
    (by rintro ⟨g, hg, hgs⟩; exact hsF (Prod.swap_injective hgs ▸ hg))
    (by rintro ⟨g, hg, hgs⟩; exact htF (Prod.swap_injective hgs ▸ hg))
    ξ hξ1 hξ2 hξF'
  refine ⟨l.map Prod.swap, by simpa using hl.swap, fun z hz => ?_⟩
  rw [List.mem_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨hw1, hw2⟩ := hmem w hw
  refine ⟨?_, fun hzF => hw2 ⟨w.swap, hzF, Prod.swap_swap w⟩⟩
  rw [mem_boxR_iff] at hw1 ⊢; simp only [Prod.fst_swap, Prod.snd_swap]; tauto

/-! ## Self-avoiding lattice paths in the slab, as vertex lists -/

/-- A self-avoiding lattice path of the slab from `s` to `t`, as a vertex list. [folklore] -/
structure SPath (l : List (slab 3 k)) (s t : slab 3 k) : Prop where
  ne_nil : l ≠ []
  chain : l.IsChain (fun a b => (slabGraph 3 k).Adj a b)
  nodup : l.Nodup
  head : l.head? = some s
  last : l.getLast? = some t

/-- A slab path contains its last vertex. [folklore] -/
theorem SPath.last_mem {l : List (slab 3 k)} {s t : slab 3 k} (h : SPath l s t) : t ∈ l :=
  List.mem_of_getLast? h.last

/-- Reversal of a slab path. [folklore] -/
theorem SPath.reverse {l : List (slab 3 k)} {s t : slab 3 k} (h : SPath l s t) : SPath l.reverse t s where
  ne_nil := by simpa using h.ne_nil
  chain := by
    rw [List.isChain_reverse]
    exact h.chain.imp fun a b hab => hab.symm
  nodup := List.nodup_reverse.2 h.nodup
  head := by rw [List.head?_reverse, h.last]
  last := by rw [List.getLast?_reverse, h.head]

/-- **Gluing slab paths at a common vertex.** [folklore] -/
theorem SPath.trans {l₁ l₂ : List (slab 3 k)} {s m t : slab 3 k} (h₁ : SPath l₁ s m) (h₂ : SPath l₂ m t)
    (hdisj : ∀ z ∈ l₁, z ∈ l₂ → z = m) : SPath (l₁ ++ l₂.tail) s t ∧
      ∀ z, z ∈ l₁ ++ l₂.tail ↔ z ∈ l₁ ∨ z ∈ l₂ := by
  obtain ⟨m', r, rfl⟩ := List.exists_cons_of_ne_nil h₂.ne_nil
  have hm' : m = m' := by have := h₂.head; simp at this; exact this.symm
  subst hm'
  have hmr : m ∉ r := (List.nodup_cons.1 h₂.nodup).1
  refine ⟨⟨by simp [h₁.ne_nil], ?_, ?_, ?_, ?_⟩, fun z => ?_⟩
  · rw [List.isChain_append]
    refine ⟨h₁.chain, h₂.chain.tail, fun x hx y hy => ?_⟩
    rw [h₁.last, Option.mem_def, Option.some.injEq] at hx
    subst hx
    have hc := h₂.chain
    rw [List.isChain_cons] at hc
    exact hc.1 y hy
  · rw [List.nodup_append]
    refine ⟨h₁.nodup, (List.nodup_cons.1 h₂.nodup).2, fun a ha b hb hab => ?_⟩
    subst hab
    rw [List.tail_cons] at hb
    have := hdisj a ha (List.mem_cons_of_mem _ hb)
    subst this
    exact hmr hb
  · rw [List.head?_append, h₁.head]; rfl
  · rw [List.getLast?_append, List.tail_cons]
    cases hr : r with
    | nil =>
      have := h₂.last
      rw [hr] at this
      simp at this
      subst this
      simpa using h₁.last
    | cons y ys =>
      have := h₂.last
      rw [hr, List.getLast?_cons_cons] at this
      rw [this]; rfl
  · rw [List.mem_append, List.tail_cons, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl h
      · exact Or.inl h₁.last_mem
      · exact Or.inr h

variable (k)

/-- The vertical lattice path over `c` from height `h` to height `h'` (up or down). [folklore] -/
def vline (c : ℤ × ℤ) (h h' : ℕ) : List (slab 3 k) :=
  if h ≤ h' then vcol k c h h' else (vcol k c h' h).reverse

variable {k}

/-- Membership in a vertical path. [folklore] -/
theorem mem_vline_iff {c : ℤ × ℤ} {h h' : ℕ} (hh : h ≤ k) (hh' : h' ≤ k) (v : slab 3 k) :
    v ∈ vline k c h h' ↔ planar k v = c ∧ min h h' ≤ ht v ∧ ht v ≤ max h h' := by
  rw [vline]
  split_ifs with hle
  · rw [mem_vcol_iff hh', min_eq_left hle, max_eq_right hle]
  · rw [List.mem_reverse, mem_vcol_iff hh, min_eq_right (by omega), max_eq_left (by omega)]

/-- A vertical path is a slab path between its ends. [folklore] -/
theorem vline_spath (c : ℤ × ℤ) {h h' : ℕ} (hh : h ≤ k) (hh' : h' ≤ k) :
    SPath (vline k c h h') (vtx k c h) (vtx k c h') := by
  rw [vline]
  split_ifs with hle
  · exact ⟨vcol_ne_nil hle, vcol_isChain c hh', vcol_nodup c hh', head?_vcol c hle, getLast?_vcol c hle⟩
  · exact (show SPath (vcol k c h' h) (vtx k c h') (vtx k c h) from
      ⟨vcol_ne_nil (by omega), vcol_isChain c hh, vcol_nodup c hh, head?_vcol c (by omega),
        getLast?_vcol c (by omega)⟩).reverse

/-- The vertical path of length zero. [folklore] -/
theorem vline_self (c : ℤ × ℤ) (h : ℕ) : vline k c h h = [vtx k c h] := by
  rw [vline, if_pos le_rfl, vcol, show h + 1 - h = 1 by omega]
  simp

/-- Splitting off the first vertex of a vertical segment. [folklore] -/
theorem vcol_succ_left (c : ℤ × ℤ) {lo hi : ℕ} (h : lo ≤ hi) :
    vcol k c lo hi = vtx k c lo :: vcol k c (lo + 1) hi := by
  rw [vcol, vcol, show hi + 1 - lo = (hi + 1 - (lo + 1)) + 1 by omega, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  simp only [Nat.add_zero]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1; omega

/-- A vertical path of positive length starts with a unit step. [folklore] -/
theorem vline_eq_cons_cons_up (c : ℤ × ℤ) {h h' : ℕ} (hlt : h < h') :
    ∃ r, vline k c h h' = vtx k c h :: vtx k c (h + 1) :: r := by
  rw [vline, if_pos hlt.le, vcol_succ_left c hlt.le, vcol_succ_left c (by omega)]
  exact ⟨_, rfl⟩

/-- Splitting off the last vertex of a vertical segment. [folklore] -/
theorem vcol_concat_right (c : ℤ × ℤ) {lo hi : ℕ} (h : lo ≤ hi + 1) :
    vcol k c lo (hi + 1) = vcol k c lo hi ++ [vtx k c (hi + 1)] := by
  rw [vcol, vcol, show hi + 1 + 1 - lo = (hi + 1 - lo) + 1 by omega, List.range_succ, List.map_append,
    List.map_singleton, show lo + (hi + 1 - lo) = hi + 1 by omega]

/-- A descending vertical path of positive length starts with a unit step down. [folklore] -/
theorem vline_eq_cons_cons_down (c : ℤ × ℤ) {h h' : ℕ} (hlt : h' < h) :
    ∃ r, vline k c h h' = vtx k c h :: vtx k c (h - 1) :: r := by
  rw [vline, if_neg (by omega)]
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by omega⟩
  rw [vcol_concat_right c (by omega), show m + 1 - 1 = m from rfl]
  rcases Nat.lt_or_ge h' m with hlt' | hge
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [vcol_concat_right c (by omega)]
    exact ⟨(vcol k c h' m').reverse, by simp⟩
  · have : h' = m := by omega
    subst this
    refine ⟨[], ?_⟩
    rw [vcol, show h' + 1 - h' = 1 by omega]
    simp

/-- A planar path with distinct ends has at least two vertices, the second adjacent to the first.
[folklore] -/
theorem PPath.eq_cons_cons {l : List (ℤ × ℤ)} {s t : ℤ × ℤ} (h : PPath l s t) (hst : s ≠ t) :
    ∃ s' r, l = s :: s' :: r ∧ planarAdj s s' := by
  obtain ⟨s₀, r₀, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  have hs₀ : s₀ = s := by simpa using h.head
  subst hs₀
  cases r₀ with
  | nil => have := h.last; simp at this; exact absurd this hst
  | cons s' r =>
    refine ⟨s', r, rfl, ?_⟩
    have := h.chain
    rw [List.isChain_cons_cons] at this
    exact this.1

/-- Lifting a list with a distinguished head. [folklore] -/
theorem liftH_cons (h : ℕ) (z : ℤ × ℤ) (l : List (ℤ × ℤ)) :
    liftH k h (z :: l) = vtx k z h :: liftH k h l := rfl

/-- A planar path lifted to height `h ≤ k` is a slab path. [folklore] -/
theorem liftH_spath {l : List (ℤ × ℤ)} {s t : ℤ × ℤ} (hl : PPath l s t) (h : ℕ) :
    SPath (liftH k h l) (vtx k s h) (vtx k t h) :=
  ⟨liftH_ne_nil hl.ne_nil, liftH_isChain h hl.chain, liftH_nodup hl.nodup,
    by rw [head?_liftH, hl.head]; rfl, by rw [getLast?_liftH, hl.last]; rfl⟩

/-- Gluing three slab paths. [folklore] -/
theorem SPath.trans3 {X Y Z : List (slab 3 k)} {s m₁ m₂ t : slab 3 k} (hX : SPath X s m₁)
    (hY : SPath Y m₁ m₂) (hZ : SPath Z m₂ t) (hXY : ∀ v ∈ X, v ∈ Y → v = m₁)
    (hXYZ : ∀ v, v ∈ X ∨ v ∈ Y → v ∈ Z → v = m₂) :
    SPath (X ++ Y.tail ++ Z.tail) s t ∧ ∀ v, v ∈ X ++ Y.tail ++ Z.tail ↔ v ∈ X ∨ v ∈ Y ∨ v ∈ Z := by
  obtain ⟨h1, hm1⟩ := hX.trans hY hXY
  obtain ⟨h2, hm2⟩ := h1.trans hZ fun v hv hvZ => hXYZ v ((hm1 v).1 hv) hvZ
  exact ⟨h2, fun v => by rw [hm2, hm1, or_assoc]⟩

/-- In a list without duplicates the successor of an element is determined. [folklore] -/
theorem eq_of_cons_cons_eq_append {α : Type*} {L : List α} {x y₀ y : α} {l₀ r l₁ l₂ : List α}
    (hnd : L.Nodup) (h0 : L = l₀ ++ x :: y₀ :: r) (h : L = l₁ ++ x :: y :: l₂) : y = y₀ := by
  have hx : x ∉ l₁ := by
    intro hx
    rw [h] at hnd
    exact (List.nodup_append.1 hnd).2.2 x hx x (by simp) rfl
  have hx₀ : x ∉ l₀ := by
    intro hx
    rw [h0] at hnd
    exact (List.nodup_append.1 hnd).2.2 x hx x (by simp) rfl
  have := split_unique (l₁ := l₀) (r₁ := y₀ :: r) (l₂ := l₁) (r₂ := y :: l₂) (by rw [← h0, h]) hx₀ hx
  exact (List.cons.inj this.2).1.symm

/-- Keys compare first by height. [folklore] -/
theorem vKey_lt_of_ht_lt {v w : slab 3 k} (h : ht v < ht w) : vKey k v < vKey k w := by
  have hv := ht_coe v
  have hw := ht_coe w
  have : v.1 0 < w.1 0 := by omega
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl this)

/-- Keys at equal height compare by the first planar coordinate. [folklore] -/
theorem vKey_lt_of_fst_lt {v w : slab 3 k} (h : ht v = ht w) (h1 : (planar k v).1 < (planar k w).1) :
    vKey k v < vKey k w := by
  have hv := ht_coe v
  have hw := ht_coe w
  have h0 : v.1 0 = w.1 0 := by omega
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h0, ?_⟩)
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h1)

/-- Keys at equal height and first planar coordinate compare by the second. [folklore] -/
theorem vKey_lt_of_snd_lt {v w : slab 3 k} (h : ht v = ht w) (h1 : (planar k v).1 = (planar k w).1)
    (h2 : (planar k v).2 < (planar k w).2) : vKey k v < vKey k w := by
  have hv := ht_coe v
  have hw := ht_coe w
  have h0 : v.1 0 = w.1 0 := by omega
  refine Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h0, ?_⟩)
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨h1, h2⟩)

/-- The tail of a slab path with distinct ends. [folklore] -/
theorem SPath.tail_props {CB : List (slab 3 k)} {c w : slab 3 k} (h : SPath CB c w) (hcw : c ≠ w) :
    CB = c :: CB.tail ∧ CB.tail ≠ [] ∧ (∀ v ∈ CB.tail, v ∈ CB ∧ v ≠ c) ∧
      CB.tail.getLast? = some w := by
  obtain ⟨c₀, r, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  have hc₀ : c₀ = c := by simpa using h.head
  subst hc₀
  have hcr : c₀ ∉ r := (List.nodup_cons.1 h.nodup).1
  have hr : r ≠ [] := by
    rintro rfl
    have := h.last; simp at this; exact hcw this
  refine ⟨rfl, hr, fun v hv => ⟨List.mem_cons_of_mem _ hv, fun hvc => hcr (hvc ▸ hv)⟩, ?_⟩
  have := h.last
  rw [List.tail_cons]
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hr
  rwa [List.getLast?_cons_cons] at this

/-! ## Routing templates -/

section Templates

/-- **What the routing must produce** (geometry-free form of DST's "three disjoint self-avoiding
paths", proof of Fact 2): a self-avoiding lattice path `L` from `E₁` to `E₂` inside the columns
over `RP`, an attachment vertex `c` on it other than `E₂`, and a branch `Br` inside the columns
over `D`, off `L`, with `c :: Br` a self-avoiding lattice path ending at `w'`, such that the
successor of `c` on `L` has a smaller key than the first vertex of the branch (DST's
"`(z,v) ≺ (z,w)`"). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
structure RouteSpec (k : ℕ) (RP D : Set (ℤ × ℤ)) (E₁ E₂ w' : slab 3 k) (L Br : List (slab 3 k))
    (c : slab 3 k) : Prop where
  hL : SPath L E₁ E₂
  hL_sub : ∀ v ∈ L, planar k v ∈ RP
  hc : c ∈ L
  hcE₂ : c ≠ E₂
  hBr : Br ≠ []
  hCB : SPath (c :: Br) c w'
  hBr_sub : ∀ v ∈ Br, planar k v ∈ D
  hBr_L : ∀ v ∈ Br, v ∉ L
  hfwd : ∀ (l₁ l₂ : List (slab 3 k)) (y : slab 3 k), L = l₁ ++ c :: y :: l₂ →
    ∀ b₀ ∈ Br.head?, vKey k y < vKey k b₀

variable {xL xR' xR rB rP rT : ℤ}

/-- A free column for a single obstacle. [folklore] -/
theorem free_col (hcols : xL < xR') (f : ℤ × ℤ) :
    ∃ ξ, xL ≤ ξ ∧ ξ ≤ xR' ∧ ξ ≠ f.1 :=
  if h : f.1 = xL then ⟨xR', hcols.le, le_rfl, by omega⟩ else ⟨xL, le_rfl, hcols.le, fun h' => h h'.symm⟩

/-- **Assembling a route from its pieces**: given the main path `L`, an attachment vertex `c` on
it, and a path `CB` from `c` to `w'` meeting `L` only at `c`, with the key condition on the
successor of `c` and the second vertex of `CB`. [folklore] -/
theorem routeSpec_of_paths {RP D : Set (ℤ × ℤ)} {E₁ E₂ w' c : slab 3 k} {L CB : List (slab 3 k)}
    (hL : SPath L E₁ E₂) (hL_sub : ∀ v ∈ L, planar k v ∈ RP) (hcE : c ≠ E₂)
    (hCB : SPath CB c w') (hCB_sub : ∀ v ∈ CB, planar k v ∈ D) (hw : c ≠ w')
    (hdisj : ∀ v ∈ CB, v ∈ L → v = c)
    {y₀ b₀ : slab 3 k} {l₀ rL rB : List (slab 3 k)} (hy₀ : L = l₀ ++ c :: y₀ :: rL) (hb₀ : CB = c :: b₀ :: rB)
    (hkey : vKey k y₀ < vKey k b₀) :
    RouteSpec k RP D E₁ E₂ w' L CB.tail c := by
  obtain ⟨hCBeq, htail, htailmem, hlast⟩ := hCB.tail_props hw
  refine ⟨hL, hL_sub, by rw [hy₀]; simp, hcE, htail, by rw [← hCBeq]; exact hCB,
    fun v hv => hCB_sub v (htailmem v hv).1, fun v hv hvL => (htailmem v hv).2 (hdisj v (htailmem v hv).1 hvL),
    fun l₁ l₂ y h b hb => ?_⟩
  have hy : y = y₀ := eq_of_cons_cons_eq_append hL.nodup hy₀ h
  have hb' : b₀ = b := by rw [hb₀] at hb; simpa using hb
  rw [hy, ← hb']; exact hkey

/-- Prepending a vertex to a slab path. [folklore] -/
theorem SPath.cons {l : List (slab 3 k)} {s t : slab 3 k} (h : SPath l s t) {x : slab 3 k}
    (hadj : (slabGraph 3 k).Adj x s) (hx : x ∉ l) : SPath (x :: l) x t where
  ne_nil := List.cons_ne_nil _ _
  chain := by
    rw [List.isChain_cons]
    refine ⟨fun y hy => ?_, h.chain⟩
    rw [h.head] at hy; simp at hy; rw [← hy]; exact hadj
  nodup := List.nodup_cons.2 ⟨hx, h.nodup⟩
  head := rfl
  last := by
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
    rw [List.getLast?_cons_cons]; exact h.last

/-- Appending a vertex to a slab path. [folklore] -/
theorem SPath.concat {l : List (slab 3 k)} {s t : slab 3 k} (h : SPath l s t) {x : slab 3 k}
    (hadj : (slabGraph 3 k).Adj t x) (hx : x ∉ l) : SPath (l ++ [x]) s x := by
  have := (h.reverse.cons hadj.symm (by simpa using hx)).reverse
  simpa using this

/-- A path with given last vertex splits off that vertex. [folklore] -/
theorem exists_eq_append_of_getLast? {α : Type*} {l : List α} {t : α} (h : l.getLast? = some t) :
    ∃ init, l = init ++ [t] :=
  ⟨l.dropLast, by rw [List.dropLast_append_getLast? t (by simp [h])]⟩

/-- **Planar routing with no obstacle.** [folklore] -/
theorem exists_ppath_free (hcols : xL < xR) (hrows : rB < rT) {s t : ℤ × ℤ}
    (hs : s ∈ boxR xL xR rB rT) (ht : t ∈ boxR xL xR rB rT) (hst : s ≠ t) :
    ∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT := by
  obtain ⟨l, hl, hm⟩ := exists_ppath_avoiding_row hrows hs ht hst ∅ 0 (by simp) (by simp) (by simp)
    xL le_rfl hcols.le (by simp)
  exact ⟨l, hl, fun z hz => (hm z hz).1⟩

/-- **Planar routing around one obstacle.** [folklore] -/
theorem exists_ppath_avoiding_one (hcols : xL < xR) (hrows : rB < rT) {s t : ℤ × ℤ}
    (hs : s ∈ boxR xL xR rB rT) (ht : t ∈ boxR xL xR rB rT) (hst : s ≠ t) (f : ℤ × ℤ) (hsf : s ≠ f)
    (htf : t ≠ f) : ∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT ∧ z ≠ f := by
  obtain ⟨ξ, hξ1, hξ2, hξf⟩ := free_col hcols f
  obtain ⟨l, hl, hm⟩ := exists_ppath_avoiding_row hrows hs ht hst {f} f.2 (by simp) (by simpa using hsf)
    (by simpa using htf) ξ hξ1 hξ2 (fun h => hξf (by
      rw [Set.mem_singleton_iff] at h; have := congrArg Prod.fst h; simpa using this))
  exact ⟨l, hl, fun z hz => ⟨(hm z hz).1, by simpa using (hm z hz).2⟩⟩

/-- **Planar routing around a domino** (two adjacent obstacles), in a rectangle with at least
three columns and three rows. [folklore] -/
theorem exists_ppath_avoiding_pair (hcols : xL + 2 ≤ xR) (hrows : rB + 2 ≤ rT) {s t : ℤ × ℤ}
    (hs : s ∈ boxR xL xR rB rT) (ht : t ∈ boxR xL xR rB rT) (hst : s ≠ t) {f g : ℤ × ℤ}
    (hfg : planarAdj f g) (hsf : s ≠ f) (hsg : s ≠ g) (htf : t ≠ f) (htg : t ≠ g) :
    ∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT ∧ z ≠ f ∧ z ≠ g := by
  have key : ∀ (F : Set (ℤ × ℤ)), F = {f, g} →
      (∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT ∧ z ∉ F) →
      ∃ l, PPath l s t ∧ ∀ z ∈ l, z ∈ boxR xL xR rB rT ∧ z ≠ f ∧ z ≠ g := by
    rintro F rfl ⟨l, hl, hm⟩
    refine ⟨l, hl, fun z hz => ⟨(hm z hz).1, ?_, ?_⟩⟩ <;>
    · intro h; apply (hm z hz).2; simp [h]
  have hsF : s ∉ ({f, g} : Set (ℤ × ℤ)) := by simp [hsf, hsg]
  have htF : t ∉ ({f, g} : Set (ℤ × ℤ)) := by simp [htf, htg]
  obtain ⟨f1, f2⟩ := f
  obtain ⟨g1, g2⟩ := g
  simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at hfg
  rcases hfg with hh | hv
  · -- horizontal domino on the row `f2 = g2`
    have hrow : ∀ z ∈ ({(f1, f2), (g1, g2)} : Set (ℤ × ℤ)), z.2 = f2 := by
      intro z hz; simp at hz; rcases hz with rfl | rfl; rfl; simp; omega
    -- a free column among `xL, xL+1, xL+2`
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ : ∃ ξ, xL ≤ ξ ∧ ξ ≤ xR ∧ ξ ≠ f1 ∧ ξ ≠ g1 := by
      by_cases h0 : xL ≠ f1 ∧ xL ≠ g1
      · exact ⟨xL, le_rfl, by omega, h0⟩
      by_cases h1 : xL + 1 ≠ f1 ∧ xL + 1 ≠ g1
      · exact ⟨xL + 1, by omega, by omega, h1⟩
      · exact ⟨xL + 2, by omega, hcols, by push Not at h0 h1; omega⟩
    refine key _ rfl (exists_ppath_avoiding_row (by omega) hs ht hst _ f2 hrow hsF htF ξ hξ1 hξ2 ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    exact ⟨fun h => hξ.1 h.1, fun h => hξ.2 h.1⟩
  · -- vertical domino on the column `f1 = g1`
    have hcol : ∀ z ∈ ({(f1, f2), (g1, g2)} : Set (ℤ × ℤ)), z.1 = f1 := by
      intro z hz; simp at hz; rcases hz with rfl | rfl; rfl; simp; omega
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ : ∃ ξ, rB ≤ ξ ∧ ξ ≤ rT ∧ ξ ≠ f2 ∧ ξ ≠ g2 := by
      by_cases h0 : rB ≠ f2 ∧ rB ≠ g2
      · exact ⟨rB, le_rfl, by omega, h0⟩
      by_cases h1 : rB + 1 ≠ f2 ∧ rB + 1 ≠ g2
      · exact ⟨rB + 1, by omega, by omega, h1⟩
      · exact ⟨rB + 2, by omega, hrows, by push Not at h0 h1; omega⟩
    refine key _ rfl (exists_ppath_avoiding_col (by omega) hs ht hst _ f1 hcol hsF htF ξ hξ1 hξ2 ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
    exact ⟨fun h => hξ.1 h.2, fun h => hξ.2 h.2⟩

/-- **Two lattice neighbours inside a rectangle**, the first avoiding a prescribed point: in a
rectangle with at least two columns and two rows, every point has a horizontal and a vertical
neighbour inside. [folklore] -/
theorem exists_two_nbrs (hcols : xL < xR) (hrows : rB < rT) {a : ℤ × ℤ} (ha : a ∈ boxR xL xR rB rT)
    (d : ℤ × ℤ) : ∃ q q', q ∈ boxR xL xR rB rT ∧ planarAdj a q ∧ q ≠ d ∧
      q' ∈ boxR xL xR rB rT ∧ planarAdj a q' ∧ q' ≠ q := by
  rw [mem_boxR_iff] at ha
  obtain ⟨a1, a2⟩ := a
  simp only at ha
  -- a horizontal and a vertical neighbour
  obtain ⟨hq, hhq, hhadj⟩ : ∃ hq : ℤ × ℤ, hq ∈ boxR xL xR rB rT ∧ planarAdj (a1, a2) hq ∧ hq.2 = a2 := by
    by_cases h : a1 < xR
    · exact ⟨(a1 + 1, a2), by rw [mem_boxR_iff]; simp; omega, by simp [planarAdj], rfl⟩
    · exact ⟨(a1 - 1, a2), by rw [mem_boxR_iff]; simp; omega, by simp [planarAdj], rfl⟩
  obtain ⟨vq, hvq, hvadj⟩ : ∃ vq : ℤ × ℤ, vq ∈ boxR xL xR rB rT ∧ planarAdj (a1, a2) vq ∧ vq.1 = a1 := by
    by_cases h : a2 < rT
    · exact ⟨(a1, a2 + 1), by rw [mem_boxR_iff]; simp; omega, by simp [planarAdj], rfl⟩
    · exact ⟨(a1, a2 - 1), by rw [mem_boxR_iff]; simp; omega, by simp [planarAdj], rfl⟩
  have hne : hq ≠ vq := by
    intro h
    have h1 := hvadj.2; rw [← h] at h1
    have h2 := hhadj.2
    have : hq = (a1, a2) := Prod.ext h1 h2
    rw [this] at hhadj
    simp [planarAdj] at hhadj
  by_cases hd : hq = d
  · exact ⟨vq, hq, hvq, hvadj.1, fun h => hne (hd.trans h.symm), hhq, hhadj.1, hne⟩
  · exact ⟨hq, vq, hhq, hhadj.1, hd, hvq, hvadj.1, hne.symm⟩

/-- **Template MAIN** (`E₁`, `E₂` in different columns): descend from `E₁` to the bottom layer,
run along a planar path to the column of `E₂`, climb to `E₂`; the branch climbs from `E₁` to the
top layer, runs along a planar path to the column of `w'`, and descends to `w'`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the rerouting)] -/
theorem route_main (hk : 1 ≤ k) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {E₁ E₂ w' : slab 3 k}
    (ha : planar k E₁ ∈ boxR xL xR' rB rP) (hb : planar k E₂ ∈ boxR xL xR' rB rP)
    (hd : planar k w' ∈ boxR xL xR rB rT) (hab : planar k E₁ ≠ planar k E₂)
    (had : planar k E₁ ≠ planar k w') (hbd : planar k E₂ ≠ planar k w') :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) E₁ E₂ w' L Br c := by
  set a := planar k E₁ with ha_def
  set b := planar k E₂ with hb_def
  set d := planar k w' with hd_def
  set h₁ := ht E₁
  set h₂ := ht E₂
  set hw := ht w'
  have hh₁ : h₁ ≤ k := ht_le E₁
  have hh₂ : h₂ ≤ k := ht_le E₂
  have hhw : hw ≤ k := ht_le w'
  have hE₁ : E₁ = vtx k a h₁ := (vtx_planar_ht E₁).symm
  have hE₂ : E₂ = vtx k b h₂ := (vtx_planar_ht E₂).symm
  have hw' : w' = vtx k d hw := (vtx_planar_ht w').symm
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  -- the two planar paths
  obtain ⟨ξ₁, hξ₁1, hξ₁2, hξ₁d⟩ := free_col (show xL < xR' by omega) d
  obtain ⟨l₁, hl₁, hl₁m⟩ := exists_ppath_avoiding_row (show rB < rP by omega) ha hb hab
    {z | z = d ∧ hw = 0} d.2 (fun f hf => by rw [hf.1]) (fun h => had h.1) (fun h => hbd h.1)
    ξ₁ hξ₁1 hξ₁2 (fun h => hξ₁d (by have := congrArg Prod.fst h.1; simpa using this))
  obtain ⟨ξ₂, hξ₂1, hξ₂2, hξ₂b⟩ := free_col (show xL < xR by omega) b
  obtain ⟨l₂, hl₂, hl₂m⟩ := exists_ppath_avoiding_row (show rB < rT by omega) (hRPD ha) hd had
    {z | z = b ∧ h₂ = k} b.2 (fun f hf => by rw [hf.1]) (fun h => hab h.1) (fun h => hbd h.1.symm)
    ξ₂ hξ₂1 hξ₂2 (fun h => hξ₂b (by have := congrArg Prod.fst h.1; simpa using this))
  -- the main path `L`
  have hX₁ := vline_spath (k := k) a hh₁ (Nat.zero_le k)
  have hY₁ := liftH_spath (k := k) hl₁ 0
  have hZ₁ := vline_spath (k := k) b (Nat.zero_le k) hh₂
  obtain ⟨hL, hLm⟩ := SPath.trans3 hX₁ hY₁ hZ₁
    (fun v hvX hvY => by
      rw [mem_vline_iff hh₁ (Nat.zero_le k)] at hvX
      rw [mem_liftH_iff (Nat.zero_le k)] at hvY
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvX.1, by rw [ht_vtx (Nat.zero_le k)]; exact hvY.2⟩)
    (fun v hv hvZ => by
      rw [mem_vline_iff (Nat.zero_le k) hh₂] at hvZ
      rcases hv with hv | hv
      · rw [mem_vline_iff hh₁ (Nat.zero_le k)] at hv
        exact absurd (hv.1.symm.trans hvZ.1) hab
      · rw [mem_liftH_iff (Nat.zero_le k)] at hv
        exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx (Nat.zero_le k)]; exact hv.2⟩)
  -- the branch path `CB`
  have hX₂ := vline_spath (k := k) a hh₁ le_rfl
  have hY₂ := liftH_spath (k := k) hl₂ k
  have hZ₂ := vline_spath (k := k) d le_rfl hhw
  obtain ⟨hCB, hCBm⟩ := SPath.trans3 hX₂ hY₂ hZ₂
    (fun v hvX hvY => by
      rw [mem_vline_iff hh₁ le_rfl] at hvX
      rw [mem_liftH_iff le_rfl] at hvY
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvX.1, by rw [ht_vtx le_rfl]; exact hvY.2⟩)
    (fun v hv hvZ => by
      rw [mem_vline_iff le_rfl hhw] at hvZ
      rcases hv with hv | hv
      · rw [mem_vline_iff hh₁ le_rfl] at hv
        exact absurd (hv.1.symm.trans hvZ.1) had
      · rw [mem_liftH_iff le_rfl] at hv
        exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx le_rfl]; exact hv.2⟩)
  rw [← hE₁] at hL hCB
  rw [← hE₂] at hL
  rw [← hw'] at hCB
  -- second vertices
  obtain ⟨a', r₁, hl₁eq, -⟩ := hl₁.eq_cons_cons hab
  obtain ⟨a'', r₂, hl₂eq, -⟩ := hl₂.eq_cons_cons had
  obtain ⟨y₀, rL, hy₀, hy₀h⟩ : ∃ y₀ rL, vline k a h₁ 0 ++ (liftH k 0 l₁).tail ++ (vline k b 0 h₂).tail =
      E₁ :: y₀ :: rL ∧ ht y₀ + 1 ≤ max h₁ 1 := by
    rcases Nat.eq_zero_or_pos h₁ with h0 | hpos
    · refine ⟨vtx k a' 0, liftH k 0 r₁ ++ (vline k b 0 h₂).tail, ?_, by rw [ht_vtx (Nat.zero_le k)]; omega⟩
      rw [h0, vline_self, hl₁eq, liftH_cons, liftH_cons, hE₁, h0]; rfl
    · obtain ⟨r, hr⟩ := vline_eq_cons_cons_down (k := k) a hpos
      refine ⟨vtx k a (h₁ - 1), r ++ (liftH k 0 l₁).tail ++ (vline k b 0 h₂).tail, ?_,
        by rw [ht_vtx (by omega)]; omega⟩
      rw [hr, hE₁]; rfl
  obtain ⟨b₀, rB', hb₀, hb₀h⟩ : ∃ b₀ rB', vline k a h₁ k ++ (liftH k k l₂).tail ++ (vline k d k hw).tail =
      E₁ :: b₀ :: rB' ∧ max h₁ 1 ≤ ht b₀ := by
    rcases (lt_or_eq_of_le hh₁) with hlt | heq
    · obtain ⟨r, hr⟩ := vline_eq_cons_cons_up (k := k) a hlt
      refine ⟨vtx k a (h₁ + 1), r ++ (liftH k k l₂).tail ++ (vline k d k hw).tail, ?_,
        by rw [ht_vtx (by omega)]; omega⟩
      rw [hr, hE₁]; rfl
    · refine ⟨vtx k a'' k, liftH k k r₂ ++ (vline k d k hw).tail, ?_, by rw [ht_vtx le_rfl]; omega⟩
      rw [heq, vline_self, hl₂eq, liftH_cons, liftH_cons, hE₁, heq]; rfl
  refine ⟨_, _, E₁, routeSpec_of_paths (l₀ := []) hL ?_ (fun h => hab (congrArg (planar k) h)) hCB ?_
    (fun h => had (congrArg (planar k) h)) ?_ hy₀ hb₀ (vKey_lt_of_ht_lt (by omega))⟩
  · -- `L` lies over `RP`
    intro v hv
    rcases (hLm v).1 hv with hv | hv | hv
    · rw [mem_vline_iff hh₁ (Nat.zero_le k)] at hv; rw [hv.1]; exact ha
    · rw [mem_liftH_iff (Nat.zero_le k)] at hv; exact (hl₁m _ hv.1).1
    · rw [mem_vline_iff (Nat.zero_le k) hh₂] at hv; rw [hv.1]; exact hb
  · -- `CB` lies over `D`
    intro v hv
    rcases (hCBm v).1 hv with hv | hv | hv
    · rw [mem_vline_iff hh₁ le_rfl] at hv; rw [hv.1]; exact hRPD ha
    · rw [mem_liftH_iff le_rfl] at hv; exact (hl₂m _ hv.1).1
    · rw [mem_vline_iff le_rfl hhw] at hv; rw [hv.1]; exact hd
  · -- `CB` meets `L` only at `E₁`
    intro v hvC hvL
    rcases (hCBm v).1 hvC with hvC | hvC | hvC <;> rcases (hLm v).1 hvL with hvL | hvL | hvL
    · rw [mem_vline_iff hh₁ le_rfl] at hvC; rw [mem_vline_iff hh₁ (Nat.zero_le k)] at hvL
      rw [hE₁]; exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvC.1, by rw [ht_vtx hh₁]; omega⟩
    · rw [mem_vline_iff hh₁ le_rfl] at hvC; rw [mem_liftH_iff (Nat.zero_le k)] at hvL
      rw [hE₁]; exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvC.1, by rw [ht_vtx hh₁]; omega⟩
    · rw [mem_vline_iff hh₁ le_rfl] at hvC; rw [mem_vline_iff (Nat.zero_le k) hh₂] at hvL
      exact absurd (hvC.1.symm.trans hvL.1) hab
    · rw [mem_liftH_iff le_rfl] at hvC; rw [mem_vline_iff hh₁ (Nat.zero_le k)] at hvL
      rw [hE₁]; exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvL.1, by rw [ht_vtx hh₁]; omega⟩
    · rw [mem_liftH_iff le_rfl] at hvC; rw [mem_liftH_iff (Nat.zero_le k)] at hvL; omega
    · rw [mem_liftH_iff le_rfl] at hvC; rw [mem_vline_iff (Nat.zero_le k) hh₂] at hvL
      exfalso
      have hk2 : h₂ = k := by omega
      exact (hl₂m _ hvC.1).2 ⟨hvL.1, hk2⟩
    · rw [mem_vline_iff le_rfl hhw] at hvC; rw [mem_vline_iff hh₁ (Nat.zero_le k)] at hvL
      exact absurd (hvL.1.symm.trans hvC.1) had
    · rw [mem_vline_iff le_rfl hhw] at hvC; rw [mem_liftH_iff (Nat.zero_le k)] at hvL
      exfalso
      have hw0 : hw = 0 := by omega
      exact (hl₁m _ hvL.1).2 ⟨hvC.1, hw0⟩
    · rw [mem_vline_iff le_rfl hhw] at hvC; rw [mem_vline_iff (Nat.zero_le k) hh₂] at hvL
      exact absurd (hvL.1.symm.trans hvC.1) hbd

end Templates

section SameColumn

variable {xL xR' xR rB rP rT : ℤ}

/-- **The branch from a vertex `c` through the top layer**: climb from `c = (h₀, q)` to height
`k`, run along a planar path `l₂` from `q` to `d`, descend to `w' = (hw, d)`. Returns the path,
its second vertex and a membership description. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the branch γ_w)] -/
theorem exists_branch_top {q d : ℤ × ℤ} {h₀ hw : ℕ} (hh₀ : h₀ ≤ k) (hhw : hw ≤ k)
    {l₂ : List (ℤ × ℤ)} (hl₂ : PPath l₂ q d) (hqd : q ≠ d) :
    ∃ CB b₀ rB, SPath CB (vtx k q h₀) (vtx k d hw) ∧ CB = vtx k q h₀ :: b₀ :: rB ∧ h₀ ≤ ht b₀ ∧
      (h₀ < k → ht b₀ = h₀ + 1) ∧
      ∀ v ∈ CB, (planar k v = q ∧ h₀ ≤ ht v) ∨ (ht v = k ∧ planar k v ∈ l₂) ∨
        (planar k v = d ∧ min k hw ≤ ht v) := by
  have hX := vline_spath (k := k) q hh₀ le_rfl
  have hY := liftH_spath (k := k) hl₂ k
  have hZ := vline_spath (k := k) d le_rfl hhw
  obtain ⟨hCB, hCBm⟩ := SPath.trans3 hX hY hZ
    (fun v hvX hvY => by
      rw [mem_vline_iff hh₀ le_rfl] at hvX
      rw [mem_liftH_iff le_rfl] at hvY
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvX.1, by rw [ht_vtx le_rfl]; exact hvY.2⟩)
    (fun v hv hvZ => by
      rw [mem_vline_iff le_rfl hhw] at hvZ
      rcases hv with hv | hv
      · rw [mem_vline_iff hh₀ le_rfl] at hv
        exact absurd (hv.1.symm.trans hvZ.1) hqd
      · rw [mem_liftH_iff le_rfl] at hv
        exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx le_rfl]; exact hv.2⟩)
  obtain ⟨q', r₂, hl₂eq, -⟩ := hl₂.eq_cons_cons hqd
  obtain ⟨b₀, rB', hb₀, hb₀h, hb₀h'⟩ : ∃ b₀ rB', vline k q h₀ k ++ (liftH k k l₂).tail ++
      (vline k d k hw).tail = vtx k q h₀ :: b₀ :: rB' ∧ h₀ ≤ ht b₀ ∧ (h₀ < k → ht b₀ = h₀ + 1) := by
    rcases (lt_or_eq_of_le hh₀) with hlt | heq
    · obtain ⟨r, hr⟩ := vline_eq_cons_cons_up (k := k) q hlt
      refine ⟨vtx k q (h₀ + 1), r ++ (liftH k k l₂).tail ++ (vline k d k hw).tail, ?_,
        by rw [ht_vtx (by omega)]; omega, fun _ => by rw [ht_vtx (by omega)]⟩
      rw [hr]; rfl
    · rw [heq]
      refine ⟨vtx k q' k, liftH k k r₂ ++ (vline k d k hw).tail, ?_, by rw [ht_vtx le_rfl],
        fun h => absurd h (lt_irrefl _)⟩
      rw [vline_self, hl₂eq, liftH_cons, liftH_cons]; rfl
  refine ⟨_, b₀, rB', hCB, hb₀, hb₀h, hb₀h', fun v hv => ?_⟩
  rcases (hCBm v).1 hv with hv | hv | hv
  · rw [mem_vline_iff hh₀ le_rfl] at hv; exact Or.inl ⟨hv.1, by omega⟩
  · rw [mem_liftH_iff le_rfl] at hv; exact Or.inr (Or.inl ⟨hv.2, hv.1⟩)
  · rw [mem_vline_iff le_rfl hhw] at hv; exact Or.inr (Or.inr ⟨hv.1, by omega⟩)

/-- Every slab vertex is `vtx` of its planar part and a height `≤ k`. [folklore] -/
theorem exists_eq_vtx (v : slab 3 k) : ∃ (z : ℤ × ℤ) (h : ℕ), h ≤ k ∧ v = vtx k z h :=
  ⟨planar k v, ht v, ht_le v, (vtx_planar_ht v).symm⟩

/-- **Template DESC** (`E₂` strictly below `E₁` in the same column): the straight descent, with
the branch through the top layer. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_desc (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d : ℤ × ℤ} {h₁ h₂ hw : ℕ} (hh₁ : h₁ ≤ k) (hh₂ : h₂ ≤ k) (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (h12 : h₂ < h₁) (had : a ≠ d) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a h₁) (vtx k a h₂) (vtx k d hw)
      L Br c := by
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  -- `L`: the descent
  have hL := vline_spath (k := k) a hh₁ hh₂
  obtain ⟨r, hr⟩ := vline_eq_cons_cons_down (k := k) a h12
  -- the branch
  obtain ⟨l₂, hl₂, hl₂m⟩ := exists_ppath_free (show xL < xR by omega) (show rB < rT by omega)
    (hRPD ha) hd had
  obtain ⟨CB, b₀, rB', hCB, hb₀, hb₀h, -, hCBm⟩ := exists_branch_top hh₁ hhw hl₂ had
  refine ⟨_, _, _, routeSpec_of_paths (l₀ := []) hL ?_ (fun h => ?_)
    hCB ?_ (fun h => had ?_) ?_ (by rw [hr]; rfl) hb₀
    (vKey_lt_of_ht_lt (by rw [ht_vtx (by omega)]; omega))⟩
  · intro v hv
    rw [mem_vline_iff hh₁ hh₂] at hv; rw [hv.1]; exact ha
  · have := congrArg ht h; rw [ht_vtx hh₁, ht_vtx hh₂] at this; omega
  · intro v hv
    rcases hCBm v hv with hv | hv | hv
    · rw [hv.1]; exact hRPD ha
    · exact hl₂m _ hv.2
    · rw [hv.1]; exact hd
  · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
  · intro v hvC hvL
    rw [mem_vline_iff hh₁ hh₂] at hvL
    rcases hCBm v hvC with hv | hv | hv
    · exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvL.1, by rw [ht_vtx hh₁]; omega⟩
    · exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvL.1, by rw [ht_vtx hh₁]; omega⟩
    · exact absurd (hvL.1.symm.trans hv.1) had

/-- **Template BETA** (`E₂` strictly above `E₁` in the same column, below the top layer): reroute
through a side column, attach the branch at its top and climb. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_beta (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d : ℤ × ℤ} {h₁ h₂ hw : ℕ} (hh₁ : h₁ ≤ k) (hh₂ : h₂ ≤ k) (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (h12 : h₁ < h₂) (h2k : h₂ < k)
    (had : a ≠ d) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a h₁) (vtx k a h₂) (vtx k d hw)
      L Br c := by
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  obtain ⟨q, -, hqRP, haq, hqd, -, -, -⟩ := exists_two_nbrs (show xL < xR' by omega) (show rB < rP by omega) ha d
  have hqa : q ≠ a := by rintro rfl; simp [planarAdj] at haq
  set E₁ := vtx k a h₁ with hE₁
  set E₂ := vtx k a h₂ with hE₂
  set c := vtx k q h₂ with hc
  -- `L = E₁ :: (side column) ++ [E₂]`, attachment at the top of the side column
  have hV := vline_spath (k := k) q hh₁ hh₂
  have hE₁V : E₁ ∉ vline k q h₁ h₂ := fun h => by
    rw [mem_vline_iff hh₁ hh₂, hE₁, planar_vtx] at h; exact hqa h.1.symm
  have hE₂V : E₂ ∉ vline k q h₁ h₂ := fun h => by
    rw [mem_vline_iff hh₁ hh₂, hE₂, planar_vtx] at h; exact hqa h.1.symm
  have hE₁₂ : E₁ ≠ E₂ := fun h => by
    have := congrArg ht h; rw [hE₁, hE₂, ht_vtx hh₁, ht_vtx hh₂] at this; omega
  have hL : SPath (E₁ :: (vline k q h₁ h₂ ++ [E₂])) E₁ E₂ := by
    refine (hV.concat (x := E₂) ?_ hE₂V).cons ?_ ?_
    · exact (vtx_adj_vtx_planar haq h₂).symm
    · exact vtx_adj_vtx_planar haq h₁
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hE₁V, hE₁₂⟩
  obtain ⟨init, hinit⟩ := exists_eq_append_of_getLast? hV.last
  have hLeq : E₁ :: (vline k q h₁ h₂ ++ [E₂]) = (E₁ :: init) ++ c :: E₂ :: [] := by
    rw [hinit]; simp [hc]
  -- the branch from `c`
  obtain ⟨l₂, hl₂, hl₂m⟩ := exists_ppath_free (show xL < xR by omega) (show rB < rT by omega)
    (hRPD hqRP) hd hqd
  obtain ⟨CB, b₀, rB', hCB, hb₀, -, hb₀h, hCBm⟩ := exists_branch_top hh₂ hhw hl₂ hqd
  refine ⟨_, _, c, routeSpec_of_paths hL ?_ (fun h => hqa ?_) hCB ?_ (fun h => hqd ?_) ?_ hLeq hb₀
    (vKey_lt_of_ht_lt (by rw [hb₀h h2k, hE₂, ht_vtx hh₂]; omega))⟩
  · intro v hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · rw [planar_vtx]; exact ha
    · rw [mem_vline_iff hh₁ hh₂] at hv; rw [hv.1]; exact hqRP
    · rw [planar_vtx]; exact ha
  · have := congrArg (planar k) h; rwa [hc, hE₂, planar_vtx, planar_vtx] at this
  · intro v hv
    rcases hCBm v hv with hv | hv | hv
    · rw [hv.1]; exact hRPD hqRP
    · exact hl₂m _ hv.2
    · rw [hv.1]; exact hd
  · have := congrArg (planar k) h; rwa [hc, planar_vtx, planar_vtx] at this
  · intro v hvC hvL
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hvL
    rcases hCBm v hvC with hv | hv | hv
    · rcases hvL with rfl | hvL | rfl
      · rw [hE₁, planar_vtx] at hv; exact absurd hv.1 hqa.symm
      · rw [mem_vline_iff hh₁ hh₂] at hvL
        rw [hc]; exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvL.1, by rw [ht_vtx hh₂]; omega⟩
      · rw [hE₂, planar_vtx] at hv; exact absurd hv.1 hqa.symm
    · exfalso
      rcases hvL with rfl | hvL | rfl
      · rw [hE₁, ht_vtx hh₁] at hv; omega
      · rw [mem_vline_iff hh₁ hh₂] at hvL; omega
      · rw [hE₂, ht_vtx hh₂] at hv; omega
    · exfalso
      rcases hvL with rfl | hvL | rfl
      · rw [hE₁, planar_vtx] at hv; exact had hv.1
      · rw [mem_vline_iff hh₁ hh₂] at hvL; exact hqd (hvL.1.symm.trans hv.1)
      · rw [hE₂, planar_vtx] at hv; exact had hv.1

/-- A single lattice step as a planar path. [folklore] -/
theorem ppath_pair {a q : ℤ × ℤ} (h : planarAdj a q) (hne : a ≠ q) : PPath [a, q] a q :=
  ⟨by simp, List.isChain_cons_cons.2 ⟨h, List.isChain_singleton _⟩, by simp [hne], rfl, rfl⟩

/-- A slab path starts with its head. [folklore] -/
theorem SPath.exists_eq_cons {l : List (slab 3 k)} {s t : slab 3 k} (h : SPath l s t) :
    ∃ r, l = s :: r := by
  obtain ⟨s₀, r, rfl⟩ := List.exists_cons_of_ne_nil h.ne_nil
  have : s₀ = s := by simpa using h.head
  exact ⟨r, by rw [this]⟩

/-- **Template DELTA1** (`E₂` at the top of the column of `E₁`, `E₁` not at the bottom): descend
from `E₁` to the bottom, step to a side column and climb it to the top, step back to `E₂`; the
branch leaves `E₁` horizontally into a second side column. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_delta1 (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d : ℤ × ℤ} {h₁ hw : ℕ} (hh₁ : h₁ < k) (h1 : 1 ≤ h₁) (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (had : a ≠ d) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a h₁) (vtx k a k) (vtx k d hw)
      L Br c := by
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  have hD3 : xL + 2 ≤ xR ∧ rB + 2 ≤ rT := ⟨by omega, by omega⟩
  obtain ⟨q, q', hqRP, haq, hqd, hq'RP, haq', hq'q⟩ :=
    exists_two_nbrs (show xL < xR' by omega) (show rB < rP by omega) ha d
  have hqa : q ≠ a := by rintro rfl; simp [planarAdj] at haq
  have hq'a : q' ≠ a := by rintro rfl; simp [planarAdj] at haq'
  set E₁ := vtx k a h₁ with hE₁
  set E₂ := vtx k a k with hE₂
  -- the main path
  have hX := vline_spath (k := k) a hh₁.le (Nat.zero_le k)
  have hY := liftH_spath (k := k) (ppath_pair haq hqa.symm) 0
  have hZ := vline_spath (k := k) q (Nat.zero_le k) le_rfl
  obtain ⟨hL₀, hL₀m⟩ := SPath.trans3 hX hY hZ
    (fun v hvX hvY => by
      rw [mem_vline_iff hh₁.le (Nat.zero_le k)] at hvX
      rw [mem_liftH_iff (Nat.zero_le k)] at hvY
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvX.1, by rw [ht_vtx (Nat.zero_le k)]; exact hvY.2⟩)
    (fun v hv hvZ => by
      rw [mem_vline_iff (Nat.zero_le k) le_rfl] at hvZ
      rcases hv with hv | hv
      · rw [mem_vline_iff hh₁.le (Nat.zero_le k)] at hv; exact absurd (hv.1.symm.trans hvZ.1) hqa.symm
      · rw [mem_liftH_iff (Nat.zero_le k)] at hv
        exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx (Nat.zero_le k)]; exact hv.2⟩)
  have hmemL₀ : ∀ v, v ∈ vline k a h₁ 0 ++ (liftH k 0 [a, q]).tail ++ (vline k q 0 k).tail →
      (planar k v = a ∧ ht v ≤ h₁) ∨ (planar k v = q) := by
    intro v hv
    rcases (hL₀m v).1 hv with hv | hv | hv
    · rw [mem_vline_iff hh₁.le (Nat.zero_le k)] at hv; exact Or.inl ⟨hv.1, by omega⟩
    · rw [mem_liftH_iff (Nat.zero_le k)] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv.1 with h | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr h
    · rw [mem_vline_iff (Nat.zero_le k) le_rfl] at hv; exact Or.inr hv.1
  have hL : SPath (vline k a h₁ 0 ++ (liftH k 0 [a, q]).tail ++ (vline k q 0 k).tail ++ [E₂]) E₁ E₂ := by
    refine hL₀.concat (vtx_adj_vtx_planar haq k).symm fun h => ?_
    rcases hmemL₀ _ h with h | h
    · rw [hE₂, ht_vtx le_rfl] at h; omega
    · rw [hE₂, planar_vtx] at h; exact hqa h.symm
  obtain ⟨r, hr⟩ := vline_eq_cons_cons_down (k := k) a (show 0 < h₁ by omega)
  have hLeq : vline k a h₁ 0 ++ (liftH k 0 [a, q]).tail ++ (vline k q 0 k).tail ++ [E₂] =
      [] ++ E₁ :: vtx k a (h₁ - 1) :: (r ++ (liftH k 0 [a, q]).tail ++ (vline k q 0 k).tail ++ [E₂]) := by
    rw [hr]; rfl
  have hLsub : ∀ v ∈ vline k a h₁ 0 ++ (liftH k 0 [a, q]).tail ++ (vline k q 0 k).tail ++ [E₂],
      planar k v ∈ boxR xL xR' rB rP := by
    intro v hv
    rw [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · rcases hmemL₀ v hv with h | h
      · rw [h.1]; exact ha
      · rw [h]; exact hqRP
    · rw [planar_vtx]; exact ha
  have hE₁₂ : E₁ ≠ E₂ := fun h => by
    have := congrArg ht h; rw [hE₁, hE₂, ht_vtx hh₁.le, ht_vtx le_rfl] at this; omega
  -- the branch: first vertex `(h₁, q')`
  by_cases hq'd : q' = d
  · subst hq'd
    have hV := vline_spath (k := k) q' hh₁.le hhw
    obtain ⟨rest, hrest⟩ := hV.exists_eq_cons
    have hCB : SPath (E₁ :: vline k q' h₁ hw) E₁ (vtx k q' hw) :=
      hV.cons (vtx_adj_vtx_planar haq' h₁) fun h => by
        rw [mem_vline_iff hh₁.le hhw, hE₁, planar_vtx] at h; exact hq'a h.1.symm
    refine ⟨_, _, E₁, routeSpec_of_paths hL hLsub hE₁₂ hCB ?_ (fun h => had ?_) ?_ hLeq
      (by rw [hrest]) (vKey_lt_of_ht_lt (by rw [ht_vtx (by omega), ht_vtx hh₁.le]; omega))⟩
    · intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [planar_vtx]; exact hRPD ha
      · rw [mem_vline_iff hh₁.le hhw] at hv; rw [hv.1]; exact hd
    · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
    · intro v hvC hvL
      rw [List.mem_cons] at hvC
      rcases hvC with rfl | hvC
      · rfl
      · exfalso
        rw [mem_vline_iff hh₁.le hhw] at hvC
        rw [List.mem_append, List.mem_singleton] at hvL
        rcases hvL with hvL | rfl
        · rcases hmemL₀ v hvL with h | h
          · exact hq'a (hvC.1.symm.trans h.1)
          · exact hq'q (hvC.1.symm.trans h)
        · rw [planar_vtx] at hvC; exact hq'a hvC.1.symm
  · obtain ⟨l₂, hl₂, hl₂m⟩ := exists_ppath_avoiding_pair hD3.1 hD3.2 (hRPD hq'RP) hd hq'd haq
      hq'a hq'q had.symm hqd.symm
    obtain ⟨CB', b₀', rB', hCB', hb₀', -, -, hCB'm⟩ := exists_branch_top hh₁.le hhw hl₂ hq'd
    have hE₁CB' : E₁ ∉ CB' := fun h => by
      rcases hCB'm _ h with h | h | h
      · rw [hE₁, planar_vtx] at h; exact hq'a h.1.symm
      · rw [hE₁, ht_vtx hh₁.le] at h; omega
      · rw [hE₁, planar_vtx] at h; exact had h.1
    have hCB : SPath (E₁ :: CB') E₁ (vtx k d hw) := hCB'.cons (vtx_adj_vtx_planar haq' h₁) hE₁CB'
    refine ⟨_, _, E₁, routeSpec_of_paths hL hLsub hE₁₂ hCB ?_ (fun h => had ?_) ?_ hLeq
      (by rw [hb₀']) (vKey_lt_of_ht_lt (by rw [ht_vtx (by omega), ht_vtx hh₁.le]; omega))⟩
    · intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [planar_vtx]; exact hRPD ha
      · rcases hCB'm v hv with h | h | h
        · rw [h.1]; exact hRPD hq'RP
        · exact (hl₂m _ h.2).1
        · rw [h.1]; exact hd
    · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
    · intro v hvC hvL
      rw [List.mem_cons] at hvC
      rcases hvC with rfl | hvC
      · rfl
      · exfalso
        rw [List.mem_append, List.mem_singleton] at hvL
        rcases hCB'm v hvC with h | h | h
        · rcases hvL with hvL | rfl
          · rcases hmemL₀ v hvL with h' | h'
            · exact hq'a (h.1.symm.trans h'.1)
            · exact hq'q (h.1.symm.trans h')
          · rw [planar_vtx] at h; exact hq'a h.1.symm
        · obtain ⟨-, hza, hzq⟩ := hl₂m _ h.2
          rcases hvL with hvL | rfl
          · rcases (hL₀m v).1 hvL with hv | hv | hv
            · rw [mem_vline_iff hh₁.le (Nat.zero_le k)] at hv; omega
            · rw [mem_liftH_iff (Nat.zero_le k)] at hv; omega
            · rw [mem_vline_iff (Nat.zero_le k) le_rfl] at hv; exact hzq hv.1
          · rw [planar_vtx] at hza; exact hza rfl
        · rcases hvL with hvL | rfl
          · rcases hmemL₀ v hvL with h' | h'
            · exact had (h'.1.symm.trans h.1)
            · exact hqd (h'.symm.trans h.1)
          · rw [planar_vtx] at h; exact had h.1

/-- **Template DELTA0** (`E₁` at the bottom and `E₂` at the top of the same column, `k ≥ 2`):
step to a side column and climb it; the branch goes up one unit from `E₁` and runs at height `1`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_delta0 (hk : 2 ≤ k) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d : ℤ × ℤ} {hw : ℕ} (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (had : a ≠ d) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a 0) (vtx k a k) (vtx k d hw)
      L Br c := by
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  obtain ⟨q, -, hqRP, haq, hqd, -, -, -⟩ := exists_two_nbrs (show xL < xR' by omega) (show rB < rP by omega) ha d
  have hqa : q ≠ a := by rintro rfl; simp [planarAdj] at haq
  set E₁ := vtx k a 0 with hE₁
  set E₂ := vtx k a k with hE₂
  -- `L = E₁ :: (side column) ++ [E₂]`
  have hV := vline_spath (k := k) q (Nat.zero_le k) le_rfl
  have hE₁V : E₁ ∉ vline k q 0 k := fun h => by
    rw [mem_vline_iff (Nat.zero_le k) le_rfl, hE₁, planar_vtx] at h; exact hqa h.1.symm
  have hE₂V : E₂ ∉ vline k q 0 k := fun h => by
    rw [mem_vline_iff (Nat.zero_le k) le_rfl, hE₂, planar_vtx] at h; exact hqa h.1.symm
  have hE₁₂ : E₁ ≠ E₂ := fun h => by
    have := congrArg ht h; rw [hE₁, hE₂, ht_vtx (Nat.zero_le k), ht_vtx le_rfl] at this; omega
  have hL : SPath (E₁ :: (vline k q 0 k ++ [E₂])) E₁ E₂ := by
    refine (hV.concat (x := E₂) ?_ hE₂V).cons ?_ ?_
    · exact (vtx_adj_vtx_planar haq k).symm
    · exact vtx_adj_vtx_planar haq 0
    · simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hE₁V, hE₁₂⟩
  obtain ⟨r, hr⟩ := vline_eq_cons_cons_up (k := k) q (show 0 < k by omega)
  have hLeq : E₁ :: (vline k q 0 k ++ [E₂]) = [] ++ E₁ :: vtx k q 0 :: (vtx k q (0 + 1) :: r ++ [E₂]) := by
    rw [hr]; rfl
  -- the branch at height `1`
  obtain ⟨l₂, hl₂, hl₂m⟩ := exists_ppath_avoiding_one (show xL < xR by omega) (show rB < rT by omega)
    (hRPD ha) hd had q hqa.symm hqd.symm
  have hY := liftH_spath (k := k) hl₂ 1
  have hZ := vline_spath (k := k) d (show 1 ≤ k by omega) hhw
  obtain ⟨hCB', hCB'm⟩ := hY.trans hZ fun v hvY hvZ => by
    rw [mem_liftH_iff (show 1 ≤ k by omega)] at hvY
    rw [mem_vline_iff (show 1 ≤ k by omega) hhw] at hvZ
    exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx (by omega)]; exact hvY.2⟩
  have hE₁CB' : E₁ ∉ liftH k 1 l₂ ++ (vline k d 1 hw).tail := fun h => by
    rcases (hCB'm _).1 h with h | h
    · rw [mem_liftH_iff (show 1 ≤ k by omega), hE₁, ht_vtx (Nat.zero_le k)] at h; omega
    · rw [mem_vline_iff (show 1 ≤ k by omega) hhw, hE₁, planar_vtx] at h; exact had h.1
  have hCB : SPath (E₁ :: (liftH k 1 l₂ ++ (vline k d 1 hw).tail)) E₁ (vtx k d hw) :=
    hCB'.cons (vtx_adj_vtx_succ a (by omega)) hE₁CB'
  obtain ⟨a', r₂, hl₂eq, -⟩ := hl₂.eq_cons_cons had
  refine ⟨_, _, E₁, routeSpec_of_paths hL ?_ hE₁₂ hCB ?_ (fun h => had ?_) ?_ hLeq
    (show E₁ :: (liftH k 1 l₂ ++ (vline k d 1 hw).tail) = E₁ :: vtx k a 1 :: (liftH k 1 (a' :: r₂) ++
      (vline k d 1 hw).tail) by rw [hl₂eq, liftH_cons]; rfl)
    (vKey_lt_of_ht_lt (by rw [ht_vtx (Nat.zero_le k), ht_vtx (by omega)]; omega))⟩
  · intro v hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · rw [planar_vtx]; exact ha
    · rw [mem_vline_iff (Nat.zero_le k) le_rfl] at hv; rw [hv.1]; exact hqRP
    · rw [planar_vtx]; exact ha
  · intro v hv
    rw [List.mem_cons] at hv
    rcases hv with rfl | hv
    · rw [planar_vtx]; exact hRPD ha
    · rcases (hCB'm v).1 hv with h | h
      · rw [mem_liftH_iff (show 1 ≤ k by omega)] at h; exact (hl₂m _ h.1).1
      · rw [mem_vline_iff (show 1 ≤ k by omega) hhw] at h; rw [h.1]; exact hd
  · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
  · intro v hvC hvL
    rw [List.mem_cons] at hvC
    rcases hvC with rfl | hvC
    · rfl
    · exfalso
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hvL
      rcases (hCB'm v).1 hvC with h | h
      · rw [mem_liftH_iff (show 1 ≤ k by omega)] at h
        rcases hvL with rfl | hvL | rfl
        · rw [ht_vtx (Nat.zero_le k)] at h; omega
        · rw [mem_vline_iff (Nat.zero_le k) le_rfl] at hvL; exact (hl₂m _ h.1).2 hvL.1
        · rw [ht_vtx le_rfl] at h; omega
      · rw [mem_vline_iff (show 1 ≤ k by omega) hhw] at h
        rcases hvL with rfl | hvL | rfl
        · rw [planar_vtx] at h; exact had h.1
        · rw [mem_vline_iff (Nat.zero_le k) le_rfl] at hvL; exact hqd (hvL.1.symm.trans h.1)
        · rw [planar_vtx] at h; exact had h.1

/-- Planar lexicographic comparison gives key comparison at equal heights. [folklore] -/
theorem vKey_vtx_lt_vtx {p p' : ℤ × ℤ} {h : ℕ} (hh : h ≤ k)
    (hlex : p.1 < p'.1 ∨ (p.1 = p'.1 ∧ p.2 < p'.2)) : vKey k (vtx k p h) < vKey k (vtx k p' h) := by
  rcases hlex with h1 | ⟨h1, h2⟩
  · exact vKey_lt_of_fst_lt (by rw [ht_vtx hh, ht_vtx hh]) (by rwa [planar_vtx, planar_vtx])
  · exact vKey_lt_of_snd_lt (by rw [ht_vtx hh, ht_vtx hh]) (by rwa [planar_vtx, planar_vtx])
      (by rwa [planar_vtx, planar_vtx])

/-- The main path of the MICRO templates: `E₁ = (0,a)`, `(0,q)`, `(1,q)`, `E₂ = (1,a)`. [folklore] -/
theorem micro_L (hk : 1 ≤ k) {a q : ℤ × ℤ} (haq : planarAdj a q) (hqa : q ≠ a) :
    SPath (vtx k a 0 :: (vline k q 0 1 ++ [vtx k a 1])) (vtx k a 0) (vtx k a 1) ∧
      (∀ v ∈ vtx k a 0 :: (vline k q 0 1 ++ [vtx k a 1]),
        (planar k v = a ∧ (ht v = 0 ∨ ht v = 1)) ∨ (planar k v = q ∧ ht v ≤ 1)) ∧
      vline k q 0 1 = [vtx k q 0, vtx k q 1] := by
  have hV := vline_spath (k := k) q (Nat.zero_le k) hk
  have hVeq : vline k q 0 1 = [vtx k q 0, vtx k q 1] := by
    rw [vline, if_pos (by omega), vcol_succ_left q (by omega), vcol, show 1 + 1 - (0 + 1) = 1 by rfl]
    simp
  have hmem : ∀ v ∈ vtx k a 0 :: (vline k q 0 1 ++ [vtx k a 1]),
      (planar k v = a ∧ (ht v = 0 ∨ ht v = 1)) ∨ (planar k v = q ∧ ht v ≤ 1) := by
    intro v hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | hv | rfl
    · left; rw [planar_vtx, ht_vtx (Nat.zero_le k)]; simp
    · rw [mem_vline_iff (Nat.zero_le k) hk] at hv; right; exact ⟨hv.1, by omega⟩
    · left; rw [planar_vtx, ht_vtx hk]; simp
  refine ⟨?_, hmem, hVeq⟩
  refine (hV.concat (x := vtx k a 1) (vtx_adj_vtx_planar haq 1).symm fun h => ?_).cons
    (vtx_adj_vtx_planar haq 0) ?_
  · rw [mem_vline_iff (Nat.zero_le k) hk, planar_vtx] at h; exact hqa h.1.symm
  · simp only [List.mem_append, List.mem_singleton, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [mem_vline_iff (Nat.zero_le k) hk, planar_vtx] at h; exact hqa h.1.symm
    · have := congrArg ht h; rw [ht_vtx (Nat.zero_le k), ht_vtx hk] at this; omega

/-- **Template MICRO-A** (`k = 1`, `E₁ = (0,a)`, `E₂ = (1,a)`): the main path through the side
column `q`, the branch leaving `E₁` horizontally into a lexicographically larger column `q'` and
running at height `0`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_microA (hk : k = 1) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d q q' : ℤ × ℤ} {hw : ℕ} (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (had : a ≠ d)
    (hq : q ∈ boxR xL xR' rB rP) (haq : planarAdj a q) (hqd : q ≠ d)
    (hq' : q' ∈ boxR xL xR rB rT) (haq' : planarAdj a q') (hq'q : q' ≠ q)
    (hlex : q.1 < q'.1 ∨ (q.1 = q'.1 ∧ q.2 < q'.2)) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a 0) (vtx k a 1) (vtx k d hw)
      L Br c := by
  have hk1 : 1 ≤ k := by omega
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  have hqa : q ≠ a := by rintro rfl; simp [planarAdj] at haq
  have hq'a : q' ≠ a := by rintro rfl; simp [planarAdj] at haq'
  set E₁ := vtx k a 0 with hE₁
  set E₂ := vtx k a 1 with hE₂
  obtain ⟨hL, hLm, hVeq⟩ := micro_L hk1 haq hqa
  have hLeq : E₁ :: (vline k q 0 1 ++ [E₂]) = [] ++ E₁ :: vtx k q 0 :: ([vtx k q 1] ++ [E₂]) := by
    rw [hVeq]; rfl
  have hLsub : ∀ v ∈ E₁ :: (vline k q 0 1 ++ [E₂]), planar k v ∈ boxR xL xR' rB rP := by
    intro v hv
    rcases hLm v hv with h | h
    · rw [h.1]; exact ha
    · rw [h.1]; exact hq
  have hE₁₂ : E₁ ≠ E₂ := fun h => by
    have := congrArg ht h; rw [hE₁, hE₂, ht_vtx (Nat.zero_le k), ht_vtx hk1] at this; omega
  have hkey : vKey k (vtx k q 0) < vKey k (vtx k q' 0) := vKey_vtx_lt_vtx (Nat.zero_le k) hlex
  by_cases hq'd : q' = d
  · subst hq'd
    have hV := vline_spath (k := k) q' (Nat.zero_le k) hhw
    obtain ⟨rest, hrest⟩ := hV.exists_eq_cons
    have hCB : SPath (E₁ :: vline k q' 0 hw) E₁ (vtx k q' hw) :=
      hV.cons (vtx_adj_vtx_planar haq' 0) fun h => by
        rw [mem_vline_iff (Nat.zero_le k) hhw, hE₁, planar_vtx] at h; exact hq'a h.1.symm
    refine ⟨_, _, E₁, routeSpec_of_paths hL hLsub hE₁₂ hCB ?_ (fun h => had ?_) ?_ hLeq
      (by rw [hrest]) hkey⟩
    · intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [planar_vtx]; exact hRPD ha
      · rw [mem_vline_iff (Nat.zero_le k) hhw] at hv; rw [hv.1]; exact hd
    · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
    · intro v hvC hvL
      rw [List.mem_cons] at hvC
      rcases hvC with rfl | hvC
      · rfl
      · exfalso
        rw [mem_vline_iff (Nat.zero_le k) hhw] at hvC
        rcases hLm v hvL with h | h
        · exact hq'a (hvC.1.symm.trans h.1)
        · exact hq'q (hvC.1.symm.trans h.1)
  · obtain ⟨l₃, hl₃, hl₃m⟩ := exists_ppath_avoiding_pair (by omega) (by omega) hq' hd hq'd haq
      hq'a hq'q had.symm hqd.symm
    have hY := liftH_spath (k := k) hl₃ 0
    have hZ := vline_spath (k := k) d (Nat.zero_le k) hhw
    obtain ⟨hCB', hCB'm⟩ := hY.trans hZ fun v hvY hvZ => by
      rw [mem_liftH_iff (Nat.zero_le k)] at hvY
      rw [mem_vline_iff (Nat.zero_le k) hhw] at hvZ
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx (Nat.zero_le k)]; omega⟩
    have hE₁CB' : E₁ ∉ liftH k 0 l₃ ++ (vline k d 0 hw).tail := fun h => by
      rcases (hCB'm _).1 h with h | h
      · rw [mem_liftH_iff (Nat.zero_le k), hE₁, planar_vtx] at h; exact (hl₃m _ h.1).2.1 rfl
      · rw [mem_vline_iff (Nat.zero_le k) hhw, hE₁, planar_vtx] at h; exact had h.1
    have hCB : SPath (E₁ :: (liftH k 0 l₃ ++ (vline k d 0 hw).tail)) E₁ (vtx k d hw) :=
      hCB'.cons (vtx_adj_vtx_planar haq' 0) hE₁CB'
    obtain ⟨q₂, r₃, hl₃eq, -⟩ := hl₃.eq_cons_cons hq'd
    refine ⟨_, _, E₁, routeSpec_of_paths hL hLsub hE₁₂ hCB ?_ (fun h => had ?_) ?_ hLeq
      (show E₁ :: (liftH k 0 l₃ ++ (vline k d 0 hw).tail) = E₁ :: vtx k q' 0 :: (liftH k 0 (q₂ :: r₃) ++
        (vline k d 0 hw).tail) by rw [hl₃eq, liftH_cons]; rfl) hkey⟩
    · intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [planar_vtx]; exact hRPD ha
      · rcases (hCB'm v).1 hv with h | h
        · rw [mem_liftH_iff (Nat.zero_le k)] at h; exact (hl₃m _ h.1).1
        · rw [mem_vline_iff (Nat.zero_le k) hhw] at h; rw [h.1]; exact hd
    · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
    · intro v hvC hvL
      rw [List.mem_cons] at hvC
      rcases hvC with rfl | hvC
      · rfl
      · exfalso
        rcases (hCB'm v).1 hvC with h | h
        · rw [mem_liftH_iff (Nat.zero_le k)] at h
          obtain ⟨-, hza, hzq⟩ := hl₃m _ h.1
          rcases hLm v hvL with h' | h'
          · exact hza h'.1
          · exact hzq h'.1
        · rw [mem_vline_iff (Nat.zero_le k) hhw] at h
          rcases hLm v hvL with h' | h'
          · exact had (h'.1.symm.trans h.1)
          · exact hqd (h'.1.symm.trans h.1)

/-- **Template MICRO-B** (`k = 1`): the same main path, the branch attached at `(1,q)` (whose
successor is `E₂ = (1,a)`), leaving horizontally into a column `q''` lexicographically larger than
`a`, and running at height `1`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_microB (hk : k = 1) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d q q'' : ℤ × ℤ} {hw : ℕ} (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (had : a ≠ d)
    (hq : q ∈ boxR xL xR' rB rP) (haq : planarAdj a q) (hqd : q ≠ d)
    (hq'' : q'' ∈ boxR xL xR rB rT) (hqq'' : planarAdj q q'') (hq''a : q'' ≠ a)
    (hlex : a.1 < q''.1 ∨ (a.1 = q''.1 ∧ a.2 < q''.2)) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a 0) (vtx k a 1) (vtx k d hw)
      L Br c := by
  have hk1 : 1 ≤ k := by omega
  have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
    rw [mem_boxR_iff] at hz ⊢; omega
  have hqa : q ≠ a := by rintro rfl; simp [planarAdj] at haq
  have hq''q : q'' ≠ q := by rintro rfl; simp [planarAdj] at hqq''
  set E₁ := vtx k a 0 with hE₁
  set E₂ := vtx k a 1 with hE₂
  set c := vtx k q 1 with hc
  obtain ⟨hL, hLm, hVeq⟩ := micro_L hk1 haq hqa
  have hLeq : E₁ :: (vline k q 0 1 ++ [E₂]) = [E₁, vtx k q 0] ++ c :: E₂ :: [] := by
    rw [hVeq]; rfl
  have hLsub : ∀ v ∈ E₁ :: (vline k q 0 1 ++ [E₂]), planar k v ∈ boxR xL xR' rB rP := by
    intro v hv
    rcases hLm v hv with h | h
    · rw [h.1]; exact ha
    · rw [h.1]; exact hq
  have hcE₂ : c ≠ E₂ := fun h => by
    have := congrArg (planar k) h; rw [hc, hE₂, planar_vtx, planar_vtx] at this; exact hqa this
  have hkey : vKey k E₂ < vKey k (vtx k q'' 1) := vKey_vtx_lt_vtx hk1 hlex
  by_cases hq''d : q'' = d
  · subst hq''d
    have hV := vline_spath (k := k) q'' hk1 hhw
    obtain ⟨rest, hrest⟩ := hV.exists_eq_cons
    have hCB : SPath (c :: vline k q'' 1 hw) c (vtx k q'' hw) :=
      hV.cons (vtx_adj_vtx_planar hqq'' 1) fun h => by
        rw [mem_vline_iff hk1 hhw, hc, planar_vtx] at h; exact hq''q h.1.symm
    refine ⟨_, _, c, routeSpec_of_paths hL hLsub hcE₂ hCB ?_ (fun h => hqd ?_) ?_ hLeq
      (by rw [hrest]) hkey⟩
    · intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [planar_vtx]; exact hRPD hq
      · rw [mem_vline_iff hk1 hhw] at hv; rw [hv.1]; exact hd
    · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
    · intro v hvC hvL
      rw [List.mem_cons] at hvC
      rcases hvC with rfl | hvC
      · rfl
      · exfalso
        rw [mem_vline_iff hk1 hhw] at hvC
        rcases hLm v hvL with h | h
        · exact hq''a (hvC.1.symm.trans h.1)
        · exact hq''q (hvC.1.symm.trans h.1)
  · obtain ⟨l₃, hl₃, hl₃m⟩ := exists_ppath_avoiding_pair (by omega) (by omega) hq'' hd hq''d haq
      hq''a hq''q had.symm hqd.symm
    have hY := liftH_spath (k := k) hl₃ 1
    have hZ := vline_spath (k := k) d hk1 hhw
    obtain ⟨hCB', hCB'm⟩ := hY.trans hZ fun v hvY hvZ => by
      rw [mem_liftH_iff hk1] at hvY
      rw [mem_vline_iff hk1 hhw] at hvZ
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx hk1]; omega⟩
    have hcCB' : c ∉ liftH k 1 l₃ ++ (vline k d 1 hw).tail := fun h => by
      rcases (hCB'm _).1 h with h | h
      · rw [mem_liftH_iff hk1, hc, planar_vtx] at h; exact (hl₃m _ h.1).2.2 rfl
      · rw [mem_vline_iff hk1 hhw, hc, planar_vtx] at h; exact hqd h.1
    have hCB : SPath (c :: (liftH k 1 l₃ ++ (vline k d 1 hw).tail)) c (vtx k d hw) :=
      hCB'.cons (vtx_adj_vtx_planar hqq'' 1) hcCB'
    obtain ⟨q₂, r₃, hl₃eq, -⟩ := hl₃.eq_cons_cons hq''d
    refine ⟨_, _, c, routeSpec_of_paths hL hLsub hcE₂ hCB ?_ (fun h => hqd ?_) ?_ hLeq
      (show c :: (liftH k 1 l₃ ++ (vline k d 1 hw).tail) = c :: vtx k q'' 1 :: (liftH k 1 (q₂ :: r₃) ++
        (vline k d 1 hw).tail) by rw [hl₃eq, liftH_cons]; rfl) hkey⟩
    · intro v hv
      rw [List.mem_cons] at hv
      rcases hv with rfl | hv
      · rw [planar_vtx]; exact hRPD hq
      · rcases (hCB'm v).1 hv with h | h
        · rw [mem_liftH_iff hk1] at h; exact (hl₃m _ h.1).1
        · rw [mem_vline_iff hk1 hhw] at h; rw [h.1]; exact hd
    · have := congrArg (planar k) h; rwa [planar_vtx, planar_vtx] at this
    · intro v hvC hvL
      rw [List.mem_cons] at hvC
      rcases hvC with rfl | hvC
      · rfl
      · exfalso
        rcases (hCB'm v).1 hvC with h | h
        · rw [mem_liftH_iff hk1] at h
          obtain ⟨-, hza, hzq⟩ := hl₃m _ h.1
          rcases hLm v hvL with h' | h'
          · exact hza h'.1
          · exact hzq h'.1
        · rw [mem_vline_iff hk1 hhw] at h
          rcases hLm v hvL with h' | h'
          · exact had (h'.1.symm.trans h.1)
          · exact hqd (h'.1.symm.trans h.1)

/-- **Template MICRO-C** (`k = 1`, `E₁`, `E₂` over the top-right corner `a` of the box, `w'`
in the column left of it): the explicit local route of the text. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_microC (hk : k = 1) (hcols : xL + 2 ≤ xR') (hxR : xR' = xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP = rT) {hw : ℕ} (hhw : hw ≤ k) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k (xR', rP) 0) (vtx k (xR', rP) 1)
      (vtx k (xR' - 1, rP) hw) L Br c := by
  have hk1 : 1 ≤ k := by omega
  subst hxR; subst hrP
  set a : ℤ × ℤ := (xR', rP) with ha
  set d : ℤ × ℤ := (xR' - 1, rP) with hd
  set dn : ℤ × ℤ := (xR', rP - 1) with hdn
  set m : ℤ × ℤ := (xR' - 1, rP - 1) with hm
  set E₁ := vtx k a 0 with hE₁
  set E₂ := vtx k a 1 with hE₂
  set c := vtx k dn 0 with hc
  -- the main path: `(0,a) (0,dn) (0,m) (1,m) (1,dn) (1,a)`
  have hP3 : PPath [a, dn, m] a m := by
    refine ⟨by simp, ?_, ?_, rfl, rfl⟩
    · refine List.isChain_cons_cons.2 ⟨?_, List.isChain_cons_cons.2 ⟨?_, List.isChain_singleton _⟩⟩
      · simp [ha, hdn, planarAdj]
      · simp [hdn, hm, planarAdj]
    · simp [ha, hdn, hm]; omega
  have hX := liftH_spath (k := k) hP3 0
  have hY := vline_spath (k := k) m (Nat.zero_le k) hk1
  have hZ := liftH_spath (k := k) hP3.reverse 1
  have hYeq : vline k m 0 1 = [vtx k m 0, vtx k m 1] := by
    rw [vline, if_pos (by omega), vcol_succ_left m (by omega), vcol, show 1 + 1 - (0 + 1) = 1 by rfl]
    simp
  obtain ⟨hL, hLm⟩ := SPath.trans3 hX hY hZ
    (fun v hvX hvY => by
      rw [mem_liftH_iff (Nat.zero_le k)] at hvX
      rw [mem_vline_iff (Nat.zero_le k) hk1] at hvY
      exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvY.1, by rw [ht_vtx (Nat.zero_le k)]; exact hvX.2⟩)
    (fun v hv hvZ => by
      rw [mem_liftH_iff hk1] at hvZ
      rcases hv with hv | hv
      · rw [mem_liftH_iff (Nat.zero_le k)] at hv; omega
      · rw [mem_vline_iff (Nat.zero_le k) hk1] at hv
        exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hv.1, by rw [ht_vtx hk1]; exact hvZ.2⟩)
  have hLmem : ∀ v, v ∈ liftH k 0 [a, dn, m] ++ (vline k m 0 1).tail ++ (liftH k 1 [a, dn, m].reverse).tail →
      planar k v = a ∨ planar k v = dn ∨ planar k v = m := by
    intro v hv
    rcases (hLm v).1 hv with hv | hv | hv
    · rw [mem_liftH_iff (Nat.zero_le k)] at hv; simpa using hv.1
    · rw [mem_vline_iff (Nat.zero_le k) hk1] at hv; exact Or.inr (Or.inr hv.1)
    · rw [mem_liftH_iff hk1] at hv; have := hv.1; simp at this; tauto
  have hLeq : liftH k 0 [a, dn, m] ++ (vline k m 0 1).tail ++ (liftH k 1 [a, dn, m].reverse).tail =
      [E₁] ++ c :: vtx k m 0 :: ([vtx k m 1] ++ (liftH k 1 [a, dn, m].reverse).tail) := by
    rw [hYeq]; rfl
  -- the branch, at height `0`, around the corner
  set B : List (ℤ × ℤ) := [dn, (xR', rP - 2), (xR' - 1, rP - 2), (xR' - 2, rP - 2), (xR' - 2, rP - 1),
    (xR' - 2, rP), d] with hB
  have hPB : PPath B dn d := by
    refine ⟨by simp [hB], ?_, ?_, rfl, rfl⟩
    · simp only [hB, hdn, hd, List.isChain_cons_cons, List.isChain_singleton, and_true, planarAdj,
        Prod.mk_add_mk, Prod.mk.injEq]
      omega
    · simp only [hB, hdn, hd, List.nodup_cons, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false,
        not_or, List.nodup_nil, and_true, true_and, not_false_eq_true]
      omega
  have hBmem : ∀ z ∈ B, xR' - 2 ≤ z.1 ∧ z.1 ≤ xR' ∧ rP - 2 ≤ z.2 ∧ z.2 ≤ rP ∧ z ≠ a ∧ z ≠ m ∧
      (z = dn ∨ z.2 = rP - 2 ∨ z.1 = xR' - 2 ∨ z = d) := by
    intro z hz
    simp only [hB, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [ha, hm, hdn, hd, ne_eq, Prod.ext_iff]
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hdn, hd] <;> omega
  have hBY := liftH_spath (k := k) hPB 0
  have hBZ := vline_spath (k := k) d (Nat.zero_le k) hhw
  obtain ⟨hCB, hCBm⟩ := hBY.trans hBZ fun v hvY hvZ => by
    rw [mem_liftH_iff (Nat.zero_le k)] at hvY
    rw [mem_vline_iff (Nat.zero_le k) hhw] at hvZ
    exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact hvZ.1, by rw [ht_vtx (Nat.zero_le k)]; omega⟩
  have hCBeq : liftH k 0 B ++ (vline k d 0 hw).tail = c :: vtx k (xR', rP - 2) 0 ::
      (liftH k 0 [(xR' - 1, rP - 2), (xR' - 2, rP - 2), (xR' - 2, rP - 1), (xR' - 2, rP), d] ++
        (vline k d 0 hw).tail) := by rw [hB]; rfl
  have hdna : dn ≠ a := by simp [hdn, ha]
  have hdnd : dn ≠ d := by simp [hdn, hd, Prod.ext_iff]
  have hdm : d ≠ m := by simp [hd, hm, Prod.ext_iff]; omega
  have hda : d ≠ a := by simp [hd, ha, Prod.ext_iff]
  refine ⟨_, _, c, routeSpec_of_paths hL ?_ (fun h => hdna ?_) hCB ?_ (fun h => hdnd ?_) ?_ hLeq hCBeq
    (vKey_vtx_lt_vtx (Nat.zero_le k) (Or.inl (by simp [hm])))⟩
  · intro v hv
    rw [mem_boxR_iff]
    rcases hLmem v hv with h | h | h <;> rw [h] <;> simp [ha, hdn, hm] <;> omega
  · have := congrArg (planar k) h; rwa [hc, planar_vtx, planar_vtx] at this
  · intro v hv
    rw [mem_boxR_iff]
    rcases (hCBm v).1 hv with h | h
    · rw [mem_liftH_iff (Nat.zero_le k)] at h
      obtain ⟨h1, h2, h3, h4, -⟩ := hBmem _ h.1
      omega
    · rw [mem_vline_iff (Nat.zero_le k) hhw] at h; rw [h.1]; simp [hd]; omega
  · have := congrArg (planar k) h; rwa [hc, planar_vtx, planar_vtx] at this
  · intro v hvC hvL
    rcases (hCBm v).1 hvC with h | h
    · rw [mem_liftH_iff (Nat.zero_le k)] at h
      obtain ⟨-, -, -, -, hza, hzm, hz⟩ := hBmem _ h.1
      rcases hLmem v hvL with h' | h' | h'
      · exact absurd h' hza
      · rw [hc]; exact (slab_ext_iff _ _).2 ⟨by rw [planar_vtx]; exact h', by rw [ht_vtx (Nat.zero_le k)]; exact h.2⟩
      · exact absurd h' hzm
    · rw [mem_vline_iff (Nat.zero_le k) hhw] at h
      exfalso
      rcases hLmem v hvL with h' | h' | h'
      · exact hda (h.1.symm.trans h')
      · exact hdnd (h'.symm.trans h.1)
      · exact hdm (h.1.symm.trans h')

/-- **Template MICRO** (`k = 1`, `E₁ = (0,a)`, `E₂ = (1,a)`): dispatch to MICRO-A/B/C according
to which neighbours of `a` are available. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_micro (hk : k = 1) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d : ℤ × ℤ} {hw : ℕ} (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (had : a ≠ d) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a 0) (vtx k a 1) (vtx k d hw)
      L Br c := by
  have ha' := ha; have hd' := hd
  rw [mem_boxR_iff] at ha' hd'
  obtain ⟨a1, a2⟩ := a
  simp only at ha'
  have hB := fun (q q'' : ℤ × ℤ) (hq : q ∈ boxR xL xR' rB rP) (haq : planarAdj (a1, a2) q) (hqd : q ≠ d)
    (hq'' : q'' ∈ boxR xL xR rB rT) (hqq'' : planarAdj q q'') (hq''a : q'' ≠ (a1, a2))
    (hlex : (a1, a2).1 < q''.1 ∨ ((a1, a2).1 = q''.1 ∧ (a1, a2).2 < q''.2)) =>
    route_microB hk hcols hxR hrows hrP hhw ha hd had hq haq hqd hq'' hqq'' hq''a hlex
  have hA := fun (q q' : ℤ × ℤ) (hq : q ∈ boxR xL xR' rB rP) (haq : planarAdj (a1, a2) q) (hqd : q ≠ d)
    (hq' : q' ∈ boxR xL xR rB rT) (haq' : planarAdj (a1, a2) q') (hq'q : q' ≠ q)
    (hlex : q.1 < q'.1 ∨ (q.1 = q'.1 ∧ q.2 < q'.2)) =>
    route_microA hk hcols hxR hrows hrP hhw ha hd had hq haq hqd hq' haq' hq'q hlex
  by_cases M1 : a1 + 1 ≤ xR' ∧ ((a1 + 1, a2) : ℤ × ℤ) ≠ d
  · refine hB (a1 + 1, a2) (if a2 + 1 ≤ rT then (a1 + 1, a2 + 1) else (a1 + 1, a2 - 1))
      (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj]) M1.2 ?_ ?_ ?_ (Or.inl ?_)
    · split_ifs <;> (rw [mem_boxR_iff]; simp only; omega)
    · split_ifs <;> simp [planarAdj]
    · split_ifs <;> simp
    · split_ifs <;> simp
  by_cases M2 : a2 + 1 ≤ rP ∧ ((a1, a2 + 1) : ℤ × ℤ) ≠ d
  · by_cases hx : a1 + 1 ≤ xR
    · exact hB (a1, a2 + 1) (a1 + 1, a2 + 1) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
        M2.2 (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj]) (by simp) (Or.inl (by simp))
    by_cases hy : a2 + 2 ≤ rT
    · exact hB (a1, a2 + 1) (a1, a2 + 2) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
        M2.2 (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj]; omega) (by simp)
        (Or.inr ⟨rfl, by simp⟩)
    · by_cases hl : ((a1 - 1, a2) : ℤ × ℤ) ≠ d
      · exact hA (a1 - 1, a2) (a1, a2 + 1) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
          hl (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj]) (by simp) (Or.inl (by simp))
      · push Not at hl
        exact hA (a1, a2 - 1) (a1, a2 + 1) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
          (by rw [← hl]; simp) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
          (by simp; omega) (Or.inr ⟨rfl, by simp⟩)
  by_cases M3 : rB ≤ a2 - 1 ∧ ((a1, a2 - 1) : ℤ × ℤ) ≠ d
  · by_cases hx : a1 + 1 ≤ xR
    · exact hB (a1, a2 - 1) (a1 + 1, a2 - 1) (by rw [mem_boxR_iff]; simp only; omega)
        (by simp [planarAdj]) M3.2 (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
        (by simp) (Or.inl (by simp))
    by_cases hy : a2 + 1 ≤ rT
    · exact hA (a1, a2 - 1) (a1, a2 + 1) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
        M3.2 (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj]) (by simp; omega)
        (Or.inr ⟨rfl, by simp⟩)
    · by_cases hl : ((a1 - 1, a2) : ℤ × ℤ) ≠ d
      · exact hA (a1 - 1, a2) (a1, a2 - 1) (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj])
          hl (by rw [mem_boxR_iff]; simp only; omega) (by simp [planarAdj]) (by simp) (Or.inl (by simp))
      · -- the corner case
        push Not at hl
        have h1 : xR' = a1 := by omega
        have h2 : rP = a2 := by omega
        subst h1; subst h2
        have hxR' : xR' = xR := by omega
        have hrP' : rP = rT := by omega
        rw [← hl]
        exact route_microC hk hcols hxR' hrows hrP' hhw
  · -- only the left neighbour is usable for the main path
    obtain ⟨q₀, q₀', hq₀RP, haq₀, hq₀d, hq₀'RP, haq₀', hq₀'q₀⟩ :=
      exists_two_nbrs (show xL < xR' by omega) (show rB < rP by omega) ha d
    have hRPD : boxR xL xR' rB rP ⊆ boxR xL xR rB rT := fun z hz => by
      rw [mem_boxR_iff] at hz ⊢; omega
    have hq₀RP' := hq₀RP; have hq₀'RP' := hq₀'RP
    rw [mem_boxR_iff] at hq₀RP' hq₀'RP'
    obtain ⟨x, y⟩ := q₀
    obtain ⟨x', y'⟩ := q₀'
    simp only at hq₀RP' hq₀'RP'
    have haq₀u := haq₀; have haq₀'u := haq₀'
    simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at haq₀u haq₀'u
    have hleft : x = a1 - 1 ∧ y = a2 := by
      rcases haq₀u with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exfalso; apply M1; refine ⟨by omega, ?_⟩; rw [← h1, ← h2]; exact hq₀d
      · exact ⟨by omega, by omega⟩
      · exfalso; apply M2; refine ⟨by omega, ?_⟩; rw [← h1, ← h2]; exact hq₀d
      · exfalso; apply M3; refine ⟨by omega, ?_⟩
        rw [show a2 - 1 = y by omega, h1]; exact hq₀d
    obtain ⟨hx1, hy1⟩ := hleft
    subst hx1
    have hy1' := hy1.symm
    subst hy1'
    refine hA (a1 - 1, a2) (x', y') hq₀RP haq₀ hq₀d (hRPD hq₀'RP) haq₀' hq₀'q₀ (Or.inl ?_)
    simp only
    rcases haq₀'u with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · omega
    · exfalso; apply hq₀'q₀; ext <;> simp <;> omega
    · omega
    · omega

/-- **Same-column routing**: `E₁ = (h₁, a)`, `E₂ = (h₂, a)` with `h₁ ≠ h₂`; dispatch on the heights.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2] -/
theorem route_sameCol (hk : 1 ≤ k) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {a d : ℤ × ℤ} {h₁ h₂ hw : ℕ} (hh₁ : h₁ ≤ k) (hh₂ : h₂ ≤ k) (hhw : hw ≤ k)
    (ha : a ∈ boxR xL xR' rB rP) (hd : d ∈ boxR xL xR rB rT) (h12 : h₁ ≠ h₂) (had : a ≠ d) :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) (vtx k a h₁) (vtx k a h₂) (vtx k d hw)
      L Br c := by
  rcases lt_or_gt_of_ne h12 with hlt | hgt
  · rcases lt_or_eq_of_le hh₂ with h2k | rfl
    · exact route_beta hcols hxR hrows hrP hh₁ hh₂ hhw ha hd hlt h2k had
    · rcases Nat.eq_zero_or_pos h₁ with rfl | hpos
      · rcases lt_or_eq_of_le hk with h2 | h1
        · exact route_delta0 h2 hcols hxR hrows hrP hhw ha hd had
        · have := route_micro h1.symm hcols hxR hrows hrP hhw ha hd had
          rwa [h1] at this
      · exact route_delta1 hcols hxR hrows hrP hlt hpos hhw ha hd had
  · exact route_desc hcols hxR hrows hrP hh₁ hh₂ hhw ha hd hgt had

/-- **Routing in the cleared box** (geometry-free form): for distinct vertices `E₁`, `E₂` over
the rectangle `RP` and `w'` over the rectangle `D ⊇ RP` in a column different from theirs, with
`RP` at least `3 × 4` and `k ≥ 1`, a route in the sense of `RouteSpec` exists (DST 2016, proof of
Fact 2: "there exist three disjoint self-avoiding paths … Note that such an `R` exists since …
`k` is assumed to be strictly larger than `0`").
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (existence of R)] -/
theorem exists_route (hk : 1 ≤ k) (hcols : xL + 2 ≤ xR') (hxR : xR' ≤ xR) (hrows : rB + 3 ≤ rP)
    (hrP : rP ≤ rT) {E₁ E₂ w' : slab 3 k}
    (ha : planar k E₁ ∈ boxR xL xR' rB rP) (hb : planar k E₂ ∈ boxR xL xR' rB rP)
    (hd : planar k w' ∈ boxR xL xR rB rT) (hE : E₁ ≠ E₂)
    (had : planar k E₁ ≠ planar k w') (hbd : planar k E₂ ≠ planar k w') :
    ∃ L Br c, RouteSpec k (boxR xL xR' rB rP) (boxR xL xR rB rT) E₁ E₂ w' L Br c := by
  by_cases hab : planar k E₁ = planar k E₂
  · obtain ⟨a, h₁, hh₁, rfl⟩ := exists_eq_vtx E₁
    obtain ⟨b, h₂, hh₂, rfl⟩ := exists_eq_vtx E₂
    obtain ⟨d, hw, hhw, rfl⟩ := exists_eq_vtx w'
    rw [planar_vtx, planar_vtx] at hab
    subst hab
    rw [planar_vtx] at ha had hd
    have h12 : h₁ ≠ h₂ := fun h => hE (by rw [h])
    exact route_sameCol hk hcols hxR hrows hrP hh₁ hh₂ hhw ha hd h12 had
  · exact route_main hk hcols hxR hrows hrP ha hb hd hab had hbd

end SameColumn

/-! ## The cleared box around a point of `U(ω)` -/

namespace GlueGeom

variable (G : GlueGeom)

/-- Left column of the cleared box `D(z)`: `max(z₁ - 3, n)`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the ball B_R(z))] -/
def bxL (z : ℤ × ℤ) : ℤ := max (z.1 - 3) G.n
/-- Right column of the cleared box: `min(z₁ + 3, 3n)`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the ball B_R(z))] -/
def bxR (z : ℤ × ℤ) : ℤ := min (z.1 + 3) (3 * G.n)
/-- Bottom row of the cleared box: `z₂ - 3`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the ball B_R(z))] -/
def brB (_G : GlueGeom) (z : ℤ × ℤ) : ℤ := z.2 - 3
/-- Top row of the cleared box: `min(z₂ + 3, max(3n, y + n))`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the ball B_R(z))] -/
def brT (z : ℤ × ℤ) : ℤ := min (z.2 + 3) (max (3 * G.n) (G.y + G.n))
/-- Top row of the part of the box inside `B_{3n}`. [folklore] -/
def brP (z : ℤ × ℤ) : ℤ := min (G.brT z) (3 * G.n)
/-- The right column of the box is entirely covered by `Z_n`. [folklore] -/
def Zfull (z : ℤ × ℤ) : Prop := G.bxR z = 3 * G.n ∧ G.y - G.α ≤ G.brB z ∧ G.brT z ≤ G.y + G.α

/-- `Zfull` is decidable. [folklore] -/
instance (z : ℤ × ℤ) : Decidable (G.Zfull z) := by unfold Zfull; infer_instance

/-- Right column of the routing rectangle of the rerouted piece: the right column of the box is
dropped when it is covered by `Z_n`. [folklore] -/
def bxR' (z : ℤ × ℤ) : ℤ := if G.Zfull z then G.bxR z - 1 else G.bxR z

/-- **The cleared box `D(z)`** (the formalisation's `\overline{B_R(z)}`, `R = 3`, clipped to
`B_{3n} ∪ B'_n` and to the columns `x ≥ n`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (the ball B_R(z))] -/
def Dbox (z : ℤ × ℤ) : Set (ℤ × ℤ) := boxR (G.bxL z) (G.bxR z) (G.brB z) (G.brT z)

/-- The routing rectangle of the rerouted piece of `γ_min`: the part of `D(z)` inside `B_{3n}`,
minus the right column when that column lies in `Z_n`. [folklore] -/
def RPbox (z : ℤ × ℤ) : Set (ℤ × ℤ) := boxR (G.bxL z) (G.bxR' z) (G.brB z) (G.brP z)

/-- The points near the two ends of `Z_n` whose box would be cut partially by `Z_n` (excluded
from the surgery; a bounded set). [folklore] -/
def zBad : Set (ℤ × ℤ) :=
  {z | 3 * (G.n : ℤ) - 3 ≤ z.1 ∧ z.1 ≤ 3 * G.n ∧
    ((G.y - G.α - 3 ≤ z.2 ∧ z.2 ≤ G.y - G.α + 2) ∨ (G.y + G.α - 2 ≤ z.2 ∧ z.2 ≤ G.y + G.α + 3))}

variable {G}

section BoxFacts

variable {z : ℤ × ℤ}

/-- **The box is large**: at least four columns (three for the routing rectangle) and four rows inside `B_{3n}` (uses `n ≥ 2`). [folklore] -/
theorem box_frame (hG : G.InRange) (hzb : z ∈ G.big) (hzs : z ∈ G.small) :
    G.bxL z + 3 ≤ G.bxR z ∧ G.bxL z + 2 ≤ G.bxR' z ∧ G.bxR' z ≤ G.bxR z ∧
    G.brB z + 3 ≤ G.brP z ∧ G.brP z ≤ G.brT z := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, small, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hzb hzs
  simp only [bxL, bxR, bxR', brB, brP, brT, Zfull]
  split_ifs <;> omega

/-- `D(z) ⊆ B_{3n} ∪ B'_n`. [folklore] -/
theorem Dbox_subset_region (hG : G.InRange) (hzb : z ∈ G.big) (hzs : z ∈ G.small) :
    G.Dbox z ⊆ G.big ∪ G.small := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, small, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hzb hzs
  intro q hq
  simp only [Dbox, mem_boxR_iff, bxL, bxR, brB, brT] at hq
  simp only [big, small, sqBox, Set.mem_union, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero]
  omega

/-- `D(z) ⊆ z + B_3`. [folklore] -/
theorem Dbox_subset_sqBox : G.Dbox z ⊆ sqBox z 3 := by
  intro q hq
  simp only [Dbox, mem_boxR_iff, bxL, bxR, brB, brT] at hq
  simp only [sqBox, Set.mem_setOf_eq, abs_le, Nat.cast_ofNat]
  omega

/-- `z ∈ D(z)`. [folklore] -/
theorem mem_Dbox_self (hG : G.InRange) (hzb : z ∈ G.big) (hzs : z ∈ G.small) : z ∈ G.Dbox z := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, small, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hzb hzs
  simp only [Dbox, mem_boxR_iff, bxL, bxR, brB, brT]
  omega

/-- The routing rectangle lies in the box. [folklore] -/
theorem RPbox_subset_Dbox (hG : G.InRange) (hzb : z ∈ G.big) (hzs : z ∈ G.small) : G.RPbox z ⊆ G.Dbox z := by
  intro q hq
  have := box_frame hG hzb hzs
  simp only [RPbox, Dbox, mem_boxR_iff] at hq ⊢
  omega

/-- The routing rectangle lies in `B_{3n}`. [folklore] -/
theorem RPbox_subset_big (hG : G.InRange) (hzb : z ∈ G.big) (hzs : z ∈ G.small) {q : ℤ × ℤ}
    (hq : q ∈ G.RPbox z) : q ∈ G.big := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, small, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hzb hzs
  simp only [RPbox, mem_boxR_iff, bxL, bxR', bxR, brB, brP, brT, Zfull] at hq
  simp only [big, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero]
  split_ifs at hq <;> omega

/-- Off the excluded strip `zBad`, the routing rectangle avoids `Z_n`. [folklore] -/
theorem RPbox_not_zSeg (hG : G.InRange) (hzb : z ∈ G.big) (hbad : z ∉ G.zBad) {q : ℤ × ℤ}
    (hq : q ∈ G.RPbox z) : q ∉ G.zSeg := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hzb
  simp only [zBad, Set.mem_setOf_eq, not_and, not_or] at hbad
  simp only [RPbox, mem_boxR_iff, bxL, bxR', bxR, brB, brP, brT, Zfull] at hq
  simp only [zSeg, sideSeg, Set.mem_setOf_eq, not_and]
  intro h1
  split_ifs at hq with hZ <;> omega

/-- For `u_{3n} < n`, the box avoids `S_{3n}`. [folklore] -/
theorem Dbox_not_src (hu : G.u₃ + 1 ≤ G.n) {q : ℤ × ℤ} (hq : q ∈ G.Dbox z) : q ∉ G.src := by
  simp only [Dbox, mem_boxR_iff, bxL, bxR, brB, brT] at hq
  simp only [src, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero, not_and]
  intro h; omega

/-- A lattice neighbour of `z` inside `B_{3n}` but outside `D(z)` is the left neighbour. [folklore] -/
theorem nbr_eq_of_not_Dbox (hG : G.InRange) (hzb : z ∈ G.big) (hzs : z ∈ G.small) {q : ℤ × ℤ}
    (hadj : planarAdj z q) (hqb : q ∈ G.big) (hqD : q ∉ G.Dbox z) : q = (z.1 - 1, z.2) := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, small, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hzb hzs hqb
  simp only [Dbox, mem_boxR_iff, bxL, bxR, brB, brT, not_and] at hqD
  obtain ⟨z1, z2⟩ := z
  obtain ⟨q1, q2⟩ := q
  simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at hadj
  simp only [Prod.mk.injEq] at *
  omega

/-- The unit box around `z`, within `B'_n`, lies in `D(z)`. [folklore] -/
theorem mem_Dbox_of_sqBox_one (hG : G.InRange) {q : ℤ × ℤ} (hq : q ∈ sqBox z 1) (hqs : q ∈ G.small) :
    q ∈ G.Dbox z := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [small, sqBox, Set.mem_setOf_eq, abs_le, Nat.cast_one] at hq hqs
  simp only [Dbox, mem_boxR_iff, bxL, bxR, brB, brT]
  omega

/-- A point of `D(z)` inside `B_{3n}` and off `Z_n` lies in the routing rectangle. [folklore] -/
theorem mem_RPbox_of (hG : G.InRange) {q : ℤ × ℤ} (hq : q ∈ G.Dbox z) (hqb : q ∈ G.big) (hqZ : q ∉ G.zSeg) :
    q ∈ G.RPbox z := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  simp only [big, sqBox, Set.mem_setOf_eq, abs_le, Prod.fst_zero, Prod.snd_zero, sub_zero] at hqb
  simp only [zSeg, sideSeg, Set.mem_setOf_eq, not_and] at hqZ
  simp only [Dbox, mem_boxR_iff] at hq
  simp only [RPbox, mem_boxR_iff, bxR', brP, Zfull]
  split_ifs with hZ
  · simp only [bxR, brT, brB] at hZ hq ⊢
    refine ⟨hq.1, ?_, hq.2.2.1, by omega⟩
    rcases lt_or_eq_of_le hq.2.1 with h | h
    · omega
    · exfalso; exact hqZ (by omega) (by omega) (by omega)
  · exact ⟨hq.1, hq.2.1, hq.2.2.1, by omega⟩

end BoxFacts

end GlueGeom

/-! ## The surgery at a good point of `U(ω)` -/

section Build

variable {k : ℕ}

/-- Splitting a list at the last element satisfying a predicate. [folklore] -/
theorem exists_last_split {α : Type*} {p : α → Prop} (l : List α) (h : ∃ x ∈ l, p x) :
    ∃ (l₁ : List α) (x : α) (l₂ : List α), l = l₁ ++ x :: l₂ ∧ p x ∧ ∀ y ∈ l₂, ¬p y := by
  obtain ⟨x, hx, hpx⟩ := h
  obtain ⟨m₁, y, m₂, hm, hpy, hm₁⟩ := exists_first_split l.reverse ⟨x, List.mem_reverse.2 hx, hpx⟩
  refine ⟨m₂.reverse, y, m₁.reverse, ?_, hpy, fun w hw => hm₁ w (List.mem_reverse.1 hw)⟩
  have := congrArg List.reverse hm
  rw [List.reverse_reverse] at this
  rw [this]; simp

/-- **Open connections are witnessed by open self-avoiding paths** (vertex lists). [folklore] -/
theorem exists_isOSAP_of_openConnIn {ω : BondConfig (slab 3 k)} {S : Set (slab 3 k)} {x y : slab 3 k}
    (h : ω ∈ openConnIn S x y) : ∃ l, IsOSAP k ω S {x} {y} l := by
  classical
  obtain ⟨hx, hy, ⟨W⟩⟩ := h
  set φ : (openGraph ω).induce S →g openGraph ω := (SimpleGraph.Embedding.induce S).toHom with hφ
  have hφinj : Function.Injective φ := fun a b h => Subtype.ext h
  set W' : (openGraph ω).Walk x y := W.toPath.1.map φ with hW'
  have hsupp : W'.support = W.toPath.1.support.map φ := Walk.support_map _ _
  have hnd : W'.support.Nodup := by
    rw [hsupp]
    exact W.toPath.2.support_nodup.map hφinj
  have hS : ∀ v ∈ W'.support, v ∈ S := by
    intro v hv
    rw [hsupp, List.mem_map] at hv
    obtain ⟨w, -, rfl⟩ := hv
    exact w.2
  refine ⟨W'.support, hnd, ?_, hS, Walk.support_ne_nil W', fun h => ?_, fun h => ?_⟩
  · exact W'.isChain_adj_support.imp fun a b hab => (openGraph_adj ω a b).1 hab
  · rw [Walk.head_support]; rfl
  · rw [Walk.getLast_support]; rfl

/-- A slab path with distinct ends is its head, then the inner part, then its last vertex. [folklore] -/
theorem SPath.eq_cons_dropLast_concat {L : List (slab 3 k)} {s t : slab 3 k} (h : SPath L s t)
    (hst : s ≠ t) : L = s :: (L.tail.dropLast ++ [t]) := by
  obtain ⟨hL, htl, -, hlast⟩ := h.tail_props hst
  conv_lhs => rw [hL]
  congr 1
  rw [List.dropLast_append_getLast? t (by simp [hlast])]

namespace GlueGeom

/-- The set of points whose box could contain the last vertex of `γ_min(ω)` (excluded from the
surgery; a bounded set). [folklore] -/
def lastBad (G : GlueGeom) (k : ℕ) (ω : BondConfig (slab 3 k)) : Set (ℤ × ℤ) :=
  {z | ∃ v ∈ (G.γmin k ω).getLast?, z ∈ sqBox (planar k v) 3}

variable {G : GlueGeom}

/-- Symmetry of sup-norm boxes. [folklore] -/
theorem mem_sqBox_comm {z w : ℤ × ℤ} {m : ℕ} (h : z ∈ sqBox w m) : w ∈ sqBox z m := by
  simp only [sqBox, Set.mem_setOf_eq] at h ⊢
  rw [abs_sub_comm w.1, abs_sub_comm w.2]
  exact h

/-- **the local surgery exists at every good point of `U(ω)`** (DST 2016, §2.3, proof
of Fact 2: the construction of `ω^{(z)}` — here as the data `GlueGeom.Surgery` of
`SlabGluingFact2Core.lean`, with cleared box `D(z) ⊆ z + B_3`). Hypotheses: `ω ∈ 𝒳` a
lattice configuration, `z ∈ U(ω)` not within distance `3` of the end of `γ_min(ω)` and not in the
strip `zBad` near the ends of `Z_n`; the geometric range RESTRICTED by `u_{3n} + 1 ≤ n` (so that
the box does not meet `S̄_{3n}`; the case `u_{3n} = n` of `GlueGeom.InRange`, allowed by the printed
Lemma 6, is NOT covered here — the Fact 2 assembly handles it by working with
`DuminilCopinSidoraviciusTassion2016_lemma6'` of `SlabCriticalityChain4.lean`, see the module
docstring). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (construction of ω^{(z)})] -/
theorem exists_surgery (hG : G.InRange) (hu : G.u₃ + 1 ≤ G.n) (hk : 0 < k)
    {ω : BondConfig (slab 3 k)} (hω : ω ⊆ (slabGraph 3 k).edgeSet) (hX : ω ∈ G.evX k)
    {z : ℤ × ℤ} (hz : z ∈ G.U k ω) (hzl : z ∉ G.lastBad k ω) (hzb : z ∉ G.zBad) :
    ∃ sg : G.Surgery k ω, sg.D ⊆ sqBox z 3 := by
  classical
  have hA : ω ∈ G.evA k := hX.1.1.1
  obtain ⟨hγO, -⟩ := G.γmin_spec k hA
  set γ := G.γmin k ω with hγdef
  obtain ⟨hzs, ⟨g, hgγ, hgz⟩, x₀, hx₀, s', hs', hπ⟩ := hz
  rw [← hγdef] at hgγ
  have hγmp : minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) = γ := rfl
  have hzbig : z ∈ G.big := by rw [← hgz]; exact hγO.subset g hgγ
  set D := G.Dbox z with hDdef
  have hzD : z ∈ D := mem_Dbox_self hG hzbig hzs
  have hDsq : D ⊆ sqBox z 3 := Dbox_subset_sqBox
  have hS := G.big_finite k
  have hex : ∃ l, IsOSAP k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) l :=
    (mem_slabConn_iff_exists_isOSAP ω _ _ _).1 hA
  -- the last vertex of `γ` is off `D̄`
  have hlastD : ∀ v, γ.getLast? = some v → planar k v ∉ D := by
    intro v hv hvD
    exact hzl ⟨v, by rw [hv]; rfl, mem_sqBox_comm (hDsq hvD)⟩
  -- first visit of `γ` to `D̄`
  obtain ⟨p₀, E₁, rest₁, hγ1, hE₁D, hp₀D⟩ :=
    exists_first_split (p := fun x => planar k x ∈ D) γ ⟨g, hgγ, by rw [hgz]; exact hzD⟩
  have hp₀ : p₀ ≠ [] := by
    rintro rfl
    have h := hγO.head_mem hγO.ne_nil
    simp only [hγ1, List.nil_append, List.head_cons, mem_slabLift_iff] at h
    exact Dbox_not_src hu hE₁D h
  have hrest₁ : rest₁ ≠ [] := by
    rintro rfl
    exact hlastD E₁ (by rw [hγ1]; simp) hE₁D
  -- `γ` visits `D̄` again after `E₁`
  have hmeet : ∃ x ∈ rest₁, planar k x ∈ D := by
    by_contra hno
    push Not at hno
    have hgE₁ : g = E₁ := by
      rw [hγ1] at hgγ
      rcases List.mem_append.1 hgγ with h | h
      · exact absurd (hgz ▸ hzD) (hp₀D g h)
      · rcases List.mem_cons.1 h with h | h
        · exact h
        · exact absurd (hgz ▸ hzD) (hno g h)
    have hch := hγO.chain
    rw [hγ1, List.isChain_append] at hch
    obtain ⟨-, hch2, hlink⟩ := hch
    set u := p₀.getLast hp₀ with hu'
    set w := rest₁.head hrest₁ with hw
    have huE : s(u, E₁) ∈ ω := (hlink u (by rw [List.getLast?_eq_some_getLast hp₀]; rfl) E₁ (by simp)).1
    have hEw : s(E₁, w) ∈ ω := by
      rw [List.isChain_cons] at hch2
      exact (hch2.1 w (by rw [List.head?_eq_some_head hrest₁]; rfl)).1
    have hup₀ : u ∈ p₀ := List.getLast_mem hp₀
    have hwr : w ∈ rest₁ := List.head_mem hrest₁
    have huγ : u ∈ γ := by rw [hγ1]; exact List.mem_append_left _ hup₀
    have hwγ : w ∈ γ := by rw [hγ1]; simp [hwr]
    have hadj₁ := (slab_adj_iff _ _).1 ((SimpleGraph.mem_edgeSet _).1 (hω huE))
    have hadj₂ := (slab_adj_iff _ _).1 ((SimpleGraph.mem_edgeSet _).1 (hω hEw))
    have hpE₁ : planar k E₁ = z := by rw [← hgE₁]; exact hgz
    rw [hpE₁] at hadj₁ hadj₂
    have hu1 : planar k u = (z.1 - 1, z.2) := by
      rcases hadj₁ with ⟨-, hpa⟩ | ⟨hpe, -⟩
      · exact nbr_eq_of_not_Dbox hG hzbig hzs (planarAdj_symm hpa) (hγO.subset u huγ) (hp₀D u hup₀)
      · exact absurd (hpe ▸ hzD) (hp₀D u hup₀)
    have hw1 : planar k w = (z.1 - 1, z.2) := by
      rcases hadj₂ with ⟨-, hpa⟩ | ⟨hpe, -⟩
      · exact nbr_eq_of_not_Dbox hG hzbig hzs hpa (hγO.subset w hwγ) (hno w hwr)
      · exact absurd (hpe ▸ hzD) (hno w hwr)
    have hht : ht u = ht w := by
      rcases hadj₁ with ⟨h1, -⟩ | ⟨hpe, -⟩
      · rcases hadj₂ with ⟨h2, -⟩ | ⟨hpe, -⟩
        · omega
        · exact absurd (hpe ▸ hzD) (hno w hwr)
      · exact absurd (hpe ▸ hzD) (hp₀D u hup₀)
    have huw : u = w := (slab_ext_iff u w).2 ⟨hu1.trans hw1.symm, hht⟩
    have hnd := hγO.nodup
    rw [hγ1, List.nodup_append] at hnd
    exact hnd.2.2 u hup₀ w (List.mem_cons_of_mem _ hwr) huw
  -- last visit of `γ` to `D̄`
  obtain ⟨mid, E₂, s₀, hrest, hE₂D, hs₀D⟩ := exists_last_split (p := fun x => planar k x ∈ D) rest₁ hmeet
  have hγeq : γ = p₀ ++ E₁ :: (mid ++ E₂ :: s₀) := by rw [hγ1, hrest]
  have hs₀ : s₀ ≠ [] := by
    rintro rfl
    have : γ = (p₀ ++ E₁ :: mid) ++ [E₂] := by rw [hγeq]; simp
    exact hlastD E₂ (by rw [this, List.getLast?_concat]) hE₂D
  have hE₁₂ : E₁ ≠ E₂ := by
    intro h
    have hnd := hγO.nodup
    rw [hγeq, List.nodup_append] at hnd
    have := (List.nodup_cons.1 hnd.2.1).1
    exact this (by rw [h]; simp)
  -- `E₁`, `E₂` are off `Z_n`
  have hE₁Z : planar k E₁ ∉ G.zSeg := by
    have h := minPath_prefix_getLast_not_mem hS hex (p := p₀ ++ [E₁]) (s := mid ++ E₂ :: s₀)
      (by rw [hγmp, hγeq]; simp) (by simp) (by simp)
    simpa using h
  have hE₂Z : planar k E₂ ∉ G.zSeg := by
    have h := minPath_prefix_getLast_not_mem hS hex (p := p₀ ++ E₁ :: mid ++ [E₂]) (s := s₀)
      (by rw [hγmp, hγeq]; simp) hs₀ (by simp)
    simpa using h
  have hE₁γ : E₁ ∈ γ := by rw [hγeq]; simp
  have hE₂γ : E₂ ∈ γ := by rw [hγeq]; simp
  have hE₁RP : planar k E₁ ∈ G.RPbox z := mem_RPbox_of hG hE₁D (hγO.subset E₁ hE₁γ) hE₁Z
  have hE₂RP : planar k E₂ ∈ G.RPbox z := mem_RPbox_of hG hE₂D (hγO.subset E₂ hE₂γ) hE₂Z
  -- the witness path `π` of (P2) and its last vertex `w'` in `D̄`
  obtain ⟨π, hπO⟩ := exists_isOSAP_of_openConnIn hπ
  have hx₀π : x₀ ∈ π := by
    have := hπO.head_mem hπO.ne_nil
    rw [Set.mem_singleton_iff] at this
    rw [← this]; exact List.head_mem _
  have hx₀D : planar k x₀ ∈ D := mem_Dbox_of_sqBox_one hG hx₀ (hπO.subset x₀ hx₀π).1
  obtain ⟨πpre, w', sgt, hπeq, hw'D, hsgtD⟩ := exists_last_split (p := fun x => planar k x ∈ D) π ⟨x₀, hx₀π, hx₀D⟩
  have hw'π : w' ∈ π := by rw [hπeq]; simp
  have hw'γ : planar k w' ∉ G.γcols k ω := (hπO.subset w' hw'π).2
  have hw'E₁ : planar k E₁ ≠ planar k w' := fun h => hw'γ ⟨E₁, hE₁γ, h⟩
  have hw'E₂ : planar k E₂ ≠ planar k w' := fun h => hw'γ ⟨E₂, hE₂γ, h⟩
  -- routing
  obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := box_frame hG hzbig hzs
  obtain ⟨L, Br, c, spec⟩ := exists_route (xL := G.bxL z) (xR' := G.bxR' z) (xR := G.bxR z) (rB := G.brB z)
    (rP := G.brP z) (rT := G.brT z) hk hf2 hf3 hf4 hf5 hE₁RP hE₂RP hw'D hE₁₂ hw'E₁ hw'E₂
  have hRPD : G.RPbox z ⊆ D := RPbox_subset_Dbox hG hzbig hzs
  set P := L.tail.dropLast with hP
  have hLeq : L = E₁ :: (P ++ [E₂]) := spec.hL.eq_cons_dropLast_concat hE₁₂
  have hPL : ∀ v ∈ P, v ∈ L := fun v hv => by
    rw [hLeq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
  have hBrlast : Br.getLast spec.hBr = w' := by
    have h1 := spec.hCB.last
    rw [List.getLast?_cons, List.getLast?_eq_some_getLast spec.hBr] at h1
    simpa using h1
  -- the `S'`-side path `σ = w' :: sgt`
  have hπch := hπO.chain
  rw [hπeq, List.isChain_append] at hπch
  refine ⟨⟨D, p₀, E₁, mid, E₂, s₀, P, c, Br, w' :: sgt,
    Dbox_subset_region hG hzbig hzs, hγeq, hp₀, hs₀, hp₀D, hs₀D, hE₁D, hE₂D,
    fun x hx => hRPD (spec.hL_sub x (hPL x hx)),
    fun x hx => RPbox_subset_big hG hzbig hzs (spec.hL_sub x (hPL x hx)),
    fun x hx => RPbox_not_zSeg hG hzbig hzb (spec.hL_sub x (hPL x hx)),
    hLeq ▸ spec.hL.chain, hLeq ▸ spec.hL.nodup,
    ?_, spec.hBr, spec.hBr_sub,
    spec.hCB.chain.imp fun a b h => h, spec.hCB.nodup,
    fun x hx => hLeq ▸ spec.hBr_L x hx,
    fun l₁ l₂ y h => spec.hfwd l₁ l₂ y (hLeq.trans h) _ (List.head?_eq_some_head spec.hBr ▸ rfl),
    ?_, (by rw [hBrlast]; rfl), hπch.2.1,
    fun x hx => (hπO.subset x (by rw [hπeq]; exact List.mem_append_right _ hx)).1,
    fun x hx => (hπO.subset x (by rw [hπeq]; exact List.mem_append_right _ hx)).2,
    hsgtD,
    fun h => ?_⟩, hDsq⟩
  · -- `c ∈ E₁ :: P`
    have hc := spec.hc
    rw [hLeq] at hc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h spec.hcE₂
  · -- no structure vertex over `S_{3n}`
    intro v hv hvsrc _
    rw [mem_slabLift_iff] at hvsrc
    rcases List.mem_append.1 hv with h | h
    · exact absurd hvsrc (Dbox_not_src hu (hRPD (spec.hL_sub v (hPL v h))))
    · exact absurd hvsrc (Dbox_not_src hu (spec.hBr_sub v (List.dropLast_subset _ h)))
  · -- `σ` ends in `S̄'_n`
    have := hπO.last_mem hπO.ne_nil
    rw [Set.mem_singleton_iff] at this
    have h2 : (w' :: sgt).getLast h = π.getLast hπO.ne_nil := by
      rw [List.getLast_congr _ (by simp) hπeq, List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    rw [h2, this]; exact hs'

end GlueGeom

end Build

end Percolation.Literature

end
