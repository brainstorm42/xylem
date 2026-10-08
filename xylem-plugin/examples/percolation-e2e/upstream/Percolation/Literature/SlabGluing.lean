import Percolation.Literature.MultiValuedMapPrinciple
import Percolation.Literature.PlanarDuality
import Percolation.Literature.SlabCriticality
import Percolation.Util.Linter

/-!
# The Gluing Lemma of Duminil-Copin–Sidoravicius–Tassion (DST 2016, Lemma 6): decomposition into Facts 1–2, the minimal path `γ_min`, the set `U(ω)`, and the planar crossing fact

* `IsOSAP`, `pathKey`, `minPath` — open self-avoiding paths as vertex lists, the
  lexicographic order on them (vertex form, as in Newman–Tassion–Wu 2017, §3.2; DST fix "an
  arbitrary order" of this lexicographic kind), and **`γ_min(ω)`**, the minimal open
  self-avoiding path, with its basic API: existence and minimality (`minPath_spec`),
  characterisation (`minPath_eq_of_min`), and the stability used in the proof of Fact 1
  (`minPath_eq_of_subset`: closing edges off `γ_min` does not change it); the exact link with
  the events `X ⟷^B Y` of `SlabCriticality.lean` (`mem_slabConn_iff_exists_isOSAP`).
* `exists_mem_support_of_side_crossing` — proved: **the planar crossing fact** behind Fact 1
  ("Projections of paths from `S̄_{3n}` to `Z̄_n` and from `S̄'_n` to `Ȳ_n^-` and `Ȳ_n^+` must
  intersect", p. 5): a lattice walk of `ℤ²` in the half-plane `{x₀ ≤ R}` from `{x₀ ≤ L}` to a
  point `e` of `{x₀ = R}` meets every lattice walk inside `[L, R] × [B, T]` joining two points
  of the right side on either side of `e`. Reduced to this library's
  `exists_mem_support_of_crossing` (`PlanarDuality.lean`: a left-right and a top-bottom crossing
  of a rectangle meet, by winding numbers) by extending both walks to crossings of
  `[L-1, R+1] × [B-1, T+1]` (`exists_prefix_within`, straight walks).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: Lemma 6 (p. 5), §2.3 (pp. 6–7: Lemma 7, the order on paths, `γ_min`,
  `U(ω)`, the event `𝒳`, Facts 1 and 2, conclusion p. 7). Pages are those of the arXiv
  version's text.
* C. M. Newman, V. Tassion, W. Wu, *Critical percolation and the minimal spanning tree in
  slabs*, Comm. Pure Appl. Math. 70 (2017), no. 11, 2084–2120, doi:10.1002/cpa.21714, §3.2
  (the vertex-lexicographic order; Lemma 3.6 = DST Lemma 7; Thms. 3.8–3.9 and their proof,
  Facts 1–2; PDF pp. 10–14 of the held copy) [NewmanTassionWu2017].

## Design choices

* Paths are vertex lists (`IsOSAP`): the set of self-avoiding lists inside a finite set is
  finite (`finite_setOf_nodup_subset`), so minima exist without a `Fintype` on the vertex
  type; openness is `s(a, b) ∈ ω ∧ a ≠ b` (the adjacency of `openGraph ω`), so that no lattice
  hypothesis enters the definitions (for lattice configurations open edges are lattice edges).
* The order on paths is the lexicographic order of `List (ℤ ×ₗ ℤ ×ₗ ℤ)` on the coordinate keys
  (`vKey`, injective): a proper prefix is smaller, as in DST's first clause; no order instance
  is put on `slab 3 k` (which already carries the pointwise order of `Fin 3 → ℤ`).
* In (P2) the path `π` is taken inside `B̄'_n` and the distance is the sup-norm one
  (`z + B_1 = sqBox z 1`), matching the use of (P2) for the paths of `B^±` in Fact 1 and for the
  branch to `S̄'_n` in Fact 2; "distance exactly `1`" is rendered as "`π` avoids the columns of
  `γ_min` and starts over `z + B_1`" (the distance at the start is then `1` by (P1)).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph Filter Topology

/-! ## The planar crossing fact behind Fact 1 ("projections of paths … must intersect") -/

section PlanarCrossing

/-- A straight walk up the column `x₀ = z₀`, `m` steps. [folklore] -/
theorem exists_walk_up (z : Site 2) (m : ℕ) :
    ∃ (w : Site 2) (W : (zdGraph 2).Walk z w), w 0 = z 0 ∧ w 1 = z 1 + m ∧
      ∀ x ∈ W.support, x 0 = z 0 ∧ z 1 ≤ x 1 ∧ x 1 ≤ z 1 + m := by
  induction m generalizing z with
  | zero =>
    refine ⟨z, Walk.nil, rfl, by simp, fun x hx => ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hx
    subst hx
    simp
  | succ m ih =>
    have hadj : (zdGraph 2).Adj z (z + Pi.single 1 1) := adj_of_stepKind (.up (by simp) (by simp))
    obtain ⟨w, W, hw0, hw1, hW⟩ := ih (z + Pi.single 1 1)
    refine ⟨w, Walk.cons hadj W, by simpa using hw0, by rw [hw1]; simp; ring, fun x hx => ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨rfl, le_rfl, by push_cast; omega⟩
    · have h := hW x hx
      simp only [Pi.add_apply, single_one_apply_zero, add_zero, single_one_apply_one] at h
      push_cast
      omega

/-- A straight walk to the right along the row `x₁ = z₁`, `m` steps. [folklore] -/
theorem exists_walk_right (z : Site 2) (m : ℕ) :
    ∃ (w : Site 2) (W : (zdGraph 2).Walk z w), w 1 = z 1 ∧ w 0 = z 0 + m ∧
      ∀ x ∈ W.support, x 1 = z 1 ∧ z 0 ≤ x 0 ∧ x 0 ≤ z 0 + m := by
  induction m generalizing z with
  | zero =>
    refine ⟨z, Walk.nil, rfl, by simp, fun x hx => ?_⟩
    rw [Walk.support_nil, List.mem_singleton] at hx
    subst hx
    simp
  | succ m ih =>
    have hadj : (zdGraph 2).Adj z (z + Pi.single 0 1) :=
      adj_of_stepKind (.right (by simp) (by simp))
    obtain ⟨w, W, hw1, hw0, hW⟩ := ih (z + Pi.single 0 1)
    refine ⟨w, Walk.cons hadj W, by simpa using hw1, by rw [hw0]; simp; ring, fun x hx => ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨rfl, le_rfl, by push_cast; omega⟩
    · have h := hW x hx
      simp only [Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero] at h
      push_cast
      omega

/-- A straight vertical walk between two points of a column, covering exactly the segment.
[folklore] -/
theorem exists_walk_vertical {z w : Site 2} (h0 : z 0 = w 0) (h1 : z 1 ≤ w 1) :
    ∃ W : (zdGraph 2).Walk z w, ∀ x ∈ W.support, x 0 = z 0 ∧ z 1 ≤ x 1 ∧ x 1 ≤ w 1 := by
  obtain ⟨w', W, hw0, hw1, hW⟩ := exists_walk_up z (w 1 - z 1).toNat
  have hm : ((w 1 - z 1).toNat : ℤ) = w 1 - z 1 := Int.toNat_of_nonneg (by omega)
  have hww : w' = w := by
    rw [Site.eq_iff_two, hw0, hw1, hm, h0]
    constructor <;> ring
  subst hww
  exact ⟨W, fun x hx => by have := hW x hx; rw [hm] at this; omega⟩

/-- A straight horizontal walk between two points of a row, covering exactly the segment.
[folklore] -/
theorem exists_walk_horizontal {z w : Site 2} (h1 : z 1 = w 1) (h0 : z 0 ≤ w 0) :
    ∃ W : (zdGraph 2).Walk z w, ∀ x ∈ W.support, x 1 = z 1 ∧ z 0 ≤ x 0 ∧ x 0 ≤ w 0 := by
  obtain ⟨w', W, hw1, hw0, hW⟩ := exists_walk_right z (w 0 - z 0).toNat
  have hm : ((w 0 - z 0).toNat : ℤ) = w 0 - z 0 := Int.toNat_of_nonneg (by omega)
  have hww : w' = w := by
    rw [Site.eq_iff_two, hw0, hw1, hm, h1]
    constructor <;> ring
  subst hww
  exact ⟨W, fun x hx => by have := hW x hx; rw [hm] at this; omega⟩

/-- **Maximal initial segment inside a set.** A walk starting in `S` either stays in `S`, or has
an initial segment inside `S` — a walk along vertices of the original one — ending at a vertex
`f ∈ S` adjacent to a vertex `g ∉ S` of the walk. [folklore] -/
theorem exists_prefix_within {V : Type*} {G : SimpleGraph V} (S : Set V) {u v : V}
    (W : G.Walk u v) (hu : u ∈ S) :
    (∀ x ∈ W.support, x ∈ S) ∨
      ∃ f g, f ∈ S ∧ g ∉ S ∧ g ∈ W.support ∧ G.Adj f g ∧
        ∃ W' : G.Walk u f, (∀ x ∈ W'.support, x ∈ W.support) ∧ ∀ x ∈ W'.support, x ∈ S := by
  induction W with
  | nil => exact Or.inl fun x hx => by rw [Walk.support_nil, List.mem_singleton] at hx; exact hx ▸ hu
  | @cons u v w h W ih =>
    by_cases hv : v ∈ S
    · rcases ih hv with hall | ⟨f, g, hf, hg, hgW, hadj, W', hW'1, hW'2⟩
      · refine Or.inl fun x hx => ?_
        rw [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hu
        · exact hall x hx
      · refine Or.inr ⟨f, g, hf, hg, by simp [hgW], hadj, Walk.cons h W', fun x hx => ?_,
          fun x hx => ?_⟩
        · rw [Walk.support_cons, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr (hW'1 x hx)
        · rw [Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hu
          · exact hW'2 x hx
    · exact Or.inr ⟨u, v, hu, hv, by simp, h, Walk.nil, fun x hx => by
        rw [Walk.support_nil, List.mem_singleton] at hx; simp [hx], fun x hx => by
        rw [Walk.support_nil, List.mem_singleton] at hx; exact hx ▸ hu⟩

/-- **The planar crossing fact.** Let `γ` be a lattice walk of `ℤ²` in the half-plane
`{x₀ ≤ R}` from a point `s` with `s₀ ≤ L` to a point `e` of the line `{x₀ = R}`, and let `Q`
be a lattice walk inside the rectangle `[L, R] × [B, T]` between two points `a⁻`, `a⁺` of its
right side `{x₀ = R}` with `a⁻₁ < e₁ < a⁺₁`. Then `γ` and `Q` have a common vertex. (The
discrete Jordan-curve fact behind "Projections of paths from `S̄_{3n}` to `Z̄_n` and from
`S̄'_n` to `Ȳ_n^-` and `Ȳ_n^+` must intersect", DST 2016, p. 5, and "two paths from
`S̄'_n` to `Ȳ_n^-` and `Ȳ_n^+` respectively must intersect at least one set of the form
`\overline{\{z\}}` with `z` in `U(ω)`", proof of Fact 1, p. 6; reduced here to this library's
`exists_mem_support_of_crossing` — a left-right and a top-bottom crossing of a rectangle meet —
by extending both walks into crossings of `[L-1, R+1] × [B-1, T+1]`.)
[cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
theorem exists_mem_support_of_side_crossing {L R B T : ℤ} {s e am ap : Site 2}
    (γ : (zdGraph 2).Walk s e) (Q : (zdGraph 2).Walk am ap)
    (hγ : ∀ x ∈ γ.support, x 0 ≤ R) (hs : s 0 ≤ L) (he : e 0 = R)
    (hQ : ∀ x ∈ Q.support, L ≤ x 0 ∧ x 0 ≤ R ∧ B ≤ x 1 ∧ x 1 ≤ T)
    (ham : am 0 = R) (hap : ap 0 = R) (h1 : am 1 < e 1) (h2 : e 1 < ap 1) :
    ∃ x ∈ γ.support, x ∈ Q.support := by
  have hamQ := hQ am Q.start_mem_support
  have hapQ := hQ ap Q.end_mem_support
  have hLR : L ≤ R := hamQ.1.trans hamQ.2.1
  have heR : L ≤ e 0 ∧ e 0 ≤ R ∧ B ≤ e 1 ∧ e 1 ≤ T := by omega
  -- the rectangle as a set
  set S : Set (Site 2) := {x | L ≤ x 0 ∧ x 0 ≤ R ∧ B ≤ x 1 ∧ x 1 ≤ T} with hS
  -- final segment of `γ` inside the rectangle, read backwards from `e`
  have hprefix := exists_prefix_within S γ.reverse (show e ∈ S from heR)
  -- in both cases we produce `f ∈ S` on the left/top/bottom side and a walk `M : f → e` along `γ` inside `S`
  obtain ⟨f, hfS, hfside, M, hMγ, hMS⟩ : ∃ f : Site 2, f ∈ S ∧ (f 0 = L ∨ f 1 = T ∨ f 1 = B) ∧
      ∃ M : (zdGraph 2).Walk f e, (∀ x ∈ M.support, x ∈ γ.support) ∧ ∀ x ∈ M.support, x ∈ S := by
    rcases hprefix with hall | ⟨f, g, hf, hg, hgγ, hadj, W', hW'1, hW'2⟩
    · refine ⟨s, ?_, Or.inl ?_, γ, fun x hx => hx, fun x hx => hall x (by simpa using hx)⟩
      · exact hall s (by simp)
      · have := (hall s (by simp)).1; omega
    · refine ⟨f, hf, ?_, W'.reverse, fun x hx => ?_, fun x hx => ?_⟩
      · have hg' : g 0 ≤ R := hγ g (by simpa using hgγ)
        have hgS : ¬(L ≤ g 0 ∧ g 0 ≤ R ∧ B ≤ g 1 ∧ g 1 ≤ T) := hg
        obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
        rcases stepKind_of_adj hadj with ⟨k0, k1⟩ | ⟨k0, k1⟩ | ⟨k1, k0⟩ | ⟨k1, k0⟩ <;> omega
      · rw [Walk.support_reverse, List.mem_reverse] at hx
        simpa using hW'1 x hx
      · rw [Walk.support_reverse, List.mem_reverse] at hx
        exact hW'2 x hx
  -- the prefix from the left side of the big rectangle to `f`, outside `S` except at `f`
  obtain ⟨st, Pre, hst, hPre⟩ : ∃ (st : Site 2) (Pre : (zdGraph 2).Walk st f), st 0 = L - 1 ∧
      ∀ x ∈ Pre.support, x = f ∨ (L - 1 ≤ x 0 ∧ x 0 ≤ R ∧ B - 1 ≤ x 1 ∧ x 1 ≤ T + 1 ∧
        (x 0 = L - 1 ∨ x 1 = T + 1 ∨ x 1 = B - 1)) := by
    obtain ⟨hf1S, hf2S, hf3S, hf4S⟩ := id hfS
    rcases id hfside with hf0 | hf1 | hf1
    · -- left side: one step from `f - e₀`
      refine ⟨f - Pi.single 0 1, Walk.cons (adj_of_stepKind (.right (by simp) (by simp))) Walk.nil,
        by simp [hf0], fun x hx => ?_⟩
      rw [Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_singleton] at hx
      rcases hx with rfl | rfl
      · right; simp; omega
      · exact Or.inl rfl
    · -- top side: along the row `T + 1` from `(L-1, T+1)` to `(f₀, T+1)`, then down to `f`
      set c : Site 2 := ![L - 1, T + 1] with hc
      set c' : Site 2 := ![f 0, T + 1] with hc'
      obtain ⟨H, hH⟩ := exists_walk_horizontal (z := c) (w := c') (by simp [hc, hc'])
        (by simp [hc, hc']; omega)
      have hadj : (zdGraph 2).Adj c' f := adj_of_stepKind (.down (by simp [hc', hf1]) (by simp [hc']))
      refine ⟨c, H.append (Walk.cons hadj Walk.nil), by simp [hc], fun x hx => ?_⟩
      rw [Walk.support_append, List.mem_append, Walk.support_cons, Walk.support_nil, List.tail_cons,
        List.mem_singleton] at hx
      rcases hx with hx | rfl
      · right
        have := hH x hx
        simp only [hc, hc', Matrix.cons_val_zero, Matrix.cons_val_one] at this
        omega
      · exact Or.inl rfl
    · -- bottom side: along the row `B - 1`, then up to `f`
      set c : Site 2 := ![L - 1, B - 1] with hc
      set c' : Site 2 := ![f 0, B - 1] with hc'
      obtain ⟨H, hH⟩ := exists_walk_horizontal (z := c) (w := c') (by simp [hc, hc'])
        (by simp [hc, hc']; omega)
      have hadj : (zdGraph 2).Adj c' f := adj_of_stepKind (.up (by simp [hc', hf1]) (by simp [hc']))
      refine ⟨c, H.append (Walk.cons hadj Walk.nil), by simp [hc], fun x hx => ?_⟩
      rw [Walk.support_append, List.mem_append, Walk.support_cons, Walk.support_nil, List.tail_cons,
        List.mem_singleton] at hx
      rcases hx with hx | rfl
      · right
        have := hH x hx
        simp only [hc, hc', Matrix.cons_val_zero, Matrix.cons_val_one] at this
        omega
      · exact Or.inl rfl
  -- the extended `γ`: `Pre`, then `M`, then one step to the right of `e`
  set e' : Site 2 := e + Pi.single 0 1 with he'
  have hee' : (zdGraph 2).Adj e e' := adj_of_stepKind (.right (by simp [he']) (by simp [he']))
  let P : (zdGraph 2).Walk st e' := Pre.append (M.append (Walk.cons hee' Walk.nil))
  -- the extended `Q`: up the column `R + 1` from level `B - 1` to `a⁻`, `Q`, and up to level `T + 1`
  set b₀ : Site 2 := ![R + 1, B - 1] with hb₀
  set b₁ : Site 2 := ![R + 1, am 1] with hb₁
  set t₁ : Site 2 := ![R + 1, ap 1] with ht₁
  set t₀ : Site 2 := ![R + 1, T + 1] with ht₀
  obtain ⟨V₁, hV₁⟩ := exists_walk_vertical (z := b₀) (w := b₁) (by simp [hb₀, hb₁])
    (by simp [hb₀, hb₁]; omega)
  obtain ⟨V₂, hV₂⟩ := exists_walk_vertical (z := t₁) (w := t₀) (by simp [ht₁, ht₀])
    (by simp [ht₁, ht₀]; omega)
  have hba : (zdGraph 2).Adj b₁ am := adj_of_stepKind (.left (by simp [hb₁, ham]) (by simp [hb₁]))
  have hat : (zdGraph 2).Adj ap t₁ := adj_of_stepKind (.right (by simp [ht₁, hap]) (by simp [ht₁]))
  let Q' : (zdGraph 2).Walk b₀ t₀ :=
    V₁.append (Walk.cons hba (Q.append (Walk.cons hat V₂)))
  -- supports
  have hPsupp : ∀ x ∈ P.support, x ∈ Pre.support ∨ x ∈ M.support ∨ x = e' := by
    intro x hx
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_cons,
      Walk.support_nil, List.mem_cons, List.mem_singleton] at hx
    rcases hx with hx | hx | rfl | rfl
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inl M.end_mem_support)
    · exact Or.inr (Or.inr rfl)
  have hQ'supp : ∀ x ∈ Q'.support, x ∈ V₁.support ∨ x ∈ Q.support ∨ x ∈ V₂.support := by
    intro x hx
    rw [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons,
      Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | rfl | hx | rfl | hx
    · exact Or.inl hx
    · exact Or.inl V₁.end_mem_support
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inl Q.end_mem_support)
    · exact Or.inr (Or.inr hx)
  have hPbd : ∀ x ∈ P.support, L - 1 ≤ x 0 ∧ x 0 ≤ R + 1 ∧ B - 1 ≤ x 1 ∧ x 1 ≤ T + 1 := by
    intro x hx
    rcases hPsupp x hx with h | h | rfl
    · rcases hPre x h with rfl | h
      · obtain ⟨h1, h2, h3, h4⟩ := hfS; omega
      · omega
    · obtain ⟨h1, h2, h3, h4⟩ := hMS x h; omega
    · simp only [he', Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero]; omega
  have hQbd : ∀ x ∈ Q'.support, L - 1 ≤ x 0 ∧ x 0 ≤ R + 1 ∧ B - 1 ≤ x 1 ∧ x 1 ≤ T + 1 := by
    intro x hx
    rcases hQ'supp x hx with h | h | h
    · have := hV₁ x h
      simp only [hb₀, hb₁, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
    · obtain ⟨h1, h2, h3, h4⟩ := hQ x h; omega
    · have := hV₂ x h
      simp only [ht₁, ht₀, Matrix.cons_val_zero, Matrix.cons_val_one] at this
      omega
  obtain ⟨x, hxP, hxQ⟩ := exists_mem_support_of_crossing (L := L - 1) (R := R + 1) (B := B - 1)
    (T := T + 1) P Q' hPbd hQbd hst (by simp [he', he]) (by simp [hb₀]) (by simp [ht₀])
  -- the common vertex lies on `M ⊆ γ` and on `Q`
  rcases hQ'supp x hxQ with hx | hx | hx
  · -- on the lower column: `x₀ = R + 1`, impossible for points of `P` other than `e'`
    have hx' := hV₁ x hx
    simp only [hb₀, hb₁, Matrix.cons_val_zero, Matrix.cons_val_one] at hx'
    exfalso
    rcases hPsupp x hxP with h | h | rfl
    · rcases hPre x h with rfl | h
      · have := hfS.2.1; omega
      · omega
    · have := (hMS x h).2.1; omega
    · simp only [he', Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero] at hx'; omega
  · refine ⟨x, ?_, hx⟩
    have hxS := hQ x hx
    rcases hPsupp x hxP with h | h | rfl
    · rcases hPre x h with rfl | h
      · exact hMγ _ M.start_mem_support
      · exfalso; omega
    · exact hMγ x h
    · exfalso; simp only [he', Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero] at hxS; omega
  · have hx' := hV₂ x hx
    simp only [ht₁, ht₀, Matrix.cons_val_zero, Matrix.cons_val_one] at hx'
    exfalso
    rcases hPsupp x hxP with h | h | rfl
    · rcases hPre x h with rfl | h
      · have := hfS.2.1; omega
      · omega
    · have := (hMS x h).2.1; omega
    · simp only [he', Pi.add_apply, single_zero_apply_zero, single_zero_apply_one, add_zero] at hx'; omega

end PlanarCrossing

/-! ## Open self-avoiding paths and the minimal path `γ_min` -/

section Paths

/-- Lists of bounded length with entries in a finite set form a finite set. [folklore] -/
theorem finite_setOf_length_le {α : Type*} {S : Set α} (hS : S.Finite) (N : ℕ) :
    {l : List α | l.length ≤ N ∧ ∀ x ∈ l, x ∈ S}.Finite := by
  induction N with
  | zero =>
    refine (Set.finite_singleton ([] : List α)).subset ?_
    rintro l ⟨hl, -⟩
    exact List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
  | succ N ih =>
    have hsub : {l : List α | l.length ≤ N + 1 ∧ ∀ x ∈ l, x ∈ S} ⊆
        {[]} ∪ ⋃ a ∈ S, (fun l => a :: l) '' {l : List α | l.length ≤ N ∧ ∀ x ∈ l, x ∈ S} := by
      rintro l ⟨hl, hmem⟩
      cases l with
      | nil => exact Or.inl rfl
      | cons a l =>
        refine Or.inr (Set.mem_biUnion (hmem a (by simp)) ⟨l, ⟨?_, fun x hx => hmem x (by simp [hx])⟩, rfl⟩)
        simpa using hl
    exact ((Set.finite_singleton _).union (hS.biUnion fun a _ => (ih.image _))).subset hsub

/-- Self-avoiding lists with entries in a finite set form a finite set. [folklore] -/
theorem finite_setOf_nodup_subset {α : Type*} {S : Set α} (hS : S.Finite) :
    {l : List α | l.Nodup ∧ ∀ x ∈ l, x ∈ S}.Finite := by
  classical
  refine (finite_setOf_length_le hS hS.toFinset.card).subset ?_
  rintro l ⟨hnd, hmem⟩
  refine ⟨?_, hmem⟩
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card fun x hx => hS.mem_toFinset.2 (hmem x (List.mem_toFinset.1 hx))

variable (k : ℕ)

/-- **Open self-avoiding paths.** `l` is an `ω`-open self-avoiding path inside `S` from `X` to
`Y`: a non-empty list of distinct vertices of `S`, consecutive ones joined by open edges, starting
in `X` and ending in `Y` (DST 2016, §2.3: "self-avoiding paths from `S̄_{3n}` to `Z̄_n`"; no
lattice adjacency is imposed, so that the link with the events `X ⟷^B Y` is exact — for lattice
configurations open edges are lattice edges). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (the order on self-avoiding paths)] -/
structure IsOSAP (ω : BondConfig (slab 3 k)) (S X Y : Set (slab 3 k)) (l : List (slab 3 k)) : Prop where
  /-- self-avoiding -/
  nodup : l.Nodup
  /-- consecutive vertices are joined by open edges -/
  chain : l.IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b)
  /-- inside `S` -/
  subset : ∀ x ∈ l, x ∈ S
  /-- non-empty -/
  ne_nil : l ≠ []
  /-- starts in `X` -/
  head_mem : ∀ h : l ≠ [], l.head h ∈ X
  /-- ends in `Y` -/
  last_mem : ∀ h : l ≠ [], l.getLast h ∈ Y

variable {k}

/-- Open self-avoiding paths persist in larger configurations. [folklore] -/
theorem IsOSAP.mono {ω ω' : BondConfig (slab 3 k)} (h : ω ⊆ ω') {S X Y : Set (slab 3 k)}
    {l : List (slab 3 k)} (hl : IsOSAP k ω S X Y l) : IsOSAP k ω' S X Y l :=
  ⟨hl.nodup, hl.chain.imp fun _ _ hab => ⟨h hab.1, hab.2⟩, hl.subset, hl.ne_nil, hl.head_mem,
    hl.last_mem⟩

/-- An open self-avoiding path whose edges all lie in `ω'` is `ω'`-open. [folklore] -/
theorem IsOSAP.of_edges {ω ω' : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)}
    {l : List (slab 3 k)} (hl : IsOSAP k ω S X Y l)
    (h : ∀ a ∈ l, ∀ b ∈ l, s(a, b) ∈ ω → s(a, b) ∈ ω') : IsOSAP k ω' S X Y l :=
  ⟨hl.nodup, hl.chain.imp_of_mem_imp fun a b ha hb hab => ⟨h a ha b hb hab.1, hab.2⟩, hl.subset,
    hl.ne_nil, hl.head_mem, hl.last_mem⟩

/-- A chain of open edges joins its ends inside any set containing its vertices. [folklore] -/
theorem openConnIn_of_isChain {ω : BondConfig (slab 3 k)} {S : Set (slab 3 k)} :
    ∀ (a : slab 3 k) (l : List (slab 3 k)), (a :: l).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) →
      (∀ x ∈ a :: l, x ∈ S) → ω ∈ openConnIn S a ((a :: l).getLast (List.cons_ne_nil a l)) := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ hS
    rw [mem_openConnIn_iff_pathIn]
    exact PathIn.refl (hS a (by simp))
  | cons b l ih =>
    intro hc hS
    rw [List.isChain_cons_cons] at hc
    have h1 : ω ∈ openConnIn S a b := by
      rw [mem_openConnIn_iff_pathIn]
      exact PathIn.of_adj (hS a (by simp)) (hS b (by simp)) ((openGraph_adj ω a b).2 hc.1)
    have h2 := ih b hc.2 fun x hx => hS x (by simp [hx])
    rw [List.getLast_cons (List.cons_ne_nil b l)]
    exact SlabCriticality.openConnIn_trans h1 h2

/-- **`X ⟷^B Y` holds iff there is an open self-avoiding path inside `B̄` from `X̄` to `Ȳ`.**
[folklore] -/
theorem mem_slabConn_iff_exists_isOSAP (ω : BondConfig (slab 3 k)) (B X Y : Set (ℤ × ℤ)) :
    ω ∈ slabConn k B X Y ↔ ∃ l, IsOSAP k ω (slabLift k B) (slabLift k X) (slabLift k Y) l := by
  classical
  constructor
  · rintro ⟨x, hx, y, hy, hxB, hyB, hr⟩
    obtain ⟨W⟩ := hr
    -- a self-avoiding walk in the induced open graph, pushed to the slab
    set φ : (openGraph ω).induce (slabLift k B) →g openGraph ω :=
      (SimpleGraph.Embedding.induce (slabLift k B)).toHom with hφ
    have hφinj : Function.Injective φ := fun a b h => Subtype.ext h
    set W' : (openGraph ω).Walk x y := W.toPath.1.map φ with hW'
    have hsupp : W'.support = W.toPath.1.support.map φ := Walk.support_map _ _
    have hnd : W'.support.Nodup := by
      rw [hsupp]
      exact W.toPath.2.support_nodup.map hφinj
    have hS : ∀ v ∈ W'.support, v ∈ slabLift k B := by
      intro v hv
      rw [hsupp, List.mem_map] at hv
      obtain ⟨w, -, rfl⟩ := hv
      exact w.2
    refine ⟨W'.support, hnd, ?_, hS, Walk.support_ne_nil W', fun h => ?_, fun h => ?_⟩
    · exact W'.isChain_adj_support.imp fun a b hab => (openGraph_adj ω a b).1 hab
    · rw [Walk.head_support]; exact hx
    · rw [Walk.getLast_support]; exact hy
  · rintro ⟨l, hl⟩
    obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
    refine ⟨a, hl.head_mem (List.cons_ne_nil a l'), (a :: l').getLast (List.cons_ne_nil a l'),
      hl.last_mem _, openConnIn_of_isChain a l' hl.chain hl.subset⟩

variable (k)

/-- A linear key for slab vertices: the coordinates in lexicographic order (the "arbitrary
order `≪` on vertices of `S_k`" of DST 2016, §2.3; Newman–Tassion–Wu 2017, §3.2 fix a similar
lexicographic order). [cite: DuminilCopinSidoraviciusTassion2016, §2.3] -/
def vKey (x : slab 3 k) : ℤ ×ₗ ℤ ×ₗ ℤ := toLex (x.1 0, toLex (x.1 1, x.1 2))

/-- The key of a path: the list of keys of its vertices, compared lexicographically (a proper
prefix is smaller) — the lexicographical order on self-avoiding paths of DST 2016, §2.3, in the
vertex form of Newman–Tassion–Wu 2017, §3.2.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3] [cite: NewmanTassionWu2017, §3.2] -/
def pathKey (l : List (slab 3 k)) : List (ℤ ×ₗ ℤ ×ₗ ℤ) := l.map (vKey k)

variable {k}

/-- `vKey` is injective. [folklore] -/
theorem vKey_injective : Function.Injective (vKey k) := by
  intro x y h
  simp only [vKey, toLex_inj, Prod.mk.injEq] at h
  apply Subtype.ext
  funext j
  fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2

/-- `pathKey` is injective. [folklore] -/
theorem pathKey_injective : Function.Injective (pathKey k) :=
  List.map_injective_iff.2 vKey_injective

variable (k)

/-- **The minimal open self-avoiding path** `γ_min(ω)` from `X` to `Y` inside `S` (DST 2016,
§2.3, Definition: "Define `γ_min(ω)` to be the minimal (for the order defined above) open
self-avoiding path from `S̄_{3n}` to `Z̄_n`"); the empty list when there is no such path (or `S`
is infinite). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Definition of γ_min)] -/
def minPath (ω : BondConfig (slab 3 k)) (S X Y : Set (slab 3 k)) : List (slab 3 k) :=
  open scoped Classical in
  if h : S.Finite ∧ ∃ l, IsOSAP k ω S X Y l then
    Classical.choose (Set.exists_min_image {l | IsOSAP k ω S X Y l} (pathKey k)
      ((finite_setOf_nodup_subset h.1).subset fun _ hl => ⟨hl.nodup, hl.subset⟩) h.2)
  else []

variable {k}

/-- When an open self-avoiding path exists (inside a finite `S`), `minPath` is one of them and
its key is minimal. [folklore] -/
theorem minPath_spec {ω : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)} (hS : S.Finite)
    (h : ∃ l, IsOSAP k ω S X Y l) :
    IsOSAP k ω S X Y (minPath k ω S X Y) ∧
      ∀ l, IsOSAP k ω S X Y l → pathKey k (minPath k ω S X Y) ≤ pathKey k l := by
  have hh : S.Finite ∧ ∃ l, IsOSAP k ω S X Y l := ⟨hS, h⟩
  rw [minPath, dif_pos hh]
  exact Classical.choose_spec (Set.exists_min_image {l | IsOSAP k ω S X Y l} (pathKey k)
    ((finite_setOf_nodup_subset hh.1).subset fun _ hl => ⟨hl.nodup, hl.subset⟩) hh.2)

/-- Without open self-avoiding paths, `minPath` is empty. [folklore] -/
theorem minPath_eq_nil {ω : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)}
    (h : ¬∃ l, IsOSAP k ω S X Y l) : minPath k ω S X Y = [] := by
  rw [minPath, dif_neg (fun hh => h hh.2)]

/-- Characterisation of the minimal path: the open self-avoiding path with minimal key.
[folklore] -/
theorem minPath_eq_of_min {ω : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)} (hS : S.Finite)
    {l : List (slab 3 k)} (hl : IsOSAP k ω S X Y l)
    (hmin : ∀ l', IsOSAP k ω S X Y l' → pathKey k l ≤ pathKey k l') : minPath k ω S X Y = l := by
  obtain ⟨h1, h2⟩ := minPath_spec hS ⟨l, hl⟩
  exact pathKey_injective (le_antisymm (h2 l hl) (hmin _ h1))

/-- **Stability of the minimal path under closing edges off it** (DST 2016, §2.3, proof of Fact 1:
"`γ_min(ω') = γ_min(ω)` for any pre-image of `ω'` (since P1 guarantees that no edge of
`γ_min(ω')` was closed in the process)"): if `ω' ⊆ ω` and the minimal path of `ω` is still
`ω'`-open, it is the minimal path of `ω'`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
theorem minPath_eq_of_subset {ω ω' : BondConfig (slab 3 k)} (hω : ω' ⊆ ω) {S X Y : Set (slab 3 k)}
    (hS : S.Finite) (h : ∃ l, IsOSAP k ω S X Y l) (h' : IsOSAP k ω' S X Y (minPath k ω S X Y)) :
    minPath k ω' S X Y = minPath k ω S X Y :=
  minPath_eq_of_min hS h' fun l' hl' => (minPath_spec hS h).2 l' (hl'.mono hω)

end Paths

/-! ## The geometry and the events of the Gluing Lemma; the set `U(ω)` -/

section GlueEvents

/-- The geometric data of DST 2016, Lemma 6: the scale `n`, the radii `u₃ = u_{3n}` and
`u₁ = u_n` of `S_{3n} = B_{u_{3n}}` and `S_n = B_{u_n}`, the height `α = α_n`, and the vertical
offset `y = y_{3n}` (p. 5). [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5, the sets B'_n, S'_n, Y_n^±, Z_n)] -/
structure GlueGeom where
  /-- the scale -/
  n : ℕ
  /-- the radius of `S_{3n} = B_{u_{3n}}` -/
  u₃ : ℕ
  /-- the radius of `S_n = B_{u_n}` -/
  u₁ : ℕ
  /-- `α_n` -/
  α : ℕ
  /-- `y = y_{3n}` -/
  y : ℤ

namespace GlueGeom

variable (G : GlueGeom)

/-- The range of the construction of §2.1: `n ≥ 2`, `u_{3n} ≤ n`, `3 u_n ≤ n`, `1 ≤ α_n ≤ n - 1`, `0 ≤
 y_{3n} ≤ 3n`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 6]
-/
def InRange (G : GlueGeom) : Prop :=
  2 ≤ G.n ∧ G.u₃ ≤ G.n ∧ 3 * G.u₁ ≤ G.n ∧ 1 ≤ G.α ∧ G.α + 1 ≤ G.n ∧ 0 ≤ G.y ∧ G.y ≤ 3 * G.n

/-- `B_{3n}`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def big : Set (ℤ × ℤ) := sqBox 0 (3 * G.n)
/-- `B'_n = (2n, y) + B_n`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def small : Set (ℤ × ℤ) := sqBox (2 * (G.n : ℤ), G.y) G.n
/-- `S_{3n} = B_{u_{3n}}`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def src : Set (ℤ × ℤ) := sqBox 0 G.u₃
/-- `S'_n = (2n, y) + B_{u_n}`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def src' : Set (ℤ × ℤ) := sqBox (2 * (G.n : ℤ), G.y) G.u₁
/-- `Z_n = {3n} × [y - α, y + α]`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def zSeg : Set (ℤ × ℤ) := sideSeg (3 * G.n) (G.y - G.α) (G.y + G.α)
/-- `Y_n^- = {3n} × [y - n, y - α]`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def ym : Set (ℤ × ℤ) := sideSeg (3 * G.n) (G.y - G.n) (G.y - G.α)
/-- `Y_n^+ = {3n} × [y + α, y + n]`. [cite: DuminilCopinSidoraviciusTassion2016, §2.1 (p. 5)] -/
def yp : Set (ℤ × ℤ) := sideSeg (3 * G.n) (G.y + G.α) (G.y + G.n)

variable (k : ℕ)

/-- `{S_{3n} ⟷^{B_{3n}} Z_n}`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 6] -/
def evA : Set (BondConfig (slab 3 k)) := slabConn k G.big G.src G.zSeg
/-- `{S'_n ⟷^{B'_n} Y_n^-}`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 6] -/
def evBm : Set (BondConfig (slab 3 k)) := slabConn k G.small G.src' G.ym
/-- `{S'_n ⟷^{B'_n} Y_n^+}`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 6] -/
def evBp : Set (BondConfig (slab 3 k)) := slabConn k G.small G.src' G.yp
/-- `{S_{3n} ⟷^{B_{3n} ∪ B'_n} S'_n}`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 6] -/
def evC : Set (BondConfig (slab 3 k)) := slabConn k (G.big ∪ G.small) G.src G.src'
/-- `𝒳 = {S_{3n} ⟷^{B_{3n}} Z_n, S'_n ⟷^{B'_n} Y_n^-, S'_n ⟷^{B'_n} Y_n^+} ∩ {S_{3n} ⟷^{B_{3n} ∪ B'_n} S'_n}ᶜ`
(DST 2016, §2.3, p. 6). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (p. 6, the event 𝒳)] -/
def evX : Set (BondConfig (slab 3 k)) := G.evA k ∩ G.evBm k ∩ G.evBp k ∩ (G.evC k)ᶜ

/-- `γ_min(ω)`: the minimal open self-avoiding path from `S̄_{3n}` to `Z̄_n` inside `B̄_{3n}`
(DST 2016, §2.3, Definition). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Definition of γ_min)] -/
def γmin (ω : BondConfig (slab 3 k)) : List (slab 3 k) :=
  minPath k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg)

/-- The columns of `γ_min(ω)`: the projection of `γ_min(ω)` onto `ℤ²`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (P1, P2)] -/
def γcols (ω : BondConfig (slab 3 k)) : Set (ℤ × ℤ) := {z | ∃ x ∈ G.γmin k ω, planar k x = z}

/-- **The set `U(ω)`** (DST 2016, §2.3, Definition, p. 6): the points `z` of `B'_n` such that
(P1) `\overline{\{z\}} ∩ γ_min(ω) ≠ ∅`, and (P2) `\overline{z + B_1}` is connected to `S̄'_n` by
an open path `π` such that the (sup-norm) distance between the projections of `π` and `γ_min`
onto `ℤ²` is exactly `1` — here: `π` runs inside `B̄'_n`, starts over `z + B_1`, and all its
vertices project off the columns of `γ_min` (given (P1), the distance at the start is then
exactly `1`). The restriction of `π` to `B̄'_n` is implicit in the use made of (P2) in the proofs
of Facts 1–2 (paths from `S̄'_n` inside `B̄'_n`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Definition of U(ω), p. 6)] -/
def U (ω : BondConfig (slab 3 k)) : Set (ℤ × ℤ) :=
  {z | z ∈ G.small ∧ z ∈ G.γcols k ω ∧
    ∃ x₀ : slab 3 k, planar k x₀ ∈ sqBox z 1 ∧ ∃ s' ∈ slabLift k G.src',
      ω ∈ openConnIn (slabLift k G.small ∩ {v | planar k v ∉ G.γcols k ω}) x₀ s'}

/-- `U(ω)` lies in the (finite) set of columns of `γ_min(ω)`. [folklore] -/
theorem U_subset_γcols (ω : BondConfig (slab 3 k)) : G.U k ω ⊆ G.γcols k ω := fun _ h => h.2.1

/-- The columns of `γ_min` form a finite set. [folklore] -/
theorem γcols_finite (ω : BondConfig (slab 3 k)) : (G.γcols k ω).Finite := by
  have : G.γcols k ω = (planar k) '' {x | x ∈ G.γmin k ω} := by
    ext z; simp [γcols]
  rw [this]
  exact (List.finite_toSet _).image _

/-- `U(ω)` is finite. [folklore] -/
theorem U_finite (ω : BondConfig (slab 3 k)) : (G.U k ω).Finite :=
  (G.γcols_finite k ω).subset (G.U_subset_γcols k ω)

end GlueGeom

end GlueEvents

/-! ## Facts 1 and 2 of DST 2016, §2.3, and Lemma 6 from them -/

section Facts

open GlueGeom

/-- — **DST 2016, §2.3, Fact 1** (p. 6): "Fix `ε > 0` and `t > 0`. There exists `δ
 > 0` so that `P[S'_n ⟷^{B'_n} Y_n^-, S'_n ⟷^{B'_n} Y_n^+] > 1 - δ` implies `P[𝒳 ∩ {|U| < t}] ≤ ε`",
 in the quantitative form established by its proof: `P[𝒳 ∩ {|U| < t}] ≤ (2 / min{p, 1-p})^{s(t)} ·
 P[{S'_n ⟷^{B'_n} Y_n^-, S'_n ⟷^{B'_n} Y_n^+}ᶜ]` (Lemma 7 applied to the single-valued map closing
 the edges at the columns of `U(ω)` whose other endpoint is joined to `S̄'_n`). The printed exponent
 is `6kt`; a column of `S_k` has `k + 1` vertices and at most `5k + 4` incident edges, so the
 exponent is rendered as `(5k + 4)·t` (this only changes the constant). Users take `(h :
 DuminilCopinSidoraviciusTassion2016_fact1)`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Fact
 1, p. 6)]
-/
def DuminilCopinSidoraviciusTassion2016_fact1 : Prop :=
  ∀ k : ℕ, 0 < k → ∀ p : unitInterval, 0 < (p : ℝ) → (p : ℝ) < 1 →
    ∀ G : GlueGeom, G.InRange → ∀ t : ℕ,
      (bondPercolation (slabGraph 3 k) p).real (G.evX k ∩ {ω | (G.U k ω).ncard < t}) ≤
        (2 / min (p : ℝ) (1 - p)) ^ ((5 * k + 4) * t) *
          (bondPercolation (slabGraph 3 k) p).real (G.evBm k ∩ G.evBp k)ᶜ

variable (k : ℕ)

/-- The event `𝒳` splits along `|U| < t` / `|U| ≥ t`. [folklore] -/
theorem real_evX_le (G : GlueGeom) (p : unitInterval) (t : ℕ) :
    (bondPercolation (slabGraph 3 k) p).real (G.evX k) ≤
      (bondPercolation (slabGraph 3 k) p).real (G.evX k ∩ {ω | (G.U k ω).ncard < t}) +
        (bondPercolation (slabGraph 3 k) p).real (G.evX k ∩ {ω | t ≤ (G.U k ω).ncard}) := by
  have : G.evX k ⊆ (G.evX k ∩ {ω | (G.U k ω).ncard < t}) ∪ (G.evX k ∩ {ω | t ≤ (G.U k ω).ncard}) := by
    intro ω hω
    by_cases h : (G.U k ω).ncard < t
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr ⟨hω, not_lt.1 h⟩
  exact (measureReal_mono this).trans (measureReal_union_le _ _)

/-- `{A, B⁻, B⁺} ⊆ C ∪ 𝒳`. [folklore] -/
theorem real_triple_le (G : GlueGeom) (p : unitInterval) :
    (bondPercolation (slabGraph 3 k) p).real (G.evA k ∩ G.evBm k ∩ G.evBp k) ≤
      (bondPercolation (slabGraph 3 k) p).real (G.evC k) +
        (bondPercolation (slabGraph 3 k) p).real (G.evX k) := by
  have : G.evA k ∩ G.evBm k ∩ G.evBp k ⊆ G.evC k ∪ G.evX k := by
    intro ω hω
    by_cases hC : ω ∈ G.evC k
    · exact Or.inl hC
    · exact Or.inr ⟨hω, hC⟩
  exact (measureReal_mono this).trans (measureReal_union_le _ _)

/-- The events `B^±` are measurable. [folklore] -/
theorem measurableSet_evBm_inter_evBp (G : GlueGeom) : MeasurableSet (G.evBm k ∩ G.evBp k) :=
  (measurableSet_slabConn_of_finite k (sqBox_finite _ _) _ _).inter
    (measurableSet_slabConn_of_finite k (sqBox_finite _ _) _ _)

/-- In the full configuration, `S_{3n} ⟷^{B_{3n} ∪ B'_n} S'_n` holds (a lattice path along the
axis and up the column `x = 2n`). [folklore] -/
theorem edgeSet_mem_evC (G : GlueGeom) (hG : G.InRange) : (slabGraph 3 k).edgeSet ∈ G.evC k := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  refine ⟨baseVertex k 0, by simp [GlueGeom.src, sqBox], baseVertex k (2 * (G.n : ℤ), G.y),
    by simp [GlueGeom.src', sqBox], ?_⟩
  have hT : sqBox (0 : ℤ × ℤ) (3 * G.n) ⊆ G.big ∪ G.small := fun z hz => Or.inl hz
  refine openConnIn_mono (slabLift_mono k hT) _ _ ?_
  have h1 := edgeSet_openConnIn_horizontal k (T := sqBox (0 : ℤ × ℤ) (3 * G.n)) 0 0 (2 * G.n)
    (fun j hj => by
      simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]
      push_cast; omega)
  have h2 := edgeSet_openConnIn_vertical k (T := sqBox (0 : ℤ × ℤ) (3 * G.n)) (2 * G.n) 0 G.y.toNat
    (fun j hj => by
      simp only [sqBox, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]
      push_cast; omega)
  have e1 : ((0 : ℤ) + ((2 * G.n : ℕ) : ℤ), (0 : ℤ)) = (2 * (G.n : ℤ), 0) := by push_cast; ring_nf
  have e3 : ((2 * (G.n : ℤ)), (0 : ℤ) + (G.y.toNat : ℤ)) = (2 * (G.n : ℤ), G.y) := by
    rw [Int.toNat_of_nonneg hy0]; simp
  rw [e1] at h1
  rw [e3] at h2
  exact SlabCriticality.openConnIn_trans h1 h2

end Facts

end Percolation.Literature
