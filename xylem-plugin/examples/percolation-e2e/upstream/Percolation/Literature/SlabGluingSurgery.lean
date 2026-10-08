import Percolation.Literature.SlabGluingFact1
import Percolation.Util.Linter

/-!
# DST 2016, §2.3 — towards Fact 2: stability of the minimal path under a local surgery

A generic **exchange lemma** for the lexicographically
minimal open self-avoiding path `minPath` of `SlabGluing.lean` (Duminil-Copin–Sidoravicius–Tassion
2016, §2.3): if a configuration `ω'` is obtained from `ω` by adding a set `Enew` of "structure"
edges (a branch attached to `γ = γ_min(ω)` plus possibly outer vertices) and deleting arbitrary
other edges, in such a way that

* `γ` stays open (`h1`);
* every new edge joins two structure vertices (`Sw ∪ γ`), never two vertices of `γ`, and a new
  edge at a vertex of `γ` leads into the protected set `Wv ⊆ Sw` (`h8`);
* protected vertices can only be entered from structure vertices (`h2`: all other edges at them
  are closed in `ω'`);
* unprotected structure vertices off `γ` are not `ω`-joined inside `S` to the source set `X`
  (`h4`; in DST's setting they are joined to `S̄'_n`, and the configuration is not in `C_n`);
* protected vertices in the source set lie on `γ` or have key at least that of `γ_0` (`h5`);
* FORWARD-BRANCH CONDITION (`h6`, DST's "`(z,v) ≺ (z,w)`"): a new edge leaving `γ` at `γ_j`
  towards a structure vertex off `γ` leads to a key larger than that of `γ_{j+1}`,

then `γ_min(ω') = γ_min(ω)`. This is the step "the minimality of `γ_min(ω)` … implies …" of DST
2016, p. 7 (and of Newman–Tassion–Wu 2017, proof of Thm. 3.9), in the variant where `γ_min(ω)`
itself is kept and only a branch is attached; the proof is the exchange argument: a competitor first
differing from `γ` at index `i` is followed to its first structure vertex and spliced into `γ`,
producing an `ω`-open self-avoiding path smaller than `γ`. The form needed for DST's own surgery (a
prefix `pfx` of `γ` is kept and continued by a rerouted piece `P` along which every other edge is
closed or leads to a larger key) is `minPath_prefix_of_surgery`: the minimal path of `ω'` is `pfx ++
P ++ tail` for some `tail` ("`γ_min(ω^{(z)})` and `γ_min(ω)` coincide at least until `u'` … it must
contain `z`"); nothing is claimed about `tail`. Also: the first-difference decomposition of the path
order (`pathKey_lt_decomp`), the comparison lemmas `pathKey_lt_append`, `pathKey_append_cons_lt`,
and `minPath_prefix_getLast_not_mem` (the minimal path meets `Y` only at its end).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, CPAM 69 (2016), arXiv:1401.7130, §2.3, proof of Fact 2 (p. 7).
* C. M. Newman, V. Tassion, W. Wu, *Critical percolation and the minimal spanning tree in slabs*,
  CPAM 70 (2017), §3.2 (vertex-lexicographic order), proof of Thm. 3.9.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Percolation.Literature

open LatticeModels

/-! ## First-difference decomposition of the lexicographic order on lists -/

section Lex

/-- If `l₁ < l₂` lexicographically then either `l₁` is a proper prefix of `l₂` or the two lists
agree up to a first position where `l₁` carries the smaller letter. [folklore] -/
theorem lt_decomp {K : Type*} [LinearOrder K] :
    ∀ l₁ l₂ : List K, l₁ < l₂ →
      (∃ s : List K, s ≠ [] ∧ l₂ = l₁ ++ s) ∨
        ∃ (p : List K) (a : K) (t₁ : List K) (b : K) (t₂ : List K),
          l₁ = p ++ a :: t₁ ∧ l₂ = p ++ b :: t₂ ∧ a < b
  | [], [], h => absurd h (lt_irrefl _)
  | [], b :: t, _ => Or.inl ⟨b :: t, List.cons_ne_nil _ _, rfl⟩
  | _ :: _, [], h => absurd h (List.not_lt_nil _)
  | a :: t₁, b :: t₂, h => by
    rcases List.cons_lt_cons_iff.1 h with hab | ⟨rfl, ht⟩
    · exact Or.inr ⟨[], a, t₁, b, t₂, rfl, rfl, hab⟩
    · rcases lt_decomp t₁ t₂ ht with ⟨s, hs, rfl⟩ | ⟨p, a', u₁, b', u₂, rfl, rfl, hab⟩
      · exact Or.inl ⟨s, hs, rfl⟩
      · exact Or.inr ⟨a :: p, a', u₁, b', u₂, rfl, rfl, hab⟩

variable {k : ℕ}

/-- First-difference decomposition for path keys (`pathKey` compares the vertex keys `vKey`
lexicographically, a proper prefix being smaller; NTW 2017, §3.2). [folklore] -/
theorem pathKey_lt_decomp {l₁ l₂ : List (slab 3 k)} (h : pathKey k l₁ < pathKey k l₂) :
    (∃ s : List (slab 3 k), s ≠ [] ∧ l₂ = l₁ ++ s) ∨
      ∃ (p : List (slab 3 k)) (a : slab 3 k) (t₁ : List (slab 3 k)) (b : slab 3 k)
        (t₂ : List (slab 3 k)), l₁ = p ++ a :: t₁ ∧ l₂ = p ++ b :: t₂ ∧ vKey k a < vKey k b := by
  rcases lt_decomp _ _ h with ⟨s, hs, hs'⟩ | ⟨p, a, t₁, b, t₂, h₁, h₂, hab⟩
  · rw [pathKey, pathKey, List.map_eq_append_iff] at hs'
    obtain ⟨m₁, m₂, rfl, hm₁, hm₂⟩ := hs'
    obtain rfl : m₁ = l₁ := pathKey_injective hm₁
    refine Or.inl ⟨m₂, ?_, rfl⟩
    rintro rfl
    exact hs (by simpa using hm₂.symm)
  · rw [pathKey, List.map_eq_append_iff] at h₁ h₂
    obtain ⟨p₁, q₁, rfl, hp₁, hq₁⟩ := h₁
    obtain ⟨p₂, q₂, rfl, hp₂, hq₂⟩ := h₂
    rw [List.map_eq_cons_iff] at hq₁ hq₂
    obtain ⟨a', t₁', rfl, rfl, -⟩ := hq₁
    obtain ⟨b', t₂', rfl, rfl, -⟩ := hq₂
    obtain rfl : p₁ = p₂ := pathKey_injective (hp₁.trans hp₂.symm)
    exact Or.inr ⟨p₁, a', t₁', b', t₂', rfl, rfl, hab⟩

/-- A proper prefix has a smaller key. [folklore] -/
theorem pathKey_lt_append {l s : List (slab 3 k)} (hs : s ≠ []) :
    pathKey k l < pathKey k (l ++ s) := by
  simp only [pathKey, List.map_append]
  have hs' : s.map (vKey k) ≠ [] := by simpa using hs
  generalize s.map (vKey k) = M at hs'
  generalize l.map (vKey k) = L
  induction L with
  | nil =>
    cases M with
    | nil => exact absurd rfl hs'
    | cons x xs => exact List.Lex.nil
  | cons x xs ih => exact List.Lex.cons ih

/-- Keys are decided at the first difference. [folklore] -/
theorem pathKey_append_cons_lt {p t₁ t₂ : List (slab 3 k)} {a b : slab 3 k}
    (hab : vKey k a < vKey k b) : pathKey k (p ++ a :: t₁) < pathKey k (p ++ b :: t₂) := by
  simp only [pathKey, List.map_append, List.map_cons]
  generalize p.map (vKey k) = P
  induction P with
  | nil => exact List.Lex.rel hab
  | cons x xs ih => exact List.Lex.cons ih

end Lex

/-! ## The exchange lemma -/

section Surgery

variable {k : ℕ}

/-- The minimal path meets the target set `Y` only at its last vertex: no proper prefix of it ends
in `Y`. [folklore] -/
theorem minPath_prefix_getLast_not_mem {ω : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)}
    (hS : S.Finite) (hex : ∃ l, IsOSAP k ω S X Y l) {p s : List (slab 3 k)}
    (hps : minPath k ω S X Y = p ++ s) (hs : s ≠ []) (hp : p ≠ []) : p.getLast hp ∉ Y := by
  intro hY
  obtain ⟨hγO, hmin⟩ := minPath_spec hS hex
  have hpO : IsOSAP k ω S X Y p := by
    refine ⟨?_, ?_, ?_, hp, ?_, fun _ => hY⟩
    · exact (hps ▸ hγO.nodup).sublist (List.sublist_append_left p s)
    · exact (List.isChain_append.1 (hps ▸ hγO.chain)).1
    · exact fun x hx => hγO.subset x (by rw [hps]; exact List.mem_append_left _ hx)
    · intro hne
      obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
      have := hγO.head_mem hγO.ne_nil
      have h0 : (minPath k ω S X Y).head hγO.ne_nil = y := by
        simp only [hps, List.cons_append, List.head_cons]
      rw [h0] at this
      exact this
  have := hmin p hpO
  rw [hps] at this
  exact absurd (pathKey_lt_append (l := p) hs) (not_lt.2 this)

/-- **the minimal path is forced through a rerouted prefix** (the form of the exchange
argument needed for DST's ball surgery, DST 2016, §2.3, proof of Fact 2, p. 7: "`γ_min(ω^{(z)})`
and `γ_min(ω)` coincide at least until `u'` … the fact that `γ_min(ω^{(z)})` contains `u'` forces
it to go inside `\overline{B_R(z)}` … it must contain `z`"). Setting: `γ = minPath ω S X Y =
pfx ++ rest` with `pfx, rest ≠ []`; the new configuration `ω' ⊆ ω ∪ Enew` carries an open
self-avoiding path `pfx ++ P ++ sfx` from `X` to `Y` in `S`; `Sw` = structure vertices (both ends
of every new edge; no vertex of `pfx` except possibly its last), `Wv ⊆ Sw` = protected vertices.
Hypotheses: `ω'`-open edges into protected vertices off `γ` start at structure vertices (`h2`);
unprotected structure vertices off `γ` are not `ω`-joined in `S` to `X` (`h4`); protected
vertices of `X` lie on `γ` or have key `≥ key γ_0` (`h5`); FORCING (`h6`): at the last vertex
of `pfx` and at every vertex of `P` but the last, any `ω'`-open edge other than the path's next
edge leads back into the path or to a larger key (this contains DST's `(z,v) ≺ (z,w)`); no vertex
of `P` but the last lies in `Y` (`h9`). Conclusion: `minPath ω' S X Y = pfx ++ P ++ tail` for
some `tail` — the minimal path of `ω'` runs through the rerouted piece (nothing is claimed about
its continuation).
[cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (p. 7)] -/
theorem minPath_prefix_of_surgery {ω ω' : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)}
    (hS : S.Finite) (hex : ∃ l, IsOSAP k ω S X Y l)
    (pfx rest P sfx : List (slab 3 k)) (hγ : minPath k ω S X Y = pfx ++ rest)
    (hpfxne : pfx ≠ []) (hrest : rest ≠ [])
    (hT : IsOSAP k ω' S X Y (pfx ++ P ++ sfx))
    (Enew : Set (Sym2 (slab 3 k))) (Wv Sw : Set (slab 3 k))
    (h3 : ω' ⊆ ω ∪ Enew) (hEnew : ∀ a b, s(a, b) ∈ Enew → a ∈ Sw ∧ b ∈ Sw)
    (hpfx : ∀ x ∈ pfx.dropLast, x ∉ Sw)
    (h2 : ∀ q x, s(q, x) ∈ ω' → x ∈ Wv → x ∉ minPath k ω S X Y → q ∈ Sw)
    (h4 : ∀ q ∈ Sw, q ∉ Wv → q ∉ minPath k ω S X Y → ∀ x ∈ X, ω ∉ openConnIn S x q)
    (h5 : ∀ v ∈ Wv, v ∈ X → v ∈ minPath k ω S X Y ∨
      ∀ b ∈ (minPath k ω S X Y).head?, vKey k b ≤ vKey k v)
    (h6 : ∀ (p₁ : List (slab 3 k)) (x y : slab 3 k) (r : List (slab 3 k)),
      pfx ++ P = p₁ ++ x :: y :: r → pfx.length ≤ p₁.length + 1 →
        ∀ q, s(x, q) ∈ ω' → q ≠ y → q ∈ p₁ ∨ vKey k y < vKey k q)
    (h9 : ∀ x ∈ P.dropLast, x ∉ Y) :
    ∃ tail, minPath k ω' S X Y = pfx ++ P ++ tail := by
  obtain ⟨hγO, hmin⟩ := minPath_spec hS hex
  obtain ⟨hμO, hμmin⟩ := minPath_spec (X := X) (Y := Y) hS ⟨_, hT⟩
  have hlastpfx : pfx.getLast hpfxne ∉ Y := minPath_prefix_getLast_not_mem hS hex hγ hrest hpfxne
  set γ := minPath k ω S X Y with hγdef
  set μ := minPath k ω' S X Y with hμdef
  -- edges of `ω'` with an endpoint off the structure are `ω`-edges
  have hE : ∀ c d, s(c, d) ∈ ω' → c ∉ Sw → s(c, d) ∈ ω := by
    intro c d hcd hc
    rcases h3 hcd with h | h
    · exact h
    · exact absurd (hEnew c d h).1 hc
  have hE' : ∀ c d, s(c, d) ∈ ω' → d ∉ Sw → s(c, d) ∈ ω := by
    intro c d hcd hd
    rw [Sym2.eq_swap] at hcd ⊢
    exact hE d c hcd hd
  have hle : pathKey k μ ≤ pathKey k (pfx ++ P ++ sfx) := hμmin _ hT
  rcases hle.lt_or_eq with hlt | heq
  swap
  · exact ⟨sfx, pathKey_injective heq⟩
  rcases pathKey_lt_decomp hlt with ⟨s, hs, hTeq⟩ | ⟨p, a, t₁, b, t₂, hμeq, hTeq, hab⟩
  · -- `μ` is a proper prefix of `pfx ++ P ++ sfx`
    rcases List.append_eq_append_iff.1 hTeq with ⟨a', hμ', -⟩ | ⟨c', hPc, -⟩
    · exact ⟨a', hμ'⟩
    · -- `pfx ++ P = μ ++ c'`
      rcases List.append_eq_append_iff.1 hPc with ⟨a'', hμ'', hP⟩ | ⟨c'', hpfx', -⟩
      · -- `μ = pfx ++ a''`, `P = a'' ++ c'`
        by_cases hc' : c' = []
        · subst hc'
          refine ⟨[], hμ''.trans ?_⟩
          rw [List.append_nil, hP, List.append_nil]
        exfalso
        have hlast := hμO.last_mem hμO.ne_nil
        by_cases ha'' : a'' = []
        · subst ha''
          rw [List.append_nil] at hμ''
          have : μ.getLast hμO.ne_nil = pfx.getLast hpfxne := List.getLast_congr _ _ hμ''
          rw [this] at hlast
          exact hlastpfx hlast
        · have : μ.getLast hμO.ne_nil = a''.getLast ha'' := by
            rw [List.getLast_congr _ (by simp [ha'']) hμ'']
            exact List.getLast_append_of_ne_nil _ ha''
          rw [this] at hlast
          refine h9 _ ?_ hlast
          rw [hP, List.dropLast_append_of_ne_nil hc']
          exact List.mem_append_left _ (List.getLast_mem ha'')
      · -- `pfx = μ ++ c''`: `μ` is a proper prefix of `γ`
        exfalso
        have hγμ : γ = μ ++ (c'' ++ rest) := by rw [hγ, hpfx', List.append_assoc]
        have hμω : IsOSAP k ω S X Y μ := by
          refine ⟨hμO.nodup, ?_, hμO.subset, hμO.ne_nil, hμO.head_mem, hμO.last_mem⟩
          have := hγO.chain
          rw [hγμ] at this
          exact (List.isChain_append.1 this).1
        have := hmin μ hμω
        rw [hγμ] at this
        exact absurd (pathKey_lt_append (l := μ) (by simp [hrest])) (not_lt.2 this)
  -- main case: `μ = p ++ a :: t₁`, `pfx ++ P ++ sfx = p ++ b :: t₂`, `key a < key b`
  have hab' : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  have hμnd : (p ++ a :: t₁).Nodup := hμeq ▸ hμO.nodup
  have hμch : (p ++ a :: t₁).IsChain (fun a b => s(a, b) ∈ ω' ∧ a ≠ b) := hμeq ▸ hμO.chain
  have hnotp : ∀ x ∈ a :: t₁, x ∉ p := by
    intro x hx hxp
    exact (List.nodup_append.1 hμnd).2.2 x hxp x hx rfl
  -- the junction edge, from the chain of `μ`
  have hJ0 : ∀ c, p.getLast? = some c → s(c, a) ∈ ω' ∧ c ≠ a := fun c hc =>
    (List.isChain_append.1 hμch).2.2 c (by simp [hc]) a (by simp)
  rcases List.append_eq_append_iff.1 hTeq with ⟨a', hp, -⟩ | ⟨c', hPc, hbt⟩
  · -- `p = pfx ++ P ++ a'`: the two paths agree beyond `pfx ++ P`
    exact ⟨a' ++ a :: t₁, hμeq.trans (by rw [hp]; simp)⟩
  by_cases hc'nil : c' = []
  · subst hc'nil
    rw [List.append_nil] at hPc
    exact ⟨a :: t₁, hμeq.trans (by rw [← hPc])⟩
  obtain ⟨c'', rfl⟩ : ∃ c'', c' = b :: c'' := by
    cases c' with
    | nil => exact absurd rfl hc'nil
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at hbt
      exact ⟨xs, by rw [hbt.1]⟩
  -- now `pfx ++ P = p ++ b :: c''`
  rcases List.append_eq_append_iff.1 hPc with ⟨a'', hp, hP⟩ | ⟨c₃, hpfx', hbc⟩
  · -- FORCING case: the junction `x = (pfx ++ a'').getLast` is `u'` or a vertex of `P`
    exfalso
    have hne : pfx ++ a'' ≠ [] := by simp [hpfxne]
    set x := (pfx ++ a'').getLast hne with hx
    have hdecomp : pfx ++ P = (pfx ++ a'').dropLast ++ x :: b :: c'' := by
      rw [hP, ← List.append_assoc]
      conv_lhs => rw [← List.dropLast_append_getLast hne]
      rw [List.append_assoc, List.singleton_append]
    have hlen : pfx.length ≤ (pfx ++ a'').dropLast.length + 1 := by
      rw [List.length_dropLast, List.length_append]
      have : 1 ≤ pfx.length := List.length_pos_iff.2 hpfxne
      omega
    have hxlast : p.getLast? = some x := by
      rw [hp, List.getLast?_eq_some_getLast hne]
    obtain ⟨hxa, -⟩ := hJ0 x hxlast
    rcases h6 _ x b c'' hdecomp hlen a hxa hab' with h | h
    · -- `a` already lies on the common part `p`
      refine hnotp a (by simp) ?_
      rw [hp]
      exact List.mem_of_mem_dropLast h
    · exact absurd hab (not_lt.2 h.le)
  -- EXCHANGE case: `pfx = p ++ c₃`, `b :: c'' = c₃ ++ P`
  by_cases hc₃ : c₃ = []
  · -- then `p = pfx` and the junction is `u'`: forcing again
    exfalso
    subst hc₃
    rw [List.append_nil] at hpfx'
    rw [List.nil_append] at hbc
    -- hpfx' : pfx = p ; hbc : b :: c'' = P
    have hdecomp : pfx ++ P = pfx.dropLast ++ pfx.getLast hpfxne :: b :: c'' := by
      rw [← hbc]
      conv_lhs => rw [← List.dropLast_append_getLast hpfxne]
      rw [List.append_assoc, List.singleton_append]
    have hlen : pfx.length ≤ pfx.dropLast.length + 1 := by
      rw [List.length_dropLast]; omega
    have hxlast : p.getLast? = some (pfx.getLast hpfxne) := by
      rw [← hpfx', List.getLast?_eq_some_getLast]
    obtain ⟨hxa, -⟩ := hJ0 _ hxlast
    rcases h6 _ _ b c'' hdecomp hlen a hxa hab' with h | h
    · refine hnotp a (by simp) ?_
      rw [← hpfx']
      exact List.mem_of_mem_dropLast h
    · exact absurd hab (not_lt.2 h.le)
  obtain ⟨c₄, rfl⟩ : ∃ c₄, c₃ = b :: c₄ := by
    cases c₃ with
    | nil => exact absurd rfl hc₃
    | cons x xs =>
      simp only [List.cons_append, List.cons.injEq] at hbc
      exact ⟨xs, by rw [hbc.1]⟩
  -- `γ = p ++ b :: t₂'` with `t₂' = c₄ ++ rest`, and `p ⊆ pfx.dropLast` is off the structure
  set t₂' := c₄ ++ rest with ht₂'
  have hγeq : γ = p ++ b :: t₂' := by rw [hγ, hpfx', List.append_assoc, List.cons_append]
  have hpSw : ∀ x ∈ p, x ∉ Sw := by
    intro x hx
    apply hpfx
    rw [hpfx', List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
    exact List.mem_append_left _ hx
  have hpγ : ∀ x ∈ p, x ∈ γ := fun x hx => by rw [hγeq]; exact List.mem_append_left _ hx
  have hγnd : (p ++ b :: t₂').Nodup := hγeq ▸ hγO.nodup
  have hγch : (p ++ b :: t₂').IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) := hγeq ▸ hγO.chain
  have hpch : p.IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) := (List.isChain_append.1 hγch).1
  have hJ : ∀ c, p.getLast? = some c → (s(c, a) ∈ ω ∧ c ≠ a) ∧ c ∈ γ := by
    intro c hc
    have hcp : c ∈ p := List.mem_of_getLast? hc
    obtain ⟨hca, hne⟩ := hJ0 c hc
    exact ⟨⟨hE c a hca (hpSw c hcp), hne⟩, hpγ c hcp⟩
  have haμ : a ∈ μ := by rw [hμeq]; simp
  have haX : p = [] → a ∈ X := by
    rintro rfl
    have := hμO.head_mem hμO.ne_nil
    simp only [hμeq, List.nil_append, List.head_cons] at this
    exact this
  have hγ0X : γ.head hγO.ne_nil ∈ X := hγO.head_mem hγO.ne_nil
  have hγ0X' : ∀ (L : List (slab 3 k)) (hL : γ = L) (hne : L ≠ []), L.head hne ∈ X := by
    rintro L rfl hne
    exact hγO.head_mem hne
  -- `X ∋ x₀ ~ a` inside `S` by `ω`-open edges
  have hXa : ∃ x₀ ∈ X, ω ∈ openConnIn S x₀ a := by
    cases hp : p.getLast? with
    | none =>
      rw [List.getLast?_eq_none_iff] at hp
      refine ⟨a, haX hp, ?_⟩
      rw [mem_openConnIn_iff_pathIn]
      exact PathIn.refl (hμO.subset a haμ)
    | some c =>
      obtain ⟨⟨hca, hne⟩, hcγ⟩ := hJ c hp
      refine ⟨γ.head hγO.ne_nil, hγ0X,
        SlabCriticality.openConnIn_trans (hγO.openConnIn_of_mem (k := k) hcγ) ?_⟩
      have hcS : c ∈ S := hγO.subset _ hcγ
      have haS : a ∈ S := hμO.subset a haμ
      exact openConnIn_head_of_mem c [a]
        (List.isChain_cons_cons.2 ⟨⟨hca, hne⟩, List.isChain_singleton _⟩)
        (fun v hv => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact hcS
          · exact haS) a (by simp)
  -- Case analysis on whether `a :: t₁` meets the structure `γ ∪ Sw`.
  by_cases htouch : ∃ x ∈ a :: t₁, x ∈ γ ∨ x ∈ Sw
  swap
  · -- no touch: `μ` is `ω`-open, and smaller than `γ`
    push Not at htouch
    have hμω : IsOSAP k ω S X Y μ := by
      refine ⟨hμO.nodup, ?_, hμO.subset, hμO.ne_nil, hμO.head_mem, hμO.last_mem⟩
      rw [hμeq, List.isChain_append]
      refine ⟨hpch, ?_, ?_⟩
      · exact (List.isChain_append.1 hμch).2.1.imp_of_mem_imp fun x y hx _ hxy =>
          ⟨hE x y hxy.1 (htouch x hx).2, hxy.2⟩
      · intro c hc y hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact (hJ c hc).1
    have := hmin μ hμω
    rw [hγeq, hμeq] at this
    exact absurd (pathKey_append_cons_lt (p := p) (t₁ := t₁) (t₂ := t₂') hab) (not_lt.2 this)
  -- first touch `x`: `a :: t₁ = l₁ ++ x :: l₂`, `l₁` off the structure
  obtain ⟨l₁, x, l₂, hsplit, hxS1, hl₁⟩ := exists_first_split (a :: t₁) htouch
  have hl₁' : ∀ y ∈ l₁, y ∉ γ ∧ y ∉ Sw := fun y hy => not_or.1 (hl₁ y hy)
  have hxμ' : x ∈ a :: t₁ := by rw [hsplit]; simp
  have hhead : ∀ m : List (slab 3 k), (l₁ ++ x :: m).head (by simp) = a := by
    intro m
    have h0 : (l₁ ++ x :: l₂).head (by simp) = a := by
      have : (a :: t₁).head (List.cons_ne_nil _ _) = a := rfl
      simp only [hsplit] at this
      exact this
    cases l₁ with
    | nil => simpa using h0
    | cons y ys => simpa using h0
  have hcons : ∀ m : List (slab 3 k), ∃ rest', l₁ ++ x :: m = a :: rest' := by
    intro m
    cases hl : l₁ with
    | nil => exact ⟨m, by simpa [hl] using hhead m⟩
    | cons z zs =>
      have : z = a := by simpa [hl] using hhead m
      exact ⟨zs ++ x :: m, by simp [this]⟩
  have hμch2 : (l₁ ++ x :: l₂).IsChain (fun a b => s(a, b) ∈ ω' ∧ a ≠ b) := by
    have := (List.isChain_append.1 hμch).2.1
    rwa [hsplit] at this
  have hl₁ch : l₁.IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) :=
    (List.isChain_append.1 hμch2).1.imp_of_mem_imp fun u v hu _ huv =>
      ⟨hE u v huv.1 (hl₁' u hu).2, huv.2⟩
  have hlinkx' : ∀ u, l₁.getLast? = some u → s(u, x) ∈ ω' ∧ u ≠ x := fun u hu =>
    (List.isChain_append.1 hμch2).2.2 u (by rw [hu]; rfl) x (by simp)
  have hlinkx : ∀ u, l₁.getLast? = some u → s(u, x) ∈ ω ∧ u ≠ x := by
    intro u hu
    have hul₁ : u ∈ l₁ := List.mem_of_getLast? hu
    exact ⟨hE u x (hlinkx' u hu).1 (hl₁' u hul₁).2, (hlinkx' u hu).2⟩
  have hsegch : ∀ m : List (slab 3 k), (x :: m).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) →
      (l₁ ++ x :: m).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) := by
    intro m hm
    rw [List.isChain_append]
    refine ⟨hl₁ch, hm, fun u hu y hy => ?_⟩
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact hlinkx u hu
  have hl₁S : ∀ v ∈ l₁, v ∈ S := fun v hv =>
    hμO.subset v (by rw [hμeq, hsplit]; exact List.mem_append_right _ (List.mem_append_left _ hv))
  have hxS : x ∈ S := hμO.subset x (by rw [hμeq]; exact List.mem_append_right _ hxμ')
  have hax : ω ∈ openConnIn S a x := by
    obtain ⟨rest', hrest⟩ := hcons []
    have hch' : (a :: rest').IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) :=
      hrest ▸ hsegch [] (List.isChain_singleton _)
    have hS' : ∀ v ∈ a :: rest', v ∈ S := by
      intro v hv
      rw [← hrest] at hv
      rcases List.mem_append.1 hv with h | h
      · exact hl₁S v h
      · rw [List.mem_singleton] at h
        rw [h]
        exact hxS
    exact openConnIn_head_of_mem a rest' hch' hS' x (by rw [← hrest]; simp)
  by_cases hxγ : x ∈ γ
  · -- SPLICE
    have hxγ' : x ∈ b :: t₂' := by
      have := hxγ
      rw [hγeq, List.mem_append] at this
      exact this.resolve_left (hnotp x hxμ')
    obtain ⟨q, r, hqr⟩ := List.append_of_mem hxγ'
    have hxr_sub : ∀ v ∈ x :: r, v ∈ γ := fun v hv => by
      rw [hγeq, hqr]; exact List.mem_append_right _ (List.mem_append_right _ hv)
    have hxr : (x :: r).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) := by
      have := (List.isChain_append.1 hγch).2.1
      rw [hqr] at this
      exact (List.isChain_append.1 this).2.1
    obtain ⟨rest', hrest⟩ := hcons r
    have hsp : IsOSAP k ω S X Y (p ++ a :: rest') := by
      rw [← hrest]
      refine ⟨?_, ?_, ?_, by simp, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨(List.nodup_append.1 hγnd).1, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨?_, ?_, ?_⟩
          · have : (l₁ ++ x :: l₂).Nodup := hsplit ▸ (List.nodup_append.1 hμnd).2.1
            exact (List.nodup_append.1 this).1
          · have : (q ++ x :: r).Nodup := hqr ▸ (List.nodup_append.1 hγnd).2.1
            exact (List.nodup_append.1 this).2.1
          · intro u hu v hv huv
            subst huv
            exact (hl₁' u hu).1 (hxr_sub u hv)
        · intro u hu v hv huv
          subst huv
          rcases List.mem_append.1 hv with h | h
          · exact hnotp u (by rw [hsplit]; exact List.mem_append_left _ h) hu
          · have : (p ++ (q ++ x :: r)).Nodup := hqr ▸ hγnd
            exact (List.nodup_append.1 this).2.2 u hu u (List.mem_append_right _ h) rfl
      · rw [List.isChain_append]
        refine ⟨hpch, hsegch r hxr, ?_⟩
        intro c hc y hy
        rw [hrest] at hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact (hJ c hc).1
      · intro v hv
        rcases List.mem_append.1 hv with h | h
        · exact hγO.subset v (hpγ v h)
        · rcases List.mem_append.1 h with h' | h'
          · exact hl₁S v h'
          · exact hγO.subset v (hxr_sub v h')
      · intro hne
        by_cases hp : p = []
        · subst hp
          simp only [List.nil_append, hrest, List.head_cons]
          exact haX rfl
        · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hp
          have := hγ0X' _ hγeq (by simp)
          simp only [List.cons_append, List.head_cons] at this ⊢
          exact this
      · intro hne
        have h1 : (p ++ (l₁ ++ x :: r)).getLast hne = (x :: r).getLast (List.cons_ne_nil _ _) := by
          rw [List.getLast_append_of_ne_nil _ (by simp)]
          exact List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)
        have h2 : γ.getLast hγO.ne_nil = (x :: r).getLast (List.cons_ne_nil _ _) := by
          have : γ = (p ++ q) ++ x :: r := by rw [hγeq, hqr, List.append_assoc]
          rw [List.getLast_congr _ (by simp) this]
          exact List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)
        rw [h1, ← h2]
        exact hγO.last_mem hγO.ne_nil
    have hkey : pathKey k (p ++ a :: rest') < pathKey k γ := by
      rw [hγeq]
      exact pathKey_append_cons_lt hab
    exact absurd (hmin _ hsp) (not_le.2 hkey)
  · exfalso
    have hxSw : x ∈ Sw := hxS1.resolve_left hxγ
    by_cases hxW : x ∈ Wv
    · -- entering a protected vertex from off the structure: impossible by `h2`
      cases hl : l₁.getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff] at hl
        have hxa : x = a := by simpa [hl] using hhead l₂
        subst hxa
        -- the predecessor is the junction `c ∈ p` (off the structure) or nothing (`x ∈ X`)
        cases hp : p.getLast? with
        | none =>
          rw [List.getLast?_eq_none_iff] at hp
          rcases h5 x hxW (haX hp) with h | h
          · exact hxγ h
          · subst hp
            have hb : b ∈ γ.head? := by simp [hγeq]
            exact absurd hab (not_lt.2 (h b hb))
        | some c =>
          exact hpSw c (List.mem_of_getLast? hp) (h2 c x (hJ0 c hp).1 hxW hxγ)
      | some u =>
        have hul₁ : u ∈ l₁ := List.mem_of_getLast? hl
        exact (hl₁' u hul₁).2 (h2 u x (hlinkx' u hl).1 hxW hxγ)
    · obtain ⟨x₀, hx₀X, hx₀⟩ := hXa
      exact h4 x hxSw hxW hxγ x₀ hx₀X (SlabCriticality.openConnIn_trans hx₀ hax)

end Surgery

end Percolation.Literature
