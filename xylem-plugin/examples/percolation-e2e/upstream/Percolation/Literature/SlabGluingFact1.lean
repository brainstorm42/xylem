import Percolation.Literature.SlabGluing
import Percolation.Util.Linter

/-!
# The Gluing Lemma of Duminil-Copin–Sidoravicius–Tassion: proof of Fact 1 (DST 2016, §2.3)

Sibling proof file of `SlabGluing.lean`, which set up
the objects of DST 2016, §2.3 (open self-avoiding paths, the minimal path `γ_min`, the set `U(ω)`,
the events `A, B^±, C, 𝒳`) and reduced Lemma 6 to two named facts, Fact 1 and Fact 2. Here **Fact 1 is proved**:

* `DuminilCopinSidoraviciusTassion2016_fact1_holds` — proved:
  `P[𝒳 ∩ {|U| < t}] ≤ (2/min{p,1-p})^{(5k+4)t} · P[{B⁻ ∩ B⁺}ᶜ]` for `k > 0`, `0 < p < 1`, all
  geometric data in range and all `t`; and the same with the subset `U'(ω) ⊆ U(ω)` of points whose
  (P2)-witness starts over a lattice neighbour (`GlueGeom.U'`, `fact1_U'`), which is the form the
  surgery of Fact 2 consumes.

## The printed proof and its formalisation

DST 2016, §2.3, proof of Fact 1 (p. 6 of arXiv:1401.7130): "Let `ω ∈ 𝒳` such that
`|U(ω)| < t`. Define `ω'` to be the configuration obtained from `ω` by closing, for any
`z ∈ U(ω)`, all the edges `{u, v}` such that `u ∈ \overline{\{z\}}` and `v` is connected to `S̄'_n`
by an open path. Observe that `ω'` cannot contain two open paths in `B̄'_n` from `S̄'_n` to `Ȳ_n^-`
and `Ȳ_n^+` respectively. Indeed, an open path in `ω'` must be in `ω`. Furthermore, two paths from
`S̄'_n` to `Ȳ_n^-` and `Ȳ_n^+` respectively must intersect at least one set of the form
`\overline{\{z\}}` with `z` in `U(ω)`. But this implies that one edge of one of these two paths was
turned to closed in `ω'`, which is a contradiction. We therefore constructed a map
`Φ : 𝒳 ∩ {|U| < t} → {S'_n ⟷ Y_n^-, S'_n ⟷ Y_n^+}ᶜ` … For any `ω'` in the image of `Φ`, the set
`{ω : Φ(ω) = ω'}` contains only configurations that are equal to `ω'` except possibly on the edges
adjacent to `U(ω')`. Here, we use the fact that `U(ω') = U(ω)` and `γ_min(ω') = γ_min(ω)` …
Lemma 7 can be applied."

* The map (`GlueGeom.phi1`, closing `GlueGeom.closeSet ω`: the open edges `s(u, v)` with `u` in a
  column of `U(ω)` and `v` joined to `S̄'_n` inside `B̄'_n`, `GlueGeom.JoinedSrc'`).
* "must intersect": `GlueGeom.exists_mem_γcols` — the planar shadows (`exists_walk_of_chain`) of
  `γ_min(ω)` (from `{x₀ ≤ u_{3n} ≤ n}` to `Z_n ⊆ {x₀ = 3n}`, inside `{x₀ ≤ 3n}`) and of
  `π⁻ ∪ (\text{link in } S'_n) ∪ π⁺` (inside `B'_n = [n, 3n] × [y-n, y+n]`, between `Y_n^-` and
  `Y_n^+`) meet by the planar crossing fact `exists_mem_support_of_side_crossing` of
  `SlabGluing.lean`; a meeting point over `S'_n` is excluded since a vertex of `γ_min` over `S'_n`
  would give `C` (`evC_of_mem_γmin_of_src'`). Then `GlueGeom.exists_closed_edge`: the first
  vertex `x₁` of the path in a column of `γ_min` has its column in `U(ω)` — (P1) by construction,
  (P2) witnessed by the initial segment of the path (off the columns of `γ_min`, inside `B̄'_n`,
  from `S̄'_n` to the predecessor `x₀` of `x₁`, which lies over `z + B_1`) — and `x₀` is joined to
  `S̄'_n`, so `s(x₀, x₁) ∈ closeSet ω` although it is open in `ω'`: `GlueGeom.phi1_not_mem`.
* "equal to `ω'` except possibly on the edges adjacent to `U(ω')`": `GlueGeom.diff_phi1_subset`;
  these are at most `(5k+4)·|U(ω')|` lattice edges (`card_filter_colEdges_le`, via the explicit
  list `colCover` of the `4(k+1)` planar and `k` vertical edges at a column).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: §2.3, Lemma 7 and Fact 1 with its proof (pp. 6–7 of the arXiv text).
* C. M. Newman, V. Tassion, W. Wu, Comm. Pure Appl. Math. 70 (2017), 2084–2120, §3.2, proof of
  Thm. 3.9, Fact 1 (the same map, "closing for every `z ∈ U(ω)` all the edges adjacent to a vertex
  in `B_r(z)` that are not in `γ`") [NewmanTassionWu2017].
* G. Grimmett, *Percolation*, 2nd ed. (1999), §2.2 (events depending on finitely many edges;
  cylinder decomposition) [GrimmettPercolation1999].
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph Filter Topology Finset

/-! ## The multi-valued map principle for bond percolation events in a finite window -/

section MultiValuedBridge

variable {ι : Type*}

/-- The Bernoulli weight of a finite configuration `S` relative to the finite window `K`:
`∏_{i ∈ K} (p if i ∈ S, 1 - p otherwise)`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 7 (proof)] -/
def winWeight [DecidableEq ι] (K : Finset ι) (p : ℝ) (S : Finset ι) : ℝ :=
  ∏ i ∈ K, if i ∈ S then p else 1 - p

/-- Window weights are nonnegative. [folklore] -/
theorem winWeight_nonneg [DecidableEq ι] (K : Finset ι) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset ι) :
    0 ≤ winWeight K p S :=
  prod_nonneg fun i _ => by split_ifs <;> linarith

/-- If `S` agrees with `S'` off `T`, then `w(S) ≤ w(S') / min{p, 1-p}^{|T|}`
(DST 2016, proof of Lemma 7, the inequality behind eq. (14)). [cite: DuminilCopinSidoraviciusTassion2016, Lemma 7 (proof, eq. (14))] -/
theorem winWeight_le_of_agree_off [DecidableEq ι] (K : Finset ι) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {S S' T : Finset ι} (h : ∀ i, i ∉ T → (i ∈ S ↔ i ∈ S')) :
    winWeight K p S ≤ winWeight K p S' / (min p (1 - p)) ^ T.card := by
  set m := min p (1 - p) with hm
  have hm0 : 0 < m := lt_min hp0 (by linarith)
  have hm1 : m ≤ 1 := (min_le_left _ _).trans hp1.le
  set f : Finset ι → ι → ℝ := fun η i => if i ∈ η then p else 1 - p with hf
  have hle1 : ∀ η i, f η i ≤ 1 := by intro η i; simp only [hf]; split_ifs <;> linarith
  have hnn : ∀ η i, 0 ≤ f η i := by intro η i; simp only [hf]; split_ifs <;> linarith
  have hge : ∀ η i, m ≤ f η i := by
    intro η i; simp only [hf]; split_ifs
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hsplit : ∀ η, winWeight K p η =
      (∏ i ∈ K.filter (· ∈ T), f η i) * ∏ i ∈ K.filter (· ∉ T), f η i := by
    intro η
    rw [winWeight, ← prod_filter_mul_prod_filter_not K (· ∈ T)]
  have hoff : (∏ i ∈ K.filter (· ∉ T), f S i) = ∏ i ∈ K.filter (· ∉ T), f S' i := by
    refine prod_congr rfl fun i hi => ?_
    have hi' : i ∉ T := (mem_filter.1 hi).2
    simp only [hf, h i hi']
  have hS_le : (∏ i ∈ K.filter (· ∈ T), f S i) ≤ 1 :=
    prod_le_one (fun i _ => hnn S i) fun i _ => hle1 S i
  have hcard : (K.filter (· ∈ T)).card ≤ T.card :=
    card_le_card fun i hi => (mem_filter.1 hi).2
  have hS_ge : m ^ T.card ≤ ∏ i ∈ K.filter (· ∈ T), f S' i := by
    calc m ^ T.card ≤ m ^ (K.filter (· ∈ T)).card := pow_le_pow_of_le_one hm0.le hm1 hcard
      _ = ∏ _i ∈ K.filter (· ∈ T), m := by rw [prod_const]
      _ ≤ ∏ i ∈ K.filter (· ∈ T), f S' i := prod_le_prod (fun _ _ => hm0.le) fun i _ => hge S' i
  have hC : 0 ≤ ∏ i ∈ K.filter (· ∉ T), f S' i := prod_nonneg fun i _ => hnn S' i
  rw [hsplit S, hsplit S', hoff, le_div_iff₀ (pow_pos hm0 _)]
  calc (∏ i ∈ K.filter (· ∈ T), f S i) * (∏ i ∈ K.filter (· ∉ T), f S' i) * m ^ T.card
      ≤ 1 * (∏ i ∈ K.filter (· ∉ T), f S' i) * ∏ i ∈ K.filter (· ∈ T), f S' i := by
        gcongr
    _ = (∏ i ∈ K.filter (· ∈ T), f S' i) * ∏ i ∈ K.filter (· ∉ T), f S' i := by ring

/-- **The multi-valued map principle on a finite window**, weighted-sum form (DST 2016, Lemma 7): for
 finite families `𝒜, ℬ` of configurations inside the window `K` and `Φ : 𝒜 → 𝔓(ℬ)` with `|Φ(ω)| ≥ t`
 and, for each `ω' ∈ ℬ`, a set `T` of at most `s` coordinates off which every preimage of `ω'`
 agrees with `ω'`: `Σ_{ω ∈ 𝒜} w(ω) ≤ (2/min{p,1-p})^s / t · Σ_{ω' ∈ ℬ} w(ω')`. [cite:
 DuminilCopinSidoraviciusTassion2016, Lemma 7]
-/
theorem lemma7_winWeight [DecidableEq ι] (K : Finset ι) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (s : ℕ) {t : ℝ}
    (ht : 0 < t) (A B : Finset (Finset ι)) (Φ : Finset ι → Finset (Finset ι))
    (hΦB : ∀ ω ∈ A, Φ ω ⊆ B) (hΦt : ∀ ω ∈ A, t ≤ (Φ ω).card)
    (hΦs : ∀ ω' ∈ B, ∃ T : Finset ι, T.card ≤ s ∧
      ∀ ω ∈ A, ω' ∈ Φ ω → ∀ i, i ∉ T → (i ∈ ω ↔ i ∈ ω')) :
    ∑ ω ∈ A, winWeight K p ω ≤ (2 / min p (1 - p)) ^ s / t * ∑ ω' ∈ B, winWeight K p ω' := by
  set m := min p (1 - p) with hm
  have hm0 : 0 < m := lt_min hp0 (by linarith)
  have hm1 : m ≤ 1 := (min_le_left _ _).trans hp1.le
  have hms : 0 < m ^ s := pow_pos hm0 s
  have hw0 : ∀ η, 0 ≤ winWeight K p η := winWeight_nonneg K hp0.le hp1.le
  choose! T hT using hΦs
  have h14 : ∀ ω ∈ A, winWeight K p ω ≤ (t * m ^ s)⁻¹ * ∑ ω' ∈ Φ ω, winWeight K p ω' := by
    intro ω hω
    have hcard : t ≤ (Φ ω).card := hΦt ω hω
    have hterm : ∀ ω' ∈ Φ ω, winWeight K p ω * m ^ s ≤ winWeight K p ω' := by
      intro ω' hω'
      obtain ⟨hTc, hTa⟩ := hT ω' (hΦB ω hω hω')
      have h1 := winWeight_le_of_agree_off K hp0 hp1 (hTa ω hω hω')
      have h2 : m ^ s ≤ m ^ (T ω').card := pow_le_pow_of_le_one hm0.le hm1 hTc
      rw [le_div_iff₀ (pow_pos hm0 _)] at h1
      calc winWeight K p ω * m ^ s ≤ winWeight K p ω * m ^ (T ω').card := by gcongr; exact hw0 ω
        _ ≤ winWeight K p ω' := h1
    have hsum : (Φ ω).card * (winWeight K p ω * m ^ s) ≤ ∑ ω' ∈ Φ ω, winWeight K p ω' := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum hterm
    rw [le_inv_mul_iff₀ (mul_pos ht hms)]
    calc t * m ^ s * winWeight K p ω = t * (winWeight K p ω * m ^ s) := by ring
      _ ≤ (Φ ω).card * (winWeight K p ω * m ^ s) := by gcongr; exact mul_nonneg (hw0 ω) hms.le
      _ ≤ ∑ ω' ∈ Φ ω, winWeight K p ω' := hsum
  have h15 : ∑ ω ∈ A, ∑ ω' ∈ Φ ω, winWeight K p ω' =
      ∑ ω' ∈ B, ((A.filter fun ω => ω' ∈ Φ ω).card : ℝ) * winWeight K p ω' := by
    have : ∀ ω ∈ A, ∑ ω' ∈ Φ ω, winWeight K p ω' =
        ∑ ω' ∈ B, if ω' ∈ Φ ω then winWeight K p ω' else 0 := by
      intro ω hω
      rw [sum_ite_mem, inter_eq_right.2 (hΦB ω hω)]
    rw [sum_congr rfl this, sum_comm]
    refine sum_congr rfl fun ω' _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  have h16 : ∀ ω' ∈ B, ((A.filter fun ω => ω' ∈ Φ ω).card : ℝ) ≤ 2 ^ s := by
    intro ω' hω'
    obtain ⟨hTc, hTa⟩ := hT ω' hω'
    have := card_filter_agree_off_le A ω' (T ω') (fun ω => ω' ∈ Φ ω) fun ω hω hP => hTa ω hω hP
    calc ((A.filter fun ω => ω' ∈ Φ ω).card : ℝ) ≤ (2 : ℝ) ^ (T ω').card := by exact_mod_cast this
      _ ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) hTc
  calc ∑ ω ∈ A, winWeight K p ω
      ≤ ∑ ω ∈ A, (t * m ^ s)⁻¹ * ∑ ω' ∈ Φ ω, winWeight K p ω' := sum_le_sum h14
    _ = (t * m ^ s)⁻¹ * ∑ ω' ∈ B, ((A.filter fun ω => ω' ∈ Φ ω).card : ℝ) * winWeight K p ω' := by
        rw [← mul_sum, h15]
    _ ≤ (t * m ^ s)⁻¹ * ∑ ω' ∈ B, 2 ^ s * winWeight K p ω' := by
        gcongr with ω' hω'
        · exact hw0 ω'
        · exact h16 ω' hω'
    _ = (2 / m) ^ s / t * ∑ ω' ∈ B, winWeight K p ω' := by
        rw [← mul_sum, div_pow]
        field_simp

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- **The probability of an event determined by a finite window is a weighted sum over the
lattice configurations inside the window**: for `A` determined by the pairs `K'` and
`K = K' ∩ E(G)`, `P_p(A) = Σ_{S ⊆ K, S ∈ A} w_K(S)` (cylinder decomposition,
`Russo.measureReal_eq_cylPoly`; coordinates off `E(G)` are almost surely closed and drop out).
[cite: GrimmettPercolation1999, §2.2] -/
theorem bondPercolation_real_eq_sum_winWeight (G : SimpleGraph V) (p : unitInterval)
    (K' : Finset (Sym2 V)) {A : Set (BondConfig V)} (hA : DeterminedBy A ↑K')
    (K : Finset (Sym2 V)) (hK : ∀ e, e ∈ K ↔ e ∈ K' ∧ e ∈ G.edgeSet) :
    (bondPercolation G p).real A =
      ∑ S ∈ K.powerset.filter (fun S : Finset (Sym2 V) => (↑S : Set (Sym2 V)) ∈ A),
        winWeight K p S := by
  rw [show bondPercolation G p = ProbabilityTheory.setBernoulli G.edgeSet p from rfl,
    Russo.measureReal_eq_cylPoly hA, Russo.cylPoly]
  have hKK' : K ⊆ K' := fun e he => ((hK e).1 he).1
  -- terms with `S ⊄ K` vanish; for `S ⊆ K` the `K'`-product is the `K`-weight
  have hterm : ∀ S ∈ K'.powerset, (if (↑S : Set (Sym2 V)) ∈ A then
      ∏ i ∈ K', Russo.weight G.edgeSet ↑S i p else 0) =
      if S ⊆ K ∧ (↑S : Set (Sym2 V)) ∈ A then winWeight K p S else 0 := by
    intro S hS
    rw [mem_powerset] at hS
    by_cases hSK : S ⊆ K
    · simp only [hSK, true_and]
      split_ifs with hSA
      · rw [winWeight, ← prod_filter_mul_prod_filter_not K' (· ∈ K)]
        have h1 : K'.filter (· ∈ K) = K := by
          ext e; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hKK' h, h⟩⟩
        have h2 : ∏ i ∈ K'.filter (· ∉ K), Russo.weight G.edgeSet (↑S : Set (Sym2 V)) i p = 1 := by
          refine prod_eq_one fun i hi => ?_
          obtain ⟨hiK', hiK⟩ := mem_filter.1 hi
          have hiE : i ∉ G.edgeSet := fun hiE => hiK ((hK i).2 ⟨hiK', hiE⟩)
          have hiS : i ∉ S := fun hiS => hiK (hSK hiS)
          simp [Russo.weight, hiE, hiS]
        rw [h1, h2, mul_one]
        refine prod_congr rfl fun i hi => ?_
        have hiE : i ∈ G.edgeSet := ((hK i).1 hi).2
        simp [Russo.weight, hiE]
      · rfl
    · simp only [hSK, false_and, if_false]
      split_ifs with hSA
      · -- some `i ∈ S \ K` is a non-edge, where the weight vanishes
        obtain ⟨i, hiS, hiK⟩ := not_subset.1 hSK
        have hiE : i ∉ G.edgeSet := fun hiE => hiK ((hK i).2 ⟨hS hiS, hiE⟩)
        exact prod_eq_zero (hS hiS) (by simp [Russo.weight, hiE, hiS])
      · rfl
  rw [sum_congr rfl hterm,
    Finset.sum_filter (fun S : Finset (Sym2 V) => (↑S : Set (Sym2 V)) ∈ A) (winWeight K p)]
  -- restrict the sum from `K'.powerset` to `K.powerset`
  have hK' : ∑ S ∈ K.powerset, (if (↑S : Set (Sym2 V)) ∈ A then winWeight K p S else 0) =
      ∑ S ∈ K.powerset, (if S ⊆ K ∧ (↑S : Set (Sym2 V)) ∈ A then winWeight K p S else 0) :=
    sum_congr rfl fun S hS => by rw [mem_powerset] at hS; simp [hS]
  rw [hK']
  exact (sum_subset (powerset_mono.2 hKK') fun S _ hSK => by
    rw [mem_powerset] at hSK; simp [hSK]).symm

open scoped Classical in
/-- **The multi-valued map principle for bond percolation** (DST 2016, Lemma 7, for events of
`BondConfig V` determined by a finite set of pairs `K'`): let `0 < p < 1`, `A, B` determined by
`K'`, `K = K' ∩ E(G)`, and `Φ` a map from lattice configurations `S ⊆ K` in `A` to families of
lattice configurations `⊆ K` in `B`, with `|Φ(S)| ≥ t` and, for each `S' ⊆ K` in `B`, a set of
at most `s` pairs off which every preimage of `S'` agrees with `S'`. Then
`P_p(A) ≤ (2/min{p,1-p})^s / t · P_p(B)`. [cite: DuminilCopinSidoraviciusTassion2016, Lemma 7] -/
theorem lemma7_bond (G : SimpleGraph V) (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (K' K : Finset (Sym2 V)) (hK : ∀ e, e ∈ K ↔ e ∈ K' ∧ e ∈ G.edgeSet)
    {A B : Set (BondConfig V)} (hA : DeterminedBy A ↑K') (hB : DeterminedBy B ↑K')
    (s : ℕ) {t : ℝ} (ht : 0 < t) (Φ : Finset (Sym2 V) → Finset (Finset (Sym2 V)))
    (hΦB : ∀ S, S ⊆ K → (↑S : Set (Sym2 V)) ∈ A → ∀ S' ∈ Φ S, S' ⊆ K ∧ (↑S' : Set (Sym2 V)) ∈ B)
    (hΦt : ∀ S, S ⊆ K → (↑S : Set (Sym2 V)) ∈ A → t ≤ (Φ S).card)
    (hΦs : ∀ S', S' ⊆ K → (↑S' : Set (Sym2 V)) ∈ B → ∃ T : Finset (Sym2 V), T.card ≤ s ∧
      ∀ S, S ⊆ K → (↑S : Set (Sym2 V)) ∈ A → S' ∈ Φ S → ∀ e, e ∉ T → (e ∈ S ↔ e ∈ S')) :
    (bondPercolation G p).real A ≤
      (2 / min (p : ℝ) (1 - p)) ^ s / t * (bondPercolation G p).real B := by
  rw [bondPercolation_real_eq_sum_winWeight G p K' hA K hK,
    bondPercolation_real_eq_sum_winWeight G p K' hB K hK]
  refine lemma7_winWeight K hp0 hp1 s ht _ _ Φ (fun S hS => ?_) (fun S hS => ?_) fun S' hS' => ?_
  · obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
    intro S' hS'
    obtain ⟨h1, h2⟩ := hΦB S (mem_powerset.1 hS1) hS2 S' hS'
    exact mem_filter.2 ⟨mem_powerset.2 h1, h2⟩
  · obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
    exact hΦt S (mem_powerset.1 hS1) hS2
  · obtain ⟨hS1, hS2⟩ := mem_filter.1 hS'
    obtain ⟨T, hT1, hT2⟩ := hΦs S' (mem_powerset.1 hS1) hS2
    exact ⟨T, hT1, fun S hS hP => hT2 S (mem_powerset.1 (mem_filter.1 hS).1) (mem_filter.1 hS).2 hP⟩

end MultiValuedBridge

/-! ## List helpers and connectivity along open self-avoiding paths -/

section ListHelpers

variable {α : Type*}

/-- Splitting a list at the first element satisfying a predicate. [folklore] -/
theorem exists_first_split {p : α → Prop} :
    ∀ l : List α, (∃ x ∈ l, p x) → ∃ (l₁ : List α) (x : α) (l₂ : List α),
      l = l₁ ++ x :: l₂ ∧ p x ∧ ∀ y ∈ l₁, ¬p y
  | [], h => by simp at h
  | a :: l, h => by
    by_cases ha : p a
    · exact ⟨[], a, l, rfl, ha, fun y hy => by simp at hy⟩
    · obtain ⟨x, hx, hpx⟩ := h
      have hxl : x ∈ l := by
        rcases List.mem_cons.1 hx with rfl | hxl
        · exact absurd hpx ha
        · exact hxl
      obtain ⟨l₁, y, l₂, rfl, hpy, hl₁⟩ := exists_first_split l ⟨x, hxl, hpx⟩
      refine ⟨a :: l₁, y, l₂, rfl, hpy, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ha
      · exact hl₁ z hz

end ListHelpers

section PathConn

variable {k : ℕ}

/-- Along a chain of open edges inside `S`, the first vertex is joined inside `S` to every vertex
of the chain. [folklore] -/
theorem openConnIn_head_of_mem {ω : BondConfig (slab 3 k)} {S : Set (slab 3 k)} :
    ∀ (a : slab 3 k) (l : List (slab 3 k)), (a :: l).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) →
      (∀ x ∈ a :: l, x ∈ S) → ∀ v ∈ a :: l, ω ∈ openConnIn S a v := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _ hS v hv
    rw [List.mem_singleton] at hv
    subst hv
    rw [mem_openConnIn_iff_pathIn]
    exact PathIn.refl (hS v (by simp))
  | cons b l ih =>
    intro hc hS v hv
    rw [List.isChain_cons_cons] at hc
    rcases List.mem_cons.1 hv with rfl | hv
    · rw [mem_openConnIn_iff_pathIn]
      exact PathIn.refl (hS v (by simp))
    · have h1 : ω ∈ openConnIn S a b := by
        rw [mem_openConnIn_iff_pathIn]
        exact PathIn.of_adj (hS a (by simp)) (hS b (by simp)) ((openGraph_adj ω a b).2 hc.1)
      exact SlabCriticality.openConnIn_trans h1 (ih b hc.2 (fun x hx => hS x (by simp [hx])) v hv)

/-- The first vertex of an open self-avoiding path is joined inside `S` to every vertex of the
path. [folklore] -/
theorem IsOSAP.openConnIn_of_mem {ω : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)}
    {l : List (slab 3 k)} (hl : IsOSAP k ω S X Y l) {v : slab 3 k} (hv : v ∈ l) :
    ω ∈ openConnIn S (l.head hl.ne_nil) v := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
  exact openConnIn_head_of_mem a l' hl.chain hl.subset v hv

end PathConn

/-! ## Planar shadows of slab paths -/

section Shadows

variable (k : ℕ)

/-- The point of `Site 2 = ℤ²` with the given coordinates. [folklore] -/
def ts (z : ℤ × ℤ) : Site 2 := ![z.1, z.2]

/-- Coordinates of `ts`. [folklore] -/
@[simp] theorem ts_apply_zero (z : ℤ × ℤ) : ts z 0 = z.1 := rfl
/-- Coordinates of `ts`. [folklore] -/
@[simp] theorem ts_apply_one (z : ℤ × ℤ) : ts z 1 = z.2 := rfl

/-- `ts` is injective. [folklore] -/
theorem ts_injective : Function.Injective ts := by
  intro z w h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [ts_apply_zero, ts_apply_one] at h0 h1
  exact Prod.ext h0 h1

/-- Planar adjacency is adjacency of `ℤ²`. [folklore] -/
theorem adj_ts_of_planarAdj {z w : ℤ × ℤ} (h : planarAdj z w) : (zdGraph 2).Adj (ts z) (ts w) := by
  rw [zdGraph_two_adj_iff]
  simp only [ts_apply_zero, ts_apply_one]
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at h
  omega

variable {k}

/-- **Planar shadow of a lattice chain.** A chain of lattice edges of the slab projects onto a
walk of `ℤ²` (vertical steps are dropped) whose vertices are projections of vertices of the
chain. [folklore] -/
theorem exists_walk_of_chain {ω : BondConfig (slab 3 k)} (hω : ω ⊆ (slabGraph 3 k).edgeSet) :
    ∀ (a : slab 3 k) (l : List (slab 3 k)), (a :: l).IsChain (fun a b => s(a, b) ∈ ω ∧ a ≠ b) →
      ∃ (e : slab 3 k) (W : (zdGraph 2).Walk (ts (planar k a)) (ts (planar k e))),
        (a :: l).getLast (List.cons_ne_nil a l) = e ∧
        ∀ x ∈ W.support, ∃ v ∈ a :: l, ts (planar k v) = x := by
  intro a l
  induction l generalizing a with
  | nil =>
    intro _
    refine ⟨a, Walk.nil, rfl, fun x hx => ⟨a, by simp, ?_⟩⟩
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact hx.symm
  | cons b l ih =>
    intro hc
    rw [List.isChain_cons_cons] at hc
    obtain ⟨e, W, he, hW⟩ := ih b hc.2
    have hadj : (slabGraph 3 k).Adj a b := (SimpleGraph.mem_edgeSet _).1 (hω hc.1.1)
    have hlast : (a :: b :: l).getLast (List.cons_ne_nil a (b :: l)) = e := by
      rw [List.getLast_cons (List.cons_ne_nil b l)]; exact he
    rcases (zdGraph_three_adj_iff a.1 b.1).1 hadj with ⟨-, hpa⟩ | ⟨hpe, -⟩
    · have hpa' : planarAdj (planar k a) (planar k b) := hpa
      refine ⟨e, Walk.cons (adj_ts_of_planarAdj hpa') W, hlast, fun x hx => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨a, by simp, rfl⟩
      · obtain ⟨v, hv, rfl⟩ := hW x hx
        exact ⟨v, by simp [hv], rfl⟩
    · have hpe' : planar k a = planar k b := hpe
      refine ⟨e, W.copy (by rw [hpe']) rfl, hlast, fun x hx => ?_⟩
      rw [Walk.support_copy] at hx
      obtain ⟨v, hv, rfl⟩ := hW x hx
      exact ⟨v, by simp [hv], rfl⟩

/-- A walk of `ℤ²` between two points of a box, inside the box (along a row, then a column).
[folklore] -/
theorem exists_walk_in_sqBox {c : ℤ × ℤ} {m : ℕ} {z w : ℤ × ℤ} (hz : z ∈ sqBox c m)
    (hw : w ∈ sqBox c m) :
    ∃ W : (zdGraph 2).Walk (ts z) (ts w), ∀ x ∈ W.support, ∃ v ∈ sqBox c m, ts v = x := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  rw [abs_le] at hz1 hz2 hw1 hw2
  -- horizontal leg from `z` to `(w.1, z.2)`, vertical leg to `w`
  set mid : ℤ × ℤ := (w.1, z.2) with hmid
  have hH : ∃ H : (zdGraph 2).Walk (ts z) (ts mid), ∀ x ∈ H.support,
      x 1 = z.2 ∧ min z.1 w.1 ≤ x 0 ∧ x 0 ≤ max z.1 w.1 := by
    rcases le_total z.1 w.1 with h | h
    · obtain ⟨H, hH⟩ := exists_walk_horizontal (z := ts z) (w := ts mid) (by simp [hmid]) (by simpa [hmid])
      exact ⟨H, fun x hx => by have := hH x hx; simp [hmid] at this; omega⟩
    · obtain ⟨H, hH⟩ := exists_walk_horizontal (z := ts mid) (w := ts z) (by simp [hmid]) (by simpa [hmid])
      refine ⟨H.reverse, fun x hx => ?_⟩
      rw [Walk.support_reverse, List.mem_reverse] at hx
      have := hH x hx; simp [hmid] at this; omega
  have hV : ∃ H : (zdGraph 2).Walk (ts mid) (ts w), ∀ x ∈ H.support,
      x 0 = w.1 ∧ min z.2 w.2 ≤ x 1 ∧ x 1 ≤ max z.2 w.2 := by
    rcases le_total z.2 w.2 with h | h
    · obtain ⟨H, hH⟩ := exists_walk_vertical (z := ts mid) (w := ts w) (by simp [hmid]) (by simpa [hmid])
      exact ⟨H, fun x hx => by have := hH x hx; simp [hmid] at this; omega⟩
    · obtain ⟨H, hH⟩ := exists_walk_vertical (z := ts w) (w := ts mid) (by simp [hmid]) (by simpa [hmid])
      refine ⟨H.reverse, fun x hx => ?_⟩
      rw [Walk.support_reverse, List.mem_reverse] at hx
      have := hH x hx; simp [hmid] at this; omega
  obtain ⟨H₁, hH₁⟩ := hH
  obtain ⟨H₂, hH₂⟩ := hV
  refine ⟨H₁.append H₂, fun x hx => ?_⟩
  rw [Walk.mem_support_append_iff] at hx
  have key : ∀ x : Site 2, (min z.1 w.1 ≤ x 0 ∧ x 0 ≤ max z.1 w.1 ∧ min z.2 w.2 ≤ x 1 ∧
      x 1 ≤ max z.2 w.2) → ∃ v ∈ sqBox c m, ts v = x := by
    intro x hx
    refine ⟨(x 0, x 1), ?_, ?_⟩
    · simp only [sqBox, Set.mem_setOf_eq, abs_le]
      rw [min_le_iff, le_max_iff, min_le_iff, le_max_iff] at hx
      omega
    · rw [Site.eq_iff_two]; simp
  rcases hx with hx | hx
  · have := hH₁ x hx
    exact key x (by rw [min_le_iff, le_max_iff]; omega)
  · have := hH₂ x hx
    exact key x (by rw [min_le_iff, le_max_iff, min_le_iff, le_max_iff]; omega)

end Shadows

/-! ## The crossing step of Fact 1: a path of `B^±` meets a column of `γ_min` -/

section Crossing

variable (k : ℕ)

/-- `B̄_{3n}` is finite. [folklore] -/
theorem GlueGeom.big_finite (G : GlueGeom) : (slabLift k G.big).Finite :=
  slabLift_finite k (sqBox_finite _ _)

/-- On `A`, `γ_min` is an open self-avoiding path from `S̄_{3n}` to `Z̄_n` inside `B̄_{3n}` with
minimal key. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Definition of γ_min)] -/
theorem GlueGeom.γmin_spec (G : GlueGeom) {ω : BondConfig (slab 3 k)} (hA : ω ∈ G.evA k) :
    IsOSAP k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) (G.γmin k ω) ∧
      ∀ l, IsOSAP k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) l →
        pathKey k (G.γmin k ω) ≤ pathKey k l :=
  minPath_spec (G.big_finite k) ((mem_slabConn_iff_exists_isOSAP ω _ _ _).1 hA)

/-- A vertex of `γ_min` joined inside `B̄'_n` to `S̄'_n` gives `C` (`S_{3n} ⟷ S'_n` in
`B̄_{3n} ∪ B̄'_n`). [folklore] -/
theorem GlueGeom.evC_of_mem_γmin_of_joined (G : GlueGeom) {ω : BondConfig (slab 3 k)}
    (hA : ω ∈ G.evA k) {v : slab 3 k} (hv : v ∈ G.γmin k ω) {s' : slab 3 k}
    (hs' : s' ∈ slabLift k G.src') (hj : ω ∈ openConnIn (slabLift k G.small) v s') :
    ω ∈ G.evC k := by
  have hγ := (G.γmin_spec k hA).1
  refine ⟨(G.γmin k ω).head hγ.ne_nil, hγ.head_mem _, s', hs', ?_⟩
  exact SlabCriticality.openConnIn_trans
    (openConnIn_mono (slabLift_mono k Set.subset_union_left) _ _ (hγ.openConnIn_of_mem hv))
    (openConnIn_mono (slabLift_mono k Set.subset_union_right) _ _ hj)

/-- A vertex of `γ_min` over `S'_n` gives `C`. [folklore] -/
theorem GlueGeom.evC_of_mem_γmin_of_src' (G : GlueGeom) {ω : BondConfig (slab 3 k)}
    (hA : ω ∈ G.evA k) {v : slab 3 k} (hv : v ∈ G.γmin k ω) (hv' : v ∈ slabLift k G.src') :
    ω ∈ G.evC k := by
  have hγ := (G.γmin_spec k hA).1
  refine ⟨(G.γmin k ω).head hγ.ne_nil, hγ.head_mem _, v, hv', ?_⟩
  exact openConnIn_mono (slabLift_mono k Set.subset_union_left) _ _ (hγ.openConnIn_of_mem hv)

/-- **The crossing step** (DST 2016, §2.3, proof of Fact 1: "two paths from `S̄'_n` to `Ȳ_n^-`
and `Ȳ_n^+` respectively must intersect at least one set of the form `\overline{\{z\}}` with `z`
in `U(ω)`" — here its first half): for `ω ∈ 𝒳` a lattice configuration and open self-avoiding
paths `π⁻ : S̄'_n → Ȳ_n^-`, `π⁺ : S̄'_n → Ȳ_n^+` inside `B̄'_n` in a sub-configuration `ω' ⊆ ω`,
one of them has a vertex in a column of `γ_min(ω)`: otherwise the planar shadows of `γ_min(ω)`
and of `π⁻ ∪ (\text{a link inside } S'_n) ∪ π⁺` would be disjoint (a common point over `S'_n`
would put a vertex of `γ_min` in `S̄'_n`, forcing `C`), contradicting
`exists_mem_support_of_side_crossing`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
theorem GlueGeom.exists_mem_γcols (G : GlueGeom) (hG : G.InRange) {ω ω' : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) (hω' : ω' ⊆ ω) (hX : ω ∈ G.evX k)
    {πm πp : List (slab 3 k)}
    (hπm : IsOSAP k ω' (slabLift k G.small) (slabLift k G.src') (slabLift k G.ym) πm)
    (hπp : IsOSAP k ω' (slabLift k G.small) (slabLift k G.src') (slabLift k G.yp) πp) :
    ∃ x, (x ∈ πm ∨ x ∈ πp) ∧ planar k x ∈ G.γcols k ω := by
  obtain ⟨hn, hu₃, hu₁, hα, hαn, hy0, hy⟩ := hG
  obtain ⟨⟨⟨hA, -⟩, -⟩, hC⟩ := hX
  have hγ := (G.γmin_spec k hA).1
  obtain ⟨a, lγ, haγ⟩ := List.exists_cons_of_ne_nil hγ.ne_nil
  obtain ⟨am0, lm, ham0⟩ := List.exists_cons_of_ne_nil hπm.ne_nil
  obtain ⟨ap0, lp, hap0⟩ := List.exists_cons_of_ne_nil hπp.ne_nil
  have hγ' : IsOSAP k ω (slabLift k G.big) (slabLift k G.src) (slabLift k G.zSeg) (a :: lγ) := haγ ▸ hγ
  have hπm' := ham0 ▸ hπm
  have hπp' := hap0 ▸ hπp
  by_contra H
  push Not at H
  have hω'E : ω' ⊆ (slabGraph 3 k).edgeSet := hω'.trans hω
  obtain ⟨eγ, Wγ, heγ, hWγ⟩ := exists_walk_of_chain hω a lγ hγ'.chain
  obtain ⟨em, Wm, hem, hWm⟩ := exists_walk_of_chain hω'E am0 lm hπm'.chain
  obtain ⟨ep, Wp, hep, hWp⟩ := exists_walk_of_chain hω'E ap0 lp hπp'.chain
  -- membership facts
  have hmemγ : ∀ v ∈ a :: lγ, v ∈ G.γmin k ω := fun v hv => haγ ▸ hv
  have hmemm : ∀ v ∈ am0 :: lm, v ∈ πm := fun v hv => ham0 ▸ hv
  have hmemp : ∀ v ∈ ap0 :: lp, v ∈ πp := fun v hv => hap0 ▸ hv
  have ha_src : a ∈ slabLift k G.src := hγ'.head_mem (List.cons_ne_nil _ _)
  have heγ_z : eγ ∈ slabLift k G.zSeg := by
    have := hγ'.last_mem (List.cons_ne_nil _ _); rwa [heγ] at this
  have heγ_mem : eγ ∈ G.γmin k ω := hmemγ _ (heγ ▸ List.getLast_mem _)
  have ham0_src : am0 ∈ slabLift k G.src' := hπm'.head_mem (List.cons_ne_nil _ _)
  have hap0_src : ap0 ∈ slabLift k G.src' := hπp'.head_mem (List.cons_ne_nil _ _)
  have hem_y : em ∈ slabLift k G.ym := by
    have := hπm'.last_mem (List.cons_ne_nil _ _); rwa [hem] at this
  have hep_y : ep ∈ slabLift k G.yp := by
    have := hπp'.last_mem (List.cons_ne_nil _ _); rwa [hep] at this
  have hem_mem : em ∈ πm := hmemm _ (hem ▸ List.getLast_mem _)
  have hep_mem : ep ∈ πp := hmemp _ (hep ▸ List.getLast_mem _)
  -- the link inside `S'_n` and the walk `Q`
  have ham0_src' : planar k am0 ∈ sqBox (2 * (G.n : ℤ), G.y) G.u₁ := ham0_src
  have hap0_src' : planar k ap0 ∈ sqBox (2 * (G.n : ℤ), G.y) G.u₁ := hap0_src
  obtain ⟨Conn, hConn⟩ := exists_walk_in_sqBox ham0_src' hap0_src'
  let Q : (zdGraph 2).Walk (ts (planar k em)) (ts (planar k ep)) := Wm.reverse.append (Conn.append Wp)
  -- unpack the planar sets
  simp only [GlueGeom.src, GlueGeom.zSeg, GlueGeom.ym, GlueGeom.yp, mem_slabLift_iff,
    sqBox, sideSeg, Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, sub_zero, abs_le]
    at ha_src heγ_z hem_y hep_y
  have hbig : ∀ v ∈ G.γmin k ω, (planar k v).1 ≤ 3 * (G.n : ℤ) := by
    intro v hv
    have := hγ.subset v hv
    simp only [GlueGeom.big, mem_slabLift_iff, sqBox, Set.mem_setOf_eq, Prod.fst_zero,
      Prod.snd_zero, sub_zero, abs_le] at this
    exact this.1.2
  have hsmall : ∀ v, v ∈ slabLift k G.small → (G.n : ℤ) ≤ (planar k v).1 ∧
      (planar k v).1 ≤ 3 * G.n ∧ G.y - G.n ≤ (planar k v).2 ∧ (planar k v).2 ≤ G.y + G.n := by
    intro v hv
    simp only [GlueGeom.small, mem_slabLift_iff, sqBox, Set.mem_setOf_eq, abs_le] at hv
    omega
  -- hypotheses of the planar crossing fact
  have hγbd : ∀ x ∈ Wγ.support, x 0 ≤ 3 * (G.n : ℤ) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := hWγ x hx
    exact hbig v (hmemγ v hv)
  have hQsupp : ∀ x ∈ Q.support, (∃ w, (w ∈ πm ∨ w ∈ πp) ∧ ts (planar k w) = x) ∨
      ∃ u ∈ sqBox (2 * (G.n : ℤ), G.y) G.u₁, ts u = x := by
    intro x hx
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨w, hw, rfl⟩ := hWm x hx
      exact Or.inl ⟨w, Or.inl (hmemm w hw), rfl⟩
    · exact Or.inr (hConn x hx)
    · obtain ⟨w, hw, rfl⟩ := hWp x hx
      exact Or.inl ⟨w, Or.inr (hmemp w hw), rfl⟩
  have hQbd : ∀ x ∈ Q.support, (G.n : ℤ) ≤ x 0 ∧ x 0 ≤ 3 * G.n ∧ G.y - G.n ≤ x 1 ∧ x 1 ≤ G.y + G.n := by
    intro x hx
    rcases hQsupp x hx with ⟨w, hw, rfl⟩ | ⟨u, hu, rfl⟩
    · have hws : w ∈ slabLift k G.small := by
        rcases hw with hw | hw
        · exact hπm.subset w hw
        · exact hπp.subset w hw
      simpa using hsmall w hws
    · simp only [sqBox, Set.mem_setOf_eq, abs_le] at hu
      simp only [ts_apply_zero, ts_apply_one]
      omega
  -- no vertex of `π^±` projects onto a column of `γ_min`, by assumption `H`
  have hoff : ∀ w, (w ∈ πm ∨ w ∈ πp) → ∀ v ∈ G.γmin k ω, planar k v ≠ planar k w :=
    fun w hw v hv heq => H w hw ⟨v, hv, heq⟩
  have h1 : (ts (planar k em)) 1 < (ts (planar k eγ)) 1 := by
    simp only [ts_apply_one]
    rcases lt_or_eq_of_le (show (planar k em).2 ≤ (planar k eγ).2 by omega) with h | h
    · exact h
    · exact absurd (Prod.ext (by omega) h.symm) (hoff em (Or.inl hem_mem) eγ heγ_mem)
  have h2 : (ts (planar k eγ)) 1 < (ts (planar k ep)) 1 := by
    simp only [ts_apply_one]
    rcases lt_or_eq_of_le (show (planar k eγ).2 ≤ (planar k ep).2 by omega) with h | h
    · exact h
    · exact absurd (Prod.ext (by omega) h) (hoff ep (Or.inr hep_mem) eγ heγ_mem)
  obtain ⟨x, hxγ, hxQ⟩ := exists_mem_support_of_side_crossing (L := G.n) (R := 3 * G.n)
    (B := G.y - G.n) (T := G.y + G.n) Wγ Q hγbd (by simp; omega) (by simp; omega) hQbd
    (by simp; omega) (by simp; omega) h1 h2
  obtain ⟨v, hv, rfl⟩ := hWγ x hxγ
  rcases hQsupp _ hxQ with ⟨w, hw, heq⟩ | ⟨u, hu, heq⟩
  · exact hoff w hw v (hmemγ v hv) (ts_injective heq).symm
  · have huv : planar k v = u := (ts_injective heq).symm
    exact hC (G.evC_of_mem_γmin_of_src' k hA (hmemγ v hv) (by rw [mem_slabLift_iff, huv]; exact hu))

end Crossing

/-! ## The set `U(ω)` receives the first crossing vertex; the closing map `Φ` of Fact 1 -/

section Closing

variable (k : ℕ)

/-- Planar adjacency puts a point in the `1`-box of the other. [folklore] -/
theorem mem_sqBox_one_of_planarAdj {z w : ℤ × ℤ} (h : planarAdj z w) : z ∈ sqBox w 1 := by
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at h
  simp only [sqBox, Set.mem_setOf_eq, abs_le, Nat.cast_one]
  omega

/-- **The set `U'(ω)` ⊆ `U(ω)`**: as `U(ω)` (DST 2016, §2.3, Definition, p. 6: P1–P2), but with the
witness path of (P2) starting over a lattice neighbour of `z` rather than over the sup-norm box
`z + B_1` (the diagonal columns of `z + B_1` are excluded). The points of `U` produced by the proof
of Fact 1 (the first vertex of a path of `B^±` in a column of `γ_min`, whose predecessor is a
planar lattice step away) lie in `U'`, so Fact 1 holds with `U'` as well; `U'` is the set the
surgery of Fact 2 is applied to. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Definition of U(ω), p. 6)] -/
def GlueGeom.U' (G : GlueGeom) (ω : BondConfig (slab 3 k)) : Set (ℤ × ℤ) :=
  {z | z ∈ G.small ∧ z ∈ G.γcols k ω ∧
    ∃ x₀ : slab 3 k, planarAdj (planar k x₀) z ∧ ∃ s' ∈ slabLift k G.src',
      ω ∈ openConnIn (slabLift k G.small ∩ {v | planar k v ∉ G.γcols k ω}) x₀ s'}

/-- `U' ⊆ U`. [folklore] -/
theorem GlueGeom.U'_subset_U (G : GlueGeom) (ω : BondConfig (slab 3 k)) : G.U' k ω ⊆ G.U k ω := by
  rintro z ⟨h1, h2, x₀, hx₀, h3⟩
  exact ⟨h1, h2, x₀, mem_sqBox_one_of_planarAdj hx₀, h3⟩

/-- `U'(ω)` is finite. [folklore] -/
theorem GlueGeom.U'_finite (G : GlueGeom) (ω : BondConfig (slab 3 k)) : (G.U' k ω).Finite :=
  (G.U_finite k ω).subset (G.U'_subset_U k ω)

/-- `|U'(ω)| ≤ |U(ω)|`. [folklore] -/
theorem GlueGeom.ncard_U'_le (G : GlueGeom) (ω : BondConfig (slab 3 k)) :
    (G.U' k ω).ncard ≤ (G.U k ω).ncard :=
  Set.ncard_le_ncard (G.U'_subset_U k ω) (G.U_finite k ω)

/-- "`v` is joined to `S̄'_n` inside `B̄'_n`" (DST 2016, proof of Fact 1: "`v` is connected to
`S̄'_n` by an open path"; here inside `B̄'_n`, which is how it is used).
[cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
def GlueGeom.JoinedSrc' (G : GlueGeom) (ω : BondConfig (slab 3 k)) (v : slab 3 k) : Prop :=
  ∃ s' ∈ slabLift k G.src', ω ∈ openConnIn (slabLift k G.small) v s'

/-- Opening edges preserves `{x ↔ y in S}`. [folklore] -/
theorem openConnIn_mono_config {V : Type*} {ω ω' : BondConfig V} (h : ω ⊆ ω') {S : Set V} {x y : V}
    (hxy : ω ∈ openConnIn S x y) : ω' ∈ openConnIn S x y := by
  rw [mem_openConnIn_iff_pathIn] at hxy ⊢
  exact hxy.mono_graph (openGraph_mono h)

/-- **The first crossing vertex** (DST 2016, §2.3, proof of Fact 1, second half): for `ω ∈ 𝒳` a
lattice configuration and an open self-avoiding path `π` from `S̄'_n` inside `B̄'_n` (in a
sub-configuration `ω' ⊆ ω`) meeting a column of `γ_min(ω)`, the first vertex `x₁` of `π` in such a
column and its predecessor `x₀` satisfy: `s(x₀, x₁)` is `ω'`-open, the column of `x₁` is a point of
`U'(ω) ⊆ U(ω)` (witnessed by the initial segment of `π`, which runs off the columns of `γ_min`,
starts in `S̄'_n` and ends at `x₀`, a planar lattice step away from `x₁`), and `x₀` is joined to
`S̄'_n` inside `B̄'_n`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
theorem GlueGeom.exists_closed_edge (G : GlueGeom) {ω ω' : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) (hω' : ω' ⊆ ω) (hX : ω ∈ G.evX k) {Y : Set (slab 3 k)}
    {π : List (slab 3 k)} (hπ : IsOSAP k ω' (slabLift k G.small) (slabLift k G.src') Y π)
    (hmeet : ∃ x ∈ π, planar k x ∈ G.γcols k ω) :
    ∃ x₀ x₁, s(x₀, x₁) ∈ ω' ∧ planar k x₁ ∈ G.U' k ω ∧ G.JoinedSrc' k ω x₀ := by
  obtain ⟨⟨⟨hA, -⟩, -⟩, hC⟩ := hX
  obtain ⟨l₁, x₁, l₂, hsplit, hx₁, hl₁⟩ := exists_first_split π hmeet
  -- `l₁` is non-empty: the start of `π` lies over `S'_n`, off the columns of `γ_min`
  have hl₁ne : l₁ ≠ [] := by
    rintro rfl
    have hhead : x₁ ∈ slabLift k G.src' := by
      have := hπ.head_mem hπ.ne_nil
      simp only [hsplit, List.nil_append, List.head_cons] at this
      exact this
    obtain ⟨v, hv, hveq⟩ := hx₁
    exact hC (G.evC_of_mem_γmin_of_src' k hA hv (by rw [mem_slabLift_iff, hveq]; exact hhead))
  obtain ⟨b, l₁', hb⟩ := List.exists_cons_of_ne_nil hl₁ne
  set x₀ := l₁.getLast hl₁ne with hx₀
  have hx₀l₁ : x₀ ∈ l₁ := List.getLast_mem hl₁ne
  -- the chain structure of `π = l₁ ++ x₁ :: l₂`
  have hchain := hπ.chain
  rw [hsplit, List.isChain_append] at hchain
  obtain ⟨hc₁, -, hlink⟩ := hchain
  have hR : s(x₀, x₁) ∈ ω' ∧ x₀ ≠ x₁ :=
    hlink x₀ (by rw [List.getLast?_eq_some_getLast hl₁ne, hx₀]; exact Option.mem_some_iff.2 rfl) x₁ (by simp)
  have hmemπ : ∀ v ∈ l₁, v ∈ π := fun v hv => by rw [hsplit]; exact List.mem_append_left _ hv
  have hx₁π : x₁ ∈ π := by rw [hsplit]; simp
  -- `x₀ x₁` is a planar step
  have hadj : (slabGraph 3 k).Adj x₀ x₁ := (SimpleGraph.mem_edgeSet _).1 (hω (hω' hR.1))
  have hpadj : planarAdj (planar k x₀) (planar k x₁) := by
    rcases (zdGraph_three_adj_iff x₀.1 x₁.1).1 hadj with ⟨-, hpa⟩ | ⟨hpe, -⟩
    · exact hpa
    · exfalso
      have hpe' : planar k x₀ = planar k x₁ := hpe
      exact hl₁ x₀ hx₀l₁ (hpe' ▸ hx₁)
  -- the initial segment joins `b ∈ S̄'_n` to `x₀` off the columns of `γ_min`
  have hb_src : b ∈ slabLift k G.src' := by
    have := hπ.head_mem hπ.ne_nil
    simp only [hsplit, hb, List.cons_append, List.head_cons] at this
    exact this
  have hseg : ω' ∈ openConnIn (slabLift k G.small ∩ {v | planar k v ∉ G.γcols k ω}) b x₀ := by
    have hc₁' : (b :: l₁').IsChain (fun a c => s(a, c) ∈ ω' ∧ a ≠ c) := hb ▸ hc₁
    refine openConnIn_head_of_mem b l₁' hc₁' (fun v hv => ?_) x₀ (hb ▸ hx₀l₁)
    have hv' : v ∈ l₁ := hb ▸ hv
    exact ⟨hπ.subset v (hmemπ v hv'), hl₁ v hv'⟩
  have hseg' : ω ∈ openConnIn (slabLift k G.small ∩ {v | planar k v ∉ G.γcols k ω}) x₀ b :=
    openConnIn_mono_config hω' (openConnIn_reverse hseg)
  refine ⟨x₀, x₁, hR.1, ⟨hπ.subset x₁ hx₁π, hx₁, x₀, hpadj, b, hb_src, hseg'⟩, b, hb_src,
    openConnIn_mono Set.inter_subset_left _ _ hseg'⟩

/-- **The set of edges closed by the map of Fact 1** (DST 2016, §2.3, proof of Fact 1: "closing,
for any `z ∈ U(ω)`, all the edges `{u, v}` such that `u ∈ \overline{\{z\}}` and `v` is connected
to `S̄'_n` by an open path" — inside `B̄'_n`; here at the columns of `U'(ω) ⊆ U(ω)`, which is where
the crossing vertices lie). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
def GlueGeom.closeSet (G : GlueGeom) (ω : BondConfig (slab 3 k)) : Set (Sym2 (slab 3 k)) :=
  {e | e ∈ ω ∧ ∃ u v, e = s(u, v) ∧ planar k u ∈ G.U' k ω ∧ G.JoinedSrc' k ω v}

/-- **The map `Φ` of Fact 1**: `ω ↦ ω'`, all the edges of `closeSet ω` being closed.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1, the map Φ)] -/
def GlueGeom.phi1 (G : GlueGeom) (ω : BondConfig (slab 3 k)) : BondConfig (slab 3 k) :=
  ω \ G.closeSet k ω

/-- `Φ(ω) ⊆ ω`. [folklore] -/
theorem GlueGeom.phi1_subset (G : GlueGeom) (ω : BondConfig (slab 3 k)) : G.phi1 k ω ⊆ ω :=
  Set.sdiff_subset

/-- On `𝒳`, no edge joining two vertices of `γ_min(ω)` is closed by `Φ` ("P1 guarantees that no
edge of `γ_min(ω')` was closed in the process": a closed edge has an endpoint joined to `S̄'_n`,
which on `γ_min` would give `C`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
theorem GlueGeom.not_mem_closeSet_of_mem_γmin (G : GlueGeom) {ω : BondConfig (slab 3 k)}
    (hX : ω ∈ G.evX k) {a b : slab 3 k} (ha : a ∈ G.γmin k ω) (hb : b ∈ G.γmin k ω) :
    s(a, b) ∉ G.closeSet k ω := by
  obtain ⟨⟨⟨hA, -⟩, -⟩, hC⟩ := hX
  rintro ⟨-, u, v, heq, -, s', hs', hj⟩
  have hv : v ∈ G.γmin k ω := by
    have : v ∈ s(a, b) := by rw [heq]; exact Sym2.mem_mk_right u v
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact ha
    · exact hb
  exact hC (G.evC_of_mem_γmin_of_joined k hA hv hs' hj)

/-- On `𝒳`, `γ_min(ω)` is `Φ(ω)`-open, hence `γ_min(Φ(ω)) = γ_min(ω)`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1: γ_min(ω') = γ_min(ω))] -/
theorem GlueGeom.γmin_phi1 (G : GlueGeom) {ω : BondConfig (slab 3 k)} (hX : ω ∈ G.evX k) :
    G.γmin k (G.phi1 k ω) = G.γmin k ω := by
  have hA : ω ∈ G.evA k := hX.1.1.1
  have hγ := (G.γmin_spec k hA).1
  refine minPath_eq_of_subset (G.phi1_subset k ω) (G.big_finite k)
    ((mem_slabConn_iff_exists_isOSAP ω _ _ _).1 hA) (hγ.of_edges fun a ha b hb hab => ?_)
  exact ⟨hab, G.not_mem_closeSet_of_mem_γmin k hX ha hb⟩

/-- The edges off the columns of `γ_min` are untouched by `Φ`. [folklore] -/
theorem GlueGeom.mem_phi1_iff_of_off (G : GlueGeom) {ω : BondConfig (slab 3 k)} {e : Sym2 (slab 3 k)}
    (he : e ∈ (slabLift k G.small ∩ {v | planar k v ∉ G.γcols k ω}).sym2) :
    e ∈ ω ↔ e ∈ G.phi1 k ω := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  rintro ⟨-, u, v, rfl, hu, -⟩
  have hu' := (Set.mk_mem_sym2_iff.1 he).1
  exact hu'.2 (G.U_subset_γcols k ω (G.U'_subset_U k ω hu))

/-- On `𝒳`, `U'(Φ(ω)) = U'(ω)`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1: U(ω') = U(ω))] -/
theorem GlueGeom.U'_phi1 (G : GlueGeom) {ω : BondConfig (slab 3 k)} (hX : ω ∈ G.evX k) :
    G.U' k (G.phi1 k ω) = G.U' k ω := by
  have hcols : G.γcols k (G.phi1 k ω) = G.γcols k ω := by
    simp only [GlueGeom.γcols, G.γmin_phi1 k hX]
  ext z
  simp only [GlueGeom.U', Set.mem_setOf_eq, hcols]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine exists_congr fun x₀ => and_congr_right fun _ => exists_congr fun s' =>
    and_congr_right fun _ => ?_
  exact (openConnIn_congr (fun e he => G.mem_phi1_iff_of_off k he) x₀ s').symm

/-- **`Φ` blocks `B⁻ ∩ B⁺`** (DST 2016, §2.3, proof of Fact 1: "`ω'` cannot contain two open paths
in `B̄'_n` from `S̄'_n` to `Ȳ_n^-` and `Ȳ_n^+` respectively … one edge of one of these two paths
was turned to closed in `ω'`, which is a contradiction"): for `ω ∈ 𝒳` a lattice configuration,
`Φ(ω) ∉ B⁻ ∩ B⁺`. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (proof of Fact 1)] -/
theorem GlueGeom.phi1_not_mem (G : GlueGeom) (hG : G.InRange) {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) (hX : ω ∈ G.evX k) : G.phi1 k ω ∉ G.evBm k ∩ G.evBp k := by
  rintro ⟨hBm, hBp⟩
  obtain ⟨πm, hπm⟩ := (mem_slabConn_iff_exists_isOSAP _ _ _ _).1 hBm
  obtain ⟨πp, hπp⟩ := (mem_slabConn_iff_exists_isOSAP _ _ _ _).1 hBp
  obtain ⟨x, hx, hxcol⟩ := G.exists_mem_γcols k hG hω (G.phi1_subset k ω) hX hπm hπp
  -- the first crossing vertex on the relevant path gives an edge of `closeSet ω` open in `Φ(ω)`
  have key : ∀ {Y : Set (slab 3 k)} {π : List (slab 3 k)},
      IsOSAP k (G.phi1 k ω) (slabLift k G.small) (slabLift k G.src') Y π →
      (∃ x ∈ π, planar k x ∈ G.γcols k ω) → False := by
    intro Y π hπ hmeet
    obtain ⟨x₀, x₁, hopen, hU, hj⟩ := G.exists_closed_edge k hω (G.phi1_subset k ω) hX hπ hmeet
    have hclosed : s(x₀, x₁) ∈ G.closeSet k ω :=
      ⟨hopen.1, x₁, x₀, Sym2.eq_swap, hU, hj⟩
    exact hopen.2 hclosed
  rcases hx with hx | hx
  · exact key hπm ⟨x, hx, hxcol⟩
  · exact key hπp ⟨x, hx, hxcol⟩

/-- The closed edges lie at the columns of `U'(Φ(ω))`. [folklore] -/
theorem GlueGeom.diff_phi1_subset (G : GlueGeom) {ω : BondConfig (slab 3 k)} (hX : ω ∈ G.evX k) :
    ω \ G.phi1 k ω ⊆ {e | ∃ u ∈ e, planar k u ∈ G.U' k (G.phi1 k ω)} := by
  rintro e ⟨he, hne⟩
  have he' : e ∈ G.closeSet k ω := by
    by_contra h
    exact hne ⟨he, h⟩
  obtain ⟨-, u, v, rfl, hu, -⟩ := he'
  exact ⟨u, Sym2.mem_mk_left u v, by rw [G.U'_phi1 k hX]; exact hu⟩

end Closing

/-! ## Counting the edges at a column -/

section ColumnEdges

variable (k : ℕ)

/-- The vertex of height `min h k` over the planar point `z` (a total version of `slabVertex`).
[folklore] -/
def vtx (z : ℤ × ℤ) (h : ℕ) : slab 3 k :=
  ⟨![((min h k : ℕ) : ℤ), z.1, z.2], ⟨by simp, by
    have : ((min h k : ℕ) : ℤ) ≤ k := by exact_mod_cast min_le_right h k
    exact this⟩⟩

/-- A slab vertex of height `h` is `vtx` of its planar part and `h`. [folklore] -/
theorem eq_vtx_of_height {a : slab 3 k} {h : ℕ} (hh : a.1 0 = h) : a = vtx k (planar k a) h := by
  have hk : h ≤ k := by have := a.2.2; rw [hh] at this; exact_mod_cast this
  apply Subtype.ext
  funext j
  fin_cases j
  · simp [vtx, Nat.min_eq_left hk, hh]
  · simp [vtx, planar]
  · simp [vtx, planar]

/-- Every slab vertex has a natural-number height. [folklore] -/
theorem exists_height (a : slab 3 k) : ∃ h : ℕ, a.1 0 = h :=
  ⟨(a.1 0).toNat, (Int.toNat_of_nonneg a.2.1).symm⟩

/-- The four planar unit vectors. [folklore] -/
def dirs : Fin 4 → ℤ × ℤ := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

/-- Planar adjacency means differing by one of the four unit vectors. [folklore] -/
theorem exists_dirs_of_planarAdj {z w : ℤ × ℤ} (h : planarAdj z w) : ∃ i, w = z + dirs i := by
  obtain ⟨z1, z2⟩ := z
  obtain ⟨w1, w2⟩ := w
  simp only [planarAdj, Prod.mk_add_mk, Prod.mk.injEq, add_zero] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact ⟨0, by simp [dirs]; omega⟩
  · exact ⟨1, by simp [dirs]; omega⟩
  · exact ⟨2, by simp [dirs]; omega⟩
  · exact ⟨3, by simp [dirs]; omega⟩

/-- An explicit list of the lattice edges at the column over `z`: the `4(k+1)` planar ones and
the `k` vertical ones. [folklore] -/
def colCover (z : ℤ × ℤ) : Finset (Sym2 (slab 3 k)) :=
  ((Finset.range (k + 1) ×ˢ (Finset.univ : Finset (Fin 4))).image
      fun q => s(vtx k z q.1, vtx k (z + dirs q.2) q.1)) ∪
    (Finset.range k).image fun h => s(vtx k z h, vtx k z (h + 1))

/-- `|colCover z| ≤ 5k + 4`. [folklore] -/
theorem card_colCover_le (z : ℤ × ℤ) : (colCover k z).card ≤ 5 * k + 4 := by
  classical
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Finset.range (k + 1) ×ˢ (Finset.univ : Finset (Fin 4)))
    (f := fun q : ℕ × Fin 4 => s(vtx k z q.1, vtx k (z + dirs q.2) q.1))
  have h2 := Finset.card_image_le (s := Finset.range k) (f := fun h => s(vtx k z h, vtx k z (h + 1)))
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin] at h1
  rw [Finset.card_range] at h2
  omega

/-- A lattice edge at the column over `z` belongs to `colCover z`. [folklore] -/
theorem mem_colCover_of_adj {z : ℤ × ℤ} {a b : slab 3 k} (hadj : (slabGraph 3 k).Adj a b)
    (ha : planar k a = z) : s(a, b) ∈ colCover k z := by
  classical
  obtain ⟨h, hh⟩ := exists_height k a
  have hak : h ≤ k := by have := a.2.2; rw [hh] at this; exact_mod_cast this
  have hav : a = vtx k z h := ha ▸ eq_vtx_of_height k hh
  rcases (zdGraph_three_adj_iff a.1 b.1).1 hadj with ⟨h0, hpa⟩ | ⟨hpe, h0⟩
  · -- planar step at height `h`
    have hpa' : planarAdj (planar k a) (planar k b) := hpa
    obtain ⟨i, hi⟩ := exists_dirs_of_planarAdj hpa'
    have hbh : b.1 0 = h := by rw [h0, hh]
    have hbv : b = vtx k (z + dirs i) h := by rw [← ha, ← hi]; exact eq_vtx_of_height k hbh
    refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨(h, i), ?_, by rw [hav, hbv]⟩)
    simp [Finset.mem_range, hak]
  · -- vertical step
    have hpe' : planar k a = planar k b := hpe
    rcases h0 with h0 | h0
    · -- `b` is above `a`
      have hbh : b.1 0 = (h + 1 : ℕ) := by rw [h0, hh]; push_cast; ring
      have hbk : h + 1 ≤ k := by have := b.2.2; rw [hbh] at this; exact_mod_cast this
      have hbv : b = vtx k z (h + 1) := by rw [← ha, hpe']; exact eq_vtx_of_height k hbh
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨h, ?_, by rw [hav, hbv]⟩)
      simp [Finset.mem_range]; omega
    · -- `b` is below `a`
      obtain ⟨h', hh'⟩ := exists_height k b
      have hah : (h : ℤ) = h' + 1 := by rw [← hh, h0, hh']
      have hh1 : h = h' + 1 := by exact_mod_cast hah
      have hbv : b = vtx k z h' := by rw [← ha, hpe']; exact eq_vtx_of_height k hh'
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨h', ?_, ?_⟩)
      · simp [Finset.mem_range]; omega
      · rw [hav, hbv, hh1, Sym2.eq_swap]

/-- **At most `(5k+4)·|U|` lattice edges have an endpoint in a column of `U`.** [folklore] -/
theorem card_filter_colEdges_le (K : Finset (Sym2 (slab 3 k)))
    (hK : ∀ e ∈ K, e ∈ (slabGraph 3 k).edgeSet) (Uz : Finset (ℤ × ℤ))
    [DecidablePred fun e : Sym2 (slab 3 k) => ∃ u ∈ e, planar k u ∈ Uz] :
    (K.filter fun e => ∃ u ∈ e, planar k u ∈ Uz).card ≤ (5 * k + 4) * Uz.card := by
  classical
  have hsub : (K.filter fun e => ∃ u ∈ e, planar k u ∈ Uz) ⊆ Uz.biUnion (colCover k) := by
    intro e he
    obtain ⟨heK, u, hue, huz⟩ := Finset.mem_filter.1 he
    rw [Finset.mem_biUnion]
    refine ⟨planar k u, huz, ?_⟩
    have hE := hK e heK
    induction e using Sym2.ind with
    | h a b =>
      have hadj : (slabGraph 3 k).Adj a b := (SimpleGraph.mem_edgeSet _).1 hE
      rcases Sym2.mem_iff.1 hue with rfl | rfl
      · exact mem_colCover_of_adj k hadj rfl
      · rw [Sym2.eq_swap]
        exact mem_colCover_of_adj k hadj.symm rfl
  calc (K.filter fun e => ∃ u ∈ e, planar k u ∈ Uz).card ≤ (Uz.biUnion (colCover k)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ z ∈ Uz, (colCover k z).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ Uz, (5 * k + 4) := Finset.sum_le_sum fun z _ => card_colCover_le k z
    _ = (5 * k + 4) * Uz.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

end ColumnEdges

/-! ## Determinacy by the window and the proof of Fact 1 -/

section Fact1Proof

variable {k : ℕ}

/-- Configurations agreeing on the pairs inside `S` have the same open self-avoiding paths inside
`S`. [folklore] -/
theorem isOSAP_congr {ω ω' : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)}
    (h : ∀ e ∈ S.sym2, e ∈ ω ↔ e ∈ ω') (l : List (slab 3 k)) :
    IsOSAP k ω S X Y l ↔ IsOSAP k ω' S X Y l :=
  ⟨fun hl => hl.of_edges fun a ha b hb hab => (h _ (Set.mk_mem_sym2_iff.2 ⟨hl.subset a ha, hl.subset b hb⟩)).1 hab,
   fun hl => hl.of_edges fun a ha b hb hab => (h _ (Set.mk_mem_sym2_iff.2 ⟨hl.subset a ha, hl.subset b hb⟩)).2 hab⟩

/-- Configurations agreeing on the pairs inside a finite `S` have the same minimal path. [folklore] -/
theorem minPath_congr {ω ω' : BondConfig (slab 3 k)} {S X Y : Set (slab 3 k)} (hS : S.Finite)
    (h : ∀ e ∈ S.sym2, e ∈ ω ↔ e ∈ ω') : minPath k ω S X Y = minPath k ω' S X Y := by
  by_cases hex : ∃ l, IsOSAP k ω S X Y l
  · obtain ⟨h1, h2⟩ := minPath_spec hS hex
    symm
    exact minPath_eq_of_min hS ((isOSAP_congr h _).1 h1) fun l' hl' => h2 l' ((isOSAP_congr h _).2 hl')
  · rw [minPath_eq_nil hex, minPath_eq_nil]
    rintro ⟨l, hl⟩
    exact hex ⟨l, (isOSAP_congr h _).2 hl⟩

variable (k)

/-- Configurations agreeing on the pairs inside `\overline{B_{3n} ∪ B'_n}` have the same `U`.
[folklore] -/
theorem GlueGeom.U_congr (G : GlueGeom) {ω ω' : BondConfig (slab 3 k)}
    (h : ∀ e ∈ (slabLift k (G.big ∪ G.small)).sym2, e ∈ ω ↔ e ∈ ω') : G.U k ω = G.U k ω' := by
  have hγ : G.γmin k ω = G.γmin k ω' :=
    minPath_congr (G.big_finite k) fun e he => h e (sym2_mono (slabLift_mono k Set.subset_union_left) he)
  have hcols : G.γcols k ω = G.γcols k ω' := by simp only [GlueGeom.γcols, hγ]
  ext z
  simp only [GlueGeom.U, Set.mem_setOf_eq, hcols]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine exists_congr fun x₀ => and_congr_right fun _ => exists_congr fun s' =>
    and_congr_right fun _ => ?_
  exact openConnIn_congr (fun e he => h e (sym2_mono
    (Set.inter_subset_left.trans (slabLift_mono k Set.subset_union_right)) he)) x₀ s'

/-- Configurations agreeing on the pairs inside `\overline{B_{3n} ∪ B'_n}` have the same `U'`.
[folklore] -/
theorem GlueGeom.U'_congr (G : GlueGeom) {ω ω' : BondConfig (slab 3 k)}
    (h : ∀ e ∈ (slabLift k (G.big ∪ G.small)).sym2, e ∈ ω ↔ e ∈ ω') : G.U' k ω = G.U' k ω' := by
  have hγ : G.γmin k ω = G.γmin k ω' :=
    minPath_congr (G.big_finite k) fun e he => h e (sym2_mono (slabLift_mono k Set.subset_union_left) he)
  have hcols : G.γcols k ω = G.γcols k ω' := by simp only [GlueGeom.γcols, hγ]
  ext z
  simp only [GlueGeom.U', Set.mem_setOf_eq, hcols]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  refine exists_congr fun x₀ => and_congr_right fun _ => exists_congr fun s' =>
    and_congr_right fun _ => ?_
  exact openConnIn_congr (fun e he => h e (sym2_mono
    (Set.inter_subset_left.trans (slabLift_mono k Set.subset_union_right)) he)) x₀ s'

/-- The events `X ⟷^B Y` with `B ⊆ B_{3n} ∪ B'_n` only depend on the window. [folklore] -/
theorem mem_slabConn_congr (G : GlueGeom) {ω ω' : BondConfig (slab 3 k)}
    (h : ∀ e ∈ (slabLift k (G.big ∪ G.small)).sym2, e ∈ ω ↔ e ∈ ω') {B : Set (ℤ × ℤ)}
    (hB : B ⊆ G.big ∪ G.small) (X Y : Set (ℤ × ℤ)) :
    ω ∈ slabConn k B X Y ↔ ω' ∈ slabConn k B X Y := by
  have hd := determinedBy_slabConn k X Y hB
  rw [determinedBy_iff] at hd
  refine hd ω ω' (Set.ext fun e => ⟨fun he => ⟨(h e he.2).1 he.1, he.2⟩, fun he => ⟨(h e he.2).2 he.1, he.2⟩⟩)

/-- **DST 2016, §2.3, Fact 1, for `U'`**:
`P[𝒳 ∩ {|U'| < t}] ≤ (2/min{p,1-p})^{(5k+4)t} · P[{B⁻ ∩ B⁺}ᶜ]`. Proof as printed: the map
`Φ : ω ↦ ω'` closing the edges at the columns of `U'(ω)` whose other endpoint is joined to
`S̄'_n` (`phi1`) sends `𝒳 ∩ {|U| < t}` into `{B⁻ ∩ B⁺}ᶜ` (`phi1_not_mem`, by the planar
crossing fact), satisfies `γ_min(Φ ω) = γ_min(ω)` and `U'(Φ ω) = U'(ω)` (`γmin_phi1`, `U'_phi1`),
so that the preimages of `ω'` agree with `ω'` off the at most `(5k+4)·t` lattice edges at the
columns of `U'(ω')` (`diff_phi1_subset`, `card_filter_colEdges_le`); Lemma 7 (`lemma7_bond`, with
`t = 1`) concludes. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Fact 1 and its proof)] -/
theorem fact1_U' (k : ℕ) (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (G : GlueGeom) (hG : G.InRange) (t : ℕ) :
    (bondPercolation (slabGraph 3 k) p).real (G.evX k ∩ {ω | (G.U' k ω).ncard < t}) ≤
      (2 / min (p : ℝ) (1 - p)) ^ ((5 * k + 4) * t) *
        (bondPercolation (slabGraph 3 k) p).real (G.evBm k ∩ G.evBp k)ᶜ := by
  classical
  set P := bondPercolation (slabGraph 3 k) p with hP
  -- the window
  have hRfin : (slabLift k (G.big ∪ G.small)).Finite :=
    slabLift_finite k ((sqBox_finite _ _).union (sqBox_finite _ _))
  set K' : Finset (Sym2 (slab 3 k)) := (finite_sym2 hRfin).toFinset with hK'def
  have hK'coe : (↑K' : Set (Sym2 (slab 3 k))) = (slabLift k (G.big ∪ G.small)).sym2 :=
    Set.Finite.coe_toFinset _
  set Kfin : Finset (Sym2 (slab 3 k)) := K'.filter (· ∈ (slabGraph 3 k).edgeSet) with hKfin
  have hK : ∀ e, e ∈ Kfin ↔ e ∈ K' ∧ e ∈ (slabGraph 3 k).edgeSet := fun e => Finset.mem_filter
  have hKE : ∀ e ∈ Kfin, e ∈ (slabGraph 3 k).edgeSet := fun e he => ((hK e).1 he).2
  -- agreement on the window
  have hagree : ∀ ω ω' : BondConfig (slab 3 k), ω ∩ ↑K' = ω' ∩ ↑K' →
      ∀ e ∈ (slabLift k (G.big ∪ G.small)).sym2, e ∈ ω ↔ e ∈ ω' := by
    intro ω ω' heq e he
    rw [← hK'coe] at he
    have := Set.ext_iff.1 heq e
    simp only [Set.mem_inter_iff, he, and_true] at this
    exact this
  -- determinacy of the two events
  have hXdet : ∀ ω ω' : BondConfig (slab 3 k), ω ∩ ↑K' = ω' ∩ ↑K' → (ω ∈ G.evX k ↔ ω' ∈ G.evX k) := by
    intro ω ω' heq
    have h := hagree ω ω' heq
    simp only [GlueGeom.evX, GlueGeom.evA, GlueGeom.evBm, GlueGeom.evBp, GlueGeom.evC,
      Set.mem_inter_iff, Set.mem_compl_iff]
    rw [mem_slabConn_congr k G h Set.subset_union_left, mem_slabConn_congr k G h Set.subset_union_right,
      mem_slabConn_congr k G h Set.subset_union_right, mem_slabConn_congr k G h subset_rfl]
  have hA : DeterminedBy (G.evX k ∩ {ω | (G.U' k ω).ncard < t}) ↑K' := by
    rw [determinedBy_iff]
    intro ω ω' heq
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hXdet ω ω' heq, G.U'_congr k (hagree ω ω' heq)]
  have hB : DeterminedBy (G.evBm k ∩ G.evBp k)ᶜ ↑K' := by
    rw [determinedBy_iff]
    intro ω ω' heq
    have h := hagree ω ω' heq
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, GlueGeom.evBm, GlueGeom.evBp]
    rw [mem_slabConn_congr k G h Set.subset_union_right, mem_slabConn_congr k G h Set.subset_union_right]
  -- the map, on lattice configurations inside the window
  let Φ : Finset (Sym2 (slab 3 k)) → Finset (Finset (Sym2 (slab 3 k))) :=
    fun S => {S.filter (· ∉ G.closeSet k ↑S)}
  have hΦcoe : ∀ S : Finset (Sym2 (slab 3 k)),
      (↑(S.filter (· ∉ G.closeSet k ↑S)) : Set (Sym2 (slab 3 k))) = G.phi1 k ↑S := by
    intro S
    ext e
    simp [GlueGeom.phi1]
  have hmain := lemma7_bond (slabGraph 3 k) p hp0 hp1 K' Kfin hK hA hB ((5 * k + 4) * t)
    one_pos Φ ?_ ?_ ?_
  · simpa using hmain
  · -- images lie in `B`
    intro S hS hSA S' hS'
    have hS'eq : S' = S.filter (· ∉ G.closeSet k ↑S) := Finset.mem_singleton.1 hS'
    subst hS'eq
    refine ⟨(Finset.filter_subset _ S).trans hS, ?_⟩
    rw [hΦcoe]
    exact G.phi1_not_mem k hG (fun e he => hKE e (hS he)) hSA.1
  · -- one image
    intro S _ _
    simp [Φ]
  · -- preimages agree off the edges at the columns of `U(ω')`
    intro S' hS' _
    by_cases hsmall : (G.U' k ↑S').ncard < t
    · refine ⟨Kfin.filter fun e => ∃ u ∈ e, planar k u ∈ (G.U'_finite k (↑S' : BondConfig (slab 3 k))).toFinset, ?_, ?_⟩
      · refine (card_filter_colEdges_le k Kfin hKE _).trans ?_
        rw [← Set.ncard_eq_toFinset_card _ (G.U'_finite k (↑S' : BondConfig (slab 3 k)))]
        exact Nat.mul_le_mul_left _ hsmall.le
      · intro S hS hSA hmem e heT
        have hS'eq : S' = S.filter (· ∉ G.closeSet k ↑S) := Finset.mem_singleton.1 hmem
        constructor
        · intro heS
          by_contra heS'
          apply heT
          have hdiff : e ∈ (↑S : Set (Sym2 (slab 3 k))) \ G.phi1 k ↑S := by
            refine ⟨heS, ?_⟩
            rw [← hΦcoe, ← hS'eq]
            exact heS'
          obtain ⟨u, hue, hu⟩ := G.diff_phi1_subset k hSA.1 hdiff
          rw [← hΦcoe, ← hS'eq] at hu
          exact Finset.mem_filter.2 ⟨hS heS, u, hue, (Set.Finite.mem_toFinset _).2 hu⟩
        · intro heS'
          rw [hS'eq] at heS'
          exact (Finset.mem_filter.1 heS').1
    · refine ⟨∅, by simp, ?_⟩
      intro S hS hSA hmem
      exfalso
      apply hsmall
      have hS'eq : S' = S.filter (· ∉ G.closeSet k ↑S) := Finset.mem_singleton.1 hmem
      rw [hS'eq, hΦcoe, G.U'_phi1 k hSA.1]
      exact hSA.2

/-- **DST 2016, §2.3, Fact 1** in the form `DuminilCopinSidoraviciusTassion2016_fact1`:
`P[𝒳 ∩ {|U| < t}] ≤ (2/min{p,1-p})^{(5k+4)t} · P[{B⁻ ∩ B⁺}ᶜ]`, from `fact1_U'` and `|U'| ≤ |U|`.
[cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Fact 1)] -/
theorem DuminilCopinSidoraviciusTassion2016_fact1_holds : DuminilCopinSidoraviciusTassion2016_fact1 := by
  intro k _ p hp0 hp1 G hG t
  refine le_trans (measureReal_mono ?_) (fact1_U' k p hp0 hp1 G hG t)
  rintro ω ⟨hX, ht⟩
  exact ⟨hX, lt_of_le_of_lt (G.ncard_U'_le k ω) ht⟩

end Fact1Proof

end Percolation.Literature
