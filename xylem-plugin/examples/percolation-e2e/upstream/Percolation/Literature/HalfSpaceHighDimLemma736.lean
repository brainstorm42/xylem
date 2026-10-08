import Percolation.Literature.HalfSpaceHighDimSymmetry
import Percolation.Util.Linter

/-!
# Lemma (7.36) in `ℤ^d` for valid seed rules, at every density: the assembly

> "Let `η > 0`, and choose `ε` such that `η = 4(4ε)^{1/4} + 8(2ε)^{1/8}`. It follows from the
> above that `P_{p_c}(B(L,H) is not good) ≤ P_{p_c}(either X_j = 0 for some j, or Y_i = 0 for some
> i) < 4(4ε)^{1/4} + 8(2ε)^{1/8} = η`, as required."

* `BGNd.prob_compl_goodR_le_of_estimates` — the last step for a valid rule: if
  `P(U < M) + (1-p^K)^{N₁} ≤ t^{2^{d-1}}` and `P(V^a < M) + (1-p^K)^{N₁} ≤ t^{2^{d-1}}` for all
  horizontal `a`, `M ≥ N₁ |B(r)|`, then `P(not goodR) ≤ (2^{d-1} + (d-1)2^{d-1}) t`;
* `BGN.exists_fineTuning'` — the abstract fine tuning (7.43)–(7.44) of `HalfSpaceBrickUp.lean`
  with the minimality of `H₁(l)` recorded (`c < a l h` for all `H₀ ≤ h < H₁ l`, `l ≥ L₀`);
* `BGNd.topGoodR` — the top half of the good event (an ok vertex in every top subfacet) and its
  estimate `BGNd.prob_compl_topGoodR_le_of_estimate`;
* `BGNd.lemma_7_36R` — **Lemma (7.36) for a family of valid seed rules, at every density**
  (Grimmett, p. 164: "It is valid for general `p` but we shall require it for `p = p_c` only";
  BGN 1991 Prop. 2.1): for `d ≥ 2`, `0 < p < 1` with `θ_ℍ(p) > 0` and `η > 0` there are `m ≥ 1`,
  `H₀ ≥ max(2m, Hmin m)`, `L ≥ max(m, Lreq m H₀)`, `H > H₀` with `P_p(goodR on B(L,H)) > 1 - η`
  and, moreover, `P_p(topGoodR on B(L,h)) > 1 - η` for EVERY height `H₀ < h ≤ H` (the bricks of
  intermediate height have many linked top vertices by the minimality of the fine-tuned height
  `H = H₁(L)`, Grimmett's (7.43); this by-product of the printed proof is recorded for the block
  construction of Lemma (7.52), and `Lreq` lets the user ask for `L` large in terms of `H₀`). The
  constants are chosen in Grimmett's order `ε, m, N₁, M, g, N₂, H₀, L₀, H₁, L₁, L`; the binomial
  estimate (7.40) is replaced by the grouping bound, no slab input is needed (the bounded-height
  null event of `HalfSpaceHighDimBounded.lean` replaces (7.38)), and the `d - 1` facet counts
  enter the FKG step through `ε = min(…, s^{d-1})`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.3, Lemma (7.36) and
  its proof, pp. 164–169.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Probab. Theory Related Fields 90 (1991) 111–148,
  §2, Prop. 2.1, pp. 120–128.
-/

noncomputable section

namespace Percolation.Literature

open _root_.MeasureTheory _root_.ProbabilityTheory _root_.Filter LatticeModels unitInterval
open scoped _root_.ENNReal _root_.Topology

namespace BGN

/-- [cite: GrimmettPercolation1999, §7.3 p. 166 (7.43)–(7.44)] -/
theorem exists_fineTuning' {a : ℕ → ℕ → ℝ} {c : ℝ} {H₀ L₀ : ℕ}
    (hmono : ∀ h l l', l ≤ l' → a l h ≤ a l' h)
    (hzero : ∀ l, ∀ᶠ h in atTop, a l h ≤ c)
    (hH₀ : ∀ l, L₀ ≤ l → c < a l H₀)
    (hlarge : ∀ h, H₀ ≤ h → ∀ᶠ l in atTop, c < a l h) :
    ∃ H₁ : ℕ → ℕ, (∀ l, H₀ < H₁ l ∧ a l (H₁ l) ≤ c) ∧ (∀ l, L₀ ≤ l → ∀ h, H₀ ≤ h → h < H₁ l → c < a l h) ∧
      Monotone H₁ ∧ Tendsto H₁ atTop atTop := by
  classical
  have hex : ∀ l, ∃ h, H₀ < h ∧ a l h ≤ c := by
    intro l
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hzero l)
    exact ⟨max N (H₀ + 1), by omega, hN _ (le_max_left _ _)⟩
  refine ⟨fun l => Nat.find (hex l), fun l => Nat.find_spec (hex l), fun l hl h hh hlt => ?_, ?_, ?_⟩
  · -- minimality: `c < a l h` for `H₀ ≤ h < H₁ l`
    rcases hh.eq_or_lt with rfl | hH₀h
    · exact hH₀ l hl
    · have hmin := Nat.find_min (hex l) hlt
      push Not at hmin
      exact lt_of_not_ge fun h' => (hmin hH₀h).not_ge h'
  · -- monotone
    intro l l' hll'
    refine Nat.find_le ⟨(Nat.find_spec (hex l')).1, ?_⟩
    exact (hmono _ l l' hll').trans (Nat.find_spec (hex l')).2
  · -- (7.44): `H₁ l → ∞`; each value is exceeded eventually
    have hstep : ∀ l₀, ∀ᶠ l in atTop, Nat.find (hex l₀) + 1 ≤ Nat.find (hex l) := by
      intro l₀
      have h0 := Nat.find_spec (hex l₀)
      filter_upwards [hlarge (Nat.find (hex l₀)) h0.1.le, eventually_ge_atTop l₀] with l hl hll₀
      have hle : Nat.find (hex l₀) ≤ Nat.find (hex l) := by
        refine Nat.find_le ⟨(Nat.find_spec (hex l)).1, ?_⟩
        exact (hmono _ l₀ l hll₀).trans (Nat.find_spec (hex l)).2
      rcases hle.lt_or_eq with hlt | heq
      · omega
      · exfalso
        have := (Nat.find_spec (hex l)).2
        rw [← heq] at this
        linarith
    rw [tendsto_atTop_atTop]
    intro K
    induction K with
    | zero => exact ⟨0, fun _ _ => Nat.zero_le _⟩
    | succ K ih =>
      obtain ⟨L, hL⟩ := ih
      obtain ⟨L', hL'⟩ := eventually_atTop.1 (hstep L)
      refine ⟨max L L', fun l hl => ?_⟩
      have h1 := hL L le_rfl
      have h2 := hL' l (le_of_max_le_right hl)
      omega

end BGN

namespace BGNd

variable {d : ℕ}

/-- The **top-good event** for the rule `E`: a linked vertex with open rule-edges in each of the
`2^{d-1}` top subfacets (the top half of `goodR`; what a brick used only for top stacking needs).
[cite: GrimmettPercolation1999, §7.3 p. 164 (good (a), (c)), p. 172 (A)] -/
def topGoodR (d : ℕ) [NeZero d] (m L H : ℕ) (E : Site d → Finset (Sym2 (Site d))) : Set (BondConfig (Site d)) :=
  ⋂ ρ : HAxis d → Bool, okEventR d m L H E (topSubfacet d L H ρ)

/-- `goodR ⊆ topGoodR`. [folklore] -/
theorem goodR_subset_topGoodR [NeZero d] (m L H : ℕ) (E : Site d → Finset (Sym2 (Site d))) :
    goodR d m L H E ⊆ topGoodR d m L H E := Set.inter_subset_left

/-- `topGoodR` is measurable. [folklore] -/
theorem measurableSet_topGoodR [NeZero d] (m L H : ℕ) (E : Site d → Finset (Sym2 (Site d))) :
    MeasurableSet (topGoodR d m L H E) :=
  MeasurableSet.iInter fun ρ => measurableSet_okEventR m L H E (topSubfacet d L H ρ)

section Conclusion

variable [NeZero d] {m L H r K : ℕ} {E : Site d → Finset (Sym2 (Site d))}

/-- Union bound: `P(not goodR) ≤ Σ_ρ P(X_ρ = 0) + Σ_{(a,τ)} P(Y_{a,τ} = 0)`. [cite: GrimmettPercolation1999, §7.3 p. 169] -/
theorem prob_compl_goodR_le (m L H : ℕ) (E : Site d → Finset (Sym2 (Site d))) (p : unitInterval) :
    (bondPercolation (zdGraph d) p).real (goodR d m L H E)ᶜ ≤
      ∑ ρ : HAxis d → Bool, (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ +
        ∑ aτ : HAxis d × (HAxis d → Bool),
          (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H aτ.1 aτ.2))ᶜ := by
  have hsub : (goodR d m L H E)ᶜ ⊆ (⋃ ρ : HAxis d → Bool, (okEventR d m L H E (topSubfacet d L H ρ))ᶜ) ∪
      ⋃ aτ : HAxis d × (HAxis d → Bool), (okEventR d m L H E (sideSubfacet d L H aτ.1 aτ.2))ᶜ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff, not_or, not_exists, not_not] at hnot
    exact hω ⟨Set.mem_iInter.2 hnot.1, Set.mem_iInter.2 fun aτ => hnot.2 aτ⟩
  calc (bondPercolation (zdGraph d) p).real (goodR d m L H E)ᶜ
      ≤ (bondPercolation (zdGraph d) p).real ((⋃ ρ : HAxis d → Bool, (okEventR d m L H E (topSubfacet d L H ρ))ᶜ) ∪
          ⋃ aτ : HAxis d × (HAxis d → Bool), (okEventR d m L H E (sideSubfacet d L H aτ.1 aτ.2))ᶜ) :=
        measureReal_mono hsub
    _ ≤ (bondPercolation (zdGraph d) p).real (⋃ ρ : HAxis d → Bool, (okEventR d m L H E (topSubfacet d L H ρ))ᶜ) +
          (bondPercolation (zdGraph d) p).real
            (⋃ aτ : HAxis d × (HAxis d → Bool), (okEventR d m L H E (sideSubfacet d L H aτ.1 aτ.2))ᶜ) :=
        measureReal_union_le _ _
    _ ≤ _ := add_le_add (measureReal_iUnion_fintype_le _) (measureReal_iUnion_fintype_le _)

/-- **The last step for a valid rule**: if `P(U < M) + (1-p^K)^{N₁} ≤ t^{NT}` and
`P(V^a < M) + (1-p^K)^{N₁} ≤ t^{NT}` for all horizontal `a`, where `NT = 2^{d-1}` is the number of
top subfacets and `M ≥ N₁ |B(r)|`, then `P(not goodR) ≤ (NT + NS) t`, `NS = (d-1) 2^{d-1}` the
number of side subfacets. [cite: GrimmettPercolation1999, §7.3 p. 169] -/
theorem prob_compl_goodR_le_of_estimates (hV : SeedRuleValid E L H r K) {M N₁ : ℕ} (hM : N₁ * (box d r).card ≤ M)
    (p : unitInterval) {t : ℝ} (ht : 0 ≤ t)
    (htop : (bondPercolation (zdGraph d) p).real (topCountLT d m L H M) + (1 - (p : ℝ) ^ K) ^ N₁ ≤
      t ^ Fintype.card (HAxis d → Bool))
    (hside : ∀ a : HAxis d,
      (bondPercolation (zdGraph d) p).real (facetCountLT d a.1 m L H M) + (1 - (p : ℝ) ^ K) ^ N₁ ≤
        t ^ Fintype.card (HAxis d → Bool)) :
    (bondPercolation (zdGraph d) p).real (goodR d m L H E)ᶜ ≤
      (Fintype.card (HAxis d → Bool) + Fintype.card (HAxis d × (HAxis d → Bool))) * t := by
  have hNT : Fintype.card (HAxis d → Bool) ≠ 0 := Fintype.card_ne_zero
  have htop' : ∀ ρ : HAxis d → Bool,
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ ≤ t := by
    intro ρ
    refine le_of_pow_le_pow_left₀ hNT ht ((prob_compl_okEventR_topSubfacet_pow_le hV p ρ).trans ?_)
    have hsub : {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω} ⊆
        topCountLT d m L H M ∪ (topCountGE d m L H M ∩ {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω}) := by
      intro ω hω
      by_cases hU : ω ∈ topCountGE d m L H M
      · exact Or.inr ⟨hU, hω⟩
      · left; rwa [topCountLT_eq_compl]
    calc (bondPercolation (zdGraph d) p).real {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω}
        ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m L H M) +
            (bondPercolation (zdGraph d) p).real (topCountGE d m L H M ∩ {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω}) :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m L H M) + (1 - (p : ℝ) ^ K) ^ N₁ :=
          add_le_add le_rfl (prob_topCountGE_inter_noOpen_le hV hM p)
      _ ≤ _ := htop
  have hside' : ∀ aτ : HAxis d × (HAxis d → Bool),
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H aτ.1 aτ.2))ᶜ ≤ t := by
    rintro ⟨a, τ⟩
    refine le_of_pow_le_pow_left₀ hNT ht ((prob_compl_okEventR_sideSubfacet_pow_le hV p a τ).trans ?_)
    have hsub : {ω | ∀ x ∈ facetLinked d a.1 m L H ω, ¬RuleOpen E x ω} ⊆
        facetCountLT d a.1 m L H M ∪ ({ω | M ≤ (facetLinked_finite a.1 m L H ω).toFinset.card} ∩
          {ω | ∀ x ∈ facetLinked d a.1 m L H ω, ¬RuleOpen E x ω}) := by
      intro ω hω
      by_cases hVc : M ≤ (facetLinked_finite a.1 m L H ω).toFinset.card
      · exact Or.inr ⟨hVc, hω⟩
      · left; exact not_le.1 hVc
    calc (bondPercolation (zdGraph d) p).real {ω | ∀ x ∈ facetLinked d a.1 m L H ω, ¬RuleOpen E x ω}
        ≤ (bondPercolation (zdGraph d) p).real (facetCountLT d a.1 m L H M) +
            (bondPercolation (zdGraph d) p).real ({ω | M ≤ (facetLinked_finite a.1 m L H ω).toFinset.card} ∩
              {ω | ∀ x ∈ facetLinked d a.1 m L H ω, ¬RuleOpen E x ω}) :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ (bondPercolation (zdGraph d) p).real (facetCountLT d a.1 m L H M) + (1 - (p : ℝ) ^ K) ^ N₁ :=
          add_le_add le_rfl (prob_facetCountGE_inter_noOpen_le hV a.1 hM p)
      _ ≤ _ := hside a
  refine (prob_compl_goodR_le m L H E p).trans ?_
  calc ∑ ρ : HAxis d → Bool, (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ +
        ∑ aτ : HAxis d × (HAxis d → Bool),
          (bondPercolation (zdGraph d) p).real (okEventR d m L H E (sideSubfacet d L H aτ.1 aτ.2))ᶜ
      ≤ ∑ _ρ : HAxis d → Bool, t + ∑ _aτ : HAxis d × (HAxis d → Bool), t :=
        add_le_add (Finset.sum_le_sum fun ρ _ => htop' ρ) (Finset.sum_le_sum fun aτ _ => hside' aτ)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- The estimate for the top-good event alone: if `P(U < M) + (1-p^K)^{N₁} ≤ t^{NT}` and
`M ≥ N₁ |B(r)|` then `P(not topGoodR) ≤ NT · t`. [cite: GrimmettPercolation1999, §7.3 p. 169] -/
theorem prob_compl_topGoodR_le_of_estimate (hV : SeedRuleValid E L H r K) {M N₁ : ℕ} (hM : N₁ * (box d r).card ≤ M)
    (p : unitInterval) {t : ℝ} (ht : 0 ≤ t)
    (htop : (bondPercolation (zdGraph d) p).real (topCountLT d m L H M) + (1 - (p : ℝ) ^ K) ^ N₁ ≤
      t ^ Fintype.card (HAxis d → Bool)) :
    (bondPercolation (zdGraph d) p).real (topGoodR d m L H E)ᶜ ≤ Fintype.card (HAxis d → Bool) * t := by
  have hNT : Fintype.card (HAxis d → Bool) ≠ 0 := Fintype.card_ne_zero
  have htop' : ∀ ρ : HAxis d → Bool,
      (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ ≤ t := by
    intro ρ
    refine le_of_pow_le_pow_left₀ hNT ht ((prob_compl_okEventR_topSubfacet_pow_le hV p ρ).trans ?_)
    have hsub : {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω} ⊆
        topCountLT d m L H M ∪ (topCountGE d m L H M ∩ {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω}) := by
      intro ω hω
      by_cases hU : ω ∈ topCountGE d m L H M
      · exact Or.inr ⟨hU, hω⟩
      · left; rwa [topCountLT_eq_compl]
    calc (bondPercolation (zdGraph d) p).real {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω}
        ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m L H M) +
            (bondPercolation (zdGraph d) p).real (topCountGE d m L H M ∩ {ω | ∀ x ∈ topLinked d m L H ω, ¬RuleOpen E x ω}) :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m L H M) + (1 - (p : ℝ) ^ K) ^ N₁ :=
          add_le_add le_rfl (prob_topCountGE_inter_noOpen_le hV hM p)
      _ ≤ _ := htop
  have hsub : (topGoodR d m L H E)ᶜ ⊆ ⋃ ρ : HAxis d → Bool, (okEventR d m L H E (topSubfacet d L H ρ))ᶜ := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_compl_iff, not_exists, not_not] at hnot
    exact hω (Set.mem_iInter.2 hnot)
  calc (bondPercolation (zdGraph d) p).real (topGoodR d m L H E)ᶜ
      ≤ (bondPercolation (zdGraph d) p).real (⋃ ρ : HAxis d → Bool, (okEventR d m L H E (topSubfacet d L H ρ))ᶜ) :=
        measureReal_mono hsub
    _ ≤ ∑ ρ : HAxis d → Bool, (bondPercolation (zdGraph d) p).real (okEventR d m L H E (topSubfacet d L H ρ))ᶜ :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ρ : HAxis d → Bool, t := Finset.sum_le_sum fun ρ _ => htop' ρ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Conclusion

/-! ## Lemma (7.36) for a family of valid rules -/

/-- **Lemma (7.36) for seed rules, in `ℤ^d`, at every density.** Let `E m L H` be seed rules valid
on all bricks with `L ≥ Lmin m`, `H ≥ Hmin m`, with separation radius `r m` and size bound `K m`
depending on `m` only, and let `Lreq m H₀` be any requested size. For `d ≥ 2`, `p ∈ (0,1)` with
`θ_ℍ(p) > 0`, and `η > 0`, there are `m ≥ 1`, `H₀ ≥ max(2m, Hmin m)`, `L ≥ max(m, Lmin m, Lreq m H₀)`
and `H > H₀` with `P_p(goodR on B(L,H)) > 1 - η` and `P_p(topGoodR on B(L,h)) > 1 - η` for every
`H₀ < h ≤ H`. This is the printed proof of Grimmett's Lemma (7.36) (pp. 164–169; "It is valid for
general `p`", p. 164; BGN 1991, Prop. 2.1) with "b(x) is a seed" replaced by "the rule-edges of `x`
are open"; the statement about the intermediate heights is the minimality clause of the fine tuning
(7.43) (`a(h) > 1 - 2ε` for `H₀ ≤ h < H₁`) combined with (7.48)–(7.49), (7.51).
[cite: GrimmettPercolation1999, Lemma (7.36) pp. 164–169] [cite: BarskyGrimmettNewman1991, Prop. 2.1] -/
theorem lemma_7_36R [NeZero d] (hd : 2 ≤ d) (E : ℕ → ℕ → ℕ → Site d → Finset (Sym2 (Site d)))
    (r K Lmin Hmin : ℕ → ℕ) (Lreq : ℕ → ℕ → ℕ)
    (hV : ∀ m L H, Lmin m ≤ L → Hmin m ≤ H → SeedRuleValid (E m L H) L H (r m) (K m))
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hθ : 0 < theta (halfSpaceGraph d) (halfSpaceOrigin d) p) {η : ℝ} (hη : 0 < η) :
    ∃ m H₀ L H : ℕ, 1 ≤ m ∧ m ≤ L ∧ 2 * m ≤ H₀ ∧ Hmin m ≤ H₀ ∧ H₀ < H ∧ Lmin m ≤ L ∧ Lreq m H₀ ≤ L ∧
      1 - η < (bondPercolation (zdGraph d) p).real (goodR d m L H (E m L H)) ∧
      ∀ h, H₀ < h → h ≤ H → 1 - η < (bondPercolation (zdGraph d) p).real (topGoodR d m L h (E m L h)) := by
  -- the numbers of subfacets and of facet families
  set NT : ℕ := Fintype.card (HAxis d → Bool) with hNT
  set NS : ℕ := Fintype.card (HAxis d × (HAxis d → Bool)) with hNS
  set k : ℕ := (hAxes d).card with hk
  have hNT0 : NT ≠ 0 := Fintype.card_ne_zero
  -- a horizontal axis
  have ha₀ : (⟨1, by omega⟩ : Fin d) ≠ 0 := by
    intro h; have := congrArg Fin.val h; simp at this
  set a₀ : Fin d := ⟨1, by omega⟩ with ha₀def
  have hk1 : 1 ≤ k := Finset.card_pos.2 ⟨a₀, mem_hAxes.2 ha₀⟩
  have hk0 : k ≠ 0 := by omega
  -- target for each of the failure probabilities
  set t : ℝ := η / (NT + NS + 1) with ht
  have ht0 : 0 < t := by positivity
  set s : ℝ := t ^ NT / 2 with hs
  have hs0 : 0 < s := by positivity
  -- Step 1: `ε`
  set ε : ℝ := min (1 / 4) (min (s / 3) (s ^ k)) with hε
  have hε0 : 0 < ε := by positivity
  have hε14 : ε ≤ 1 / 4 := min_le_left _ _
  have hεs3 : ε ≤ s / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hεsk : ε ≤ s ^ k := (min_le_right _ _).trans (min_le_right _ _)
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε2ε : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε0.le (hε14.trans (by norm_num))
  -- Step 2: `m` from (7.37)
  obtain ⟨m₀, hm₀⟩ := exists_prob_centralSquarePercolates_gt hd p hp0 hθ hε2
  set m : ℕ := max m₀ 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  have hcsq : 1 - ε ^ 2 < (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m) :=
    hm₀ m (le_max_left _ _)
  -- Step 3: seeds: `π`, `N₁`, `M`
  set π : ℝ := (p : ℝ) ^ (K m) with hπ
  have hπ0 : 0 < π := pow_pos hp0 _
  have hπ1 : π ≤ 1 := pow_le_one₀ p.2.1 p.2.2
  obtain ⟨N₁', hN₁'⟩ := exists_pow_lt_of_lt_one hs0 (show 1 - π < 1 by linarith only [hπ0])
  set N₁ : ℕ := max N₁' 1 with hN₁
  have hN₁1 : 1 ≤ N₁ := le_max_right _ _
  have hseedbd : (1 - π) ^ N₁ ≤ s :=
    (pow_le_pow_of_le_one (by linarith only [hπ1]) (by linarith only [hπ0]) (le_max_left _ _)).trans hN₁'.le
  set M : ℕ := N₁ * (box d (r m)).card with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by have := one_le_card_box (d := d) (r m); omega))
  -- Step 4: `g` and `N₂ = M g` (the vertical-edge step)
  obtain ⟨g', hg'⟩ := exists_pow_lt_of_lt_one (show 0 < ε / M by positivity) (show 1 - (p : ℝ) < 1 by linarith only [hp0])
  set g : ℕ := max g' 1 with hg
  have hMg : (M : ℝ) * (1 - (p : ℝ)) ^ g ≤ ε := by
    have h1 : (1 - (p : ℝ)) ^ g ≤ (1 - (p : ℝ)) ^ g' :=
      pow_le_pow_of_le_one (sub_nonneg.2 p.2.2) (by linarith only [hp0]) (le_max_left _ _)
    have h2 : (1 - (p : ℝ)) ^ g' < ε / M := hg'
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    calc (M : ℝ) * (1 - (p : ℝ)) ^ g ≤ M * (ε / M) := mul_le_mul_of_nonneg_left (h1.trans h2.le) hM0.le
      _ = ε := mul_div_cancel₀ ε hM0.ne'
  set N₂ : ℕ := M * g with hN₂
  have hN₂1 : 1 ≤ N₂ := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  -- Step 5: `H₀` from (7.41)
  obtain ⟨H₀', hH₀'⟩ := exists_prob_slabLevelLT_lt m N₂ p hp0 hp1 hε2 hcsq
  set H₀ : ℕ := max H₀' (max 2 (max (2 * m) (Hmin m))) with hH₀
  have hH₀2 : 2 ≤ H₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hH₀m : 2 * m ≤ H₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hH₀min : Hmin m ≤ H₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h741 : ∀ h, H₀ ≤ h → 1 - 2 * ε ^ 2 < (bondPercolation (zdGraph d) p).real (slabCountGE d m h N₂) := by
    intro h hh
    have := hH₀' h ((le_max_left _ _).trans hh)
    rw [← compl_compl (slabCountGE d m h N₂), compl_slabCountGE,
      probReal_compl_eq_one_sub (measurableSet_slabLevelLT m h N₂)]
    linarith only [this]
  -- Step 6: fine tuning of the height
  set c : ℝ := 1 - 2 * ε with hc
  have hc0 : 0 < c := by rw [hc]; linarith only [hε14]
  have hcle : c ≤ 1 - 2 * ε ^ 2 := by rw [hc]; linarith only [hε2ε]
  set a : ℕ → ℕ → ℝ := fun l h => (bondPercolation (zdGraph d) p).real (topCountGE d m l h N₂) with ha
  have hlarge : ∀ h, H₀ ≤ h → ∀ᶠ l in atTop, c < a l h := by
    intro h hh
    obtain ⟨L₀, hL₀⟩ := exists_prob_topCountGE_gt h m N₂ p (c := c) (hcle.trans_lt (h741 h hh))
    exact eventually_atTop.2 ⟨L₀, hL₀⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hlarge H₀ le_rfl)
  obtain ⟨H₁, hH₁spec, hH₁min, hH₁mono, hH₁lim⟩ := BGN.exists_fineTuning' (a := a) (c := c) (H₀ := H₀) (L₀ := L₀)
    (fun h l l' hll' => measureReal_mono (topCountGE_mono h m N₂ hll'))
    (fun l => ((tendsto_prob_topCountGE_height m l hN₂1 p hp1).eventually (Iic_mem_nhds hc0)).mono
      fun h hh => hh)
    hL₀ hlarge
  have hH₁low : ∀ l, L₀ ≤ l → c < a l (H₁ l - 1) := fun l hl =>
    hH₁min l hl (H₁ l - 1) (by have := (hH₁spec l).1; omega) (by have := (hH₁spec l).1; omega)
  -- Step 7: (7.46): `P(U(l, H₁ l) < M) ≤ 3ε` for `l ≥ L₀`
  have h746 : ∀ l, L₀ ≤ l → (bondPercolation (zdGraph d) p).real (topCountLT d m l (H₁ l) M) ≤ 3 * ε := by
    intro l hl
    have hh1 : 1 ≤ H₁ l - 1 := by have := (hH₁spec l).1; omega
    have hsucc : H₁ l - 1 + 1 = H₁ l := by have := (hH₁spec l).1; omega
    have hstep := prob_topCountGE_succ_ge (d := d) (m := m) (l := l) hh1 M g p
    rw [hsucc] at hstep
    have hlow : c < (bondPercolation (zdGraph d) p).real (topCountGE d m l (H₁ l - 1) (M * g)) := hH₁low l hl
    rw [topCountLT_eq_compl, probReal_compl_eq_one_sub (measurableSet_topCountGE _ _ _ _)]
    have h1 : (1 - ε) * c ≤ (bondPercolation (zdGraph d) p).real (topCountGE d m l (H₁ l) M) := by
      calc (1 - ε) * c ≤ (1 - M * (1 - (p : ℝ)) ^ g) * (bondPercolation (zdGraph d) p).real (topCountGE d m l (H₁ l - 1) (M * g)) :=
            mul_le_mul (by linarith only [hMg]) hlow.le hc0.le (by linarith only [hMg, hε14])
        _ ≤ _ := hstep
    rw [hc] at h1
    have h2 : (1 - ε) * (1 - 2 * ε) = 1 - 3 * ε + 2 * ε ^ 2 := by ring
    have h3 := sq_nonneg ε
    linarith only [h1, h2, h3]
  -- Step 8: (7.47): sides, `P(V^a(l, H₁ l) < M) < s` for `l ≥ L₁`
  set K' : ℕ := N₂ + k * M with hK'
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1
    ((tendsto_prob_centralSquarePercolates_inter_boundaryCountLT (d := d) m K' hH₁lim p hp1).eventually (Iio_mem_nhds hε2))
  have h747 : ∀ l, max L₀ L₁ ≤ l → ∀ a : Fin d, a ≠ 0 →
      (bondPercolation (zdGraph d) p).real (facetCountLT d a m l (H₁ l) M) ≤ s := by
    intro l hl
    have hl1 : L₁ ≤ l := (le_max_right _ _).trans hl
    -- `P(U + V < K') < 2ε²`
    have hbd : (bondPercolation (zdGraph d) p).real (boundaryCountLT d m l (H₁ l) K') < 2 * ε ^ 2 := by
      have hsplit := (measureReal_inter_add_sdiff (μ := bondPercolation (zdGraph d) p) (s := boundaryCountLT d m l (H₁ l) K')
        (measurableSet_centralSquarePercolates (d := d) m)).symm
      have h1 : (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m ∩ boundaryCountLT d m l (H₁ l) K') < ε ^ 2 :=
        hL₁ l hl1
      have h2 : (bondPercolation (zdGraph d) p).real (centralSquarePercolates d m) +
          (bondPercolation (zdGraph d) p).real (boundaryCountLT d m l (H₁ l) K' \ centralSquarePercolates d m) ≤ 1 := by
        rw [← measureReal_union (μ := bondPercolation (zdGraph d) p) Set.disjoint_sdiff_right
          ((measurableSet_boundaryCountLT m l (H₁ l) K').diff (measurableSet_centralSquarePercolates (d := d) m))]
        exact measureReal_le_one
      rw [hsplit, Set.inter_comm]
      linarith only [h1, h2, hcsq]
    -- `P(U < N₂) ≥ 2ε`
    have hU : 2 * ε ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m l (H₁ l) N₂) := by
      rw [topCountLT_eq_compl, probReal_compl_eq_one_sub (measurableSet_topCountGE _ _ _ _)]
      have := (hH₁spec l).2
      change (bondPercolation (zdGraph d) p).real (topCountGE d m l (H₁ l) N₂) ≤ 1 - 2 * ε at this
      linarith only [this]
    -- FKG with all facet factors equal to `v`
    set v := (bondPercolation (zdGraph d) p).real (facetCountLT d a₀ m l (H₁ l) M) with hv
    have hv0 : 0 ≤ v := measureReal_nonneg
    have hfkg := prob_mul_prod_le_boundaryCountLT (d := d) m l (H₁ l) N₂ M p
    have hprod : ∏ a ∈ hAxes d, (bondPercolation (zdGraph d) p).real (facetCountLT d a m l (H₁ l) M) = v ^ k := by
      rw [← Finset.prod_const]
      exact Finset.prod_congr rfl fun a ha => prob_facetCountLT_eq (mem_hAxes.1 ha) ha₀ m l (H₁ l) M p
    rw [hprod] at hfkg
    have hvk : v ^ k < s ^ k := by
      have h1 : 2 * ε * v ^ k < 2 * ε ^ 2 := by
        calc 2 * ε * v ^ k ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m l (H₁ l) N₂) * v ^ k :=
              mul_le_mul_of_nonneg_right hU (pow_nonneg hv0 _)
          _ ≤ _ := hfkg
          _ < 2 * ε ^ 2 := hbd
      have h2 : v ^ k < ε := by
        by_contra hle
        push Not at hle
        have h3 : 2 * ε * ε ≤ 2 * ε * v ^ k := mul_le_mul_of_nonneg_left hle (by linarith only [hε0])
        have h4 : ε ^ 2 = ε * ε := sq ε
        linarith only [h1, h3, h4]
      exact h2.trans_le hεsk
    have hvs : v < s := lt_of_pow_lt_pow_left₀ k hs0.le hvk
    intro a ha
    rw [prob_facetCountLT_eq ha ha₀]
    exact hvs.le
  -- Step 9: the brick `B(L, H₁ L)`
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = max (max L₀ L₁) (max (max m (Lmin m)) (Lreq m H₀)) := ⟨_, rfl⟩
  have hmL : m ≤ L := by rw [hL]; exact ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hLmin : Lmin m ≤ L := by rw [hL]; exact ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hLreq : Lreq m H₀ ≤ L := by rw [hL]; exact (le_max_right _ _).trans (le_max_right _ _)
  have hL01 : max L₀ L₁ ≤ L := by rw [hL]; exact le_max_left _ _
  have hL0 : L₀ ≤ L := (le_max_left _ _).trans hL01
  have hHmin : ∀ h, H₀ < h → Hmin m ≤ h := fun h hh => hH₀min.trans hh.le
  refine ⟨m, H₀, L, H₁ L, hm1, hmL, hH₀m, hH₀min, (hH₁spec L).1, hLmin, hLreq, ?_, ?_⟩
  -- Step 10: the failure probabilities and the conclusion
  · have hMhyp : N₁ * (box d (r m)).card ≤ M := le_rfl
    have h10 := h746 L hL0
    have h11 := h747 L hL01
    have hsNT : 2 * s = t ^ NT := by rw [hs]; ring
    have hε3s : 3 * ε ≤ s := by linarith only [hεs3]
    rw [hπ] at hseedbd
    have hgood := prob_compl_goodR_le_of_estimates (m := m) (hV m L (H₁ L) hLmin (hHmin _ (hH₁spec L).1)) hMhyp p ht0.le
      (by linarith only [h10, hseedbd, hε3s, hsNT]) (fun a => by linarith only [h11 a.1 a.2, hseedbd, hsNT])
    rw [probReal_compl_eq_one_sub (measurableSet_goodR m L (H₁ L) (E m L (H₁ L)))] at hgood
    have hfin : ((NT : ℝ) + NS) * t < η := by
      have hden : (0 : ℝ) < NT + NS + 1 := by positivity
      have : ((NT : ℝ) + NS) * t = η - t := by
        rw [ht]; field_simp; ring
      rw [this]
      linarith only [ht0]
    linarith only [hgood, hfin]
  -- Step 11: the top-good bricks of intermediate height
  · intro h hH₀h hhH
    have hMhyp : N₁ * (box d (r m)).card ≤ M := le_rfl
    have hsNT : 2 * s = t ^ NT := by rw [hs]; ring
    rw [hπ] at hseedbd
    -- `P(U(L,h) < M) ≤ 3ε`: at `h = H₁ L` by (7.46), below it by the minimality of `H₁ L`
    have hU : (bondPercolation (zdGraph d) p).real (topCountLT d m L h M) ≤ 3 * ε := by
      rcases hhH.eq_or_lt with rfl | hlt
      · exact h746 L hL0
      · have hmin := hH₁min L hL0 h hH₀h.le hlt
        have hMN₂ : topCountLT d m L h M ⊆ topCountLT d m L h N₂ := by
          intro ω hω
          simp only [topCountLT, Set.mem_setOf_eq] at hω ⊢
          have : M ≤ N₂ := Nat.le_mul_of_pos_right M (by omega)
          omega
        calc (bondPercolation (zdGraph d) p).real (topCountLT d m L h M)
            ≤ (bondPercolation (zdGraph d) p).real (topCountLT d m L h N₂) := measureReal_mono hMN₂
          _ ≤ 3 * ε := by
              rw [topCountLT_eq_compl, probReal_compl_eq_one_sub (measurableSet_topCountGE _ _ _ _)]
              change c < (bondPercolation (zdGraph d) p).real (topCountGE d m L h N₂) at hmin
              rw [hc] at hmin
              linarith only [hmin, hε0]
    have hε3s : 3 * ε ≤ s := by linarith only [hεs3]
    have htg := prob_compl_topGoodR_le_of_estimate (m := m) (hV m L h hLmin (hHmin h hH₀h)) hMhyp p ht0.le
      (by linarith only [hU, hseedbd, hε3s, hsNT])
    rw [probReal_compl_eq_one_sub (measurableSet_topGoodR m L h (E m L h))] at htg
    have hfin : (NT : ℝ) * t < η := by
      have hden : (0 : ℝ) < NT + NS + 1 := by positivity
      have : (NT : ℝ) * t = η - (NS + 1) * t := by
        rw [ht]; field_simp; ring
      rw [this]
      have : (0 : ℝ) < (NS + 1) * t := by positivity
      linarith only [this]
    linarith only [htg, hfin]

end BGNd

end Percolation.Literature

end
