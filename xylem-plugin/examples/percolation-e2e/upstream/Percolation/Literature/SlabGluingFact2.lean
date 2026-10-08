import Percolation.Literature.SlabCriticalityChain4
import Percolation.Literature.SlabGluingRouting
import Percolation.Util.Linter

/-!
# DST 2016, §2.3, Fact 2 (for large `t`), the Gluing Lemma, and Theorem 1 discharged

Last file of the bottom-up discharge of the named fact
`DuminilCopinSidoraviciusTassion2016` (`HalfSpace.lean`; Duminil-Copin–Sidoravicius–Tassion 2016,
Thm. 1: for every `k > 0`, bond percolation on the slab `S_k = ℤ² × {0,…,k}` has no infinite
cluster at its critical point, `θ_{S_k}(p_c(S_k)) = 0`):

* `fact2_large` — proved: **Fact 2 of §2.3 for `t ≥ 194`** (in the range `u_{3n} + 1 ≤ n`):
  `P[𝒳 ∩ {|U| ≥ t}] ≤ (K/t) · P[S_{3n} ⟷^{B_{3n} ∪ B'_n} S'_n]`, `K = 338 λ^{169(5k+4)}`,
  `λ = 2/min{p,1-p}`. Proof as printed (pp. 6–7 of arXiv:1401.7130): Lemma 7 (`lemma7_bond`,
  `SlabGluingFact1.lean`) applied to the multi-valued map `ω ↦ {ω^{(z)} : z ∈ Sel(ω)}`, where
  `Sel(ω)` is a `7`-separated subfamily of the good points of `U(ω)` (`GlueGeom.selF`; at least
  `(|U(ω)| - 97)/169 ≥ t/338` points, `exists_separated_subset`, `ncard_U_le_good`), `ω^{(z)}` is
  the surgery of `SlabGluingFact2Core.lean` with the data of `GlueGeom.exists_surgery`
  (`SlabGluingRouting.lean`): each `ω^{(z)} ∈ C` (`newConfig_mem_evC`), the `ω^{(z)}` are pairwise
  distinct (the attachment statistic `Att(ω^{(z)})` lies over `D(z) ⊆ z + B_3` and contains the
  attachment vertex; separation), and every preimage of `ω'` agrees with `ω'` off the
  `≤ 169(5k+4)` lattice edges touching `\overline{planar(q) + B_6}` for any `q ∈ Att(ω')`.
* `DuminilCopinSidoraviciusTassion2016_holds` — proved: **DST 2016, Theorem 1**, the named fact
  `DuminilCopinSidoraviciusTassion2016` discharged (`DuminilCopinSidoraviciusTassion2016.of_lemma6'`).

## Sources

* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Absence of infinite cluster for critical
  Bernoulli percolation on slabs*, Comm. Pure Appl. Math. 69 (2016), 1397–1411,
  arXiv:1401.7130: Thm. 1; §2.3, Lemma 7, Fact 2 and its proof (pp. 6–7 of the arXiv text: the
  map `Ψ`, "the configurations `ω^{(z)}` are all distinct", "`z` is determined uniquely",
  "`ω` and `ω^{(z)}` differ only in `\overline{B_{R+1}}(z)`", "Choosing `t` large enough"), and the
  conclusion of the proof of Lemma 6 (p. 7).
* C. M. Newman, V. Tassion, W. Wu, *Critical percolation and the minimal spanning tree in slabs*,
  CPAM 70 (2017), §3.2, proof of Thm. 3.9 [NewmanTassionWu2017].
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph Finset

/-! ## Counting: boxes, separated subfamilies, the excluded sets -/

section Counting

/-- A sup-norm box of radius `R` has `(2R+1)²` points: the points of a finite set inside it are at
most that many. [folklore] -/
theorem card_filter_mem_sqBox_le (A : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (R : ℕ)
    [DecidablePred (· ∈ sqBox z R)] :
    (A.filter (· ∈ sqBox z R)).card ≤ (2 * R + 1) ^ 2 := by
  have hsub : A.filter (· ∈ sqBox z R) ⊆
      (Finset.Icc (z.1 - R) (z.1 + R)) ×ˢ (Finset.Icc (z.2 - R) (z.2 + R)) := by
    intro w hw
    obtain ⟨-, hw⟩ := Finset.mem_filter.1 hw
    simp only [sqBox, Set.mem_setOf_eq, abs_le] at hw
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have : (z.1 + R + 1 - (z.1 - R)).toNat = 2 * R + 1 := by omega
  rw [this]
  have : (z.2 + R + 1 - (z.2 - R)).toNat = 2 * R + 1 := by omega
  rw [this]
  ring_nf; rfl

/-- **Greedy separated subfamily**: a finite planar set `A` contains a subset `Sel`, any two
distinct points of which are at sup-distance `> R`, with `|A| ≤ (2R+1)² |Sel|`. [folklore] -/
theorem exists_separated_subset (R : ℕ) : ∀ (A : Finset (ℤ × ℤ)), ∃ Sel : Finset (ℤ × ℤ), Sel ⊆ A ∧
    (∀ z ∈ Sel, ∀ z' ∈ Sel, z ≠ z' → z' ∉ sqBox z R) ∧ A.card ≤ (2 * R + 1) ^ 2 * Sel.card := by
  classical
  intro A
  induction A using Finset.strongInduction with
  | H A ih =>
    rcases A.eq_empty_or_nonempty with rfl | ⟨z, hz⟩
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
    · set A' := A.filter (· ∉ sqBox z R) with hA'
      have hzz : z ∈ sqBox z R := by simp [sqBox]
      have hA'A : A' ⊂ A := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun h => ?_⟩
        have : z ∈ A' := by rw [h]; exact hz
        exact (Finset.mem_filter.1 this).2 hzz
      obtain ⟨Sel', hSel'A', hsep', hcard'⟩ := ih A' hA'A
      have hzSel' : z ∉ Sel' := fun h => (Finset.mem_filter.1 (hSel'A' h)).2 hzz
      refine ⟨insert z Sel', ?_, ?_, ?_⟩
      · exact Finset.insert_subset hz (hSel'A'.trans (Finset.filter_subset _ _))
      · intro w hw w' hw' hne
        rw [Finset.mem_insert] at hw hw'
        rcases hw with rfl | hw <;> rcases hw' with rfl | hw'
        · exact absurd rfl hne
        · exact (Finset.mem_filter.1 (hSel'A' hw')).2
        · intro hmem
          apply (Finset.mem_filter.1 (hSel'A' hw)).2
          simp only [sqBox, Set.mem_setOf_eq] at hmem ⊢
          rw [abs_sub_comm w.1, abs_sub_comm w.2]; exact hmem
        · exact hsep' w hw w' hw' hne
      · have hsplit : A.card ≤ (A.filter (· ∈ sqBox z R)).card + A'.card := by
          rw [hA', Finset.card_filter_add_card_filter_not]
        have hbox := card_filter_mem_sqBox_le A z R
        rw [Finset.card_insert_of_notMem hzSel']
        nlinarith

variable {k : ℕ}

/-- The excluded strip `zBad` has at most `48` points. [folklore] -/
theorem GlueGeom.ncard_inter_zBad_le (G : GlueGeom) (S : Set (ℤ × ℤ)) : (S ∩ G.zBad).ncard ≤ 48 := by
  classical
  set F : Finset (ℤ × ℤ) := (Finset.Icc (3 * (G.n : ℤ) - 3) (3 * G.n)) ×ˢ
    (Finset.Icc (G.y - G.α - 3) (G.y - G.α + 2) ∪ Finset.Icc (G.y + G.α - 2) (G.y + G.α + 3)) with hF
  have hsub : S ∩ G.zBad ⊆ ↑F := by
    rintro w ⟨-, hw⟩
    simp only [GlueGeom.zBad, Set.mem_setOf_eq] at hw
    simp only [hF, Finset.coe_product, Finset.coe_union, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc,
      Set.mem_union]
    omega
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet F)).trans ?_
  rw [Set.ncard_coe_finset, Finset.card_product]
  have h1 : (Finset.Icc (3 * (G.n : ℤ) - 3) (3 * G.n)).card = 4 := by
    rw [Int.card_Icc]; omega
  have h2 : (Finset.Icc (G.y - G.α - 3) (G.y - G.α + 2) ∪ Finset.Icc (G.y + G.α - 2) (G.y + G.α + 3)).card ≤ 12 := by
    refine (Finset.card_union_le _ _).trans ?_
    rw [Int.card_Icc, Int.card_Icc]; omega
  rw [h1]; omega

/-- The excluded set `lastBad` has at most `49` points. [folklore] -/
theorem GlueGeom.ncard_inter_lastBad_le (G : GlueGeom) (ω : BondConfig (slab 3 k)) (S : Set (ℤ × ℤ)) :
    (S ∩ G.lastBad k ω).ncard ≤ 49 := by
  classical
  cases hl : (G.γmin k ω).getLast? with
  | none =>
    have : S ∩ G.lastBad k ω = ∅ := by
      ext w; simp [GlueGeom.lastBad, hl]
    rw [this, Set.ncard_empty]; omega
  | some v =>
    set F : Finset (ℤ × ℤ) := (Finset.Icc ((planar k v).1 - 3) ((planar k v).1 + 3)) ×ˢ
      (Finset.Icc ((planar k v).2 - 3) ((planar k v).2 + 3)) with hF
    have hsub : S ∩ G.lastBad k ω ⊆ ↑F := by
      rintro w ⟨-, u, hu, hw⟩
      rw [hl] at hu
      simp only [Option.mem_def, Option.some.injEq] at hu
      subst hu
      simp only [sqBox, Set.mem_setOf_eq, abs_le, Nat.cast_ofNat] at hw
      simp only [hF, Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
      omega
    refine (Set.ncard_le_ncard hsub (Finset.finite_toSet F)).trans ?_
    rw [Set.ncard_coe_finset, Finset.card_product, Int.card_Icc, Int.card_Icc]
    have h1 : ((planar k v).1 + 3 + 1 - ((planar k v).1 - 3)).toNat = 7 := by omega
    have h2 : ((planar k v).2 + 3 + 1 - ((planar k v).2 - 3)).toNat = 7 := by omega
    rw [h1, h2]

end Counting

end Percolation.Literature

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph Finset

section SurgeryFacts

variable {k : ℕ} {G : GlueGeom} {ω : BondConfig (slab 3 k)}

/-- The points of a sup-norm box of radius `R`, as a finite set, number at most `(2R+1)²`.
[folklore] -/
theorem card_toFinset_sqBox_le (z : ℤ × ℤ) (R : ℕ) :
    (sqBox_finite z R).toFinset.card ≤ (2 * R + 1) ^ 2 := by
  classical
  have : (sqBox_finite z R).toFinset = (sqBox_finite z R).toFinset.filter (· ∈ sqBox z R) := by
    ext w; simp
  rw [this]
  exact card_filter_mem_sqBox_le _ z R

/-- The new configuration of a surgery consists of old edges and of lattice edges inside the
window `\overline{B_{3n} ∪ B'_n}`. [folklore] -/
theorem GlueGeom.Surgery.mem_window_of_mem_newConfig (sg : G.Surgery k ω) (hA : ω ∈ G.evA k)
    {e : Sym2 (slab 3 k)} (he : e ∈ sg.newConfig) :
    e ∈ ω ∨ (e ∈ (slabGraph 3 k).edgeSet ∧ e ∈ (slabLift k (G.big ∪ G.small)).sym2) := by
  rcases sg.newConfig_subset hA he with h | h
  · exact Or.inl h
  · right
    refine ⟨?_, ?_⟩
    · rcases h with h | h
      · exact edgesOf_subset_edgeSet sg.hSPchain h
      · exact edgesOf_subset_edgeSet sg.hBrchain h
    · induction e using Sym2.ind with
      | h a b =>
        obtain ⟨ha, hb⟩ := sg.structEdges_Sw h
        exact Set.mk_mem_sym2_iff.2 ⟨sg.hD (sg.Sw_D ha), sg.hD (sg.Sw_D hb)⟩

/-- The attachment vertex lies over the cleared box. [folklore] -/
theorem GlueGeom.Surgery.c_D (sg : G.Surgery k ω) : planar k sg.c ∈ sg.D := sg.SP_D sg.c_mem_SP

/-- Two points at sup-distance `≤ 3` from a common point are at sup-distance `≤ 6`. [folklore] -/
theorem mem_sqBox_six_of_three {z z' q : ℤ × ℤ} (hq : q ∈ sqBox z 3) (hq' : q ∈ sqBox z' 3) : z' ∈ sqBox z 6 := by
  simp only [sqBox, Set.mem_setOf_eq, abs_le, Nat.cast_ofNat] at hq hq' ⊢
  omega

/-- A box of radius `3` around `z` lies in the box of radius `6` around any of its points.
[folklore] -/
theorem sqBox_three_subset_six {z q : ℤ × ℤ} (hq : q ∈ sqBox z 3) : sqBox z 3 ⊆ sqBox q 6 := by
  intro w hw
  simp only [sqBox, Set.mem_setOf_eq, abs_le, Nat.cast_ofNat] at hq hw ⊢
  omega

end SurgeryFacts

/-! ## The good points, the selected subfamily and the chosen surgeries -/

section Choices

variable (G : GlueGeom) (k : ℕ)

/-- The good points of `U(ω)`: off the two excluded bounded sets. [folklore] -/
def GlueGeom.good (ω : BondConfig (slab 3 k)) : Set (ℤ × ℤ) := G.U k ω \ (G.zBad ∪ G.lastBad k ω)

/-- The good points form a finite set. [folklore] -/
theorem GlueGeom.good_finite (ω : BondConfig (slab 3 k)) : (G.good k ω).Finite :=
  (G.U_finite k ω).subset Set.sdiff_subset

/-- **The selected subfamily** of good points: pairwise at sup-distance `> 6`, capturing a
`1/169` fraction of the good points (greedy choice). [folklore] -/
def GlueGeom.selF (ω : BondConfig (slab 3 k)) : Finset (ℤ × ℤ) :=
  Classical.choose (exists_separated_subset 6 (G.good_finite k ω).toFinset)

/-- The defining properties of the selected subfamily. [folklore] -/
theorem GlueGeom.selF_spec (ω : BondConfig (slab 3 k)) :
    G.selF k ω ⊆ (G.good_finite k ω).toFinset ∧
      (∀ z ∈ G.selF k ω, ∀ z' ∈ G.selF k ω, z ≠ z' → z' ∉ sqBox z 6) ∧
      (G.good_finite k ω).toFinset.card ≤ (2 * 6 + 1) ^ 2 * (G.selF k ω).card :=
  Classical.choose_spec (exists_separated_subset 6 (G.good_finite k ω).toFinset)

/-- Selected points are good. [folklore] -/
theorem GlueGeom.mem_good_of_mem_selF {ω : BondConfig (slab 3 k)} {z : ℤ × ℤ} (hz : z ∈ G.selF k ω) :
    z ∈ G.good k ω :=
  (Set.Finite.mem_toFinset _).1 ((G.selF_spec k ω).1 hz)

variable {G k}

/-- **The chosen surgery** at a good point (by `GlueGeom.exists_surgery`). [cite: DuminilCopinSidoraviciusTassion2016, §2.3, proof of Fact 2 (construction of ω^{(z)})] -/
def GlueGeom.surgAt (hG : G.InRange) (hu : G.u₃ + 1 ≤ G.n) (hk : 0 < k) {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) (hX : ω ∈ G.evX k) {z : ℤ × ℤ} (hz : z ∈ G.good k ω) :
    G.Surgery k ω :=
  Classical.choose (GlueGeom.exists_surgery hG hu hk hω hX hz.1 (fun h => hz.2 (Or.inr h)) (fun h => hz.2 (Or.inl h)))

/-- The chosen surgery clears a box of radius `3` around the point. [folklore] -/
theorem GlueGeom.surgAt_D (hG : G.InRange) (hu : G.u₃ + 1 ≤ G.n) (hk : 0 < k) {ω : BondConfig (slab 3 k)}
    (hω : ω ⊆ (slabGraph 3 k).edgeSet) (hX : ω ∈ G.evX k) {z : ℤ × ℤ} (hz : z ∈ G.good k ω) :
    (GlueGeom.surgAt hG hu hk hω hX hz).D ⊆ sqBox z 3 :=
  Classical.choose_spec (GlueGeom.exists_surgery hG hu hk hω hX hz.1 (fun h => hz.2 (Or.inr h))
    (fun h => hz.2 (Or.inl h)))

end Choices

end Percolation.Literature

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph Finset

/-! ## Fact 2 for large `t` -/

section Fact2

variable {k : ℕ}

/-- On `𝒳`, at least `|U(ω)| - 97` points of `U(ω)` are good. [folklore] -/
theorem GlueGeom.ncard_U_le_good (G : GlueGeom) (ω : BondConfig (slab 3 k)) :
    (G.U k ω).ncard ≤ (G.good_finite k ω).toFinset.card + 97 := by
  classical
  have hU := G.U_finite k ω
  have hsplit : G.U k ω ⊆ G.good k ω ∪ (G.U k ω ∩ G.zBad ∪ G.U k ω ∩ G.lastBad k ω) := by
    intro z hz
    by_cases h : z ∈ G.zBad ∪ G.lastBad k ω
    · rcases h with h | h
      · exact Or.inr (Or.inl ⟨hz, h⟩)
      · exact Or.inr (Or.inr ⟨hz, h⟩)
    · exact Or.inl ⟨hz, h⟩
  have h1 := G.ncard_inter_zBad_le (G.U k ω)
  have h2 := G.ncard_inter_lastBad_le ω (G.U k ω)
  have hfin : (G.good k ω ∪ (G.U k ω ∩ G.zBad ∪ G.U k ω ∩ G.lastBad k ω)).Finite :=
    (G.good_finite k ω).union ((hU.inter_of_left _).union (hU.inter_of_left _))
  calc (G.U k ω).ncard ≤ (G.good k ω ∪ (G.U k ω ∩ G.zBad ∪ G.U k ω ∩ G.lastBad k ω)).ncard :=
        Set.ncard_le_ncard hsplit hfin
    _ ≤ (G.good k ω).ncard + (G.U k ω ∩ G.zBad ∪ G.U k ω ∩ G.lastBad k ω).ncard := Set.ncard_union_le _ _
    _ ≤ (G.good k ω).ncard + ((G.U k ω ∩ G.zBad).ncard + (G.U k ω ∩ G.lastBad k ω).ncard) := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ (G.good_finite k ω).toFinset.card + 97 := by
        rw [Set.ncard_eq_toFinset_card _ (G.good_finite k ω)]; omega

/-- **DST 2016, §2.3, Fact 2, for `t` large** (in the range `u_{3n} + 1 ≤ n`):
`P[𝒳 ∩ {|U| ≥ t}] ≤ (K/t) · P[S_{3n} ⟷^{B_{3n} ∪ B'_n} S'_n]` for all `t ≥ 194`, with
`K = 338 λ^{169(5k+4)}`, `λ = 2/min{p, 1-p}`. Proof as printed (pp. 6–7): the multi-valued map
`ω ↦ {ω^{(z)}}` over a `7`-separated family of good points `z ∈ U(ω)` (at least `(t-97)/169 ≥ t/338`
of them), each `ω^{(z)} ∈ C` (`newConfig_mem_evC`), pairwise distinct and with `z` recovered from
`ω^{(z)}` up to a bounded window through the attachment statistic `Att` (`c_mem_att`,
`att_subset`: any `q ∈ Att(ω')` has `D(z) ⊆ planar(q) + B_6`, outside of which `ω` and `ω^{(z)}`
agree), and Lemma 7 (`lemma7_bond`) with `s = 169·(5k+4)` edges. [cite: DuminilCopinSidoraviciusTassion2016, §2.3 (Fact 2 and its proof, pp. 6–7)] -/
theorem fact2_large (k : ℕ) (hk : 0 < k) (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∀ t : ℕ, 194 ≤ t → ∀ G : GlueGeom, G.InRange → G.u₃ + 1 ≤ G.n →
      (bondPercolation (slabGraph 3 k) p).real (G.evX k ∩ {ω | t ≤ (G.U k ω).ncard}) ≤
        (338 * (2 / min (p : ℝ) (1 - p)) ^ ((5 * k + 4) * 169)) / t *
          (bondPercolation (slabGraph 3 k) p).real (G.evC k) := by
  classical
  intro t ht G hG hu
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
  have hagree : ∀ ω ω' : BondConfig (slab 3 k), ω ∩ ↑K' = ω' ∩ ↑K' →
      ∀ e ∈ (slabLift k (G.big ∪ G.small)).sym2, e ∈ ω ↔ e ∈ ω' := by
    intro ω ω' heq e he
    rw [← hK'coe] at he
    have := Set.ext_iff.1 heq e
    simp only [Set.mem_inter_iff, he, and_true] at this
    exact this
  have hXdet : ∀ ω ω' : BondConfig (slab 3 k), ω ∩ ↑K' = ω' ∩ ↑K' → (ω ∈ G.evX k ↔ ω' ∈ G.evX k) := by
    intro ω ω' heq
    have h := hagree ω ω' heq
    simp only [GlueGeom.evX, GlueGeom.evA, GlueGeom.evBm, GlueGeom.evBp, GlueGeom.evC,
      Set.mem_inter_iff, Set.mem_compl_iff]
    rw [mem_slabConn_congr k G h Set.subset_union_left, mem_slabConn_congr k G h Set.subset_union_right,
      mem_slabConn_congr k G h Set.subset_union_right, mem_slabConn_congr k G h subset_rfl]
  have hA : DeterminedBy (G.evX k ∩ {ω | t ≤ (G.U k ω).ncard}) ↑K' := by
    rw [determinedBy_iff]
    intro ω ω' heq
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [hXdet ω ω' heq, G.U_congr k (hagree ω ω' heq)]
  have hB : DeterminedBy (G.evC k) ↑K' := by
    rw [determinedBy_iff]
    intro ω ω' heq
    exact mem_slabConn_congr k G (hagree ω ω' heq) subset_rfl _ _
  -- lattice configurations inside the window
  have hlat : ∀ S : Finset (Sym2 (slab 3 k)), S ⊆ Kfin → (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet :=
    fun S hS e he => hKE e (hS he)
  -- new configurations lie in the window
  have hnewK : ∀ (S : Finset (Sym2 (slab 3 k))), S ⊆ Kfin → ∀ (hSX : (↑S : BondConfig (slab 3 k)) ∈ G.evX k)
      (sg : G.Surgery k (↑S : BondConfig (slab 3 k))), sg.newConfig ⊆ ↑Kfin := by
    intro S hS hSX sg e he
    rcases sg.mem_window_of_mem_newConfig hSX.1.1.1 he with h | ⟨h1, h2⟩
    · exact hS h
    · rw [Finset.mem_coe, hK]
      exact ⟨by rw [← Finset.mem_coe, hK'coe]; exact h2, h1⟩
  have hcoe : ∀ (S : Finset (Sym2 (slab 3 k))), S ⊆ Kfin → ∀ (hSX : (↑S : BondConfig (slab 3 k)) ∈ G.evX k)
      (sg : G.Surgery k (↑S : BondConfig (slab 3 k))),
      (↑(Kfin.filter (· ∈ sg.newConfig)) : Set (Sym2 (slab 3 k))) = sg.newConfig := by
    intro S hS hSX sg
    ext e
    simp only [Finset.coe_filter, Set.mem_setOf_eq, and_iff_right_iff_imp]
    exact fun he => hnewK S hS hSX sg he
  -- the multi-valued map
  let Φ : Finset (Sym2 (slab 3 k)) → Finset (Finset (Sym2 (slab 3 k))) := fun S =>
    if h : (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet ∧ (↑S : BondConfig (slab 3 k)) ∈ G.evX k then
      (G.selF k ↑S).attach.image fun z =>
        Kfin.filter (· ∈ (GlueGeom.surgAt hG hu hk h.1 h.2 (G.mem_good_of_mem_selF k z.2)).newConfig)
    else ∅
  have hΦ_of : ∀ (S : Finset (Sym2 (slab 3 k))) (h : (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet ∧
      (↑S : BondConfig (slab 3 k)) ∈ G.evX k), Φ S = (G.selF k ↑S).attach.image fun z =>
        Kfin.filter (· ∈ (GlueGeom.surgAt hG hu hk h.1 h.2 (G.mem_good_of_mem_selF k z.2)).newConfig) :=
    fun S h => dif_pos h
  set lam : ℝ := 2 / min (p : ℝ) (1 - p) with hlam
  set s : ℕ := (5 * k + 4) * 169 with hs
  have ht0 : (0 : ℝ) < (t : ℝ) / 338 := by positivity
  have hmain := lemma7_bond (slabGraph 3 k) p hp0 hp1 K' Kfin hK hA hB s ht0 Φ ?_ ?_ ?_
  · calc P.real (G.evX k ∩ {ω | t ≤ (G.U k ω).ncard}) ≤ lam ^ s / (t / 338) * P.real (G.evC k) := hmain
      _ = 338 * lam ^ s / t * P.real (G.evC k) := by
        congr 1
        field_simp
  · -- images lie in `C`
    intro S hS hSA S' hS'
    have h : (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet ∧ (↑S : BondConfig (slab 3 k)) ∈ G.evX k :=
      ⟨hlat S hS, hSA.1⟩
    rw [hΦ_of S h, Finset.mem_image] at hS'
    obtain ⟨z, -, rfl⟩ := hS'
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [hcoe S hS h.2]
    exact GlueGeom.Surgery.newConfig_mem_evC _ h.2
  · -- at least `t / 338` images
    intro S hS hSA
    have h : (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet ∧ (↑S : BondConfig (slab 3 k)) ∈ G.evX k :=
      ⟨hlat S hS, hSA.1⟩
    rw [hΦ_of S h]
    obtain ⟨hsub, hsep, hcard⟩ := G.selF_spec k (↑S : BondConfig (slab 3 k))
    have hinj : Set.InjOn (fun z : {z // z ∈ G.selF k (↑S : BondConfig (slab 3 k))} =>
        Kfin.filter (· ∈ (GlueGeom.surgAt hG hu hk h.1 h.2 (G.mem_good_of_mem_selF k z.2)).newConfig))
        ↑((G.selF k (↑S : BondConfig (slab 3 k))).attach) := by
      rintro ⟨z, hz⟩ - ⟨z', hz'⟩ - heq
      simp only at heq
      by_contra hne
      have hne' : z ≠ z' := fun h => hne (Subtype.ext h)
      set sg := GlueGeom.surgAt hG hu hk h.1 h.2 (G.mem_good_of_mem_selF k hz)
      set sg' := GlueGeom.surgAt hG hu hk h.1 h.2 (G.mem_good_of_mem_selF k hz')
      have heq' : sg.newConfig = sg'.newConfig := by
        rw [← hcoe S hS h.2 sg, ← hcoe S hS h.2 sg', heq]
      have hc := sg.c_mem_att h.2
      rw [heq'] at hc
      have hcD' := sg'.att_subset h.2 hc
      rw [mem_slabLift_iff] at hcD'
      have h1 : planar k sg.c ∈ sqBox z 3 := GlueGeom.surgAt_D hG hu hk h.1 h.2 _ sg.c_D
      have h2 : planar k sg.c ∈ sqBox z' 3 := GlueGeom.surgAt_D hG hu hk h.1 h.2 _ hcD'
      exact hsep z hz z' hz' hne' (mem_sqBox_six_of_three h1 h2)
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
    -- `|sel| ≥ (|U| - 97)/169 ≥ t/338`
    have hU := G.ncard_U_le_good (↑S : BondConfig (slab 3 k))
    have htU : t ≤ (G.U k (↑S : BondConfig (slab 3 k))).ncard := hSA.2
    have hc' : ((G.good_finite k (↑S : BondConfig (slab 3 k))).toFinset.card : ℝ) ≤
        169 * (G.selF k (↑S : BondConfig (slab 3 k))).card := by exact_mod_cast hcard
    have hU' : ((G.U k (↑S : BondConfig (slab 3 k))).ncard : ℝ) ≤
        (G.good_finite k (↑S : BondConfig (slab 3 k))).toFinset.card + 97 := by exact_mod_cast hU
    have htU' : (t : ℝ) ≤ (G.U k (↑S : BondConfig (slab 3 k))).ncard := by exact_mod_cast htU
    have ht' : (194 : ℝ) ≤ t := by exact_mod_cast ht
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 338)]
    linarith
  · -- recovery window
    intro S' hS' _
    by_cases hq : (G.att k (↑S' : BondConfig (slab 3 k))).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hq
      refine ⟨Kfin.filter fun e => ∃ u ∈ e, planar k u ∈ (sqBox_finite (planar k q₀) 6).toFinset, ?_, ?_⟩
      · refine (card_filter_colEdges_le k Kfin hKE _).trans ?_
        have := card_toFinset_sqBox_le (planar k q₀) 6
        rw [hs]; exact Nat.mul_le_mul_left _ this
      · intro S hS hSA hmem e heT
        have h : (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet ∧ (↑S : BondConfig (slab 3 k)) ∈ G.evX k :=
          ⟨hlat S hS, hSA.1⟩
        rw [hΦ_of S h, Finset.mem_image] at hmem
        obtain ⟨⟨z, hz⟩, -, rfl⟩ := hmem
        set sg := GlueGeom.surgAt hG hu hk h.1 h.2 (G.mem_good_of_mem_selF k hz) with hsg
        have hcoe' := hcoe S hS h.2 sg
        rw [hcoe'] at hq₀
        have hq₀D : planar k q₀ ∈ sg.D := by
          have := sg.att_subset h.2 hq₀
          rwa [mem_slabLift_iff] at this
        have hDq : sg.D ⊆ sqBox (planar k q₀) 6 :=
          (GlueGeom.surgAt_D hG hu hk h.1 h.2 _).trans (sqBox_three_subset_six (GlueGeom.surgAt_D hG hu hk h.1 h.2 _ hq₀D))
        by_cases heK : e ∈ Kfin
        · have hnt : e ∉ touch k sg.D := by
            rintro ⟨x, hx, hxD⟩
            exact heT (Finset.mem_filter.2 ⟨heK, x, hx, (Set.Finite.mem_toFinset _).2 (hDq hxD)⟩)
          have := sg.mem_newConfig_iff_of_not_touch hnt
          rw [Finset.mem_filter]
          constructor
          · intro heS; exact ⟨heK, this.2 heS⟩
          · intro heS'; exact this.1 heS'.2
        · constructor
          · intro heS; exact absurd (hS heS) heK
          · intro heS'; exact absurd (Finset.mem_filter.1 heS').1 heK
    · refine ⟨∅, by simp, ?_⟩
      intro S hS hSA hmem
      exfalso
      apply hq
      have h : (↑S : Set (Sym2 (slab 3 k))) ⊆ (slabGraph 3 k).edgeSet ∧ (↑S : BondConfig (slab 3 k)) ∈ G.evX k :=
        ⟨hlat S hS, hSA.1⟩
      rw [hΦ_of S h, Finset.mem_image] at hmem
      obtain ⟨⟨z, hz⟩, -, rfl⟩ := hmem
      rw [hcoe S hS h.2]
      exact GlueGeom.Surgery.att_nonempty _ h.2

end Fact2

end Percolation.Literature

namespace Percolation.Literature

open MeasureTheory LatticeModels SimpleGraph GlueGeom

/-! ## Lemma 6' from Fact 1 and Fact 2; DST 2016, Thm. 1 -/

section Final

/-- Choosing first `t` as in Fact 2 and then `δ` as in Fact 1 conclude the proof", §2.3, p. 7): take `t
 ≥ 194` with `K/t ≤ ε/2`, then `δ` with `δ(1 + λ^{(5k+4)t}) ≤ ε/2`. [cite:
 DuminilCopinSidoraviciusTassion2016, §2.3 (p. 7, conclusion of the proof of Lemma 6)]
-/
theorem DuminilCopinSidoraviciusTassion2016_lemma6'_holds : DuminilCopinSidoraviciusTassion2016_lemma6' := by
  intro k hk p hθ ε hε
  have hp0 : 0 < (p : ℝ) := coe_pos_of_theta_slab_pos hθ
  have h1 := DuminilCopinSidoraviciusTassion2016_fact1_holds
  -- the events of the statement are those of `GlueGeom`
  have key : ∀ (δ : ℝ), 0 < δ → (∀ G : GlueGeom, G.InRange → G.u₃ + 1 ≤ G.n →
      1 - δ ≤ (bondPercolation (slabGraph 3 k) p).real (G.evA k ∩ G.evBm k ∩ G.evBp k) →
      1 - ε ≤ (bondPercolation (slabGraph 3 k) p).real (G.evC k)) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (n u₃ u₁ α : ℕ) (y : ℤ), 2 ≤ n → u₃ + 1 ≤ n → 3 * u₁ ≤ n → 1 ≤ α → α + 1 ≤ n →
        0 ≤ y → y ≤ 3 * n →
        1 - δ ≤ (bondPercolation (slabGraph 3 k) p).real
          (slabConn k (sqBox 0 (3 * n)) (sqBox 0 u₃) (sideSeg (3 * n) (y - α) (y + α)) ∩
            slabConn k (sqBox (2 * (n : ℤ), y) n) (sqBox (2 * (n : ℤ), y) u₁)
              (sideSeg (3 * n) (y - n) (y - α)) ∩
            slabConn k (sqBox (2 * (n : ℤ), y) n) (sqBox (2 * (n : ℤ), y) u₁)
              (sideSeg (3 * n) (y + α) (y + n))) →
        1 - ε ≤ (bondPercolation (slabGraph 3 k) p).real
          (slabConn k (sqBox 0 (3 * n) ∪ sqBox (2 * (n : ℤ), y) n) (sqBox 0 u₃)
            (sqBox (2 * (n : ℤ), y) u₁)) := by
    intro δ hδ H
    refine ⟨δ, hδ, fun n u₃ u₁ α y h1 h2 h3 h4 h5 h6 h7 hP => ?_⟩
    exact H ⟨n, u₃, u₁, α, y⟩ ⟨h1, Nat.le_of_succ_le h2, h3, h4, h5, h6, h7⟩ h2 hP
  rcases lt_or_ge (p : ℝ) 1 with hp1 | hp1
  · -- the main case `0 < p < 1`
    set lam : ℝ := 2 / min (p : ℝ) (1 - p) with hlam
    obtain ⟨s, hs⟩ : ∃ s : ℕ, s = (5 * k + 4) * 169 := ⟨_, rfl⟩
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 338 * lam ^ s := ⟨_, rfl⟩
    have hK := fact2_large k hk p hp0 hp1
    have hlam1 : 1 ≤ lam := by
      rw [hlam, le_div_iff₀ (lt_min hp0 (by linarith))]
      have := min_le_left (p : ℝ) (1 - p)
      have hp1' : (p : ℝ) ≤ 1 := p.2.2
      linarith
    -- choose `t ≥ 194` with `K / t ≤ ε / 2`
    obtain ⟨t, ht1, htK⟩ : ∃ t : ℕ, 194 ≤ t ∧ K / t ≤ ε / 2 := by
      obtain ⟨t, ht⟩ := exists_nat_gt (max 194 (2 * K / ε))
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans ht.le)
      refine ⟨t, by exact_mod_cast (le_max_left (194 : ℝ) _).trans ht.le, ?_⟩
      rw [div_le_iff₀ ht0]
      have := (le_max_right (194 : ℝ) (2 * K / ε)).trans ht.le
      rw [div_le_iff₀ hε] at this
      linarith
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = lam ^ ((5 * k + 4) * t) := ⟨_, rfl⟩
    have hL1 : 1 ≤ L := hL ▸ one_le_pow₀ hlam1
    refine key (ε / (2 * (1 + L))) (by positivity) fun G hG hu hP => ?_
    set P := bondPercolation (slabGraph 3 k) p with hPdef
    have hF1 := h1 k hk p hp0 hp1 G hG t
    have hF2 := hK t ht1 G hG hu
    rw [← hs, ← hlam, ← hKdef] at hF2
    rw [← hlam, ← hL] at hF1
    have hX := real_evX_le k G p t
    have hT := real_triple_le k G p
    have hB : P.real (G.evBm k ∩ G.evBp k)ᶜ ≤ ε / (2 * (1 + L)) := by
      rw [measureReal_compl (measurableSet_evBm_inter_evBp k G), probReal_univ]
      have : P.real (G.evA k ∩ G.evBm k ∩ G.evBp k) ≤ P.real (G.evBm k ∩ G.evBp k) :=
        measureReal_mono (by rw [Set.inter_assoc]; exact Set.inter_subset_right)
      linarith
    have hC1 : P.real (G.evC k) ≤ 1 := measureReal_le_one
    have hC0 : 0 ≤ P.real (G.evC k) := measureReal_nonneg
    have hKt : K / t * P.real (G.evC k) ≤ ε / 2 * P.real (G.evC k) :=
      mul_le_mul_of_nonneg_right htK hC0
    have hLB : L * P.real (G.evBm k ∩ G.evBp k)ᶜ ≤ L * (ε / (2 * (1 + L))) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have hsum : L * (ε / (2 * (1 + L))) + ε / (2 * (1 + L)) = ε / 2 := by
      field_simp
      ring
    have hF2' : P.real (G.evX k ∩ {ω | t ≤ (G.U k ω).ncard}) ≤ K / t * P.real (G.evC k) := hF2
    nlinarith
  · -- `p = 1`
    have hp : p = 1 := Subtype.ext (le_antisymm p.2.2 hp1)
    subst hp
    refine key (1 / 2) one_half_pos fun G hG _ _ => ?_
    rw [real_eq_one_of_edgeSet_mem k (edgeSet_mem_evC k G hG)]
    linarith

/-- **Duminil-Copin–Sidoravicius–Tassion 2016, Theorem 1**: for every `k > 0`, bond
percolation on the slab `S_k = ℤ² × {0, …, k}` has no infinite cluster at its critical point,
`θ_{S_k}(p_c(S_k)) = 0` — the named fact `DuminilCopinSidoraviciusTassion2016` of
`HalfSpace.lean`, proved. The proof is the paper's: the finite-size criterion (§2.1, Lemmata
4–5, eqs. (10)–(13); `SlabCriticality.lean`, in the `u_n ≤ n/4` form of
`SlabCriticalityChain4.lean`), uniqueness of the infinite cluster (`SlabUniqueness.lean`), the
renormalisation step and dependent percolation (§2.2; `SlabCriticalityInputs.lean`), and the
Gluing Lemma 6 (§2.3) from Lemma 7 (`MultiValuedMapPrinciple.lean`), Fact 1
(`SlabGluingFact1.lean`) and Fact 2 (`SlabGluingFact2Core.lean`, `SlabGluingRouting.lean`, this
file). [cite: DuminilCopinSidoraviciusTassion2016, Thm. 1] -/
theorem DuminilCopinSidoraviciusTassion2016_holds : DuminilCopinSidoraviciusTassion2016 :=
  DuminilCopinSidoraviciusTassion2016.of_lemma6' DuminilCopinSidoraviciusTassion2016_lemma6'_holds

end Final

end Percolation.Literature

end
