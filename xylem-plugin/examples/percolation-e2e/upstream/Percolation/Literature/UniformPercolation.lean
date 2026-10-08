import Percolation.Literature.ConnectivityProofs
import Percolation.Literature.SharpnessDCTProofs
import Percolation.Util.Linter

/-!
# Uniform percolation from large sets: `P_p(S ↔ ∞) → 1` as `|S| → ∞`, uniformly in `S`

A strengthening of an input of the Martineau–Tassion form of the Grimmett–Marstrand renormalisation (S. Martineau,
V. Tassion, *Locality of percolation for abelian Cayley graphs*, Ann. Probab. 45 (2017), Lemma 3.6: "For all `ε > 0`,
there exists `m` such that, for any fixed self-avoiding path `γ` of length `m`, `P_p(γ ↔ ∞) > 1 - ε`"). We prove the
following stronger and shape-free statement for bond percolation on `ℤ^d` with `θ(p) > 0`:

* `exists_card_le_imp_lt_real_exists_percolatesAt` — **for every `η > 0` there is `m₀` such that
  every finite set `S ⊆ ℤ^d` with `|S| ≥ m₀` satisfies `P_p(some vertex of S lies in an infinite
  open cluster) > 1 - η`.**

The printed proof of Martineau–Tassion (diagonal extraction of an infinite self-avoiding path and
"any fixed infinite subset of `V` is intersected almost surely by the infinite component",
Lemma 3.4) is replaced by an elementary quantitative argument which needs neither ergodicity nor
mixing: a set of `K (4R+1)^d` vertices contains `K` vertices pairwise at sup-distance `> 2R`
(`exists_subset_card_eq_separated`, greedy); `{x ↮ ∞} ⊆ {x ↮ x + ∂Λ_R} ∪ ({x ↔ x + ∂Λ_R} \ {x ↔ ∞})`;
the local events `{xᵢ ↮ xᵢ + ∂Λ_R}` depend on the pairs of the disjoint boxes `xᵢ + Λ_R`, hence
are independent (`FiniteEnergy.bondPercolation_real_inter_of_disjoint`), each of probability
`1 - θ_R ≤ 1 - θ` where `θ_R = P_p(0 ↔ ∂Λ_R) ↓ θ` (`tendsto_real_siteToBoundary`); so
`P_p(S ↮ ∞) ≤ (1 - θ)^K + K (θ_R - θ)`, and one chooses `K`, then `R`.

## References

* S. Martineau, V. Tassion, *Locality of percolation for abelian Cayley graphs*, Ann. Probab. 45
  (2017) 1247–1277, arXiv:1312.1946, §3.3, Lemma 3.6 (the statement generalised here).
* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §1.4 (`θ(p) = lim P_p(0 ↔ ∂B(n))`),
  §2.2 (events depending on disjoint edge sets are independent).
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory Filter LatticeModels DCT16
open scoped Topology

variable {d : ℕ}

/-! ## `θ_R = P_p(0 ↔ ∂Λ_R)` decreases to `θ` -/

/-- **`P_p(0 ↔ ∂Λ_n) → θ(p)`** as `n → ∞` (Grimmett 1999, §1.4, `θ(p) = lim_{n→∞} P_p(0 ↔ ∂B(n))`):
the sequence is non-increasing (`real_siteToBoundary_antitone`), bounded below by `θ`
(`theta_le_real_siteToBoundary`), and any common lower bound is at most `θ`
(`le_theta_of_forall_le_real_siteToBoundary`). [cite: GrimmettPercolation1999, §1.4] -/
theorem tendsto_real_siteToBoundary (p : unitInterval) :
    Tendsto (fun n : ℕ => (bondPercolation (zdGraph d) p).real (siteToBoundary d n)) atTop
      (𝓝 (theta (zdGraph d) 0 p)) := by
  set f : ℕ → ℝ := fun n => (bondPercolation (zdGraph d) p).real (siteToBoundary d n) with hf
  have hanti : Antitone f := fun m n hmn => real_siteToBoundary_antitone p hmn
  have hbdd : BddBelow (Set.range f) := ⟨theta (zdGraph d) 0 p, by
    rintro _ ⟨n, rfl⟩; exact theta_le_real_siteToBoundary p n⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have heq : (⨅ n, f n) = theta (zdGraph d) 0 p := by
    refine le_antisymm ?_ (le_ciInf fun n => theta_le_real_siteToBoundary p n)
    exact le_theta_of_forall_le_real_siteToBoundary p fun n => ciInf_le hbdd n
  rwa [heq] at hlim

/-! ## Separated points in a large finite set -/

/-- Boxes are symmetric: `-x ∈ Λ_L ↔ x ∈ Λ_L`. [folklore] -/
theorem neg_mem_box_iff {L : ℕ} {x : Site d} : -x ∈ box d L ↔ x ∈ box d L := by
  simp only [mem_box, Pi.neg_apply]
  exact ⟨fun h i => by have := h i; omega, fun h i => by have := h i; omega⟩

/-- **Greedy extraction of separated points**: a finite set of at least `K · |Λ_{2R}|` vertices of
`ℤ^d` contains `K` vertices whose pairwise differences lie outside `Λ_{2R}` (sup-distance `> 2R`).
Remove a point together with the at most `|Λ_{2R}|` points of the set within sup-distance `2R` of it,
and recurse. [folklore] -/
theorem exists_subset_card_eq_separated (R : ℕ) :
    ∀ (K : ℕ) (S : Finset (Site d)), K * (box d (2 * R)).card ≤ S.card →
      ∃ T ⊆ S, T.card = K ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → y - x ∉ box d (2 * R) := by
  classical
  intro K
  induction K with
  | zero => intro S _; exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ K ih =>
    intro S hS
    have hcpos : 0 < (box d (2 * R)).card := Finset.card_pos.2 (box_nonempty d _)
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos]
      have : (box d (2 * R)).card ≤ (K + 1) * (box d (2 * R)).card :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos K)
      omega
    obtain ⟨x, hx⟩ := hSne
    -- the far part of `S`
    set S' := S.filter fun y => y - x ∉ box d (2 * R) with hS'
    have hnear : (S.filter fun y => y - x ∈ box d (2 * R)).card ≤ (box d (2 * R)).card := by
      refine Finset.card_le_card_of_injOn (fun y => y - x) (fun y hy => ?_) ?_
      · exact (Finset.mem_filter.1 hy).2
      · intro y _ y' _ h
        exact sub_left_injective h
    have hsplit : (S.filter fun y => y - x ∈ box d (2 * R)).card + S'.card = S.card := by
      rw [hS']
      exact Finset.card_filter_add_card_filter_not _
    have hS'card : K * (box d (2 * R)).card ≤ S'.card := by
      have : (K + 1) * (box d (2 * R)).card = K * (box d (2 * R)).card + (box d (2 * R)).card := by ring
      omega
    obtain ⟨T', hT'S', hT'card, hT'sep⟩ := ih S' hS'card
    have hxT' : x ∉ T' := by
      intro hxT
      have := (Finset.mem_filter.1 (hT'S' hxT)).2
      rw [sub_self] at this
      exact this (zero_mem_box d _)
    refine ⟨insert x T', ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx
      · exact (Finset.mem_filter.1 (hT'S' hy)).1
    · rw [Finset.card_insert_of_notMem hxT', hT'card]
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with hax | haT
      · rcases Finset.mem_insert.1 hb with hbx | hbT
        · exact absurd (hax.trans hbx.symm) hab
        · rw [hax]; exact (Finset.mem_filter.1 (hT'S' hbT)).2
      · rcases Finset.mem_insert.1 hb with hbx | hbT
        · have h := (Finset.mem_filter.1 (hT'S' haT)).2
          rw [hbx, ← neg_mem_box_iff, neg_sub]
          exact h
        · exact hT'sep a haT b hbT hab

/-! ## The local events `{x ↮ x + ∂Λ_R}` -/

/-- The translated one-arm event `{x ↔ x + ∂Λ_R in x + Λ_R}` is determined by the pairs of the
shifted box `x + Λ_R`. [cite: GrimmettPercolation1999, §2.2] -/
theorem determinedBy_zdArmEvent (x : Site d) (R : ℕ) :
    DeterminedBy (armEvent x R) ({z : Site d | z - x ∈ box d R}.sym2) := by
  have h : armEvent x R =
      ⋃ a ∈ {a : Site d | a - x ∈ innerBoundary (zdGraph d) (box d R)},
        openConnIn {z : Site d | z - x ∈ box d R} x a := by
    ext ω; simp [armEvent]
  rw [h]
  exact DeterminedBy.iUnion fun a => DeterminedBy.iUnion fun _ =>
    determinedBy_openConnIn _ x a subset_rfl

/-- The shifted box `x + Λ_R` as a finite set. [folklore] -/
theorem setOf_sub_mem_box_eq (x : Site d) (R : ℕ) :
    {z : Site d | z - x ∈ box d R} = ↑((box d R).image (· + x)) := by
  ext z
  simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨fun h => ⟨z - x, h, sub_add_cancel z x⟩, fun ⟨w, hw, hwz⟩ => by rw [← hwz, add_sub_cancel_right]; exact hw⟩

/-- The translated one-arm event is measurable. [folklore] -/
theorem measurableSet_zdArmEvent (x : Site d) (R : ℕ) : MeasurableSet (armEvent x R) := by
  have h := determinedBy_zdArmEvent x R
  rw [setOf_sub_mem_box_eq, ← Finset.coe_sym2] at h
  exact h.measurableSet_of_finset

/-- Pairs of two shifted boxes whose centres differ by a vector outside `Λ_{2R}` are disjoint:
a common pair would give a common vertex `z` with `z - x, z - y ∈ Λ_R`, so `y - x ∈ Λ_{2R}`.
[folklore] -/
theorem disjoint_sym2_shiftedBox {x y : Site d} {R : ℕ} (h : y - x ∉ box d (2 * R)) :
    Disjoint ({z : Site d | z - x ∈ box d R}.sym2) ({z : Site d | z - y ∈ box d R}.sym2) := by
  rw [Set.disjoint_left]
  intro e hex hey
  induction e using Sym2.ind with
  | h a b =>
    rw [Set.mk_mem_sym2_iff] at hex hey
    obtain ⟨hax, -⟩ := hex
    obtain ⟨hay, -⟩ := hey
    simp only [Set.mem_setOf_eq, mem_box] at hax hay
    apply h
    rw [mem_box]
    intro i
    have h1 := hax i
    have h2 := hay i
    simp only [Pi.sub_apply] at h1 h2 ⊢
    constructor <;> omega

/-- **An infinite cluster produces an arm**: for `ω ⊆ E(ℤ^d)`, if `|C(x)| = ∞` then
`x ↔ x + ∂Λ_R` inside `x + Λ_R` (the infinite cluster leaves the finite box; stop an open path to
a vertex outside at its first exit). [cite: GrimmettPercolation1999, §1.4] -/
theorem armEvent_of_percolatesAt {ω : BondConfig (Site d)} (hω : ω ⊆ (zdGraph d).edgeSet)
    {x : Site d} {R : ℕ} (h : ω ∈ percolatesAt x) : ω ∈ armEvent x R := by
  classical
  obtain ⟨z, hz, hzR⟩ : ∃ z ∈ openCluster ω x, z - x ∉ box d R := by
    by_contra hcon
    push Not at hcon
    refine h (((box d R).image (· + x)).finite_toSet.subset fun z hz => ?_)
    rw [Finset.coe_image]
    exact ⟨z - x, Finset.mem_coe.2 (hcon z hz), sub_add_cancel z x⟩
  exact armEvent_of_pathIn hω (pathIn_univ_of_reachable hz) (Or.inl hzR)

/-- `P_p({x ↔ x + ∂Λ_R} \ {x ↔ ∞}) = θ_R - θ`: the arm event contains the percolation event up to a
null set, and both probabilities do not depend on `x`. [cite: GrimmettPercolation1999, §1.4] -/
theorem real_armEvent_diff_percolatesAt (p : unitInterval) (x : Site d) (R : ℕ) :
    (bondPercolation (zdGraph d) p).real (armEvent x R \ percolatesAt x) =
      (bondPercolation (zdGraph d) p).real (siteToBoundary d R) - theta (zdGraph d) 0 p := by
  set μ := bondPercolation (zdGraph d) p
  have hmeas : MeasurableSet (percolatesAt x : Set (BondConfig (Site d))) :=
    measurableSet_percolatesAt_holds x
  have hunion : μ.real ((armEvent x R \ percolatesAt x) ∪ percolatesAt x) = μ.real (armEvent x R) := by
    refine real_congr_of_forall_subset_edgeSet (zdGraph d) p fun ω hω => ?_
    simp only [Set.sdiff_union_self, Set.mem_union]
    exact ⟨fun h' => h'.elim id fun hp => armEvent_of_percolatesAt hω hp, fun h' => Or.inl h'⟩
  have hdisj : Disjoint (armEvent x R \ percolatesAt x) (percolatesAt x) := Set.disjoint_sdiff_left
  rw [measureReal_union hdisj hmeas] at hunion
  have hθ : μ.real (percolatesAt x) = theta (zdGraph d) 0 p := theta_zdGraph_eq_theta_zero p x
  rw [real_armEvent] at hunion
  linarith

/-! ## Independence of the local events over separated centres -/

/-- **Product formula** for the complements of the one-arm events over pairwise separated centres:
`P_p(⋂_{x ∈ T} {x ↮ x + ∂Λ_R}) = ∏_{x ∈ T} P_p(x ↮ x + ∂Λ_R) = (1 - θ_R)^{|T|}` (events depending on
the pairs of pairwise disjoint boxes are independent; Grimmett 1999, §2.2).
[cite: GrimmettPercolation1999, §2.2] -/
theorem real_iInter_compl_armEvent (p : unitInterval) (R : ℕ) (T : Finset (Site d))
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → y - x ∉ box d (2 * R)) :
    (bondPercolation (zdGraph d) p).real (⋂ x ∈ T, (armEvent x R)ᶜ) =
      (1 - (bondPercolation (zdGraph d) p).real (siteToBoundary d R)) ^ T.card := by
  classical
  set μ := bondPercolation (zdGraph d) p
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T haT ih =>
    have hsepT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → y - x ∉ box d (2 * R) := fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have hT := ih hsepT
    -- split off the event at `a`
    have hset : (⋂ x ∈ insert a T, (armEvent x R)ᶜ) = (armEvent a R)ᶜ ∩ ⋂ x ∈ T, (armEvent x R)ᶜ := by
      ext ω; simp
    rw [hset]
    -- determining sets
    have hA : DeterminedBy (armEvent a R)ᶜ ({z : Site d | z - a ∈ box d R}.sym2) :=
      (determinedBy_zdArmEvent a R).compl
    have hB : DeterminedBy (⋂ x ∈ T, (armEvent x R)ᶜ) (⋃ x ∈ T, {z : Site d | z - x ∈ box d R}.sym2) := by
      have : (⋂ x ∈ T, (armEvent x R)ᶜ) = (⋃ x ∈ T, armEvent x R)ᶜ := by ext ω; simp
      rw [this]
      exact (DeterminedBy.iUnion fun x => DeterminedBy.iUnion fun hx =>
        (determinedBy_zdArmEvent x R).mono (Set.subset_biUnion_of_mem (u := fun x => {z : Site d | z - x ∈ box d R}.sym2) hx)).compl
    have hdisj : Disjoint ({z : Site d | z - a ∈ box d R}.sym2) (⋃ x ∈ T, {z : Site d | z - x ∈ box d R}.sym2) := by
      rw [Set.disjoint_iUnion₂_right]
      intro x hx
      have hax : a ≠ x := fun h => haT (h ▸ hx)
      exact disjoint_sym2_shiftedBox (hsep a (Finset.mem_insert_self a T) x (Finset.mem_insert_of_mem hx) hax)
    have hAm : MeasurableSet (armEvent a R)ᶜ := (measurableSet_zdArmEvent a R).compl
    have hBm : MeasurableSet (⋂ x ∈ T, (armEvent x R)ᶜ) :=
      MeasurableSet.biInter T.countable_toSet fun x _ => (measurableSet_zdArmEvent x R).compl
    rw [bondPercolation_real_inter_of_disjoint (zdGraph d) p hdisj hA hB hAm hBm, hT,
      measureReal_compl (measurableSet_zdArmEvent a R), probReal_univ, real_armEvent,
      Finset.card_insert_of_notMem haT, pow_succ, mul_comm]

/-! ## The theorem -/

/-- **Uniform percolation from large sets** (the shape-free form of Martineau–Tassion 2017,
Lemma 3.6): if `θ(p) > 0` on `ℤ^d` then for every `η > 0` there is `m₀` such that for EVERY finite
`S ⊆ ℤ^d` with `|S| ≥ m₀`, `P_p(∃ y ∈ S, |C(y)| = ∞) > 1 - η`. Proof: with `θ_R = P_p(0 ↔ ∂Λ_R)`,
pick `K` with `(1-θ)^K < η/2`, then `R` with `K (θ_R - θ) < η/2`, and `m₀ = K |Λ_{2R}|`; extract `K`
points of `S` pairwise at sup-distance `> 2R`; then
`P_p(no y ∈ S percolates) ≤ ∏ᵢ P_p(xᵢ ↮ xᵢ + ∂Λ_R) + Σᵢ P_p({xᵢ ↔ xᵢ + ∂Λ_R} \ {xᵢ ↔ ∞})
 = (1 - θ_R)^K + K(θ_R - θ) < η`. [cite: GrimmettPercolation1999, §1.4 and §2.2] -/
theorem exists_card_le_imp_lt_real_exists_percolatesAt (p : unitInterval)
    (hθ : 0 < theta (zdGraph d) (0 : Site d) p) {η : ℝ} (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ S : Finset (Site d), m₀ ≤ S.card →
      1 - η < (bondPercolation (zdGraph d) p).real {ω | ∃ y ∈ S, ω ∈ percolatesAt y} := by
  classical
  set μ := bondPercolation (zdGraph d) p with hμ
  set θ := theta (zdGraph d) (0 : Site d) p with hθdef
  have hθ1 : θ ≤ 1 := measureReal_le_one
  -- choose `K`
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 - θ) ^ K < η / 2 :=
    exists_pow_lt_of_lt_one (half_pos hη) (by linarith)
  -- choose `R`
  have hev : ∀ᶠ R : ℕ in atTop, μ.real (siteToBoundary d R) < θ + η / (2 * (K + 1)) := by
    have ht := tendsto_real_siteToBoundary (d := d) p
    have hpos : 0 < η / (2 * (K + 1)) := by positivity
    exact ht.eventually (gt_mem_nhds (by rw [← hθdef]; linarith))
  obtain ⟨R, hR⟩ := hev.exists
  refine ⟨K * (box d (2 * R)).card, fun S hS => ?_⟩
  obtain ⟨T, hTS, hTcard, hTsep⟩ := exists_subset_card_eq_separated R K S hS
  -- the bad event and its cover
  have hcover : {ω : BondConfig (Site d) | ∃ y ∈ S, ω ∈ percolatesAt y}ᶜ ⊆
      (⋂ x ∈ T, (armEvent x R)ᶜ) ∪ ⋃ x ∈ T, (armEvent x R \ percolatesAt x) := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and] at hω
    by_cases hall : ∀ x ∈ T, ω ∉ armEvent x R
    · exact Or.inl (by simpa using hall)
    · push Not at hall
      obtain ⟨x, hxT, hx⟩ := hall
      exact Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hxT) ⟨hx, hω x (hTS hxT)⟩)
  have hmeasS : MeasurableSet {ω : BondConfig (Site d) | ∃ y ∈ S, ω ∈ percolatesAt y} := by
    have : {ω : BondConfig (Site d) | ∃ y ∈ S, ω ∈ percolatesAt y} = ⋃ y ∈ S, percolatesAt y := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.biUnion S.countable_toSet fun y _ => measurableSet_percolatesAt_holds y
  -- estimate
  have h1 : μ.real (⋂ x ∈ T, (armEvent x R)ᶜ) ≤ (1 - θ) ^ K := by
    rw [real_iInter_compl_armEvent p R T hTsep, hTcard]
    exact pow_le_pow_left₀ (sub_nonneg.2 measureReal_le_one) (by linarith [theta_le_real_siteToBoundary (d := d) p R]) K
  have h2 : μ.real (⋃ x ∈ T, (armEvent x R \ percolatesAt x)) ≤ K * (μ.real (siteToBoundary d R) - θ) := by
    calc μ.real (⋃ x ∈ T, (armEvent x R \ percolatesAt x))
        ≤ ∑ x ∈ T, μ.real (armEvent x R \ percolatesAt x) := measureReal_biUnion_finset_le _ _
      _ = ∑ _x ∈ T, (μ.real (siteToBoundary d R) - θ) := by
          refine Finset.sum_congr rfl fun x _ => real_armEvent_diff_percolatesAt p x R
      _ = K * (μ.real (siteToBoundary d R) - θ) := by rw [Finset.sum_const, hTcard, nsmul_eq_mul]
  have h3 : (K : ℝ) * (μ.real (siteToBoundary d R) - θ) ≤ η / 2 := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hlt : μ.real (siteToBoundary d R) - θ < η / (2 * (K + 1)) := by linarith
    have hKK : (K : ℝ) * (η / (2 * (K + 1))) ≤ η / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_left hlt.le hK0
    linarith
  have hbad : μ.real {ω : BondConfig (Site d) | ∃ y ∈ S, ω ∈ percolatesAt y}ᶜ < η := by
    calc μ.real {ω : BondConfig (Site d) | ∃ y ∈ S, ω ∈ percolatesAt y}ᶜ
        ≤ μ.real ((⋂ x ∈ T, (armEvent x R)ᶜ) ∪ ⋃ x ∈ T, (armEvent x R \ percolatesAt x)) :=
          measureReal_mono hcover
      _ ≤ μ.real (⋂ x ∈ T, (armEvent x R)ᶜ) + μ.real (⋃ x ∈ T, (armEvent x R \ percolatesAt x)) :=
          measureReal_union_le _ _
      _ < η := by linarith
  rw [measureReal_compl hmeasS, probReal_univ] at hbad
  linarith

end Percolation.Literature
