import Percolation.Literature.KozmaNitzanPreFKG
import Percolation.Util.Linter

/-!
# Kozma–Nitzan's "`0` close to `A`" theorem for monotone cluster properties (Theorem 8, event form), and the case `|A| = 2` (Theorem 7, event form)

Source: G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a conjectured inequality*,
arXiv:2401.12397 (2024) [KozmaNitzan2024], §5.1
(pp. 31–32: monotone cluster properties, **Conjecture 4**, **Theorem 8**), with the tools of §2.2 and
§3.2 (Lemma 3, Lemma 5, Theorem 4 — reproduced for the connection events `{· ↔ b}` in
`KozmaNitzanPreFKG.lean`).  Everything in this file is proved (from the BHK theorems, via the event
forms `KNPreFKG.bhk_one_upper_lower` / `KNPreFKG.bhk_two_upper_lower`).

## Printed statements (arXiv:2401.12397, pp. 31–32)

§5.1 (p. 31): "Let `G` be a graph and let `f : G × {0,1}^{E(G)} → ℝ`. We say that `f` is a monotone
cluster property if it satisfies the following two requirements: (1) `f(v, ω)` depends only on `C_ω(v)`
the cluster of `v` in `ω`, and is increasing in it, i.e. if `C_ω(v) ⊆ C_ξ(v)` then `f(v, ω) ≤ f(v, ξ)`.
(2) if `{v, w} ∈ ω` then `f(v, ω) = f(w, ω)`."  (Here `C_ω(v) = {w : v ↔_ω w}`, p. 4 — the VERTEX cluster.)

**Conjecture 4** (p. 32): "For any graph `G`, any monotone cluster property `f`, any `A ⊂ G` and any
`0 ∈ G`, `E(f(0)·𝟙{0 ↔ A}) ≥ min_{a∈A} E(f(a)·𝟙{0 ↔ A})`."

**Theorem 8** (p. 32): "Conjecture 4 holds in any `G` in which `0` is an isolated vertex in `G ∖ A`,
for any `f`."  ("We omit the proof of these theorems, as they do not contain any ideas which we did
not already use in § 3.")

## What is reproduced, and how

The `{0,1}`-VALUED monotone cluster properties are exactly the indicators `f(v, ω) = 𝟙[P(C_ω(v))]` of a
monotone (upward closed) predicate `P` on vertex sets (requirement (2) is automatic: joined vertices have
the same cluster).  For these, Theorem 8 reads: if `0` is isolated in `G ∖ A` and `A ≠ ∅` then for some
`a ∈ A`, `P(P(C(a)), 0 ↔ A) ≤ P(P(C(0)), 0 ↔ A)` — `KozmaNitzan2024_thm8_event` below, proved along the
printed proof of Theorem 4 (pp. 13–14) with the connection event `{x ↔ b}` replaced by `{P(C(x))}`:

* `KozmaNitzan2024_lemma3_ii_cluster` — Lemma 3(ii) for a monotone cluster property: if
  `P(P(C(a₁))) ≤ P(P(C(a₂))) + δ` and `Q` is a decreasing event in the (edge) cluster of `a₁`, then
  `P(P(C(a₁)), Q) ≤ P(P(C(a₂)), Q) + δ` (BHK Thm. 1.3 inside `C_{a₁}`, Thm. 1.5 across `C_{a₂}`/`C_{a₁}`,
  given `{a₁ ↮ a₂}`; on `{a₁ ↔ a₂}` the two events coincide).
* `KozmaNitzan2024_lemma5_cluster` — Lemma 5 for a monotone cluster property: for `a, v ≠ 0`, `v ∈ B`,
  if `P_{G∖{0}}(P(C(a))) ≤ P_{G∖{0}}(P(C(v)))` then `P(P(C(a)), σ_B) ≤ P(P(C(0)), σ_B)`, `σ_B` the star
  event of Lemma 5.  Under `σ_B` the cluster of `0` is `{0} ∪ ⋃_{u ∈ B} C_{G∖0}(u)`; the cluster of `a`
  is `C_{G∖0}(a)` if `a ↮ B` off `0`, and is contained in `C(0)` otherwise (`KNPreFKG.walk_decomp`); on
  `G ∖ {0}`, Lemma 3(ii) with `Q = {a ↮ B}` gives `P(P(C(a)), a ↮ B) ≤ P(P(C(v)), a ↮ B) ≤
  P(P({0} ∪ C(B)), a ↮ B)`, and the star of `0` is independent of the pairs off `0`.
* `KozmaNitzan2024_thm7_event` — **Theorem 7** (p. 32: "Conjecture 4 holds when `|A| = 2`, for any
  `f`"; proof omitted in print) for `{0,1}`-valued monotone cluster properties, proved along the printed
  proof of Theorem 1 (pp. 7–8) with `{aᵢ ↔ b}` replaced by `{P(C(aᵢ))}`: subtract the common event
  `{0 ↔ aᵢ}` (on which `C(0) = C(aᵢ)`), then "BHK 4 times" given `{a₁ ↮ a₂}` (`KNPreFKG.clusterProp_pair`).
* `KozmaNitzan2024_thm8_event` — Theorem 8 for `{0,1}`-valued monotone cluster properties, by summing
  Lemma 5 over the stars `σ_B`, `∅ ≠ B ⊆ A` (`KNPreFKG.real_eq_sum_inter_starEvent`), with `a₀ ∈ A`
  minimising `P_{G∖{0}}(P(C(a)))`.

General form: the printed Theorems 7 and 8 for REAL-valued monotone cluster properties `f`
(conclusion `E(f(0)𝟙{0↔A}) ≥ min_a E(f(a)𝟙{0↔A})`) are proved in the companion file
`KozmaNitzanClusterPropertyReal.lean` (which imports this one): `KozmaNitzan2024_lemma3_ii_real`,
`KozmaNitzan2024_lemma5_real`, `KozmaNitzan2024_thm8_real`, `KozmaNitzan2024_thm7_real` (integrals
in place of probabilities along the same printed proofs), the printed generality
`KozmaNitzan2024_thm8_clusterProperty` / `KozmaNitzan2024_thm7_clusterProperty` (`f(v,ω) =
F(C_ω(v))`, `F` increasing along nonempty vertex sets), and the instance `f(v,ω) = |C_ω(v) ∩ A|`.

Transcription (as in `KozmaNitzanPreFKG.lean`): finite weighted graph = `w : Sym2 V → [0,1]` on a
finite vertex type, `μ = prodBernoulli w`, `C_ω(x) = openCluster ω x`, "`0` isolated in `G ∖ A`" =
`∀ u ≠ 0, u ∉ A → w s(0,u) = 0`, `P_{G∖{0}}(P(C(x)))` = `μ {ω | P {y | ω ∈ openConnIn {0}ᶜ x y}}` (the
cluster of `x` in the graph with `0` deleted is the set of vertices joined to `x` by an open path avoiding
`0`), `σ_B = starEvent 0 B`.

## A consequence

With `P(S) = (k ≤ |S ∩ A|)` Theorem 8 gives `P(|C(a₀) ∩ A| ≥ k, 0 ↔ A) ≤ P(|C(0) ∩ A| ≥ k)`, i.e. a
cumulative isolation lemma `∃ a ∈ A, P(1 ≤ |C(0)∩A| ≤ j) ≤ P(|C(a)∩A| ≤ j)` on every weighted graph
whose observer `0` is joined only to vertices of `A`.
-/

noncomputable section

open MeasureTheory Set
open Percolation.Literature.LatticeModels (prodBernoulli)

namespace Percolation.Literature

variable {V : Type*}

namespace KNPreFKG

/-! ### Monotone cluster properties read off the open edge cluster -/

/-- The vertex cluster from the edge cluster: `C(s) = {a | a = s ∨ ∃ e ∈ C_s, a ∈ e}`.
[cite: VandenbergHaggstromKahn2005, §1 p. 3] -/
theorem openCluster_eq_setOf_openEdgeCluster (ω : BondConfig V) (s : V) :
    openCluster ω s = {a | a = s ∨ ∃ e ∈ openEdgeCluster ω s, a ∈ e} := by
  ext a
  exact reachable_iff_exists_mem_openEdgeCluster ω s a

/-- The family of edge sets whose vertex span (together with `s`) has the monotone property `P`.
For monotone `P` it is an upper family. [cite: KozmaNitzan2024, §5.1 (p. 31, requirement (1))] -/
theorem isUpperSet_clusterPropFamily (s : V) (P : Set V → Prop)
    (hP : ∀ S T : Set V, S ⊆ T → P S → P T) :
    IsUpperSet {C : Set (Sym2 V) | P {a | a = s ∨ ∃ e ∈ C, a ∈ e}} := by
  intro C C' hCC' hC
  refine hP _ _ (fun a ha => ?_) hC
  rcases ha with h | ⟨e, he, hae⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hCC' he, hae⟩

/-- `{P(C(s))}` is the event that `C_s` lies in the family of `isUpperSet_clusterPropFamily`.
[cite: KozmaNitzan2024, §5.1 (p. 31)] -/
theorem setOf_prop_openCluster_eq (s : V) (P : Set V → Prop) :
    {ω : BondConfig V | P (openCluster ω s)} =
      {ω | openEdgeCluster ω s ∈ {C : Set (Sym2 V) | P {a | a = s ∨ ∃ e ∈ C, a ∈ e}}} := by
  ext ω
  simp only [mem_setOf_eq, openCluster_eq_setOf_openEdgeCluster]

/-- Joined vertices have the same cluster (requirement (2) of a monotone cluster property is automatic
for functions of the vertex cluster). [cite: KozmaNitzan2024, §5.1 (p. 32, first line)] -/
theorem openCluster_eq_of_reachable {ω : BondConfig V} {x y : V} (h : (openGraph ω).Reachable x y) :
    openCluster ω x = openCluster ω y := by
  ext a
  exact ⟨fun ha => h.symm.trans ha, fun ha => h.trans ha⟩

end KNPreFKG

/-! ### Lemma 3(ii) for a monotone cluster property -/

section Lemma3

open KNPreFKG

variable [Fintype V]

/-- **Kozma–Nitzan 2024, Lemma 3(ii), for a `{0,1}`-valued monotone cluster property** (pp. 6–7 with
§5.1, p. 31): if `P` is a monotone predicate on vertex sets, `P(P(C(a₁))) ≤ P(P(C(a₂))) + δ` with `δ ≥ 0`,
and `Q = {C_{a₁} ∈ 𝒬}` is a decreasing event in the (edge) cluster of `a₁`, then
`P(P(C(a₁)), Q) ≤ P(P(C(a₂)), Q) + δ`.  Proof as printed for `{aᵢ ↔ b}`: on `{a₁ ↔ a₂}` the two events
coincide (same cluster); on `D = {a₁ ↮ a₂}`, BHK Thm. 1.3 (increasing × decreasing in `C_{a₁}`) and
Thm. 1.5 (increasing in `C_{a₂}` × decreasing in `C_{a₁}`). [cite: KozmaNitzan2024, Lemma 3(ii) (pp. 6–7) and §5.1 (p. 31)] -/
theorem KozmaNitzan2024_lemma3_ii_cluster (w : Sym2 V → unitInterval) (a₁ a₂ : V) (P : Set V → Prop)
    (hP : ∀ S T : Set V, S ⊆ T → P S → P T) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : (prodBernoulli w).real {ω | P (openCluster ω a₁)} ≤
      (prodBernoulli w).real {ω | P (openCluster ω a₂)} + δ)
    {𝒬 : Set (Set (Sym2 V))} (h𝒬 : IsLowerSet 𝒬) :
    (prodBernoulli w).real ({ω | P (openCluster ω a₁)} ∩ {ω | openEdgeCluster ω a₁ ∈ 𝒬}) ≤
      (prodBernoulli w).real ({ω | P (openCluster ω a₂)} ∩ {ω | openEdgeCluster ω a₁ ∈ 𝒬}) + δ := by
  classical
  set μ := prodBernoulli w with hμ
  set X₁ : Set (BondConfig V) := {ω | P (openCluster ω a₁)} with hX₁
  set X₂ : Set (BondConfig V) := {ω | P (openCluster ω a₂)} with hX₂
  set Q : Set (BondConfig V) := {ω | openEdgeCluster ω a₁ ∈ 𝒬} with hQ
  by_cases h12 : a₁ = a₂
  · subst h12
    linarith [h]
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  -- on `Dᶜ` the two events agree (same cluster)
  have hagree : X₁ ∩ Dᶜ = X₂ ∩ Dᶜ := by
    ext ω
    simp only [mem_inter_iff, mem_compl_iff, mem_setOf_eq, not_not, hX₁, hX₂, hD]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [← openCluster_eq_of_reachable h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [openCluster_eq_of_reachable h2], h2⟩
  -- split every event along `D`
  have hsplit : ∀ A : Set (BondConfig V), μ.real A = μ.real (A ∩ D) + μ.real (A ∩ Dᶜ) := by
    intro A
    rw [← measureReal_inter_add_sdiff (s := A) (MeasurableSet.of_discrete : MeasurableSet D),
      Set.sdiff_eq]
  -- the hypothesis restricted to `D`
  have hH : μ.real (D ∩ X₁) ≤ μ.real (D ∩ X₂) + δ := by
    have h' := h
    rw [hsplit X₁, hsplit X₂, hagree] at h'
    rw [inter_comm D X₁, inter_comm D X₂]
    linarith
  -- the events in edge-cluster form
  have hX₁e : X₁ = {ω | openEdgeCluster ω a₁ ∈ {C : Set (Sym2 V) | P {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e}}} :=
    setOf_prop_openCluster_eq a₁ P
  have hX₂e : X₂ = {ω | openEdgeCluster ω a₂ ∈ {C : Set (Sym2 V) | P {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e}}} :=
    setOf_prop_openCluster_eq a₂ P
  -- (1) one-cluster BHK: `s = a₁`, `X = {a₂}`, increasing `X₁`, decreasing `Q`
  have hD1 : {ω : BondConfig V | ∀ x ∈ ({a₂} : Set V), ¬ (openGraph ω).Reachable a₁ x} = D := by
    ext ω
    simp [hD]
  have h1 := bhk_one_upper_lower w a₁ ({a₂} : Set V) (by simpa using h12)
    (isUpperSet_clusterPropFamily a₁ P hP) h𝒬
  rw [hD1, ← hX₁e] at h1
  -- (3) two-cluster BHK: `s = a₂`, `t = a₁`, increasing `X₂` in `C_{a₂}`, decreasing `Q` in `C_{a₁}`
  have hD2 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ a₁} = D := by
    ext ω
    simp only [mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have h3 := bhk_two_upper_lower w a₂ a₁ (Ne.symm h12) (isUpperSet_clusterPropFamily a₂ P hP) h𝒬
  rw [hD2, ← hX₂e] at h3
  have hQD : μ.real (D ∩ Q) ≤ μ.real D := measureReal_mono inter_subset_left
  -- the inequality on `D`
  have hcore : μ.real (X₁ ∩ Q ∩ D) ≤ μ.real (X₂ ∩ Q ∩ D) + δ := by
    rw [inter_comm (X₁ ∩ Q) D, inter_comm (X₂ ∩ Q) D]
    by_cases hD0 : μ.real D = 0
    · have h0 : μ.real (D ∩ (X₁ ∩ Q)) = 0 :=
        le_antisymm ((measureReal_mono inter_subset_left).trans hD0.le) measureReal_nonneg
      rw [h0]
      exact add_nonneg measureReal_nonneg hδ
    · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
      have hchain : μ.real D * μ.real (D ∩ (X₁ ∩ Q)) ≤
          μ.real D * (μ.real (D ∩ (X₂ ∩ Q)) + δ) := by
        calc μ.real D * μ.real (D ∩ (X₁ ∩ Q))
            ≤ μ.real (D ∩ X₁) * μ.real (D ∩ Q) := h1
          _ ≤ (μ.real (D ∩ X₂) + δ) * μ.real (D ∩ Q) :=
              mul_le_mul_of_nonneg_right hH measureReal_nonneg
          _ = μ.real (D ∩ X₂) * μ.real (D ∩ Q) + δ * μ.real (D ∩ Q) := by ring
          _ ≤ μ.real D * μ.real (D ∩ (X₂ ∩ Q)) + δ * μ.real D :=
              add_le_add h3 (mul_le_mul_of_nonneg_left hQD hδ)
          _ = μ.real D * (μ.real (D ∩ (X₂ ∩ Q)) + δ) := by ring
      exact le_of_mul_le_mul_left hchain hDpos
  -- conclude by adding the parts on `Dᶜ`, where the events coincide
  have hagreeQ : X₁ ∩ Q ∩ Dᶜ = X₂ ∩ Q ∩ Dᶜ := by
    rw [inter_right_comm, hagree, inter_right_comm]
  calc μ.real (X₁ ∩ Q) = μ.real (X₁ ∩ Q ∩ D) + μ.real (X₁ ∩ Q ∩ Dᶜ) := hsplit _
    _ ≤ μ.real (X₂ ∩ Q ∩ D) + δ + μ.real (X₂ ∩ Q ∩ Dᶜ) := by
        rw [hagreeQ]
        linarith [hcore]
    _ = μ.real (X₂ ∩ Q) + δ := by
        rw [hsplit (X₂ ∩ Q)]
        ring

/-- **Lemma 3(ii) for a monotone cluster property, with `δ = 0` and `Q = {a₁ ↮ B}`** (the form used for
Lemma 5): if `P(P(C(a₁))) ≤ P(P(C(a₂)))` then `P(P(C(a₁)), a₁ ↮ B) ≤ P(P(C(a₂)), a₁ ↮ B)` for every
vertex set `B`. [cite: KozmaNitzan2024, Lemma 3(ii) (pp. 6–7) and §5.1 (p. 31)] -/
theorem KozmaNitzan2024_lemma3_ii_cluster_notConn (w : Sym2 V → unitInterval) (a₁ a₂ : V)
    (P : Set V → Prop) (hP : ∀ S T : Set V, S ⊆ T → P S → P T) (B : Set V)
    (h : (prodBernoulli w).real {ω | P (openCluster ω a₁)} ≤
      (prodBernoulli w).real {ω | P (openCluster ω a₂)}) :
    (prodBernoulli w).real ({ω | P (openCluster ω a₁)} ∩
        {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a₁ u}) ≤
      (prodBernoulli w).real ({ω | P (openCluster ω a₂)} ∩
        {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a₁ u}) := by
  have key := KozmaNitzan2024_lemma3_ii_cluster w a₁ a₂ P hP le_rfl (by simpa using h)
    (isLowerSet_disconnFamily a₁ B)
  rw [← setOf_forall_not_reachable_eq, add_zero] at key
  exact key

end Lemma3

/-! ### Lemma 5 for a monotone cluster property -/

namespace KNPreFKG

/-- The vertices joined to `x` by an open path avoiding `0` are the image of the cluster of `x` in the
restricted configuration on `{0}ᶜ` (`G ∖ {0}`). [folklore] -/
theorem image_openCluster_restrictConfig (o : V) (ω : BondConfig V) (x : ({o}ᶜ : Set V)) :
    Subtype.val '' openCluster (restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ω) x =
      {y | ω ∈ openConnIn ({o}ᶜ : Set V) (x : V) y} := by
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact (reachable_restrictConfig_val_iff _ ω x y').1 hy'
  · intro hy
    have hyS : y ∈ ({o}ᶜ : Set V) := by
      obtain ⟨_, hy2, _⟩ := hy
      exact hy2
    exact ⟨⟨y, hyS⟩, (reachable_restrictConfig_val_iff _ ω x ⟨y, hyS⟩).2 hy, rfl⟩

/-- Pull-back of the event `{P(C(x))}` of `G ∖ {0}` (read through the image in `G`) along the
restriction: it is the event that the set of vertices joined to `x` off `0` has `P`. [folklore] -/
theorem preimage_setOf_prop_openCluster (o : V) (P : Set V → Prop) (x : ({o}ᶜ : Set V)) :
    restrictConfig (Subtype.val : ({o}ᶜ : Set V) → V) ⁻¹'
        {ω' | P (Subtype.val '' openCluster ω' x)} =
      {ω : BondConfig V | P {y | ω ∈ openConnIn ({o}ᶜ : Set V) (x : V) y}} := by
  ext ω
  rw [mem_preimage, mem_setOf_eq, mem_setOf_eq, image_openCluster_restrictConfig]

section Measure

variable [Fintype V]

/-- **The gluing step on `G ∖ {0}` for a monotone cluster property** (from Lemma 3(ii) with
`Q = {a ↮ B}`): if `P(P(C(a))) ≤ P(P(C(v)))` for some vertex `v`, then for every set `Z` of
configurations containing `{P(C(v))}` (in the application `v ∈ B`),
`P(({P(C(a))} ∩ {a ↮ B}) ∪ ({a ↔ B} ∩ Z)) ≤ P(Z)`.  (Used with `Z = {P({0} ∪ C(B))}`: the property of
`a`'s cluster, when `a` is cut from the glued set `B`, is paid for by the property of `B`'s cluster.)
[cite: KozmaNitzan2024, Lemma 5 (p. 13) and §5.1 (p. 32, Thm. 8)] -/
theorem real_union_le_of_le_cluster (w : Sym2 V → unitInterval) (a v : V) (B : Set V)
    (P : Set V → Prop) (hP : ∀ S T : Set V, S ⊆ T → P S → P T) (Z : Set (BondConfig V))
    (hvZ : {ω : BondConfig V | P (openCluster ω v)} ⊆ Z)
    (h : (prodBernoulli w).real {ω | P (openCluster ω a)} ≤
      (prodBernoulli w).real {ω | P (openCluster ω v)}) :
    (prodBernoulli w).real (({ω : BondConfig V | P (openCluster ω a)} ∩
          {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a u}) ∪
        ({ω | ∃ u ∈ B, (openGraph ω).Reachable a u} ∩ Z)) ≤
      (prodBernoulli w).real Z := by
  classical
  set μ := prodBernoulli w with hμ
  set X : Set (BondConfig V) := {ω | P (openCluster ω a)} with hX
  set Y : Set (BondConfig V) := {ω | ∃ u ∈ B, (openGraph ω).Reachable a u} with hY
  set N : Set (BondConfig V) := {ω | ∀ u ∈ B, ¬ (openGraph ω).Reachable a u} with hN
  have L3 := KozmaNitzan2024_lemma3_ii_cluster_notConn w a v P hP B h
  -- `{P(C(v)), a ↮ B} ⊆ Z ∩ N`
  have h2 : μ.real ({ω : BondConfig V | P (openCluster ω v)} ∩ N) ≤ μ.real (Z ∩ N) :=
    measureReal_mono fun ω ⟨h1, hn⟩ => ⟨hvZ h1, hn⟩
  -- `Y ∩ Z ⊆ Z ∖ N`
  have hYN : Y ∩ Z ⊆ Z ∩ Nᶜ := by
    rintro ω ⟨⟨u, hu, hau⟩, hz⟩
    exact ⟨hz, fun hn => hn u hu hau⟩
  have hsplit : μ.real Z = μ.real (Z ∩ N) + μ.real (Z ∩ Nᶜ) := by
    rw [← measureReal_inter_add_sdiff (s := Z) (MeasurableSet.of_discrete : MeasurableSet N),
      Set.sdiff_eq]
  calc μ.real ((X ∩ N) ∪ (Y ∩ Z)) ≤ μ.real (X ∩ N) + μ.real (Y ∩ Z) := measureReal_union_le _ _
    _ ≤ μ.real (Z ∩ N) + μ.real (Z ∩ Nᶜ) := add_le_add (L3.trans h2) (measureReal_mono hYN)
    _ = μ.real Z := hsplit.symm

end Measure

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan's Lemma 5 for a `{0,1}`-valued monotone cluster property** (Lemma 5, p. 13, with
`{x ↔ b}` replaced by `{P(C(x))}`, `P` monotone on vertex sets — the step behind Theorem 8, p. 32).
Let `a, v ≠ 0`, `v ∈ B`, and suppose that in `G ∖ {0}` the cluster of `a` has `P` at most as often as
the cluster of `v`: `P_{G∖{0}}(P(C(a))) ≤ P_{G∖{0}}(P(C(v)))`.  Then `P(P(C(a)), σ_B) ≤ P(P(C(0)), σ_B)`,
`σ_B` the event that the open pairs at `0` are exactly those to `B`.  Proof: under `σ_B` an open path from
`a` either avoids `0` or enters and leaves `0` through `B` (`walk_decomp`); so if `a ↮ B` off `0` then
`C(a) = C_{G∖0}(a)`, and otherwise `C(a) ⊆ {0} ∪ C_{G∖0}(B) ⊆ C(0)`.  On `G ∖ {0}` the gluing step
`real_union_le_of_le_cluster` (Lemma 3(ii), i.e. BHK) bounds the pulled-back event by
`{P({0} ∪ C_{G∖0}(B))}`, and the star of `0` is independent of the pairs off `0`.
[cite: KozmaNitzan2024, Lemma 5 (p. 13) and Thm. 8 (p. 32)] -/
theorem KozmaNitzan2024_lemma5_cluster {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (o a v : V) (B : Set V) (P : Set V → Prop) (hP : ∀ S T : Set V, S ⊆ T → P S → P T)
    (hao : a ≠ o) (hvo : v ≠ o) (hvB : v ∈ B)
    (hyp : (prodBernoulli w).real {ω | P {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y}} ≤
      (prodBernoulli w).real {ω | P {y | ω ∈ openConnIn ({o}ᶜ : Set V) v y}}) :
    (prodBernoulli w).real ({ω | P (openCluster ω a)} ∩ starEvent o B) ≤
      (prodBernoulli w).real ({ω | P (openCluster ω o)} ∩ starEvent o B) := by
  classical
  set μ := prodBernoulli w with hμ
  -- the graph `G ∖ {0}`
  set S : Set V := {o}ᶜ with hS
  haveI : Fintype S := Fintype.ofFinite S
  set f : S → V := Subtype.val with hf
  set w' : Sym2 S → unitInterval := w ∘ Sym2.map f with hw'
  set μ' := prodBernoulli w' with hμ'
  have haS : a ∈ S := mem_compl_singleton_iff.2 hao
  have hvS : v ∈ S := mem_compl_singleton_iff.2 hvo
  set a' : S := ⟨a, haS⟩ with ha'
  set v' : S := ⟨v, hvS⟩ with hv'
  set B' : Set S := {u | (u : V) ∈ B} with hB'
  have hvB' : v' ∈ B' := hvB
  -- the property transported to vertex sets of `G ∖ {0}` (read back in `G`)
  set P' : Set S → Prop := fun T => P (Subtype.val '' T) with hP'
  have hP'mono : ∀ T T' : Set S, T ⊆ T' → P' T → P' T' :=
    fun T T' hTT' hT => hP _ _ (image_mono hTT') hT
  -- the hypothesis, read on `G ∖ {0}`
  have hyp' : μ'.real {ω' | P' (openCluster ω' a')} ≤ μ'.real {ω' | P' (openCluster ω' v')} := by
    rw [hμ', hw', hf, ← real_preimage_restrictConfig_val, ← real_preimage_restrictConfig_val,
      preimage_setOf_prop_openCluster, preimage_setOf_prop_openCluster]
    exact hyp
  -- the events on `G ∖ {0}`
  set X : Set (BondConfig S) := {ω' | P' (openCluster ω' a')} with hX
  set N : Set (BondConfig S) := {ω' | ∀ u ∈ B', ¬ (openGraph ω').Reachable a' u} with hN
  set Y : Set (BondConfig S) := {ω' | ∃ u ∈ B', (openGraph ω').Reachable a' u} with hY
  set Z : Set (BondConfig S) :=
    {ω' | P ({o} ∪ Subtype.val '' {y' | ∃ u ∈ B', (openGraph ω').Reachable u y'})} with hZ
  have hvZ : {ω' : BondConfig S | P' (openCluster ω' v')} ⊆ Z := by
    intro ω' hω'
    refine hP _ _ ?_ hω'
    rintro y ⟨y', hy', rfl⟩
    exact Or.inr ⟨y', ⟨v', hvB', hy'⟩, rfl⟩
  have hWZ : μ.real (restrictConfig f ⁻¹' ((X ∩ N) ∪ (Y ∩ Z))) ≤ μ.real (restrictConfig f ⁻¹' Z) := by
    rw [hf, real_preimage_restrictConfig_val, real_preimage_restrictConfig_val]
    exact real_union_le_of_le_cluster w' a' v' B' P' hP'mono Z hvZ hyp'
  -- `{P(C(a))} ∩ σ ⊆ σ ∩ pull-back of (X ∩ N) ∪ (Y ∩ Z)`
  have hsub1 : {ω : BondConfig V | P (openCluster ω a)} ∩ starEvent o B ⊆
      starEvent o B ∩ restrictConfig f ⁻¹' ((X ∩ N) ∪ (Y ∩ Z)) := by
    rintro ω ⟨hPa, hσ⟩
    refine ⟨hσ, ?_⟩
    rw [mem_preimage]
    by_cases hn : ∀ u ∈ B, u ≠ o → ω ∉ openConnIn ({o}ᶜ : Set V) a u
    · -- `a ↮ B` off `0`: the cluster of `a` avoids `0` and is its cluster in `G ∖ {0}`
      left
      refine ⟨?_, ?_⟩
      · change P' (openCluster (restrictConfig f ω) a')
        rw [hP']
        change P (Subtype.val '' openCluster (restrictConfig Subtype.val ω) a')
        rw [image_openCluster_restrictConfig]
        refine hP _ _ (fun x hx => ?_) hPa
        have hxo : x ≠ o := by
          rintro rfl
          obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x).symm
          obtain ⟨u', hu'B, hu'o, hu'a⟩ := (walk_decomp hσ p hao).2 rfl
          obtain ⟨h1, h2, hr⟩ := hu'a
          exact hn u' hu'B hu'o ⟨h2, h1, hr.symm⟩
        obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x)
        rcases (walk_decomp hσ p hxo).1 hao with h | ⟨⟨u, huB, huo, hau⟩, _⟩
        · exact h
        · exact absurd hau (hn u huB huo)
      · intro u huB hau
        have huo : (u : V) ≠ o := mem_compl_singleton_iff.1 u.2
        exact hn u huB huo ((reachable_restrictConfig_val_iff S ω a' u).1 hau)
    · -- `a ↔ B` off `0`: the cluster of `a` is inside `{0} ∪ C_{G∖0}(B)`
      right
      push Not at hn
      obtain ⟨u, huB, huo, hau⟩ := hn
      have huS : u ∈ S := mem_compl_singleton_iff.2 huo
      refine ⟨⟨⟨u, huS⟩, huB, (reachable_restrictConfig_val_iff S ω a' ⟨u, huS⟩).2 hau⟩, ?_⟩
      change P ({o} ∪ Subtype.val '' {y' | ∃ u ∈ B', (openGraph (restrictConfig f ω)).Reachable u y'})
      refine hP _ _ (fun x hx => ?_) hPa
      by_cases hxo : x = o
      · exact Or.inl hxo
      · right
        have hxS : x ∈ S := mem_compl_singleton_iff.2 hxo
        obtain ⟨p⟩ := (hx : (openGraph ω).Reachable a x)
        rcases (walk_decomp hσ p hxo).1 hao with h | ⟨_, ⟨u', hu'B, hu'o, hu'x⟩⟩
        · -- `a ↔ x` off `0`, and `a ↔ u` off `0`
          refine ⟨⟨x, hxS⟩, ⟨⟨u, huS⟩, huB, ?_⟩, rfl⟩
          have h1 : (openGraph (restrictConfig f ω)).Reachable a' ⟨u, huS⟩ :=
            (reachable_restrictConfig_val_iff S ω a' ⟨u, huS⟩).2 hau
          have h2 : (openGraph (restrictConfig f ω)).Reachable a' ⟨x, hxS⟩ :=
            (reachable_restrictConfig_val_iff S ω a' ⟨x, hxS⟩).2 h
          exact h1.symm.trans h2
        · have hu'S : u' ∈ S := mem_compl_singleton_iff.2 hu'o
          exact ⟨⟨x, hxS⟩, ⟨⟨u', hu'S⟩, hu'B,
            (reachable_restrictConfig_val_iff S ω ⟨u', hu'S⟩ ⟨x, hxS⟩).2 hu'x⟩, rfl⟩
  -- `σ ∩ pull-back of Z ⊆ {P(C(0))} ∩ σ`
  have hsub2 : starEvent o B ∩ restrictConfig f ⁻¹' Z ⊆
      {ω : BondConfig V | P (openCluster ω o)} ∩ starEvent o B := by
    rintro ω ⟨hσ, hz⟩
    refine ⟨?_, hσ⟩
    rw [mem_preimage] at hz
    change P ({o} ∪ Subtype.val '' {y' | ∃ u ∈ B', (openGraph (restrictConfig f ω)).Reachable u y'}) at hz
    refine hP _ _ (fun x hx => ?_) hz
    rcases hx with hxo | ⟨y', ⟨u, huB, huy⟩, rfl⟩
    · rw [mem_singleton_iff] at hxo
      subst hxo
      exact mem_openCluster_self ω x
    · have huy' : (openGraph ω).Reachable (u : V) y' :=
        reachable_of_openConnIn ((reachable_restrictConfig_val_iff S ω u y').1 huy)
      have huo : (u : V) ≠ o := mem_compl_singleton_iff.1 u.2
      have hou : s(o, (u : V)) ∈ ω := ((mem_starEvent_iff o B ω).1 hσ u huo).2 huB
      have hadj : (openGraph ω).Adj o u := (openGraph_adj ω o u).2 ⟨hou, huo.symm⟩
      exact hadj.reachable.trans huy'
  -- assemble with the independence of `σ` from the pairs off `0`
  calc μ.real ({ω | P (openCluster ω a)} ∩ starEvent o B)
      ≤ μ.real (starEvent o B ∩ restrictConfig f ⁻¹' ((X ∩ N) ∪ (Y ∩ Z))) := measureReal_mono hsub1
    _ = μ.real (starEvent o B) * μ.real (restrictConfig f ⁻¹' ((X ∩ N) ∪ (Y ∩ Z))) :=
        real_starEvent_inter_preimage w o B _
    _ ≤ μ.real (starEvent o B) * μ.real (restrictConfig f ⁻¹' Z) :=
        mul_le_mul_of_nonneg_left hWZ measureReal_nonneg
    _ = μ.real (starEvent o B ∩ restrictConfig f ⁻¹' Z) := (real_starEvent_inter_preimage w o B _).symm
    _ ≤ μ.real ({ω | P (openCluster ω o)} ∩ starEvent o B) := measureReal_mono hsub2

/-! ### Theorem 8 (event form): `0` isolated in `G ∖ A` -/

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 8, for `{0,1}`-valued monotone cluster properties** (p. 32:
"Conjecture 4 holds in any `G` in which `0` is an isolated vertex in `G ∖ A`, for any `f`", Conjecture 4
being "`E(f(0)·𝟙{0↔A}) ≥ min_{a∈A} E(f(a)·𝟙{0↔A})`" for monotone cluster properties `f`; proof omitted in
print, "[no] ideas which we did not already use in § 3").  For `f(v,ω) = 𝟙[P(C_ω(v))]`, `P` a monotone
predicate on vertex sets: if every pair `s(0,u)` with `u ∉ A`, `u ≠ 0` has weight `0` and `A ≠ ∅`, then
some `a ∈ A` has `P(P(C(a)), 0 ↔ A) ≤ P(P(C(0)), 0 ↔ A)`.  Proof along the printed proof of Theorem 4
(pp. 13–14): `a₀ ∈ A` minimising `P_{G∖{0}}(P(C(a)))`, Lemma 5 (`KozmaNitzan2024_lemma5_cluster`) for each
star `σ_B`, `∅ ≠ B ⊆ A` (where `σ_B ⊆ {0 ↔ A}`), and summing over `B` (`real_eq_sum_inter_starEvent`;
under `σ_∅`, `0 ↮ A`).  The degenerate case `0 ∈ A` holds with `a = 0`.
[cite: KozmaNitzan2024, Thm. 8 (p. 32) with Conjecture 4 (p. 32) and Thm. 4 (pp. 12–14)] -/
theorem KozmaNitzan2024_thm8_event {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o : V) (P : Set V → Prop) (hP : ∀ S T : Set V, S ⊆ T → P S → P T)
    (hA : A.Nonempty) (hiso : ∀ u, u ≠ o → u ∉ A → w s(o, u) = 0) :
    ∃ a ∈ A, (prodBernoulli w).real ({ω | P (openCluster ω a)} ∩ ⋃ a' ∈ A, openConn o a') ≤
      (prodBernoulli w).real ({ω | P (openCluster ω o)} ∩ ⋃ a' ∈ A, openConn o a') := by
  classical
  set μ := prodBernoulli w with hμ
  by_cases hoA : o ∈ A
  · exact ⟨o, hoA, le_rfl⟩
  -- `a₀` minimising `P_{G ∖ {0}}(P(C(a)))` over `A`
  obtain ⟨a₀, ha₀, hmin⟩ := A.exists_min_image
    (fun a => μ.real {ω | P {y | ω ∈ openConnIn ({o}ᶜ : Set V) a y}}) hA
  refine ⟨a₀, ha₀, ?_⟩
  have ha₀o : a₀ ≠ o := fun h => hoA (h ▸ ha₀)
  rw [real_eq_sum_inter_starEvent w A o hoA hiso ({ω | P (openCluster ω a₀)} ∩ _),
    real_eq_sum_inter_starEvent w A o hoA hiso ({ω | P (openCluster ω o)} ∩ _)]
  refine Finset.sum_le_sum fun B hB => ?_
  have hBA : B ⊆ A := Finset.mem_powerset.1 hB
  rcases B.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
  · -- under `σ_∅`, `0 ↮ A`: the `B = ∅` term vanishes
    have h0 : ({ω | P (openCluster ω a₀)} ∩ ⋃ a' ∈ A, openConn o a') ∩ starEvent o ↑(∅ : Finset V) =
        (∅ : Set (BondConfig V)) := by
      ext ω
      simp only [mem_inter_iff, mem_iUnion, exists_prop, mem_empty_iff_false, iff_false, not_and]
      rintro ⟨-, a', ha', hoa'⟩ hσ
      rw [Finset.coe_empty] at hσ
      exact not_reachable_of_mem_starEvent_empty hσ (fun h => hoA (h ▸ ha')) hoa'
    rw [h0, measureReal_empty]
    exact measureReal_nonneg
  · -- `B ≠ ∅`: Lemma 5 with any `v ∈ B`, and `σ_B ⊆ {0 ↔ v} ⊆ {0 ↔ A}`
    have hvo : v ≠ o := fun h => hoA (h ▸ hBA hv)
    have L5 := KozmaNitzan2024_lemma5_cluster w o a₀ v (↑B) P hP ha₀o hvo (Finset.mem_coe.2 hv)
      (hmin v (hBA hv))
    have hσU : starEvent o (↑B : Set V) ⊆ ⋃ a' ∈ A, (openConn o a' : Set (BondConfig V)) := by
      intro ω hσ
      have hov : s(o, v) ∈ ω := ((mem_starEvent_iff o (↑B) ω).1 hσ v hvo).2 (Finset.mem_coe.2 hv)
      have hadj : (openGraph ω).Adj o v := (openGraph_adj ω o v).2 ⟨hov, hvo.symm⟩
      exact mem_iUnion₂.2 ⟨v, hBA hv, hadj.reachable⟩
    calc μ.real (({ω | P (openCluster ω a₀)} ∩ ⋃ a' ∈ A, openConn o a') ∩ starEvent o ↑B)
        ≤ μ.real ({ω | P (openCluster ω a₀)} ∩ starEvent o ↑B) :=
          measureReal_mono fun ω ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩
      _ ≤ μ.real ({ω | P (openCluster ω o)} ∩ starEvent o ↑B) := L5
      _ ≤ μ.real (({ω | P (openCluster ω o)} ∩ ⋃ a' ∈ A, openConn o a') ∩ starEvent o ↑B) :=
          measureReal_mono fun ω ⟨h1, h2⟩ => ⟨⟨h1, hσU h2⟩, h2⟩

/-! ### Theorem 7 (event form): `|A| = 2` -/

namespace KNPreFKG

variable [Fintype V]

/-- **The pair inequality behind Theorem 7** (Kozma–Nitzan's Theorem 1, pp. 7–8, run for a monotone
cluster property): for a monotone predicate `P` on vertex sets and vertices `0, a₁, a₂`, with
`E = {0 ↔ a₁} ∪ {0 ↔ a₂}`, `min(P(P(C(a₁)), E), P(P(C(a₂)), E)) ≤ P(P(C(0)), E)`.  Proof as printed for
`{aᵢ ↔ b}`: on `{0 ↔ aᵢ}` the events `{P(C(0))}` and `{P(C(aᵢ))}` coincide (same cluster), so
`P(P(C(0)), E) − P(P(C(a₁)), E) = P(0↔a₂, P(C(a₂)), a₁↮a₂) − P(0↔a₂, P(C(a₁)), a₁↮a₂)` and symmetrically;
"Applying BHK 4 times" (Thm. 1.3 inside one cluster, Thm. 1.4 across the two clusters, given `{a₁ ↮ a₂}`)
bounds the two differences below by `φ(2)(P(P(C(a₂)),D) − P(P(C(a₁)),D))` and
`φ(1)(P(P(C(a₁)),D) − P(P(C(a₂)),D))`, one of which is nonnegative.
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Thm. 1 (pp. 7–8)] -/
theorem clusterProp_pair (w : Sym2 V → unitInterval) (o a₁ a₂ : V) (P : Set V → Prop)
    (hP : ∀ S T : Set V, S ⊆ T → P S → P T) :
    min ((prodBernoulli w).real ((openConn o a₁ ∪ openConn o a₂) ∩ {ω | P (openCluster ω a₁)}))
        ((prodBernoulli w).real ((openConn o a₁ ∪ openConn o a₂) ∩ {ω | P (openCluster ω a₂)})) ≤
      (prodBernoulli w).real ({ω | P (openCluster ω o)} ∩ (openConn o a₁ ∪ openConn o a₂)) := by
  classical
  by_cases h12 : a₁ = a₂
  · -- `A` is a singleton: on `{0 ↔ a₁}` the clusters of `0` and `a₁` coincide
    subst h12
    rw [union_self]
    refine (min_le_left _ _).trans (measureReal_mono ?_)
    rintro ω ⟨hA, hPa⟩
    refine ⟨?_, hA⟩
    change P (openCluster ω o)
    rwa [openCluster_eq_of_reachable (hA : (openGraph ω).Reachable o a₁)]
  set μ := prodBernoulli w with hμ
  set O₁ : Set (BondConfig V) := openConn o a₁ with hO₁
  set O₂ : Set (BondConfig V) := openConn o a₂ with hO₂
  set X₀ : Set (BondConfig V) := {ω | P (openCluster ω o)} with hX₀
  set X₁ : Set (BondConfig V) := {ω | P (openCluster ω a₁)} with hX₁
  set X₂ : Set (BondConfig V) := {ω | P (openCluster ω a₂)} with hX₂
  set D : Set (BondConfig V) := {ω | ¬ (openGraph ω).Reachable a₁ a₂} with hD
  set E : Set (BondConfig V) := X₀ ∩ (O₁ ∪ O₂) with hE
  set F₁ : Set (BondConfig V) := (O₁ ∪ O₂) ∩ X₁ with hF₁
  set F₂ : Set (BondConfig V) := (O₁ ∪ O₂) ∩ X₂ with hF₂
  have hsplit : ∀ A S : Set (BondConfig V), μ.real A = μ.real (A ∩ S) + μ.real (A ∩ Sᶜ) := by
    intro A S
    rw [← measureReal_inter_add_sdiff (s := A) (MeasurableSet.of_discrete : MeasurableSet S), Set.sdiff_eq]
  -- same cluster ⇒ same property
  have hX01 : ∀ ω : BondConfig V, (openGraph ω).Reachable o a₁ → (ω ∈ X₀ ↔ ω ∈ X₁) := by
    intro ω h
    simp only [hX₀, hX₁, mem_setOf_eq]
    rw [openCluster_eq_of_reachable h]
  have hX02 : ∀ ω : BondConfig V, (openGraph ω).Reachable o a₂ → (ω ∈ X₀ ↔ ω ∈ X₂) := by
    intro ω h
    simp only [hX₀, hX₂, mem_setOf_eq]
    rw [openCluster_eq_of_reachable h]
  -- the two "subtract the common event" identities
  have hE1 : E ∩ O₁ = F₁ ∩ O₁ := by
    ext ω
    simp only [mem_inter_iff, mem_union, hE, hF₁, hO₁, hO₂, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, _⟩, h1⟩
      exact ⟨⟨Or.inl h1, (hX01 ω h1).1 hb⟩, h1⟩
    · rintro ⟨⟨_, hb⟩, h1⟩
      exact ⟨⟨(hX01 ω h1).2 hb, Or.inl h1⟩, h1⟩
  have hE1c : E ∩ O₁ᶜ = O₂ ∩ X₂ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hE, hO₁, hO₂, hD, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, h1 | h2⟩, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨⟨h2, (hX02 ω h2).1 hb⟩, fun h => hn1 (h2.trans h.symm)⟩
    · rintro ⟨⟨h2, hb⟩, hn⟩
      exact ⟨⟨(hX02 ω h2).2 hb, Or.inr h2⟩, fun h1 => hn (h1.symm.trans h2)⟩
  have hF1c : F₁ ∩ O₁ᶜ = O₂ ∩ X₁ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hF₁, hO₁, hO₂, hD, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1 | h2, hb⟩, hn1⟩
      · exact absurd h1 hn1
      · exact ⟨⟨h2, hb⟩, fun h => hn1 (h2.trans h.symm)⟩
    · rintro ⟨⟨h2, hb⟩, hn⟩
      exact ⟨⟨Or.inr h2, hb⟩, fun h1 => hn (h1.symm.trans h2)⟩
  have hE2 : E ∩ O₂ = F₂ ∩ O₂ := by
    ext ω
    simp only [mem_inter_iff, mem_union, hE, hF₂, hO₁, hO₂, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, _⟩, h2⟩
      exact ⟨⟨Or.inr h2, (hX02 ω h2).1 hb⟩, h2⟩
    · rintro ⟨⟨_, hb⟩, h2⟩
      exact ⟨⟨(hX02 ω h2).2 hb, Or.inr h2⟩, h2⟩
  have hE2c : E ∩ O₂ᶜ = O₁ ∩ X₁ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hE, hO₁, hO₂, hD, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hb, h1 | h2⟩, hn2⟩
      · exact ⟨⟨h1, (hX01 ω h1).1 hb⟩, fun h => hn2 (h1.trans h)⟩
      · exact absurd h2 hn2
    · rintro ⟨⟨h1, hb⟩, hn⟩
      exact ⟨⟨(hX01 ω h1).2 hb, Or.inl h1⟩, fun h2 => hn (h1.symm.trans h2)⟩
  have hF2c : F₂ ∩ O₂ᶜ = O₁ ∩ X₂ ∩ D := by
    ext ω
    simp only [mem_inter_iff, mem_union, mem_compl_iff, hF₂, hO₁, hO₂, hD, openConn, mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1 | h2, hb⟩, hn2⟩
      · exact ⟨⟨h1, hb⟩, fun h => hn2 (h1.trans h)⟩
      · exact absurd h2 hn2
    · rintro ⟨⟨h1, hb⟩, hn⟩
      exact ⟨⟨Or.inl h1, hb⟩, fun h2 => hn (h1.symm.trans h2)⟩
  have hdiff1 : μ.real E - μ.real F₁ = μ.real (O₂ ∩ X₂ ∩ D) - μ.real (O₂ ∩ X₁ ∩ D) := by
    rw [hsplit E O₁, hsplit F₁ O₁, hE1, hE1c, hF1c]
    ring
  have hdiff2 : μ.real E - μ.real F₂ = μ.real (O₁ ∩ X₁ ∩ D) - μ.real (O₁ ∩ X₂ ∩ D) := by
    rw [hsplit E O₂, hsplit F₂ O₂, hE2, hE2c, hF2c]
    ring
  -- "Applying BHK 4 times", given `D = {a₁ ↮ a₂}`
  have hD1 : {ω : BondConfig V | ∀ x ∈ ({a₂} : Set V), ¬ (openGraph ω).Reachable a₁ x} = D := by
    ext ω
    simp [hD]
  have hD2 : {ω : BondConfig V | ∀ x ∈ ({a₁} : Set V), ¬ (openGraph ω).Reachable a₂ x} = D := by
    ext ω
    simp only [mem_setOf_eq, mem_singleton_iff, forall_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have hD3 : {ω : BondConfig V | ¬ (openGraph ω).Reachable a₂ a₁} = D := by
    ext ω
    simp only [mem_setOf_eq, hD]
    exact not_congr ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩
  have hX₁e : X₁ = {ω | openEdgeCluster ω a₁ ∈ {C : Set (Sym2 V) | P {a | a = a₁ ∨ ∃ e ∈ C, a ∈ e}}} :=
    setOf_prop_openCluster_eq a₁ P
  have hX₂e : X₂ = {ω | openEdgeCluster ω a₂ ∈ {C : Set (Sym2 V) | P {a | a = a₂ ∨ ∃ e ∈ C, a ∈ e}}} :=
    setOf_prop_openCluster_eq a₂ P
  -- (i) `μ(D, 0↔a₂) μ(D, P(C a₂)) ≤ μ(D) μ(D, 0↔a₂, P(C a₂))` (Thm. 1.3 in `C_{a₂}`)
  have h_i := bhk_one_upper_upper w a₂ ({a₁} : Set V) (by simpa using Ne.symm h12)
    (isUpperSet_connFamily a₂ o) (isUpperSet_clusterPropFamily a₂ P hP)
  rw [hD2, ← openConn_eq_setOf_connFamily, ← hX₂e, openConn_symm a₂ o] at h_i
  -- (ii) `μ(D) μ(D, 0↔a₂, P(C a₁)) ≤ μ(D, 0↔a₂) μ(D, P(C a₁))` (Thm. 1.4, `C_{a₂}` and `C_{a₁}`)
  have h_ii := bhk_two_upper_upper w a₂ a₁ (Ne.symm h12) (isUpperSet_connFamily a₂ o)
    (isUpperSet_clusterPropFamily a₁ P hP)
  rw [hD3, ← openConn_eq_setOf_connFamily, ← hX₁e, openConn_symm a₂ o] at h_ii
  -- (iii) `μ(D, 0↔a₁) μ(D, P(C a₁)) ≤ μ(D) μ(D, 0↔a₁, P(C a₁))` (Thm. 1.3 in `C_{a₁}`)
  have h_iii := bhk_one_upper_upper w a₁ ({a₂} : Set V) (by simpa using h12)
    (isUpperSet_connFamily a₁ o) (isUpperSet_clusterPropFamily a₁ P hP)
  rw [hD1, ← openConn_eq_setOf_connFamily, ← hX₁e, openConn_symm a₁ o] at h_iii
  -- (iv) `μ(D) μ(D, 0↔a₁, P(C a₂)) ≤ μ(D, 0↔a₁) μ(D, P(C a₂))` (Thm. 1.4, `C_{a₁}` and `C_{a₂}`)
  have h_iv := bhk_two_upper_upper w a₁ a₂ h12 (isUpperSet_connFamily a₁ o)
    (isUpperSet_clusterPropFamily a₂ P hP)
  rw [← openConn_eq_setOf_connFamily, ← hX₂e, openConn_symm a₁ o] at h_iv
  -- normalise the intersections
  have e1 : D ∩ (O₂ ∩ X₂) = O₂ ∩ X₂ ∩ D := inter_comm _ _
  have e2 : D ∩ (O₂ ∩ X₁) = O₂ ∩ X₁ ∩ D := inter_comm _ _
  have e3 : D ∩ (O₁ ∩ X₁) = O₁ ∩ X₁ ∩ D := inter_comm _ _
  have e4 : D ∩ (O₁ ∩ X₂) = O₁ ∩ X₂ ∩ D := inter_comm _ _
  simp only [← hD, ← hO₁, ← hO₂] at h_i h_ii h_iii h_iv
  rw [e1] at h_i
  rw [e2] at h_ii
  rw [e3] at h_iii
  rw [e4] at h_iv
  -- combine
  by_cases hD0 : μ.real D = 0
  · have hz : ∀ A : Set (BondConfig V), μ.real (A ∩ D) = 0 := fun A =>
      le_antisymm ((measureReal_mono inter_subset_right).trans hD0.le) measureReal_nonneg
    have : μ.real E = μ.real F₁ := by
      have := hdiff1
      rw [hz, hz, sub_self, sub_eq_zero] at this
      exact this
    exact (min_le_left _ _).trans this.symm.le
  · have hDpos : 0 < μ.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hD0)
    rcases le_total (μ.real (D ∩ X₁)) (μ.real (D ∩ X₂)) with ht | ht
    · -- `μ(D, P(C a₁)) ≤ μ(D, P(C a₂))`: then `μ(E) ≥ μ(F₁)`
      refine (min_le_left _ _).trans ?_
      have key : μ.real D * (μ.real E - μ.real F₁) ≥ 0 := by
        rw [hdiff1, mul_sub]
        have hs2 : 0 ≤ μ.real (D ∩ O₂) := measureReal_nonneg
        nlinarith [h_i, h_ii, mul_le_mul_of_nonneg_left ht hs2]
      nlinarith [key]
    · refine (min_le_right _ _).trans ?_
      have key : μ.real D * (μ.real E - μ.real F₂) ≥ 0 := by
        rw [hdiff2, mul_sub]
        have hs1 : 0 ≤ μ.real (D ∩ O₁) := measureReal_nonneg
        nlinarith [h_iii, h_iv, mul_le_mul_of_nonneg_left ht hs1]
      nlinarith [key]

end KNPreFKG

open KNPreFKG in
/-- **Kozma–Nitzan 2024, Theorem 7, for `{0,1}`-valued monotone cluster properties** (p. 32:
"Conjecture 4 holds when `|A| = 2`, for any `f`", Conjecture 4 being
"`E(f(0)·𝟙{0↔A}) ≥ min_{a∈A} E(f(a)·𝟙{0↔A})`"; proof omitted in print, "[no] ideas which we did not
already use in § 3").  For `f(v,ω) = 𝟙[P(C_ω(v))]`, `P` a monotone predicate on vertex sets: if
`|A| = 2` then some `a ∈ A` has `P(P(C(a)), 0 ↔ A) ≤ P(P(C(0)), 0 ↔ A)`.  Proof: the printed proof of
Theorem 1 (pp. 7–8) with `{aᵢ ↔ b}` replaced by `{P(C(aᵢ))}` (`KNPreFKG.clusterProp_pair`).
[cite: KozmaNitzan2024, Thm. 7 (p. 32) with Conjecture 4 (p. 32) and Thm. 1 (pp. 7–8)] -/
theorem KozmaNitzan2024_thm7_event {V : Type*} [Fintype V] (w : Sym2 V → unitInterval)
    (A : Finset V) (o : V) (P : Set V → Prop) (hP : ∀ S T : Set V, S ⊆ T → P S → P T)
    (hA : A.card = 2) :
    ∃ a ∈ A, (prodBernoulli w).real ({ω | P (openCluster ω a)} ∩ ⋃ a' ∈ A, openConn o a') ≤
      (prodBernoulli w).real ({ω | P (openCluster ω o)} ∩ ⋃ a' ∈ A, openConn o a') := by
  classical
  obtain ⟨a₁, a₂, h12, rfl⟩ := Finset.card_eq_two.1 hA
  have hU : (⋃ a' ∈ ({a₁, a₂} : Finset V), (openConn o a' : Set (BondConfig V))) =
      openConn o a₁ ∪ openConn o a₂ := by
    ext ω
    simp only [mem_iUnion, exists_prop, Finset.mem_insert, Finset.mem_singleton, mem_union]
    constructor
    · rintro ⟨a, rfl | rfl, ha⟩
      · exact Or.inl ha
      · exact Or.inr ha
    · rintro (h | h)
      · exact ⟨a₁, Or.inl rfl, h⟩
      · exact ⟨a₂, Or.inr rfl, h⟩
  rw [hU]
  have key := clusterProp_pair w o a₁ a₂ P hP
  rw [inter_comm (openConn o a₁ ∪ openConn o a₂) {ω | P (openCluster ω a₁)},
    inter_comm (openConn o a₁ ∪ openConn o a₂) {ω | P (openCluster ω a₂)}] at key
  rcases min_le_iff.1 key with h | h
  · exact ⟨a₁, by simp, h⟩
  · exact ⟨a₂, by simp, h⟩

end Percolation.Literature

end
