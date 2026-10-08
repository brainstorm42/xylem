import Percolation.Continuity.AdditiveGluing.GenOfSurplusTransfer
import Percolation.Continuity.CSH.LevelForms
import Percolation.Literature.LatticeModels.ProdBernoulliWeightContinuity
import Percolation.Util.Linter

/-!
# (S5D) peeling: tools (dependence of the level forms on finitely many values, the top-relay split of the ranked surplus, the `κ`-bound, the decoy-constant and `Ψ_iso` identities)

Tools for the peeling step (Lemmas P, κ, AC, R).

* `CSH.cshMarg_congr` — (with `CSH.slForm_congr`) the level form `sl_L[f](u)` only reads `f` at `u` and at the decoys of `L`.
* `CSH.surplus_erase_add` — LEMMA P (core): for the rank-maximal relay `k` of `T`, `T' = T.erase k`, and any `u`,
  `Sur_u(T) = Sur_u(T') + ( ∫_{D_k ∩ {k↔u}} F(C_k) − μ(D_k ∩ {k↔u})·m_k )`, `D_k = {k ↮ T'}` (verbatim the bookkeeping of
  `AGloc.gen_firstRank_of_surplusTransfer`).
* `CSH.kappa_le_surplus` — LEMMA κ: `κ_k = m_k μ(D_k) − ∫_{D_k} F(C_k) ≤ Sur_k(T')` when `m_k` is maximal.
* `CSH.covD_clusterFun_eq` — the top-relay term against the denominator-free conditional covariance `covD`:
  `μ(D_k)·T_k(u) = covD(k; T'; F̂)(u) − κ_k · μ(D_k ∩ {k↔u})`.
* `CSH.covD_psiIso` — the `Ψ_iso` identity behind LEMMA AC: `covD(k; T'; Ψ_iso)(u) = μ(D_k ∩ {C_k = ∅}) · μ(D_k ∩ {k↔u})` (`u ≠ k`).
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] [cite: KozmaNitzan2024, Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open KNPreFKG

namespace CSH

variable {V : Type*}

/-! ### The level forms read `f` only at the observers and the decoys -/

/-- `Marg_L[f] = Marg_L[g]` if `f = g` at `o`, `v` and the decoys of `L` (via `CSH.slForm_congr`). [folklore] -/
theorem cshMarg_congr (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f g : V → ℝ) (P : V → Prop)
    (hL : ∀ dc ∈ L, P dc.1) (ho : P o) (hv : P v) (hfg : ∀ u, P u → f u = g u) :
    cshMarg L p o v f = cshMarg L p o v g := by
  simp only [cshMarg, slForm_congr L (hfg o ho) (fun dc hdc => hfg dc.1 (hL dc hdc)),
    slForm_congr L (hfg v hv) (fun dc hdc => hfg dc.1 (hL dc hdc))]

variable [Fintype V]

omit [Fintype V] in
/-- The decoys of `decoyList w A D` are the members of `D`. [folklore] -/
theorem mem_decoyList (w : Sym2 V → unitInterval) :
    ∀ (A : Set V) (D : List V) (dc : V × (V → ℝ)), dc ∈ decoyList w A D → dc.1 ∈ D
  | _, [], dc, h => by simp [decoyList] at h
  | A, d :: D, dc, h => by
    simp only [decoyList, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_decoyList w (insert d A) D dc h)

/-! ### The top-relay split of the ranked surplus (Lemma P, core) -/

variable {n : ℕ}

/-- **LEMMA P (core): peeling the rank-maximal relay.** For `k ∈ T` with `r a < r k` for all `a ∈ T.erase k`, and every `u`,
`Sur_u(T) = Sur_u(T.erase k) + (∫_{D_k ∩ {k↔u}} F(C_k) − μ(D_k ∩ {k↔u})·m_k)`, `D_k = {k ↮ T.erase k}`, `m_k = ∫ F(C_k)`.
[cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem surplus_erase_add (w : Sym2 (Fin n) → unitInterval) (T : Finset (Fin n)) (r : Fin n → ℕ) (F : Set (Fin n) → ℝ)
    {k : Fin n} (hkT : k ∈ T) (hlt : ∀ a ∈ T.erase k, r a < r k) (u : Fin n) :
    surplus w T r F u = surplus w (T.erase k) r F u +
      ((∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ (↑(T.erase k) : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩ openConn k u,
          F (openCluster ω k) ∂(prodBernoulli w)) -
        (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ (↑(T.erase k) : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩
          openConn k u) * ∫ ω, F (openCluster ω k) ∂(prodBernoulli w)) := by
  classical
  set μ := prodBernoulli w with hμ
  set T' := T.erase k with hT'
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hint : ∀ (g : BondConfig (Fin n) → ℝ) (S : Set (BondConfig (Fin n))), IntegrableOn g S μ :=
    fun g S => (Integrable.of_finite).integrableOn
  set f₀ : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω u) with hf₀
  set fk : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω k) with hfk
  set UT : Set (BondConfig (Fin n)) := ⋃ a ∈ T', openConn u a with hUT
  set Ok : Set (BondConfig (Fin n)) := openConn u k with hOk
  set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} with hDk
  -- patterns: for `a ∈ T'` the `T`-pattern is the `T'`-pattern; for `k` it is `Dk ∩ Ok`
  have hfiltT : ∀ a ∈ T', T.filter (fun a' => r a' < r a) = T'.filter (fun a' => r a' < r a) := by
    intro a ha
    rw [hT', AGloc.filter_erase_of_not]
    exact fun h => lt_asymm h (hlt a ha)
  have hfiltk : T.filter (fun a' => r a' < r k) = T' := by
    ext a
    simp only [Finset.mem_filter, hT', Finset.mem_erase]
    constructor
    · rintro ⟨ha, h⟩; exact ⟨fun hak => lt_irrefl _ (hak ▸ h), ha⟩
    · rintro ⟨hak, ha⟩; exact ⟨ha, hlt a (Finset.mem_erase.2 ⟨hak, ha⟩)⟩
  have hPk : (openConn u k ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r k), (openConn u a')ᶜ : Set (BondConfig (Fin n))) =
      Dk ∩ openConn k u := by
    rw [hfiltk]
    ext ω
    simp only [hDk, mem_inter_iff, mem_iInter, mem_compl_iff, openConn, mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro ⟨hk', h⟩
      exact ⟨fun a ha hka => h a ha (hk'.trans hka), hk'.symm⟩
    · rintro ⟨h, hk'⟩
      exact ⟨hk'.symm, fun a ha hoa => h a ha (hk'.trans hoa)⟩
  have hsumT : ∑ a ∈ T, μ.real (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ : Set (BondConfig (Fin n))) *
        ∫ ω, F (openCluster ω a) ∂μ =
      ∑ a ∈ T', μ.real (openConn u a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn u a')ᶜ : Set (BondConfig (Fin n))) *
        ∫ ω, F (openCluster ω a) ∂μ + μ.real (Dk ∩ openConn k u) * ∫ ω, fk ω ∂μ := by
    rw [← Finset.add_sum_erase T _ hkT, hPk, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hfiltT a ha]
  -- the union over `T` splits as `UT ∪ Ok`, and `(UT ∪ Ok) \ UT = Dk ∩ {k↔u}`
  have hUA : (⋃ a ∈ T, (openConn u a : Set (BondConfig (Fin n)))) = UT ∪ Ok := by
    ext ω
    simp only [hUT, hOk, mem_iUnion, mem_union, exists_prop, hT', Finset.mem_erase]
    constructor
    · rintro ⟨a, ha, h⟩
      by_cases hak : a = k
      · exact Or.inr (hak ▸ h)
      · exact Or.inl ⟨a, ⟨hak, ha⟩, h⟩
    · rintro (⟨a, ⟨_, ha⟩, h⟩ | h)
      · exact ⟨a, ha, h⟩
      · exact ⟨k, hkT, h⟩
  have h0k : ∀ ω ∈ Dk ∩ openConn k u, f₀ ω = fk ω := fun ω hω => by
    simp only [hf₀, hfk]
    rw [openCluster_eq_of_reachable ((hω.2 : (openGraph ω).Reachable k u).symm)]
  have hdiff : (UT ∪ Ok) \ UT = Dk ∩ openConn k u := by
    ext ω
    simp only [hUT, hOk, hDk, mem_sdiff, mem_union, mem_iUnion, mem_inter_iff, exists_prop, not_exists, not_and, openConn,
      mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro ⟨h | h, hno⟩
      · obtain ⟨a, ha, h'⟩ := h; exact absurd h' (hno a ha)
      · exact ⟨fun a ha hka => hno a ha (h.trans hka), h.symm⟩
    · rintro ⟨hd, hk'⟩
      exact ⟨Or.inr hk'.symm, fun a ha hoa => hd a ha (hk'.trans hoa)⟩
  have hsplit : ∫ ω in UT ∪ Ok, f₀ ω ∂μ = ∫ ω in UT, f₀ ω ∂μ + ∫ ω in Dk ∩ openConn k u, fk ω ∂μ := by
    rw [← integral_inter_add_sdiff (hmeas UT) (hint f₀ (UT ∪ Ok)), inter_eq_right.2 subset_union_left, hdiff,
      setIntegral_congr_fun (hmeas _) fun ω hω => h0k ω hω]
  unfold surplus
  rw [hsumT, hUA, hsplit]
  ring

/-- **LEMMA κ**: with `D_k = {k ↮ T'}` and `m_k = ∫ F(C_k)` maximal on `T' ∪ {k}` (`m_a ≤ m_k` for `a ∈ T'`), the deficit
`κ_k = m_k·μ(D_k) − ∫_{D_k} F(C_k)` is at most `Sur_k(T')`. [cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem kappa_le_surplus (w : Sym2 (Fin n) → unitInterval) (T' : Finset (Fin n)) (r : Fin n → ℕ) (F : Set (Fin n) → ℝ)
    (k : Fin n) (hrT : Set.InjOn r ↑T')
    (hmle : ∀ a ∈ T', ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω k) ∂(prodBernoulli w)) :
    (∫ ω, F (openCluster ω k) ∂(prodBernoulli w)) *
        (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} -
      ∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a}, F (openCluster ω k) ∂(prodBernoulli w) ≤
      surplus w T' r F k := by
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
  set fk : BondConfig (Fin n) → ℝ := fun ω => F (openCluster ω k) with hfk
  set mk : ℝ := ∫ ω, fk ω ∂μ with hmk
  set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} with hDk
  set Wk : Set (BondConfig (Fin n)) := ⋃ a ∈ T', openConn k a with hWk
  have hDW : Dk = Wkᶜ := by
    ext ω
    simp [hDk, hWk, openConn]
  have hDint : ∫ ω in Dk, fk ω ∂μ = mk - ∫ ω in Wk, fk ω ∂μ := by
    have := integral_add_compl (hmeas Wk) (Integrable.of_finite (f := fk) (μ := μ))
    rw [← hDW] at this
    linarith
  have hDμ : μ.real Dk = 1 - μ.real Wk := by
    have h1 : μ.real (univ : Set (BondConfig (Fin n))) = μ.real (univ ∩ Wk) + μ.real (univ \ Wk) :=
      (measureReal_inter_add_sdiff (s := univ) (h := measure_ne_top _ _) (hmeas Wk)).symm
    rw [probReal_univ, univ_inter, ← compl_eq_univ_sdiff, ← hDW] at h1
    linarith
  have hWsum : ∑ a ∈ T', μ.real (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ : Set (BondConfig (Fin n))) =
      μ.real Wk := AGloc.sum_measureReal_firstRank w T' r k hrT
  have hsum : ∑ a ∈ T', μ.real (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ : Set (BondConfig (Fin n))) *
        ∫ ω, F (openCluster ω a) ∂μ ≤ mk * μ.real Wk := by
    have : ∑ a ∈ T', μ.real (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ : Set (BondConfig (Fin n))) *
        ∫ ω, F (openCluster ω a) ∂μ ≤
        ∑ a ∈ T', μ.real (openConn k a ∩ ⋂ a' ∈ T'.filter (fun a' => r a' < r a), (openConn k a')ᶜ : Set (BondConfig (Fin n))) * mk :=
      Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hmle a ha) (hn _)
    rw [← Finset.sum_mul, hWsum] at this
    linarith
  unfold surplus
  rw [hDint, hDμ]
  change mk * (1 - μ.real Wk) - (mk - ∫ ω in Wk, fk ω ∂μ) ≤ (∫ ω in Wk, fk ω ∂μ) - _
  linarith

/-- **The top-relay term against `covD`.** With `F̂(C) = F(span_k C)` (so `F̂(C_k) = F(C(k))`), `D_k = {k ↮ T'}`,
`κ_k = m_k μ(D_k) − ∫_{D_k} F(C_k)`:  `μ(D_k)·(∫_{D_k∩{k↔u}} F(C_k) − μ(D_k∩{k↔u}) m_k) = covD(k; T'; F̂)(u) − κ_k·μ(D_k ∩ {k↔u})`.
[folklore] -/
theorem covD_clusterFun_eq (w : Sym2 (Fin n) → unitInterval) (T' : Finset (Fin n)) (F : Set (Fin n) → ℝ) (k u : Fin n) :
    (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} *
        ((∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩ openConn k u,
            F (openCluster ω k) ∂(prodBernoulli w)) -
          (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩
            openConn k u) * ∫ ω, F (openCluster ω k) ∂(prodBernoulli w)) =
      covD w k (↑T' : Set (Fin n)) (fun C => F {a | a = k ∨ ∃ e ∈ C, a ∈ e}) u -
        ((∫ ω, F (openCluster ω k) ∂(prodBernoulli w)) *
            (prodBernoulli w).real {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} -
          ∫ ω in {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a},
            F (openCluster ω k) ∂(prodBernoulli w)) *
        (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩
          openConn k u) := by
  unfold covD
  simp only [clusterFun_openEdgeCluster, Finset.mem_coe]
  ring

/-- The "not isolated" functional of an edge cluster: `Ψ_iso(C) = 1{C ≠ ∅}`. [folklore] -/
def psiIso : Set (Sym2 V) → ℝ := fun C => if C = ∅ then 0 else 1

omit [Fintype V] in
/-- `Ψ_iso` is monotone. [folklore] -/
theorem psiIso_mono : Monotone (psiIso (V := V)) := by
  intro C C' h
  unfold psiIso
  by_cases hC : C = ∅
  · rw [if_pos hC]; split_ifs <;> norm_num
  · have hC' : C' ≠ ∅ := fun h' => hC (subset_empty_iff.1 (h' ▸ h))
    rw [if_neg hC, if_neg hC']

omit [Fintype V] in
/-- On `{k ↔ u}` with `u ≠ k` the edge cluster of `k` is nonempty, so `Ψ_iso(C_k) = 1`. [folklore] -/
theorem psiIso_eq_one_of_reachable {ω : BondConfig V} {k u : V} (huk : u ≠ k) (h : (openGraph ω).Reachable k u) :
    psiIso (openEdgeCluster ω k) = 1 := by
  unfold psiIso
  rw [if_neg]
  rcases (reachable_iff_exists_mem_openEdgeCluster ω k u).1 h with h1 | ⟨e, he, _⟩
  · exact absurd h1 huk
  · exact fun h0 => by rw [h0] at he; exact he

/-- **The `Ψ_iso` identity behind LEMMA AC**: for `u ≠ k`,
`covD(k; T'; Ψ_iso)(u) = μ(D_k ∩ {C_k = ∅}) · μ(D_k ∩ {k↔u})`. [folklore] -/
theorem covD_psiIso (w : Sym2 (Fin n) → unitInterval) (T' : Finset (Fin n)) (k u : Fin n) (huk : u ≠ k) :
    covD w k (↑T' : Set (Fin n)) psiIso u =
      (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩
          {ω | openEdgeCluster ω k = ∅}) *
        (prodBernoulli w).real ({ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} ∩
          openConn k u) := by
  classical
  set μ := prodBernoulli w with hμ
  have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
  set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a} with hDk
  -- `∫_{Dk ∩ {k↔u}} Ψ_iso(C_k) = μ(Dk ∩ {k↔u})`
  have h1 : ∫ ω in Dk ∩ openConn k u, psiIso (openEdgeCluster ω k) ∂μ = μ.real (Dk ∩ openConn k u) := by
    rw [setIntegral_congr_fun (hmeas _) (fun ω hω => psiIso_eq_one_of_reachable huk hω.2), setIntegral_const, smul_eq_mul,
      mul_one]
  -- `∫_{Dk} Ψ_iso(C_k) = μ(Dk) − μ(Dk ∩ {C_k = ∅})`
  have h2 : ∫ ω in Dk, psiIso (openEdgeCluster ω k) ∂μ = μ.real Dk - μ.real (Dk ∩ {ω | openEdgeCluster ω k = ∅}) := by
    have hsplit := (integral_inter_add_sdiff (hmeas {ω : BondConfig (Fin n) | openEdgeCluster ω k = ∅})
      ((Integrable.of_finite (f := fun ω => psiIso (openEdgeCluster ω k)) (μ := μ)).integrableOn (s := Dk))).symm
    rw [hsplit]
    have ha : ∫ ω in Dk ∩ {ω | openEdgeCluster ω k = ∅}, psiIso (openEdgeCluster ω k) ∂μ = 0 := by
      rw [setIntegral_congr_fun (hmeas _) (fun ω hω => by
        show psiIso (openEdgeCluster ω k) = (0 : ℝ)
        unfold psiIso; rw [if_pos (show openEdgeCluster ω k = ∅ from hω.2)])]
      simp
    have hb : ∫ ω in Dk \ {ω | openEdgeCluster ω k = ∅}, psiIso (openEdgeCluster ω k) ∂μ =
        μ.real (Dk \ {ω | openEdgeCluster ω k = ∅}) := by
      rw [setIntegral_congr_fun (hmeas _) (fun ω hω => by
        show psiIso (openEdgeCluster ω k) = (1 : ℝ)
        unfold psiIso; rw [if_neg (show ¬ (openEdgeCluster ω k = ∅) from hω.2)]), setIntegral_const, smul_eq_mul, mul_one]
    rw [ha, hb, zero_add]
    have := measureReal_inter_add_sdiff (μ := μ) (s := Dk) (h := measure_ne_top _ _)
      (hmeas {ω : BondConfig (Fin n) | openEdgeCluster ω k = ∅})
    linarith
  unfold covD
  simp only [Finset.mem_coe] at hDk ⊢
  rw [← hDk, h1, h2]
  ring

end CSH

end Percolation.Continuity
