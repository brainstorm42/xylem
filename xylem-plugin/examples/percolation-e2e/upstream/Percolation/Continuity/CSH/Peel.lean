import Percolation.Continuity.CSH.PeelTools
import Percolation.Continuity.HullPort.TABase
import Percolation.Util.Linter

/-!
# (S5D) from CSH: the peeling induction

`CSH.surplusMargin_nonneg_of_csh`: for non-degenerate weights and observers `o ≠ v`, IF the conditioned
slack hierarchy holds for every owner/avoided-set/decoy-list with the named vertices distinct, THEN
the surplus-with-decoys margin `CSH.surplusMargin w T r D o v F` is nonnegative for every relay set `T`,
every `m`-compatible injective rank `r`, every decoy list `D` and every monotone `F`. At `D = []`
this is the surplus-transfer inequality (S5) for `|T|` relays (`CSH.surplusTransfer_of_surplusMargin_nil`), i.e. the
hypothesis `hST` of `AGloc.gen_firstRank_of_surplusTransfer` for non-degenerate weights. Proof: peel
the rank-maximal relay `k` (`CSH.surplus_erase_add`), rewrite its term through `covD`
(`CSH.covD_clusterFun_eq`), bound the deficit by `Sur_k(T')` (`CSH.kappa_le_surplus`), get the sign
of `Marg[c_k]` from CSH applied to `Ψ_iso` (`CSH.covD_psiIso`), and recognise the next level by
`CSH.cshMarg_cons`; induction on `|T|`. [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] [cite:
KozmaNitzan2024, Conj. 1 (p. 3), Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open KNPreFKG

namespace CSH

variable {V : Type*}

/-- The margin is compatible with subtraction. [folklore] -/
theorem cshMarg_sub (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f g : V → ℝ) :
    cshMarg L p o v (f - g) = cshMarg L p o v f - cshMarg L p o v g := by
  simp only [cshMarg, slForm_sub, Pi.sub_apply]; ring

variable {n : ℕ}

/-- **THEOREM 2: (S5D) — hence (S5) for every number of relays — from the conditioned slack hierarchy.**
[cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem surplusMargin_nonneg_of_csh (w : Sym2 (Fin n) → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (o v : Fin n)
    (hCSH : ∀ (x : Fin n) (Y : Finset (Fin n)) (D : List (Fin n)),
      x ∉ Y → o ≠ x → v ≠ x → o ∉ Y → v ∉ Y → D.Nodup → (∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) →
      CSHHolds w x (↑Y : Set (Fin n)) D o v) :
    ∀ (T : Finset (Fin n)) (r : Fin n → ℕ) (D : List (Fin n)) (F : Set (Fin n) → ℝ),
      (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) →
      o ∉ T → v ∉ T → D.Nodup → (∀ d ∈ D, d ∉ T ∧ d ≠ o ∧ d ≠ v) →
      0 ≤ surplusMargin w T r D o v F := by
  classical
  -- strong induction on `|T|`
  have main : ∀ (N : ℕ) (T : Finset (Fin n)) (r : Fin n → ℕ) (D : List (Fin n)) (F : Set (Fin n) → ℝ), T.card = N →
      (∀ S S' : Set (Fin n), S ⊆ S' → F S ≤ F S') → Set.InjOn r ↑T →
      (∀ a ∈ T, ∀ a' ∈ T, r a < r a' →
        ∫ ω, F (openCluster ω a) ∂(prodBernoulli w) ≤ ∫ ω, F (openCluster ω a') ∂(prodBernoulli w)) →
      o ∉ T → v ∉ T → D.Nodup → (∀ d ∈ D, d ∉ T ∧ d ≠ o ∧ d ≠ v) →
      0 ≤ surplusMargin w T r D o v F := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro T r D F hN hF hr hcompat hoT hvT hD hDT
    set μ := prodBernoulli w with hμ
    have hmeas : ∀ S : Set (BondConfig (Fin n)), MeasurableSet S := fun _ => MeasurableSet.of_discrete
    have hn := fun (S : Set (BondConfig (Fin n))) => (measureReal_nonneg : 0 ≤ μ.real S)
    rcases T.eq_empty_or_nonempty with hT0 | hne
    · -- no relays: the surplus vanishes identically
      subst hT0
      have h0 : surplus w (∅ : Finset (Fin n)) r F = fun _ => 0 := by
        funext u; simp [surplus]
      rw [surplusMargin, h0]
      have := slForm_zero (decoyList w (↑(∅ : Finset (Fin n)) : Set (Fin n)) D)
      simp only [cshMarg]
      rw [show (fun _ : Fin n => (0 : ℝ)) = (0 : Fin n → ℝ) from rfl, this]
      simp
    -- the rank-maximal relay `k` and `T' = T.erase k`
    obtain ⟨k, hkT, hkmax⟩ := Finset.exists_max_image T r hne
    set T' : Finset (Fin n) := T.erase k with hT'
    have hTcard : T'.card < N := by
      have hpos : 0 < T.card := Finset.card_pos.2 hne
      rw [hT', Finset.card_erase_of_mem hkT]; omega
    have hT'T : ∀ a ∈ T', a ∈ T := fun a ha => Finset.mem_of_mem_erase ha
    have hkT' : k ∉ T' := Finset.notMem_erase k T
    have hlt : ∀ a ∈ T', r a < r k := by
      intro a ha
      rcases (hkmax a (hT'T a ha)).lt_or_eq with h | h
      · exact h
      · exact absurd (hr (hT'T a ha) hkT h) (Finset.ne_of_mem_erase ha)
    have hrT' : Set.InjOn r ↑T' := hr.mono (by intro a ha; exact hT'T a ha)
    have hcompatT' : ∀ a ∈ T', ∀ a' ∈ T', r a < r a' →
        ∫ ω, F (openCluster ω a) ∂μ ≤ ∫ ω, F (openCluster ω a') ∂μ :=
      fun a ha a' ha' h => hcompat a (hT'T a ha) a' (hT'T a' ha') h
    have hmle : ∀ a ∈ T', ∫ ω, F (openCluster ω a) ∂μ ≤ ∫ ω, F (openCluster ω k) ∂μ :=
      fun a ha => hcompat a (hT'T a ha) k hkT (hlt a ha)
    have hko : o ≠ k := fun h => hoT (h ▸ hkT)
    have hkv : v ≠ k := fun h => hvT (h ▸ hkT)
    have hkD : k ∉ D := fun h => (hDT k h).1 hkT
    -- the objects
    set Dk : Set (BondConfig (Fin n)) := {ω : BondConfig (Fin n) | ∀ a ∈ (↑T' : Set (Fin n)), ¬ (openGraph ω).Reachable k a}
      with hDk
    set mk : ℝ := ∫ ω, F (openCluster ω k) ∂μ with hmk
    set κ : ℝ := mk * μ.real Dk - ∫ ω in Dk, F (openCluster ω k) ∂μ with hκ
    set L := decoyList w (↑T : Set (Fin n)) D with hL
    set p : ℝ := obsConst w o v ((↑T : Set (Fin n)) ∪ {d | d ∈ D}) with hp
    set ck : Fin n → ℝ := avoidConst w k (↑T' : Set (Fin n)) with hck
    set Fh : Set (Sym2 (Fin n)) → ℝ := fun C => F {a | a = k ∨ ∃ e ∈ C, a ∈ e} with hFh
    set Tk : Fin n → ℝ := fun u => (∫ ω in Dk ∩ openConn k u, F (openCluster ω k) ∂μ) - μ.real (Dk ∩ openConn k u) * mk
      with hTk
    -- positivity of the conditioning events (non-degenerate weights)
    have hempty_Dk : (∅ : BondConfig (Fin n)) ∈ Dk := by
      intro a ha h
      rw [HullPort.reachable_empty_iff] at h
      exact hkT' (h ▸ (Finset.mem_coe.1 ha))
    have hDkpos : 0 < μ.real Dk := prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty_Dk⟩
    have hisopos : 0 < μ.real (Dk ∩ {ω | openEdgeCluster ω k = ∅}) :=
      prodBernoulli_real_pos_of_nonempty hw ⟨∅, hempty_Dk, subset_empty_iff.1 (openEdgeCluster_subset ∅ k)⟩
    -- set identities between the systems `(T; D)`, `(T'; k; D)` and `(T'; k :: D)`
    have hins : insert k (↑T' : Set (Fin n)) = ↑T := by
      rw [hT', Finset.coe_erase, insert_sdiff_singleton, insert_eq_of_mem (Finset.mem_coe.2 hkT)]
    have hset2 : (↑T' : Set (Fin n)) ∪ {d | d ∈ k :: D} = (↑T : Set (Fin n)) ∪ {d | d ∈ D} := by
      ext a
      simp only [mem_union, Finset.mem_coe, hT', Finset.mem_erase, mem_setOf_eq, List.mem_cons]
      constructor
      · rintro (⟨_, ha⟩ | rfl | ha)
        · exact Or.inl ha
        · exact Or.inl hkT
        · exact Or.inr ha
      · rintro (ha | ha)
        · by_cases hak : a = k
          · exact Or.inr (Or.inl hak)
          · exact Or.inl ⟨hak, ha⟩
        · exact Or.inr (Or.inr ha)
    have hcshMargin : ∀ f : Set (Sym2 (Fin n)) → ℝ,
        cshMargin w k (↑T' : Set (Fin n)) D o v f = cshMarg L p o v (covD w k (↑T' : Set (Fin n)) f) := by
      intro f
      rw [cshMargin, hins]
    have hnext : surplusMargin w T' r (k :: D) o v F =
        cshMarg L p o v (surplus w T' r F) - surplus w T' r F k * cshMarg L p o v ck := by
      rw [surplusMargin, hset2, decoyList, hins, cshMarg_cons]
    -- (1) Lemma P: peel `k`
    have hpeel : surplus w T r F = (surplus w T' r F) + Tk := by
      funext u
      rw [Pi.add_apply, surplus_erase_add w T r F hkT hlt u]
    -- (2) the top-relay term through `covD`
    have hTk_cov : (μ.real Dk) • Tk = covD w k (↑T' : Set (Fin n)) Fh - (κ * μ.real Dk) • ck := by
      funext u
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      have h1 := covD_clusterFun_eq w T' F k u
      have h2 : μ.real (Dk ∩ openConn k u) = μ.real Dk * ck u := by
        simp only [hck, avoidConst, hDk]
        rw [mul_div_cancel₀ _ (ne_of_gt hDkpos)]
      simp only [hTk, hFh, hκ, hmk, hDk] at h1 h2 ⊢
      rw [h1, h2]
      ring
    -- (3) CSH for the peeled relay, functional `F̂`
    have hCSHk := hCSH k T' D hkT' hko hkv (fun h => hoT (hT'T o h)) (fun h => hvT (hT'T v h)) hD
      (fun d hd => ⟨fun h => hkD (h ▸ hd), fun h => (hDT d hd).1 (hT'T d h), (hDT d hd).2.1, (hDT d hd).2.2⟩)
    have h3 : 0 ≤ cshMarg L p o v (covD w k (↑T' : Set (Fin n)) Fh) := by
      rw [← hcshMargin]
      exact hCSHk Fh (monotone_clusterFun k F hF)
    -- (4) Lemma AC: `Marg[c_k] ≥ 0` from CSH applied to `Ψ_iso`
    have h4 : 0 ≤ cshMarg L p o v ck := by
      have hiso := hCSHk psiIso psiIso_mono
      rw [hcshMargin] at hiso
      have hLk : ∀ dc ∈ L, dc.1 ≠ k := fun dc hdc h => hkD (h ▸ mem_decoyList w _ D dc hdc)
      rw [cshMarg_congr L p o v (covD w k (↑T' : Set (Fin n)) psiIso)
        ((μ.real (Dk ∩ {ω | openEdgeCluster ω k = ∅}) * μ.real Dk) • ck) (fun u => u ≠ k) hLk hko hkv
        (fun u hu => by
          rw [covD_psiIso w T' k u hu, Pi.smul_apply, smul_eq_mul]
          simp only [hck, avoidConst, hDk]
          rw [mul_assoc, mul_div_cancel₀ _ (ne_of_gt hDkpos)]), cshMarg_smul] at hiso
      exact (mul_nonneg_iff_of_pos_left (mul_pos hisopos hDkpos)).1 hiso
    -- (5) Lemma κ
    have h5 : κ ≤ surplus w T' r F k := kappa_le_surplus w T' r F k hrT' hmle
    -- (6) the next level by induction
    have h6 : 0 ≤ surplusMargin w T' r (k :: D) o v F :=
      ih T'.card hTcard T' r (k :: D) F rfl hF hrT' hcompatT' (fun h => hoT (hT'T o h)) (fun h => hvT (hT'T v h))
        (List.nodup_cons.2 ⟨hkD, hD⟩)
        (fun d hd => by
          rcases List.mem_cons.1 hd with rfl | hd
          · exact ⟨hkT', hko.symm, hkv.symm⟩
          · exact ⟨fun h => (hDT d hd).1 (hT'T d h), (hDT d hd).2.1, (hDT d hd).2.2⟩)
    -- (7) combine: `μ(Dk) · surplusMargin(T; D) ≥ μ(Dk) · surplusMargin(T'; k :: D) ≥ 0`
    have hmain : μ.real Dk * surplusMargin w T r D o v F =
        μ.real Dk * cshMarg L p o v (surplus w T' r F) + cshMarg L p o v (covD w k (↑T' : Set (Fin n)) Fh) -
          κ * μ.real Dk * cshMarg L p o v ck := by
      have e1 : μ.real Dk * cshMarg L p o v Tk =
          cshMarg L p o v (covD w k (↑T' : Set (Fin n)) Fh) - κ * μ.real Dk * cshMarg L p o v ck := by
        rw [← cshMarg_smul, hTk_cov, cshMarg_sub, cshMarg_smul]
      rw [surplusMargin, ← hL, ← hp, hpeel, cshMarg_add, mul_add, e1]
      ring
    have hbound : μ.real Dk * surplusMargin w T' r (k :: D) o v F ≤ μ.real Dk * surplusMargin w T r D o v F := by
      rw [hmain, hnext]
      have := mul_le_mul_of_nonneg_right h5 (mul_nonneg hDkpos.le h4)
      nlinarith [h3, h4, this, hDkpos.le]
    exact le_of_mul_le_mul_left (by linarith [mul_nonneg hDkpos.le h6]) hDkpos
  intro T r D F hF hr hcompat hoT hvT hD hDT
  exact main T.card T r D F rfl hF hr hcompat hoT hvT hD hDT

end CSH

end Percolation.Continuity
