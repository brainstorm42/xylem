import Percolation.Continuity.CovTau.StarHPrelim
import Percolation.Util.Linter

/-!
# Lemma (★^H) — the one-source bound of the COV(τ) proof with the owner replaced by a finite SET `S ∋ x`

The proof of (S5)_r for every r runs the A2 / T_A induction of the COV(τ) proof with the functional
`H_Γ(v) = Cov_Γ(Ψ(C_x), 1{v ↔ S})` for a finite set `S ∋ x` (`S = {x} ∪ decoys`) in place of
`Cov_Γ(Ψ(C_x), 1{v ↔ x})`. Its one-source input is Lemma (★^H): for a source set `N`, `θ = μ(v ↮ N |
v ↮ S)`, `Y^H(N) := E[ H_{G∖C_N}(v) ; x ∉ C_N ] ≤ θ · H_G(v)`, i.e. `Y^H(N)·P(v ↮ S) ≤ P(v ↮ S, v ↮
N)·H_G(v)`, and its corollary `Y^H(N) ≤ H_G(v)` (decision-tree Harris alone). Proof: law of total
covariance along the exploration `ℱ_N` of `C_N` (`SetClusterExploration`; on `{x ∈ C_N}` the owner's
functional is decided, on `{x ∉ C_N, v ∈ C_N}` the indicator `1{v ↔ S}` is decided, on `{x, v ∉
C_N}` the hybrid is the world `G ∖ C_N`), the decision-tree Harris inequality for `E[Ψ(C_x) | ℱ_N]`
and the increasing event `{v ↔ S ∪ N}` (`TreeHarris.treeHarris_real`, [Gladkov2024, Thm. 3.2]), and
van den Berg–Häggström–Kahn's Theorem 1.4 with the vertex SET `S`
(`BHK2006_twoSetConditionalAssociation.negCorrelation`: given `S ↮ v`, `Ψ(C_x)` (↑ in `C_S`) and
`1{v ↔ N}` (↑ in `C_v`) are negatively correlated; finitary form `bhk14S_ED`). [cite: Gladkov2024,
Thm. 3.2 (p. 4)] [cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7) with Remark 1 (p. 5), eq. (6)
(p. 4)]
-/

noncomputable section

namespace Percolation.Continuity

namespace CovTauStarN

open Finset MeasureTheory Percolation.Literature Percolation.Literature.DecisionTree
open Percolation.Literature.LatticeModels (prodBernoulli)
open SetClusterExploration TreeHarris
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

section Main

variable (D : Finset (Sym2 V)) {p : Sym2 V → ℝ} (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
variable (N : Finset V) (x v : V) (S : Finset V) (hvS : v ∉ S) (Ψ : Set (Sym2 V) → ℝ)
include hvS
include hp0 hp1

/-- **Lemma (★^H), finitary form**: for `x ∈ S`, `v ∉ S`, any source set `N`, `Ψ` monotone nonnegative
on edge sets:  `Y^H(N) · P(v ↮ S) ≤ P(v ↮ S, v ↮ N) · H(∅)`. [cite: Gladkov2024, Thm. 3.2 (p. 4)]
[cite: VandenbergHaggstromKahn2005, Thm. 1.4 (p. 7), eq. (6) (p. 4)] -/
theorem starH_ED (hxS : x ∈ S) (hΨ : Monotone Ψ) (hΨ0 : ∀ C, 0 ≤ Ψ C) :
    yH D p Ψ x S v N * ED D p (fun K => 1 - nr S v K) ≤
      ED D p (fun K => (1 - nr S v K) * (1 - nr N v K)) * covH D p Ψ x S v ∅ := by
  have hSD : SelfDetermined (revealedAt D N) := selfDetermined_revealedAt
  have hrev : revealed (ttree D (D.card + 1) (init N)) = revealedAt D N :=
    funext fun K => (revealedAt_eq_revealed (D := D) N K).symm
  /- 1.–2. law of total covariance: `Y^H = E[f J] − E[ĝ ȷ̂]`, `E[ĝ ȷ̂] = E[ĝ J]`. -/
  have hY : yH D p Ψ x S v N = ED D p (fun K => fcl Ψ x K * nr S v K) -
      ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * cE D p (revealedAt D N) (nr S v) K) := by
    rw [← ED_cE D p hSD (fun K => fcl Ψ x K * nr S v K), ← ED_sub]
    refine ED_congr_on D p fun K hK => ?_
    have hK' := Finset.mem_powerset.1 hK
    have hM := fun K₂ (hK₂ : K₂ ∈ D.powerset) =>
      starH_markov D N x v S hvS Ψ hK' (Finset.mem_powerset.1 hK₂)
    by_cases hx : x ∈ reached D N K
    · -- the owner's functional is decided: pull it out
      rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | x ∉ reached D N L} from fun h' => h' hx), zero_mul]
      have e1 : cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K = fcl Ψ x K * cE D p (revealedAt D N) (nr S v) K :=
        cE_mul_of_local_on D p (revealedAt D N) (fun K₂ hK₂ => (hM K₂ hK₂).1 hx) (nr S v)
      have e2 : cE D p (revealedAt D N) (fcl Ψ x) K = fcl Ψ x K :=
        calc cE D p (revealedAt D N) (fcl Ψ x) K = ∑ K₂ ∈ D.powerset, wtW D p K₂ * fcl Ψ x K :=
              Finset.sum_congr rfl fun K₂ hK₂ => by rw [(hM K₂ hK₂).1 hx]
          _ = fcl Ψ x K := by rw [← Finset.sum_mul, sum_wtW, one_mul]
      rw [e1, e2]; ring
    · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | x ∉ reached D N L} from hx), one_mul]
      have e2 : cE D p (revealedAt D N) (fcl Ψ x) K = ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂)) :=
        Finset.sum_congr rfl fun K₂ hK₂ => by rw [((hM K₂ hK₂).2.1 hx)]
      by_cases hv : v ∈ reached D N K
      · -- `1{v ↔ S}` is decided, and the world indicator vanishes
        have e1 : cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K =
            nr S v K * ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂)) := by
          calc cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K
              = cE D p (revealedAt D N) (fun L => nr S v L * fcl Ψ x L) K := by
                refine Finset.sum_congr rfl fun K₂ _ => ?_
                show wtW D p K₂ * (fcl Ψ x _ * nr S v _) = wtW D p K₂ * (nr S v _ * fcl Ψ x _); ring
            _ = nr S v K * cE D p (revealedAt D N) (fcl Ψ x) K :=
                cE_mul_of_local_on D p (revealedAt D N) (fun K₂ hK₂ => (hM K₂ hK₂).2.2.1 hv) (fcl Ψ x)
            _ = _ := by rw [e2]
        have e3 : cE D p (revealedAt D N) (nr S v) K = nr S v K :=
          calc cE D p (revealedAt D N) (nr S v) K = ∑ K₂ ∈ D.powerset, wtW D p K₂ * nr S v K :=
                Finset.sum_congr rfl fun K₂ hK₂ => by rw [(hM K₂ hK₂).2.2.1 hv]
            _ = nr S v K := by rw [← Finset.sum_mul, sum_wtW, one_mul]
        have e4 : covH D p Ψ x S v (reached D N K) = 0 := by
          unfold covH
          have z1 : ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂) * nr S v (off (reached D N K) K₂)) = 0 :=
            Finset.sum_eq_zero fun K₂ hK₂ => by simp only [(hM K₂ hK₂).2.2.2.2 hv, mul_zero]
          have z2 : ED D p (fun K₂ => nr S v (off (reached D N K) K₂)) = 0 :=
            Finset.sum_eq_zero fun K₂ hK₂ => by simp only [(hM K₂ hK₂).2.2.2.2 hv, mul_zero]
          rw [z1, z2]; ring
        rw [e1, e2, e3, e4]; ring
      · -- both undecided: the world covariance
        have e1 : cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K =
            ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂) * nr S v (off (reached D N K) K₂)) :=
          Finset.sum_congr rfl fun K₂ hK₂ => by
            show wtW D p K₂ * (fcl Ψ x _ * nr S v _) = _
            rw [(hM K₂ hK₂).2.1 hx, (hM K₂ hK₂).2.2.2.1 hv]
        have e3 : cE D p (revealedAt D N) (nr S v) K = ED D p (fun K₂ => nr S v (off (reached D N K) K₂)) :=
          Finset.sum_congr rfl fun K₂ hK₂ => by rw [(hM K₂ hK₂).2.2.2.1 hv]
        rw [e1, e2, e3]; rfl
  have hC : ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * cE D p (revealedAt D N) (nr S v) K) =
      ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K) := by
    rw [ED_mul_cE_comm D p hSD (cE D p (revealedAt D N) (fcl Ψ x)) (nr S v)]
    exact ED_congr_on D p fun K _ => by rw [cE_cE D p (revealedAt D N) hSD (fcl Ψ x) K]
  have hB0 : covH D p Ψ x S v ∅ = ED D p (fun K => fcl Ψ x K * nr S v K) - ED D p (fcl Ψ x) * ED D p (nr S v) := by
    simp only [covH, off_empty]
  /- 3. decision-tree Harris for `E[Ψ(C_x) | ℱ_N]` and `{v ↔ S ∪ N}`. -/
  have hGup : IsUpperSet {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} :=
    fun L L' hLL' ⟨s, hs, h⟩ => ⟨s, hs, h.mono (openGraph_mono (Finset.coe_subset.2 hLL'))⟩
  have hTH0 := treeHarris_real D hp0 hp1 (ttree D (D.card + 1) (init N)) (fcl_mono Ψ x hΨ) (fun K => hΨ0 _) hGup
  rw [hrev, PrW_eq_sum_ind] at hTH0
  have hTH : ED D p (fcl Ψ x) * (ED D p (nr S v) + ED D p (fun K => (1 - nr S v K) * nr N v K)) ≤
      ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K) +
        ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * ((1 - nr S v K) * nr N v K)) := by
    have eG : ∑ K ∈ D.powerset, wtW D p K *
        ind {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} K =
        ED D p (nr S v) + ED D p (fun K => (1 - nr S v K) * nr N v K) := by
      rw [← ED_add]
      exact Finset.sum_congr rfl fun K _ => by
        show wtW D p K * _ = wtW D p K * (nr S v K + (1 - nr S v K) * nr N v K)
        rw [← nr_union_eq]; rfl
    have eR : ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K *
        ind {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} K) =
        ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K) +
          ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * ((1 - nr S v K) * nr N v K)) := by
      rw [← ED_add]
      exact ED_congr_on D p fun K _ => by
        show _ = cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K +
          cE D p (revealedAt D N) (fcl Ψ x) K * ((1 - nr S v K) * nr N v K)
        rw [show ind {L : Finset (Sym2 V) | ∃ s ∈ S ∪ N, (openGraph (↑L : Set (Sym2 V))).Reachable s v} K = nr (S ∪ N) v K
          from rfl, nr_union_eq]; ring
    rw [← eG, ← eR]
    exact hTH0
  /- 4. `Z = 1{v↮S}·1{v↔N}` is decided by the exploration. -/
  have hZloc : ∀ K ∈ D.powerset, ∀ K₂ ∈ D.powerset,
      (1 - nr S v (splice (revealedAt D N K) K K₂)) * nr N v (splice (revealedAt D N K) K K₂) =
        (1 - nr S v K) * nr N v K := by
    intro K hK K₂ hK₂
    have hK' := Finset.mem_powerset.1 hK
    have hK₂' := Finset.mem_powerset.1 hK₂
    have hsub : splice (revealedAt D N K) K K₂ ⊆ D := splice_subset hK' hK₂'
    have hn : nr N v (splice (revealedAt D N K) K K₂) = nr N v K := by
      refine BystanderBHK.ind_congr ?_
      show (∃ s ∈ N, _) ↔ (∃ s ∈ N, _)
      rw [← mem_reached_iff' hsub, ← mem_reached_iff' hK', reached_splice]
    rw [hn]
    by_cases hv : v ∈ reached D N K
    · rw [(starH_markov D N x v S hvS Ψ hK' hK₂').2.2.1 hv]
    · rw [show nr N v K = 0 from ind_of_not_mem fun h => hv ((mem_reached_iff' hK').2 h), mul_zero, mul_zero]
  have hEZ : ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * ((1 - nr S v K) * nr N v K)) =
      ED D p (fun K => fcl Ψ x K * ((1 - nr S v K) * nr N v K)) := by
    calc ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * ((1 - nr S v K) * nr N v K))
        = ED D p (cE D p (revealedAt D N) (fun L => ((1 - nr S v L) * nr N v L) * fcl Ψ x L)) :=
          ED_congr_on D p fun K hK => by
            rw [cE_mul_of_local_on D p (revealedAt D N) (fun K₂ hK₂ => hZloc K hK K₂ hK₂) (fcl Ψ x)]; ring
      _ = ED D p (fun L => ((1 - nr S v L) * nr N v L) * fcl Ψ x L) := ED_cE D p hSD _
      _ = ED D p (fun K => fcl Ψ x K * ((1 - nr S v K) * nr N v K)) := ED_congr_on D p fun K _ => by
          show (1 - nr S v K) * nr N v K * fcl Ψ x K = fcl Ψ x K * ((1 - nr S v K) * nr N v K); ring
  /- 5. BHK 1.4 with the set `S`, and the constants. -/
  have hG := bhk14S_ED D hp0 hp1 N x v S hxS Ψ hΨ
  have hP : ED D p (fun K => 1 - nr S v K) = 1 - ED D p (nr S v) := by
    have h := ED_sub D p (fun _ => (1 : ℝ)) (nr S v)
    have h1 : ED D p (fun _ => (1 : ℝ)) = 1 := by unfold ED; rw [← Finset.sum_mul, sum_wtW, one_mul]
    rw [h1] at h
    exact h
  have hQ : ED D p (fun K => (1 - nr S v K) * (1 - nr N v K)) =
      ED D p (fun K => 1 - nr S v K) - ED D p (fun K => (1 - nr S v K) * nr N v K) := by
    rw [← ED_sub]
    exact ED_congr_on D p fun K _ => by
      show (1 - nr S v K) * (1 - nr N v K) = (1 - nr S v K) - (1 - nr S v K) * nr N v K; ring
  have hFh : ED D p (fun K => fcl Ψ x K * (1 - nr S v K)) = ED D p (fcl Ψ x) - ED D p (fun K => fcl Ψ x K * nr S v K) := by
    rw [← ED_sub]
    exact ED_congr_on D p fun K _ => by
      show fcl Ψ x K * (1 - nr S v K) = fcl Ψ x K - fcl Ψ x K * nr S v K; ring
  have hP0 : 0 ≤ ED D p (fun K => 1 - nr S v K) :=
    Finset.sum_nonneg fun K _ => mul_nonneg (wtW_nonneg D hp0 hp1 K) (by linarith [(nr_nonneg_le_one v S K).2])
  /- 6. combination. -/
  set Efh := ED D p (fun K => fcl Ψ x K * nr S v K) with hEfh
  set Ef := ED D p (fcl Ψ x) with hEf'
  set Eh := ED D p (nr S v) with hEh'
  set Cgh := ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K) with hCgh
  set EZ := ED D p (fun K => (1 - nr S v K) * nr N v K) with hEZ'
  set EfZ := ED D p (fun K => fcl Ψ x K * ((1 - nr S v K) * nr N v K)) with hEfZ
  rw [hEZ] at hTH
  rw [hP, hFh] at hG
  rw [hY, hC, hQ, hP, hB0]
  have h1 : (1 - Eh) * (Ef * EZ - EfZ) ≤ (1 - Eh) * (Cgh - Ef * Eh) := by
    rw [hP] at hP0
    exact mul_le_mul_of_nonneg_left (by linarith) hP0
  have key : (1 - Eh - EZ) * (Efh - Ef * Eh) - (Efh - Cgh) * (1 - Eh) =
      ((1 - Eh) * (Cgh - Ef * Eh) - (1 - Eh) * (Ef * EZ - EfZ)) + (EZ * (Ef - Efh) - (1 - Eh) * EfZ) := by ring
  nlinarith [h1, hG, key]

/-- **`Y^H(N) ≤ H(∅)`**: `H(∅) − Y^H(N) = Cov(E[Ψ(C_x) | ℱ_N], 1{v ↔ S}) ≥ 0` by the decision-tree Harris
inequality alone. [cite: Gladkov2024, Thm. 3.2 (p. 4)] -/
theorem yH_le_covH (hΨ : Monotone Ψ) (hΨ0 : ∀ C, 0 ≤ Ψ C) : yH D p Ψ x S v N ≤ covH D p Ψ x S v ∅ := by
  have hSD : SelfDetermined (revealedAt D N) := selfDetermined_revealedAt
  have hrev : revealed (ttree D (D.card + 1) (init N)) = revealedAt D N :=
    funext fun K => (revealedAt_eq_revealed (D := D) N K).symm
  -- `Y^H = E[f J] − E[ĝ ȷ̂]` exactly as in `starH_ED`
  have hY : yH D p Ψ x S v N = ED D p (fun K => fcl Ψ x K * nr S v K) -
      ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * cE D p (revealedAt D N) (nr S v) K) := by
    rw [← ED_cE D p hSD (fun K => fcl Ψ x K * nr S v K), ← ED_sub]
    refine ED_congr_on D p fun K hK => ?_
    have hK' := Finset.mem_powerset.1 hK
    have hM := fun K₂ (hK₂ : K₂ ∈ D.powerset) =>
      starH_markov D N x v S hvS Ψ hK' (Finset.mem_powerset.1 hK₂)
    by_cases hx : x ∈ reached D N K
    · rw [ind_of_not_mem (show K ∉ {L : Finset (Sym2 V) | x ∉ reached D N L} from fun h' => h' hx), zero_mul]
      have e1 : cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K = fcl Ψ x K * cE D p (revealedAt D N) (nr S v) K :=
        cE_mul_of_local_on D p (revealedAt D N) (fun K₂ hK₂ => (hM K₂ hK₂).1 hx) (nr S v)
      have e2 : cE D p (revealedAt D N) (fcl Ψ x) K = fcl Ψ x K :=
        calc cE D p (revealedAt D N) (fcl Ψ x) K = ∑ K₂ ∈ D.powerset, wtW D p K₂ * fcl Ψ x K :=
              Finset.sum_congr rfl fun K₂ hK₂ => by rw [(hM K₂ hK₂).1 hx]
          _ = fcl Ψ x K := by rw [← Finset.sum_mul, sum_wtW, one_mul]
      rw [e1, e2]; ring
    · rw [ind_of_mem (show K ∈ {L : Finset (Sym2 V) | x ∉ reached D N L} from hx), one_mul]
      have e2 : cE D p (revealedAt D N) (fcl Ψ x) K = ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂)) :=
        Finset.sum_congr rfl fun K₂ hK₂ => by rw [((hM K₂ hK₂).2.1 hx)]
      by_cases hv : v ∈ reached D N K
      · have e1 : cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K =
            nr S v K * ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂)) := by
          calc cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K
              = cE D p (revealedAt D N) (fun L => nr S v L * fcl Ψ x L) K := by
                refine Finset.sum_congr rfl fun K₂ _ => ?_
                show wtW D p K₂ * (fcl Ψ x _ * nr S v _) = wtW D p K₂ * (nr S v _ * fcl Ψ x _); ring
            _ = nr S v K * cE D p (revealedAt D N) (fcl Ψ x) K :=
                cE_mul_of_local_on D p (revealedAt D N) (fun K₂ hK₂ => (hM K₂ hK₂).2.2.1 hv) (fcl Ψ x)
            _ = _ := by rw [e2]
        have e3 : cE D p (revealedAt D N) (nr S v) K = nr S v K :=
          calc cE D p (revealedAt D N) (nr S v) K = ∑ K₂ ∈ D.powerset, wtW D p K₂ * nr S v K :=
                Finset.sum_congr rfl fun K₂ hK₂ => by rw [(hM K₂ hK₂).2.2.1 hv]
            _ = nr S v K := by rw [← Finset.sum_mul, sum_wtW, one_mul]
        have e4 : covH D p Ψ x S v (reached D N K) = 0 := by
          unfold covH
          have z1 : ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂) * nr S v (off (reached D N K) K₂)) = 0 :=
            Finset.sum_eq_zero fun K₂ hK₂ => by simp only [(hM K₂ hK₂).2.2.2.2 hv, mul_zero]
          have z2 : ED D p (fun K₂ => nr S v (off (reached D N K) K₂)) = 0 :=
            Finset.sum_eq_zero fun K₂ hK₂ => by simp only [(hM K₂ hK₂).2.2.2.2 hv, mul_zero]
          rw [z1, z2]; ring
        rw [e1, e2, e3, e4]; ring
      · have e1 : cE D p (revealedAt D N) (fun L => fcl Ψ x L * nr S v L) K =
            ED D p (fun K₂ => fcl Ψ x (off (reached D N K) K₂) * nr S v (off (reached D N K) K₂)) :=
          Finset.sum_congr rfl fun K₂ hK₂ => by
            show wtW D p K₂ * (fcl Ψ x _ * nr S v _) = _
            rw [(hM K₂ hK₂).2.1 hx, (hM K₂ hK₂).2.2.2.1 hv]
        have e3 : cE D p (revealedAt D N) (nr S v) K = ED D p (fun K₂ => nr S v (off (reached D N K) K₂)) :=
          Finset.sum_congr rfl fun K₂ hK₂ => by rw [(hM K₂ hK₂).2.2.2.1 hv]
        rw [e1, e2, e3]; rfl
  have hC : ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * cE D p (revealedAt D N) (nr S v) K) =
      ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K) := by
    rw [ED_mul_cE_comm D p hSD (cE D p (revealedAt D N) (fcl Ψ x)) (nr S v)]
    exact ED_congr_on D p fun K _ => by rw [cE_cE D p (revealedAt D N) hSD (fcl Ψ x) K]
  have hUp : IsUpperSet {L : Finset (Sym2 V) | ∃ s ∈ S, (openGraph (↑L : Set (Sym2 V))).Reachable s v} :=
    fun L L' hLL' ⟨s, hs, h⟩ => ⟨s, hs, h.mono (openGraph_mono (Finset.coe_subset.2 hLL'))⟩
  have hTH := treeHarris_real D hp0 hp1 (ttree D (D.card + 1) (init N)) (fcl_mono Ψ x hΨ) (fun K => hΨ0 _) hUp
  rw [hrev, PrW_eq_sum_ind] at hTH
  change ED D p (fcl Ψ x) * ED D p (nr S v) ≤ ED D p (fun K => cE D p (revealedAt D N) (fcl Ψ x) K * nr S v K) at hTH
  have hB0 : covH D p Ψ x S v ∅ = ED D p (fun K => fcl Ψ x K * nr S v K) - ED D p (fcl Ψ x) * ED D p (nr S v) := by
    simp only [covH, off_empty]
  rw [hY, hC, hB0]
  linarith

end Main

end CovTauStarN

end Percolation.Continuity

end
