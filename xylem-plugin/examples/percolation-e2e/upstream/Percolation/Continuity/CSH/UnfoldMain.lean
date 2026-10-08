import Percolation.Continuity.CSH.Unfold
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH: LEMMA U FOR GENERAL `k`, put together (the within-margin of the multi-marker reduction = H-part + Σ_j μ(E_j)⁻¹ · lower-level margins)

Lemma U, part 4.

`CSH.within_unfold` — for non-degenerate weights `w`, owner `x`, avoided set `Y`, distinct decoys `D` (off `x`, `Y`, `o`, `v`), any real `p` and
any functional `g` of the open edge cluster of `x`, the `{x↮Y}`-integral of the level-form margin of the WORLD covariances
`u ↦ Cov_{w^ω}(g(C_x), 1{x↔u})` (verbatim the integrand of the hypothesis `hU` of the induction skeleton `CSH.cshMargin_nonneg_of_unfold`,
`Continuity/AdditiveGluing/CSHInduction.lean`, worlds `w^ω` = `w` zeroed on the pairs meeting the open vertex cluster of `Y`) EQUALS

  `∫_{x↮Y} [Cov_{w^ω}(g(C_x), 1{o ↔ S}) − p·Cov_{w^ω}(g(C_x), 1{v ↔ S})] dμ_w  +  (subT(o) − p·subT(v))`,   `S = {x} ∪ D`,

the first term literally in the shape of the conclusion of Lemma H `CSH.hpart_nonneg_of_htw` (`Continuity/AdditiveGluing/CSHHpart.lean`), the
second the accumulated lower-level terms `CSH.subT` of `Continuity/CSH/Unfold.lean` (`= Σ_j μ(E_j)⁻¹·sl_{L_{>j}}[covD_{d_j,Y_j}(Φ̃_j)](u)`).
`CSH.subT_comb_nonneg` — `subT(o) − p·subT(v) = Σ_j μ(E_j)⁻¹ · cshMargin w d_j Y_j D_{>j} o v Φ̃_j ≥ 0` as soon as every lower-level margin at the
monotone nonnegative functionals `Φ̃_j = CSH.phiT … d_j` is nonnegative (the induction hypothesis of the skeleton, indexed by the splittings
`D = pre ++ d :: ds'`), for `p = CSH.obsConst w o v ({x} ∪ Y ∪ D)`.
`CSH.within_nonneg_of_hpart` — hence the within-margin is `≥ 0` given the lower levels and `Hpart ≥ 0`: the hypothesis `hU` of the skeleton
modulo Lemma H (whose input (Htw) is `CovTau.htw_world`).
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollaries] [cite: KozmaNitzan2024, Conj. 4 (p. 32)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open BHK2006 DecisionTree HullPort

namespace CSH

variable {V : Type*}

/-! ### Small dictionary -/

/-- `u ↦ 1{x ↔ u}(ζ)` is `J_{{x}}` for the open-reachability relation of `ζ`. [folklore] -/
theorem ind_openConn_eq_jn_singleton (x : V) (ζ : Set (Sym2 V)) :
    (fun u => ind (openConn x u : Set (BondConfig V)) ζ) = jn (openGraph ζ).Reachable {x} := by
  funext u; rw [← chi_reachable_eq_ind ζ u x, jn_singleton]

/-- `{ζ | ∃ s ∈ S, u ↔ s} = ⋃_{t ∈ S} {u ↔ t}` for a finite set `S`. [folklore] -/
theorem setOf_exists_reachable_eq_iUnion (S : Finset V) (u : V) :
    {ζ : Set (Sym2 V) | ∃ s ∈ (↑S : Set V), (openGraph ζ).Reachable u s} = ⋃ t ∈ S, (openConn u t : Set (BondConfig V)) := by
  ext ζ
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe, exists_prop]
  rfl

variable [Fintype V]

/-! ### The main identity -/

/-- **LEMMA U FOR GENERAL `k`**: the `{x↮Y}`-integral of the margin of the world
covariances `u ↦ Cov_{w^ω}(g(C_x), 1{x↔u})` equals the H-part (world covariances with the SET indicators `1{o ↔ {x}∪D}`, `1{v ↔ {x}∪D}`)
plus `subT(o) − p·subT(v)`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollaries] -/
theorem within_unfold (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V) (o v : V)
    (hnd : D.Nodup) (hD : ∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) (g : Set (Sym2 V) → ℝ) (p : ℝ) :
    ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
        cshMarg (decoyList w (insert x Y) D) p o v
          (fun u => (∫ η in (openConn x u : Set (BondConfig V)), g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) -
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) *
              (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e).real (openConn x u : Set (BondConfig V)))
        ∂(prodBernoulli w) =
      (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
        (((∫ η in (⋃ t ∈ insert x D.toFinset, openConn o t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ insert x D.toFinset, openConn o t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))) -
          p * ((∫ η in (⋃ t ∈ insert x D.toFinset, openConn v t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ insert x D.toFinset, openConn v t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))))
        ∂(prodBernoulli w)) +
      (subT w x Y g o {x} D - p * subT w x Y g v {x} D) := by
  classical
  set ŵ : Sym2 V → ℝ := fun e => (w e : ℝ) with hŵ
  have hm : ∑ ω, weight ŵ ω = 1 := by
    have h1 := integral_prodBernoulli_eq_sum w fun _ => (1 : ℝ)
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    exact h1.symm
  set L := decoyList w (insert x Y) D with hLdef
  set G : Set (Sym2 V) → ℝ := fun β => g (openEdgeCluster β x) with hG
  have hDev : {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} = avoidEv x Y := rfl
  have hL' : L = decoyList w ({x} ∪ Y) D := by rw [hLdef, ← Set.insert_eq]
  have hdecs : {d : V | d ∈ L.map Prod.fst} = {d | d ∈ D} := by rw [hLdef, map_fst_decoyList]
  set Sset : Set V := {x} ∪ {d | d ∈ D} with hSset
  have hSfin : (↑(insert x D.toFinset) : Set V) = Sset := by
    ext u; simp [hSset]
  -- the world test functions
  set Jf : V → Set (Sym2 V) → ℝ := fun u ζ => jn (openGraph ζ).Reachable Sset u with hJf
  set Tf : V → Set (Sym2 V) → ℝ := fun u ζ => unfoldT (openGraph ζ).Reachable {x} L u with hTf
  -- Step A: the integrand is a world covariance margin (sum vocabulary)
  rw [hDev, setIntegral_eq_sum_ind, setIntegral_eq_sum_ind]
  simp only [world_cov_eq_wcovOff]
  -- Step B: pointwise unfolding of the margin of the world covariances
  have stepB : ∀ ω, cshMarg L p o v (fun u => wcovOff ŵ Y G (ind (openConn x u : Set (BondConfig V))) ω) =
      wcovOff ŵ Y G (Jf o) ω - p * wcovOff ŵ Y G (Jf v) ω - wcovOff ŵ Y G (Tf o) ω + p * wcovOff ŵ Y G (Tf v) ω := by
    intro ω
    rw [cshMarg_eq_sum_single, wcovOff_finset_sum]
    have inner : (fun ζ => ∑ u, cshMarg L p o v (Pi.single u (1 : ℝ)) * ind (openConn x u : Set (BondConfig V)) ζ) =
        fun ζ => (Jf o ζ - p * Jf v ζ) - (Tf o ζ - p * Tf v ζ) + (unfoldK L o - p * unfoldK L v) := by
      funext ζ
      rw [← cshMarg_eq_sum_single L p o v (fun u => ind (openConn x u : Set (BondConfig V)) ζ), ind_openConn_eq_jn_singleton]
      simp only [cshMarg, slForm_jn (openGraph ζ).Reachable (fun a b h => h.symm) (fun a b c h h' => h.trans h') L {x}, hdecs,
        hJf, hTf, hSset]
      ring
    rw [inner, wcovOff_affine ŵ hm]
  -- Step C: sum over ω; the `unfoldT` parts are `−subT`
  have hDo : ∀ d ∈ D, d ∉ ({x} : Set V) ∧ d ∉ Y ∧ d ≠ o := fun d hd =>
    ⟨fun h => (hD d hd).1 (Set.mem_singleton_iff.1 h), (hD d hd).2.1, (hD d hd).2.2.1⟩
  have hDv : ∀ d ∈ D, d ∉ ({x} : Set V) ∧ d ∉ Y ∧ d ≠ v := fun d hd =>
    ⟨fun h => (hD d hd).1 (Set.mem_singleton_iff.1 h), (hD d hd).2.1, (hD d hd).2.2.2⟩
  have stepCo := sum_wcov_unfoldT w hw x Y g o D {x} (Set.mem_singleton x) hnd hDo
  have stepCv := sum_wcov_unfoldT w hw x Y g v D {x} (Set.mem_singleton x) hnd hDv
  rw [← hL'] at stepCo stepCv
  have e : ∀ ω, weight ŵ ω * (ind (avoidEv x Y) ω *
      cshMarg L p o v (fun u => wcovOff ŵ Y G (ind (openConn x u : Set (BondConfig V))) ω)) =
      weight ŵ ω * (ind (avoidEv x Y) ω * (wcovOff ŵ Y G (Jf o) ω - p * wcovOff ŵ Y G (Jf v) ω)) -
        weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y G (Tf o) ω) +
        p * (weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y G (Tf v) ω)) := by
    intro ω; rw [stepB ω]; ring
  rw [Finset.sum_congr rfl (fun ω _ => e ω), Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (∑ ω, weight ŵ ω * (ind (avoidEv x Y) ω * (wcovOff ŵ Y G (Jf o) ω - p * wcovOff ŵ Y G (Jf v) ω))) -
      (∑ ω, weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y G
        (fun ζ => unfoldT (openGraph ζ).Reachable {x} L o) ω)) +
      p * (∑ ω, weight ŵ ω * (ind (avoidEv x Y) ω * wcovOff ŵ Y G
        (fun ζ => unfoldT (openGraph ζ).Reachable {x} L v) ω)) = _
  rw [stepCo, stepCv]
  -- Step D: the H-part back in measure form
  have hJ : ∀ u, Jf u = ind (⋃ t ∈ insert x D.toFinset, (openConn u t : Set (BondConfig V))) := by
    intro u; funext ζ
    rw [hJf]
    dsimp only
    rw [jn_reachable_eq_ind, ← setOf_exists_reachable_eq_iUnion, hSfin]
  have eH : ∀ ω, weight ŵ ω * (ind (avoidEv x Y) ω * (wcovOff ŵ Y G (Jf o) ω - p * wcovOff ŵ Y G (Jf v) ω)) =
      weight ŵ ω * (ind (avoidEv x Y) ω *
        (wcovOff ŵ Y G (ind (⋃ t ∈ insert x D.toFinset, (openConn o t : Set (BondConfig V)))) ω -
          p * wcovOff ŵ Y G (ind (⋃ t ∈ insert x D.toFinset, (openConn v t : Set (BondConfig V)))) ω)) := by
    intro ω; rw [hJ o, hJ v]
  rw [Finset.sum_congr rfl (fun ω _ => eH ω)]
  have eM : ∀ ω, weight ŵ ω * (ind (avoidEv x Y) ω *
      (((∫ η in (⋃ t ∈ insert x D.toFinset, openConn o t), g (openEdgeCluster η x)
            ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
          (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
              (⋃ t ∈ insert x D.toFinset, openConn o t) *
            (∫ η, g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))) -
        p * ((∫ η in (⋃ t ∈ insert x D.toFinset, openConn v t), g (openEdgeCluster η x)
            ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
          (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
              (⋃ t ∈ insert x D.toFinset, openConn v t) *
            (∫ η, g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))))) =
      weight ŵ ω * (ind (avoidEv x Y) ω *
        (wcovOff ŵ Y G (ind (⋃ t ∈ insert x D.toFinset, (openConn o t : Set (BondConfig V)))) ω -
          p * wcovOff ŵ Y G (ind (⋃ t ∈ insert x D.toFinset, (openConn v t : Set (BondConfig V)))) ω)) := by
    intro ω
    rw [← world_cov_eq_wcovOff w Y ω G, ← world_cov_eq_wcovOff w Y ω G]
    ring
  rw [Finset.sum_congr rfl (fun ω _ => eM ω)]
  ring

/-! ### The lower-level terms are nonnegative given the lower levels -/

/-- **`subT(o) − p·subT(v) ≥ 0` from the lower levels**: along the splittings `D₀ = pre ++ rest`, with the source set
`S = {x} ∪ pre`, `subT_S(rest)(o) − p·subT_S(rest)(v) = Σ_{d ∈ rest} μ(E_d)⁻¹ · cshMargin w d ({x}∪Y∪pre_d) rest_{>d} o v Φ̃_d`, each term nonnegative
when the lower-level margins at the monotone nonnegative functionals `Φ̃_d` are (hypothesis `hIH`, the induction hypothesis of
`CSH.cshMargin_nonneg_of_unfold`) and `p = obsConst w o v ({x} ∪ Y ∪ D₀)`.
[cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem subT_comb_nonneg (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (D₀ : List V) (o v : V) {g : Set (Sym2 V) → ℝ}
    (hg : Monotone g)
    (hIH : ∀ (pre : List V) (d : V) (ds' : List V), D₀ = pre ++ d :: ds' →
      ∀ h : Set (Sym2 V) → ℝ, Monotone h → (∀ C, 0 ≤ h C) →
        0 ≤ cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds' o v h) :
    ∀ (rest pre : List V), D₀ = pre ++ rest →
      0 ≤ subT w x Y g o ({x} ∪ {e | e ∈ pre}) rest -
        obsConst w o v (insert x Y ∪ {d | d ∈ D₀}) * subT w x Y g v ({x} ∪ {e | e ∈ pre}) rest := by
  intro rest
  induction rest with
  | nil => intro pre _; simp [subT]
  | cons d ds ih =>
    intro pre hsplit
    set A : Set V := {x} ∪ {e | e ∈ pre} ∪ Y with hA
    have hA' : A = insert x Y ∪ {e | e ∈ pre} := by
      ext u; simp only [hA, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, Set.mem_insert_iff]; tauto
    have hset : insert d A ∪ {e | e ∈ ds} = insert x Y ∪ {e | e ∈ D₀} := by
      ext u
      simp only [hA, hsplit, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_append,
        List.mem_cons]
      tauto
    -- the head term is `μ(E)⁻¹ · cshMargin w d A ds o v Φ̃_d ≥ 0`
    have hmargin : slForm (decoyList w (insert d A) ds) (covD w d A (phiT w x Y g d)) o -
        obsConst w o v (insert x Y ∪ {e | e ∈ D₀}) * slForm (decoyList w (insert d A) ds) (covD w d A (phiT w x Y g d)) v =
        cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds o v (phiT w x Y g d) := by
      rw [← hset, ← hA']; rfl
    have hhead : 0 ≤ cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds o v (phiT w x Y g d) :=
      hIH pre d ds hsplit (phiT w x Y g d) (phiT_mono w x Y hg d) (fun K => phiFun_nonneg w x Y hg _)
    have hinv : 0 ≤ ((prodBernoulli w).real (avoidEv d A))⁻¹ := inv_nonneg.2 measureReal_nonneg
    -- the tail by induction with `pre ++ [d]`
    have htail := ih (pre ++ [d]) (by rw [hsplit]; simp)
    have hS' : ({x} ∪ {e | e ∈ pre ++ [d]} : Set V) = insert d ({x} ∪ {e | e ∈ pre}) := by
      ext u
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, List.mem_append, List.mem_singleton, Set.mem_insert_iff]
      tauto
    rw [hS'] at htail
    have hSY : ({x} ∪ {e | e ∈ pre} : Set V) ∪ Y = A := rfl
    simp only [subT, hSY]
    have key : ((prodBernoulli w).real (avoidEv d A))⁻¹ *
          slForm (decoyList w (insert d A) ds) (covD w d A (phiT w x Y g d)) o +
        subT w x Y g o (insert d ({x} ∪ {e | e ∈ pre})) ds -
        obsConst w o v (insert x Y ∪ {d | d ∈ D₀}) *
          (((prodBernoulli w).real (avoidEv d A))⁻¹ *
              slForm (decoyList w (insert d A) ds) (covD w d A (phiT w x Y g d)) v +
            subT w x Y g v (insert d ({x} ∪ {e | e ∈ pre})) ds) =
        ((prodBernoulli w).real (avoidEv d A))⁻¹ * cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds o v (phiT w x Y g d) +
          (subT w x Y g o (insert d ({x} ∪ {e | e ∈ pre})) ds -
            obsConst w o v (insert x Y ∪ {d | d ∈ D₀}) * subT w x Y g v (insert d ({x} ∪ {e | e ∈ pre})) ds) := by
      rw [← hmargin]; ring
    rw [key]
    exact add_nonneg (mul_nonneg hinv hhead) htail

/-- **The within-margin is nonnegative given the lower levels and the H-part** — the hypothesis `hU` of the induction skeleton
`CSH.cshMargin_nonneg_of_unfold` modulo Lemma H: for non-degenerate weights, distinct data, `g` monotone `≥ 0`,
`0 ≤ Hpart` (`hHP`, the conclusion of `CSH.hpart_nonneg_of_htw` at `S = {x} ∪ D`, `p = obsConst w o v ({x}∪Y∪D)`) and the lower-level margins
nonnegative (`hIH`) imply `0 ≤ ∫_{x↮Y} Marg[u ↦ Cov_{w^ω}(g(C_x), 1{x↔u})] dμ_w`.
[cite: KozmaNitzan2024, Conj. 4 (p. 32)] -/
theorem within_nonneg_of_hpart (w : Sym2 V → unitInterval) (hw : ∀ e, 0 < w e ∧ w e < 1) (x : V) (Y : Set V) (D : List V)
    (o v : V) (hnd : D.Nodup) (hD : ∀ d ∈ D, d ≠ x ∧ d ∉ Y ∧ d ≠ o ∧ d ≠ v) {g : Set (Sym2 V) → ℝ} (hg : Monotone g)
    (hIH : ∀ (pre : List V) (d : V) (ds' : List V), D = pre ++ d :: ds' →
      ∀ h : Set (Sym2 V) → ℝ, Monotone h → (∀ C, 0 ≤ h C) →
        0 ≤ cshMargin w d (insert x Y ∪ {e | e ∈ pre}) ds' o v h)
    (hHP : 0 ≤ ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
        (((∫ η in (⋃ t ∈ insert x D.toFinset, openConn o t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ insert x D.toFinset, openConn o t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))) -
          obsConst w o v (insert x Y ∪ {d | d ∈ D}) *
            ((∫ η in (⋃ t ∈ insert x D.toFinset, openConn v t), g (openEdgeCluster η x)
              ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e)) -
            (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e).real
                (⋃ t ∈ insert x D.toFinset, openConn v t) *
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z) then (0 : unitInterval) else w e))))
        ∂(prodBernoulli w)) :
    0 ≤ ∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y},
        cshMarg (decoyList w (insert x Y) D) (obsConst w o v (insert x Y ∪ {d | d ∈ D})) o v
          (fun u => (∫ η in (openConn x u : Set (BondConfig V)), g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) -
              (∫ η, g (openEdgeCluster η x)
                ∂(prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e)) *
              (prodBernoulli fun e => if (∃ z ∈ e, ∃ y ∈ Y, (openGraph ω).Reachable y z)
                  then (0 : unitInterval) else w e).real (openConn x u : Set (BondConfig V)))
        ∂(prodBernoulli w) := by
  rw [within_unfold w hw x Y D o v hnd hD g]
  have hsub := subT_comb_nonneg w x Y D o v hg hIH D [] (by simp)
  have hS0 : ({x} ∪ {e | e ∈ ([] : List V)} : Set V) = {x} := by ext u; simp
  rw [hS0] at hsub
  exact add_nonneg hHP hsub

end CSH

end Percolation.Continuity

end
