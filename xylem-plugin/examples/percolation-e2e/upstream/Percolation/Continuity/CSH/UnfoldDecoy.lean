import Percolation.Continuity.CSH.LevelForms
import Percolation.Continuity.CSH.UnfoldOneTools
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH, Lemma U for GENERAL `k`: the world term of ONE decoy (Markov at `C_Y`, dead decoys drop out, Markov at `C_d`, Lemma Φ(a), centring at the decoy constant)

Lemma U, part 2.  Sum level (`BHK2006.weight`, `Σ weight = 1`), worlds = delete the pairs meeting `Y ∪ V(C_Y(ω))` (`HullPort.cut Y ω`),
in the vocabulary of k = 1 tools `Continuity/CSH/UnfoldOneTools.lean` (`CSH.wcovOff`, `CSH.wmeanOff`, `markov_merge_Y`,
`residual_orthogonal`) and of the pointwise level-form algebra `Continuity/CSH/LevelForms.lean` (`CSH.chi/jn/av`, `CSH.slForm`).

Fix the owner `x`, the avoided set `Y`, a source set `S ∋ x` (the owner and the EARLIER decoys), a decoy `d ∉ S`, its avoidance event
`E = {d ↮ S ∪ Y}` with masses `m₀ = μ(E)`, `m₁(w') = μ(E ∩ {d ↔ w'})` and constant `c(w') = m₁(w')/m₀`, the LATER decoys `L'` (with
their constants), a marker `u`, and a functional `g` of the open edge cluster of `x`.  In the world of `ω` the `d`-term of the unfolding
(`CSH.unfoldT`) is `ε(d)·sl_{L'}[χ_d − c](u)` with `ε(d) = 1{d ↮ S}` and `χ_d(w') = 1{w' ↔ d}` read IN THE WORLD.  THIS FILE proves
(`CSH.decoy_world_term`):

  `Σ_ω w(ω) 1{x↮Y}(ω) · Cov_{world(ω)}( g(C_x), ε(d)·sl_{L'}[χ_d − c](u) )  =  −m₀⁻¹ · sl_{L'}[ w' ↦ m₀·P₁(w') − m₁(w')·P₀ ](u)`,

`P₁(w') = Σ_ζ w 1_E 1{d↔w'} Φ(C_d)`, `P₀ = Σ_ζ w 1_E Φ(C_d)`, `Φ(K) = Σ_η w I_K(η)` (Lemma-Φ functional `CSH.phiIntegrand` at the
vertex cluster of `d`; `CSH.phiS`), i.e. `−m₀⁻¹·sl_{L'}[covD_{d, S∪Y}(Φ)](u)` — the term "`+(μ(E_j)/μ(x↮Y))·Marg^{(j)}[Cov_{ρ_j}(Φ(C_{d_j}),1_·)]`"
before taking the `o − p·v` combination.  Steps: Markov merge at `C_Y` (`markov_merge_Y`); in the merged configuration a decoy
INSIDE `C_Y` is isolated in the world, its term is configuration-free and dies against the residual (`residual_orthogonal`); a decoy outside
`C_Y` has world indicators = global indicators (`CSH.reachable_sdiff_cut_iff_of_avoid`); linearity of `sl_{L'}` (`CSH.slForm_eq_sum_single`);
Markov at `C_d` (`HullPort.set_sum_cond_sdiff`) and Lemma Φ(a) (`CSH.sum_phiIntegrand_eq`) turn `Σ w Θ·1_E·F(C_d)` into `−Σ w 1_E F(C_d) Φ(C_d)`
(`CSH.sum_resid_mul_clusterFn`); centring at `c = m₁/m₀` gives the denominator-free covariance (`CSH.sum_resid_decoy_moment`).
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollaries]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open BHK2006 DecisionTree HullPort

namespace CSH

variable {V : Type*}

/-! ### The abstract indicators of `Continuity/CSH/LevelForms` read on a configuration -/

/-- `χ_d(w')` for the open-reachability relation of `ζ` is `1{d ↔ w'}(ζ)`. [folklore] -/
theorem chi_reachable_eq_ind (ζ : Set (Sym2 V)) (w' d : V) :
    chi (openGraph ζ).Reachable w' d = ind (openConn d w' : Set (BondConfig V)) ζ := by
  unfold chi
  by_cases h : (openGraph ζ).Reachable w' d
  · rw [if_pos h, ind_of_mem (show ζ ∈ openConn d w' from h.symm)]
  · rw [if_neg h, ind_of_not_mem (show ζ ∉ openConn d w' from fun h' => h (SimpleGraph.Reachable.symm h'))]

/-- `ε_S(d)` for the open-reachability relation of `ζ` is `1{d ↮ S}(ζ)`. [folklore] -/
theorem av_reachable_eq_ind (ζ : Set (Sym2 V)) (S : Set V) (d : V) :
    av (openGraph ζ).Reachable S d = ind (avoidEv d S) ζ := by
  unfold av
  by_cases h : ∀ s ∈ S, ¬ (openGraph ζ).Reachable d s
  · rw [if_pos h, ind_of_mem (show ζ ∈ avoidEv d S from h)]
  · rw [if_neg h, ind_of_not_mem (show ζ ∉ avoidEv d S from h)]

/-- `J_S(u)` for the open-reachability relation of `ζ` is `1{u ↔ S}(ζ)`. [folklore] -/
theorem jn_reachable_eq_ind (ζ : Set (Sym2 V)) (S : Set V) (u : V) :
    jn (openGraph ζ).Reachable S u = ind {ζ' : Set (Sym2 V) | ∃ s ∈ S, (openGraph ζ').Reachable u s} ζ := by
  unfold jn
  by_cases h : ∃ s ∈ S, (openGraph ζ).Reachable u s
  · rw [if_pos h, ind_of_mem (show ζ ∈ {ζ' : Set (Sym2 V) | ∃ s ∈ S, (openGraph ζ').Reachable u s} from h)]
  · rw [if_neg h, ind_of_not_mem (show ζ ∉ {ζ' : Set (Sym2 V) | ∃ s ∈ S, (openGraph ζ').Reachable u s} from h)]

/-! ### World indicators of a decoy: alive (outside `C_Y`) = global; dead (inside `C_Y`) = isolated -/

/-- A decoy not joined to `Y` keeps all its connections in the world `ζ ∖ cut_Y ζ`. [folklore] -/
theorem reachable_world_iff_of_alive {ζ : Set (Sym2 V)} {Y : Set V} {d : V} (h : ζ ∈ avoidEv d Y) (a : V) :
    (openGraph (ζ \ cut Y ζ)).Reachable a d ↔ (openGraph ζ).Reachable a d := by
  rw [SimpleGraph.reachable_comm, reachable_sdiff_cut_iff_of_avoid h a, SimpleGraph.reachable_comm]

/-- A decoy joined to `Y` is isolated in the world `ζ ∖ cut_Y ζ`. [folklore] -/
theorem reachable_world_iff_of_dead {ζ : Set (Sym2 V)} {Y : Set V} {d : V} (h : ζ ∉ avoidEv d Y) (a : V) :
    (openGraph (ζ \ cut Y ζ)).Reachable a d ↔ a = d := by
  constructor
  · intro hr; exact eq_of_reachable_sdiff_cut h ζ a hr.symm
  · rintro rfl; exact SimpleGraph.Reachable.refl a

/-- Alive decoy: the world term `ε(d)·sl_{L'}[χ_d − c](u)` equals `1{d ↮ S}(ζ) · sl_{L'}[1{d ↔ ·}(ζ) − c](u)` (global indicators).
[folklore] -/
theorem world_term_alive {ζ : Set (Sym2 V)} {Y : Set V} {d : V} (h : ζ ∈ avoidEv d Y) (S : Set V)
    (L' : List (V × (V → ℝ))) (c : V → ℝ) (u : V) :
    av (openGraph (ζ \ cut Y ζ)).Reachable S d *
        slForm L' (fun w' => chi (openGraph (ζ \ cut Y ζ)).Reachable w' d - c w') u =
      ind (avoidEv d S) ζ * slForm L' (fun w' => ind (openConn d w' : Set (BondConfig V)) ζ - c w') u := by
  have hfun : (fun w' => chi (openGraph (ζ \ cut Y ζ)).Reachable w' d - c w') =
      fun w' => ind (openConn d w' : Set (BondConfig V)) ζ - c w' := by
    funext w'
    rw [← chi_reachable_eq_ind ζ w' d]
    unfold chi
    rw [show ((openGraph (ζ \ cut Y ζ)).Reachable w' d) = ((openGraph ζ).Reachable w' d) from
      propext (reachable_world_iff_of_alive h w')]
  have hav : av (openGraph (ζ \ cut Y ζ)).Reachable S d = ind (avoidEv d S) ζ := by
    rw [← av_reachable_eq_ind ζ S d]
    unfold av
    have : (∀ s ∈ S, ¬ (openGraph (ζ \ cut Y ζ)).Reachable d s) ↔ (∀ s ∈ S, ¬ (openGraph ζ).Reachable d s) :=
      forall₂_congr fun s _ => by rw [reachable_sdiff_cut_iff_of_avoid h s]
    rw [show (∀ s ∈ S, ¬ (openGraph (ζ \ cut Y ζ)).Reachable d s) = (∀ s ∈ S, ¬ (openGraph ζ).Reachable d s) from
      propext this]
  rw [hfun, hav]

/-- Dead decoy: the world term `ε(d)·sl_{L'}[χ_d − c](u)` is the CONFIGURATION-FREE number `−sl_{L'}[c](u)` (for `d ∉ S`, `u ≠ d` and
`d` not among the later decoys). [folklore] -/
theorem world_term_dead {ζ : Set (Sym2 V)} {Y : Set V} {d : V} (h : ζ ∉ avoidEv d Y) {S : Set V} (hdS : d ∉ S)
    (L' : List (V × (V → ℝ))) (hL' : ∀ dc ∈ L', dc.1 ≠ d) (c : V → ℝ) {u : V} (hu : u ≠ d) :
    av (openGraph (ζ \ cut Y ζ)).Reachable S d *
        slForm L' (fun w' => chi (openGraph (ζ \ cut Y ζ)).Reachable w' d - c w') u = - slForm L' c u := by
  have hav : av (openGraph (ζ \ cut Y ζ)).Reachable S d = 1 := by
    unfold av
    rw [if_pos]
    intro s hs hr
    rw [SimpleGraph.reachable_comm, reachable_world_iff_of_dead h s] at hr
    exact hdS (hr ▸ hs)
  have hchi : ∀ w', w' ≠ d → chi (openGraph (ζ \ cut Y ζ)).Reachable w' d = 0 := by
    intro w' hw'
    unfold chi
    rw [if_neg (fun hr => hw' ((reachable_world_iff_of_dead h w').1 hr))]
  have hsl : slForm L' (fun w' => chi (openGraph (ζ \ cut Y ζ)).Reachable w' d - c w') u =
      slForm L' (fun w' => (-1 : ℝ) • c w') u := by
    refine slForm_congr L' ?_ fun dc hdc => ?_
    · rw [hchi u hu]; simp
    · rw [hchi dc.1 (hL' dc hdc)]; simp
  rw [hav, one_mul, hsl, show (fun w' => (-1 : ℝ) • c w') = (-1 : ℝ) • c from rfl, slForm_smul, Pi.smul_apply,
    smul_eq_mul]
  ring

/-! ### The residual `Θ` and the Lemma-Φ functional at the cluster of a decoy (sum level) -/

variable [Fintype V]

/-- **The telescoping residual** `Θ(ζ) = 1{x ↮ Y}(ζ)·(g(C_x(ζ)) − ḡ(C_Y(ζ)))`, `ḡ` the world mean.
[folklore] -/
def resid (w : Sym2 V → ℝ) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (ζ : Set (Sym2 V)) : ℝ :=
  ind (avoidEv x Y) ζ * (g (openEdgeCluster ζ x) - wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ)

/-- **`Φ(C_d(ζ))`**, sum level: Lemma-Φ functional `Σ_η w I_K(η)` at the open VERTEX cluster `K = C_d(ζ)`.
[folklore] -/
def phiS (w : Sym2 V → ℝ) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ) (d : V) (ζ : Set (Sym2 V)) : ℝ :=
  ∑ η, weight w η * phiIntegrand x Y (openCluster ζ d) g η

/-- Deleting the cut set of a decoy avoiding `{x} ∪ Y` does not change the residual `Θ`. [folklore] -/
theorem resid_sdiff_cut_singleton (w : Sym2 V → ℝ) {x : V} {Y : Set V} (g : Set (Sym2 V) → ℝ) {d : V}
    {ζ : Set (Sym2 V)} (h : ζ ∈ avoidEv d (insert x Y)) : resid w x Y g (ζ \ cut {d} ζ) = resid w x Y g ζ := by
  have hdY : ζ ∈ avoidEv d Y := fun y hy => h y (mem_insert_of_mem x hy)
  have hxd : ζ ∈ avoidEv x {d} := fun t ht => by
    rw [mem_singleton_iff] at ht; subst ht
    exact fun hr => h x (mem_insert x Y) hr.symm
  unfold resid
  have e1 : openEdgeCluster (ζ \ cut {d} ζ) x = openEdgeCluster ζ x := openEdgeCluster_sdiff_cut_of_avoid hxd
  have e2 : wmeanOff w Y (fun β => g (openEdgeCluster β x)) (ζ \ cut {d} ζ) =
      wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ := by
    unfold wmeanOff; rw [cut_sdiff_cut_singleton_of_avoid hdY]
  have e3 : ind (avoidEv x Y) (ζ \ cut {d} ζ) = ind (avoidEv x Y) ζ := by
    by_cases hx : ζ ∈ avoidEv x Y
    · rw [ind_of_mem hx, ind_of_mem]
      exact fun y hy hr => hx y hy ((reachable_sdiff_cut_iff_of_avoid hxd y).1 hr)
    · rw [ind_of_not_mem hx, ind_of_not_mem]
      exact fun h' => hx fun y hy hr => h' y hy ((reachable_sdiff_cut_iff_of_avoid hxd y).2 hr)
  rw [e1, e2, e3]

/-- **Lemma Φ(a) in residual form**: the world mean of `Θ` off the cluster of `d` is `−Φ(C_d)`:
`Σ_η w(η) Θ(η ∖ cut_{d} ζ) = −Φ(C_d(ζ))`. [folklore] -/
theorem sum_resid_world_singleton (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) (ζ : Set (Sym2 V)) :
    ∑ η, weight w η * resid w x Y g (η \ cut {d} ζ) = - phiS w x Y g d ζ := by
  unfold phiS
  rw [sum_phiIntegrand_eq w hm x Y (openCluster ζ d) g, ← cut_singleton_eq_edgesOf, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun η _ => ?_
  unfold resid; ring

/-- `1{d ↮ A}` read off the edge cluster of `d`. [folklore] -/
theorem ind_avoidEv_eq_ite_cluster (d : V) (A : Set V) (ζ : Set (Sym2 V)) :
    ind (avoidEv d A) ζ = if (∀ a ∈ A, ¬ (a ∈ ({d} : Set V) ∨ ∃ e ∈ setCl ζ {d}, a ∈ e)) then 1 else 0 := by
  have key : (∀ a ∈ A, ¬ (a ∈ ({d} : Set V) ∨ ∃ e ∈ setCl ζ {d}, a ∈ e)) ↔ ζ ∈ avoidEv d A := by
    refine forall₂_congr fun a _ => not_congr ?_
    rw [← setReach_iff ζ {d} a]
    simp only [mem_singleton_iff, exists_eq_left]
  by_cases h : ζ ∈ avoidEv d A
  · rw [ind_of_mem h, if_pos (key.2 h)]
  · rw [ind_of_not_mem h, if_neg (fun h' => h (key.1 h'))]

/-- **Markov at the cluster of a decoy + Lemma Φ(a)**: for every function `f` of the open edge cluster of `d` and every avoided set
`A ⊇ {x} ∪ Y`:  `Σ_ζ w Θ(ζ)·1{d ↮ A}(ζ)·f(C_d(ζ)) = −Σ_ζ w 1{d ↮ A}(ζ)·f(C_d(ζ))·Φ(C_d(ζ))`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) — corollary] -/
theorem sum_resid_mul_clusterFn (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) {A : Set V} (hA : insert x Y ⊆ A) (f : Set (Sym2 V) → ℝ) :
    ∑ ζ, weight w ζ * (resid w x Y g ζ * (ind (avoidEv d A) ζ * f (openEdgeCluster ζ d))) =
      - ∑ ζ, weight w ζ * (ind (avoidEv d A) ζ * f (openEdgeCluster ζ d) * phiS w x Y g d ζ) := by
  classical
  set K : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun W β =>
    (if (∀ a ∈ A, ¬ (a ∈ ({d} : Set V) ∨ ∃ e ∈ W, a ∈ e)) then 1 else 0) * f W * resid w x Y g β with hK
  have key := set_sum_cond_sdiff w hm {d} K
  have hL : ∀ ζ, weight w ζ * K (setCl ζ {d}) (ζ \ barOf {d} (setCl ζ {d})) =
      weight w ζ * (resid w x Y g ζ * (ind (avoidEv d A) ζ * f (openEdgeCluster ζ d))) := by
    intro ζ
    simp only [hK]
    rw [← ind_avoidEv_eq_ite_cluster d A ζ, ← cut_eq_barOf, setCl_singleton]
    by_cases h : ζ ∈ avoidEv d A
    · rw [resid_sdiff_cut_singleton w g (fun a ha => h a (hA ha))]; ring
    · rw [ind_of_not_mem h]; ring
  have hR : ∀ ζ, weight w ζ * ∑ η, weight w η * K (setCl ζ {d}) (η \ barOf {d} (setCl ζ {d})) =
      - (weight w ζ * (ind (avoidEv d A) ζ * f (openEdgeCluster ζ d) * phiS w x Y g d ζ)) := by
    intro ζ
    simp only [hK]
    rw [← ind_avoidEv_eq_ite_cluster d A ζ, ← cut_eq_barOf, setCl_singleton]
    have e : ∑ η, weight w η * (ind (avoidEv d A) ζ * f (openEdgeCluster ζ d) * resid w x Y g (η \ cut {d} ζ)) =
        ind (avoidEv d A) ζ * f (openEdgeCluster ζ d) * ∑ η, weight w η * resid w x Y g (η \ cut {d} ζ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun η _ => by ring
    rw [e, sum_resid_world_singleton w hm x Y g d ζ]; ring
  calc _ = ∑ ζ, weight w ζ * K (setCl ζ {d}) (ζ \ barOf {d} (setCl ζ {d})) :=
        Finset.sum_congr rfl fun ζ _ => (hL ζ).symm
    _ = ∑ ζ, weight w ζ * ∑ η, weight w η * K (setCl ζ {d}) (η \ barOf {d} (setCl ζ {d})) := key
    _ = ∑ ζ, - (weight w ζ * (ind (avoidEv d A) ζ * f (openEdgeCluster ζ d) * phiS w x Y g d ζ)) :=
        Finset.sum_congr rfl fun ζ _ => hR ζ
    _ = _ := by rw [Finset.sum_neg_distrib]

/-! ### Centring at the decoy constant -/

/-- `1{d ↔ w'}` read off the edge cluster of `d`. [folklore] -/
theorem ind_openConn_eq_ite_cluster (d w' : V) (ζ : Set (Sym2 V)) :
    ind (openConn d w' : Set (BondConfig V)) ζ = if (w' = d ∨ ∃ e ∈ openEdgeCluster ζ d, w' ∈ e) then 1 else 0 := by
  by_cases h : (openGraph ζ).Reachable d w'
  · rw [ind_of_mem (show ζ ∈ openConn d w' from h), if_pos ((reachable_iff_exists_mem_openEdgeCluster ζ d w').1 h)]
  · rw [ind_of_not_mem (show ζ ∉ openConn d w' from h),
      if_neg (fun h' => h ((reachable_iff_exists_mem_openEdgeCluster ζ d w').2 h'))]

/-- **The centred decoy moment** (`E_{ρ_j}[Θ·(1{w∈C_{d_j}} − c_j(w))] = −Cov_{ρ_j}(Φ(C_{d_j}), 1{w∈C_{d_j}})`, denominator-free):
with `E = {d ↮ A}` (`A ⊇ {x} ∪ Y`), `m₀ = μ(E) ≠ 0`, `m₁ = μ(E ∩ {d↔w'})`, `c = m₁/m₀`, `P₁ = Σ w 1_E 1{d↔w'} Φ(C_d)`, `P₀ = Σ w 1_E Φ(C_d)`:
`Σ_ζ w Θ·1_E·(1{d↔w'} − c) = −m₀⁻¹·(m₀ P₁ − m₁ P₀)`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) — corollary] -/
theorem sum_resid_decoy_moment (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (x : V) (Y : Set V)
    (g : Set (Sym2 V) → ℝ) (d : V) {A : Set V} (hA : insert x Y ⊆ A) (w' : V) {c : ℝ}
    (hm₀ : ∑ ζ, weight w ζ * ind (avoidEv d A) ζ ≠ 0)
    (hc : c = (∑ ζ, weight w ζ * ind (avoidEv d A ∩ openConn d w') ζ) / ∑ ζ, weight w ζ * ind (avoidEv d A) ζ) :
    ∑ ζ, weight w ζ * (resid w x Y g ζ * (ind (avoidEv d A) ζ * (ind (openConn d w' : Set (BondConfig V)) ζ - c))) =
      - ((∑ ζ, weight w ζ * ind (avoidEv d A) ζ)⁻¹ *
          ((∑ ζ, weight w ζ * ind (avoidEv d A) ζ) *
              (∑ ζ, weight w ζ * (ind (avoidEv d A ∩ openConn d w') ζ * phiS w x Y g d ζ)) -
            (∑ ζ, weight w ζ * ind (avoidEv d A ∩ openConn d w') ζ) *
              (∑ ζ, weight w ζ * (ind (avoidEv d A) ζ * phiS w x Y g d ζ)))) := by
  -- the test function as a function of the edge cluster of `d`
  set f : Set (Sym2 V) → ℝ := fun K => (if (w' = d ∨ ∃ e ∈ K, w' ∈ e) then (1 : ℝ) else 0) - c with hf
  have hfK : ∀ ζ : Set (Sym2 V), f (openEdgeCluster ζ d) = ind (openConn d w' : Set (BondConfig V)) ζ - c := by
    intro ζ; rw [hf, ind_openConn_eq_ite_cluster]
  have h1 := sum_resid_mul_clusterFn w hm x Y g d hA f
  simp only [hfK] at h1
  rw [h1]
  set m₀ := ∑ ζ, weight w ζ * ind (avoidEv d A) ζ with hm₀'
  set m₁ := ∑ ζ, weight w ζ * ind (avoidEv d A ∩ openConn d w') ζ with hm₁'
  set P₁ := ∑ ζ, weight w ζ * (ind (avoidEv d A ∩ openConn d w') ζ * phiS w x Y g d ζ) with hP₁
  set P₀ := ∑ ζ, weight w ζ * (ind (avoidEv d A) ζ * phiS w x Y g d ζ) with hP₀
  have e : ∑ ζ, weight w ζ * (ind (avoidEv d A) ζ * (ind (openConn d w' : Set (BondConfig V)) ζ - c) * phiS w x Y g d ζ) =
      P₁ - c * P₀ := by
    rw [hP₁, hP₀, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [ind_inter]; ring
  rw [e, hc]
  field_simp

/-! ### The world term of one decoy -/

omit [Fintype V] in
/-- `1{d ↮ Y} · 1{d ↮ S} = 1{d ↮ S ∪ Y}`. [folklore] -/
theorem ind_avoidEv_mul_union (d : V) (S Y : Set V) (ζ : Set (Sym2 V)) :
    ind (avoidEv d Y) ζ * ind (avoidEv d S) ζ = ind (avoidEv d (S ∪ Y)) ζ := by
  by_cases hY : ζ ∈ avoidEv d Y
  · by_cases hS : ζ ∈ avoidEv d S
    · rw [ind_of_mem hY, ind_of_mem hS, one_mul, ind_of_mem]
      intro a ha
      rcases ha with ha | ha
      · exact hS a ha
      · exact hY a ha
    · rw [ind_of_mem hY, ind_of_not_mem hS, mul_zero, ind_of_not_mem]
      exact fun h => hS fun a ha => h a (Or.inl ha)
  · rw [ind_of_not_mem hY, zero_mul, ind_of_not_mem]
    exact fun h => hY fun a ha => h a (Or.inr ha)

/-- `1{d ↮ Y}` read off the cluster of `Y`: `1 − 1{d ↮ Y}(ζ)` is a function of `C_Y(ζ)` (stated in the `Fintype` context of its use,
so that the decidability instances agree). [folklore] -/
theorem one_sub_ind_avoidEv_eq (d : V) (Y : Set V) (ζ : Set (Sym2 V)) :
    1 - ind (avoidEv d Y) ζ = 1 - (if (d ∈ Y ∨ ∃ e ∈ setCl ζ Y, d ∈ e) then 0 else 1) := by
  by_cases h : (d ∈ Y ∨ ∃ e ∈ setCl ζ Y, d ∈ e)
  · rw [if_pos h, ind_of_not_mem (fun h' => (mem_avoidEv_iff_notMem_span d Y ζ).1 h' h)]
  · rw [if_neg h, ind_of_mem ((mem_avoidEv_iff_notMem_span d Y ζ).2 h)]

/-- **THE WORLD TERM OF ONE DECOY**.  Data: owner `x`,
avoided set `Y`, source set `S ∋ x` (owner + earlier decoys), decoy `d ∉ S`, later decoys `L'` (none equal to `d`), marker `u ≠ d`,
`E = {d ↮ S ∪ Y}`, `m₀ = μ(E) ≠ 0`, `c(w') = μ(E ∩ {d↔w'})/m₀`.  Then
`Σ_ω w 1{x↮Y} Cov_{world(ω)}(g(C_x), ε(d)·sl_{L'}[χ_d − c](u)) = −m₀⁻¹ · sl_{L'}[w' ↦ m₀·P₁(w') − m₁(w')·P₀](u)`
with `P₁(w') = Σ w 1_E 1{d↔w'} Φ(C_d)`, `P₀ = Σ w 1_E Φ(C_d)`.
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollaries] -/
theorem decoy_world_term (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    {S : Set V} (hxS : x ∈ S) {d : V} (hdS : d ∉ S) (L' : List (V × (V → ℝ))) (hL' : ∀ dc ∈ L', dc.1 ≠ d)
    {u : V} (hu : u ≠ d) (c : V → ℝ)
    (hm₀ : ∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y)) ζ ≠ 0)
    (hc : ∀ w', c w' = (∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ) /
      ∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y)) ζ) :
    ∑ ω, weight w ω * (ind (avoidEv x Y) ω *
        wcovOff w Y (fun β => g (openEdgeCluster β x))
          (fun ζ => av (openGraph ζ).Reachable S d * slForm L' (fun w' => chi (openGraph ζ).Reachable w' d - c w') u) ω) =
      - ((∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y)) ζ)⁻¹ *
          slForm L' (fun w' =>
            (∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y)) ζ) *
                (∑ ζ, weight w ζ * (ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ * phiS w x Y g d ζ)) -
              (∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ) *
                (∑ ζ, weight w ζ * (ind (avoidEv d (S ∪ Y)) ζ * phiS w x Y g d ζ))) u) := by
  classical
  have hA : insert x Y ⊆ S ∪ Y := by
    intro a ha
    rcases mem_insert_iff.1 ha with rfl | ha
    · exact Or.inl hxS
    · exact Or.inr ha
  set G : Set (Sym2 V) → ℝ := fun β => g (openEdgeCluster β x) with hG
  set ψ : Set (Sym2 V) → ℝ := fun ζ =>
    av (openGraph ζ).Reachable S d * slForm L' (fun w' => chi (openGraph ζ).Reachable w' d - c w') u with hψ
  -- abbreviations for the right-hand side
  set m₀ := ∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y)) ζ with hm₀'
  set Q : V → ℝ := fun w' =>
    m₀ * (∑ ζ, weight w ζ * (ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ * phiS w x Y g d ζ)) -
      (∑ ζ, weight w ζ * ind (avoidEv d (S ∪ Y) ∩ openConn d w') ζ) *
        (∑ ζ, weight w ζ * (ind (avoidEv d (S ∪ Y)) ζ * phiS w x Y g d ζ)) with hQ
  -- Step 1: world covariance as a centred world mean, and the Markov merge at `C_Y`
  have step1 : ∑ ω, weight w ω * (ind (avoidEv x Y) ω * wcovOff w Y G ψ ω) =
      ∑ ζ, weight w ζ * (resid w x Y g ζ * ψ (ζ \ cut Y ζ)) := by
    have h := markov_merge_Y w hm x Y g ψ
    have lhs : ∀ ω, weight w ω * (ind (avoidEv x Y) ω * wcovOff w Y G ψ ω) =
        weight w ω * (ind (avoidEv x Y) ω * ∑ η, weight w η * ((g (openEdgeCluster (η \ cut Y ω) x) -
          wmeanOff w Y (fun β => g (openEdgeCluster β x)) ω) * ψ (η \ cut Y ω))) := by
      intro ω; rw [wcovOff_eq_sum]
    rw [Finset.sum_congr rfl (fun ω _ => lhs ω), h]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    unfold resid; ring
  -- Step 2: the world test function in the merged configuration (alive / dead decoy)
  have step2 : ∀ ζ, ψ (ζ \ cut Y ζ) =
      ind (avoidEv d (S ∪ Y)) ζ * slForm L' (fun w' => ind (openConn d w' : Set (BondConfig V)) ζ - c w') u +
        (1 - ind (avoidEv d Y) ζ) * (- slForm L' c u) := by
    intro ζ
    by_cases h : ζ ∈ avoidEv d Y
    · rw [hψ]
      dsimp only
      rw [world_term_alive h S L' c u, ← ind_avoidEv_mul_union d S Y ζ, ind_of_mem h]; ring
    · rw [hψ]
      dsimp only
      rw [world_term_dead h hdS L' hL' c hu, ind_of_not_mem h]
      have h0 : ind (avoidEv d (S ∪ Y)) ζ = 0 := ind_of_not_mem fun h' => h fun y hy => h' y (Or.inr hy)
      rw [h0]; ring
  -- Step 3: the dead part dies against the residual
  have step3 : ∑ ζ, weight w ζ * (resid w x Y g ζ * ((1 - ind (avoidEv d Y) ζ) * (- slForm L' c u))) = 0 := by
    have h := residual_orthogonal w hm x Y g
      (fun W => (1 - (if (d ∈ Y ∨ ∃ e ∈ W, d ∈ e) then (0 : ℝ) else 1)) * (- slForm L' c u))
    rw [← h]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    unfold resid
    rw [one_sub_ind_avoidEv_eq d Y ζ]; ring
  -- Step 4: the alive part, by linearity of `sl_{L'}` and the centred decoy moments
  have step4 : ∑ ζ, weight w ζ * (resid w x Y g ζ * (ind (avoidEv d (S ∪ Y)) ζ *
      slForm L' (fun w' => ind (openConn d w' : Set (BondConfig V)) ζ - c w') u)) = - (m₀⁻¹ * slForm L' Q u) := by
    have lin : ∀ ζ, slForm L' (fun w' => ind (openConn d w' : Set (BondConfig V)) ζ - c w') u =
        ∑ w', slForm L' (Pi.single w' (1 : ℝ)) u * (ind (openConn d w' : Set (BondConfig V)) ζ - c w') :=
      fun ζ => slForm_eq_sum_single L' _ u
    simp only [lin, Finset.mul_sum]
    rw [Finset.sum_comm]
    have inner : ∀ w', ∑ ζ, weight w ζ * (resid w x Y g ζ * (ind (avoidEv d (S ∪ Y)) ζ *
        (slForm L' (Pi.single w' (1 : ℝ)) u * (ind (openConn d w' : Set (BondConfig V)) ζ - c w')))) =
        slForm L' (Pi.single w' (1 : ℝ)) u * (- (m₀⁻¹ * Q w')) := by
      intro w'
      rw [← sum_resid_decoy_moment w hm x Y g d hA w' hm₀ (hc w'), Finset.mul_sum]
      exact Finset.sum_congr rfl fun ζ _ => by ring
    rw [Finset.sum_congr rfl (fun w' _ => inner w'), slForm_eq_sum_single L' Q u, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun w' _ => by ring
  -- combine
  rw [step1]
  have split : ∀ ζ, weight w ζ * (resid w x Y g ζ * ψ (ζ \ cut Y ζ)) =
      weight w ζ * (resid w x Y g ζ * (ind (avoidEv d (S ∪ Y)) ζ *
        slForm L' (fun w' => ind (openConn d w' : Set (BondConfig V)) ζ - c w') u)) +
      weight w ζ * (resid w x Y g ζ * ((1 - ind (avoidEv d Y) ζ) * (- slForm L' c u))) := by
    intro ζ; rw [step2 ζ]; ring
  rw [Finset.sum_congr rfl (fun ζ _ => split ζ), Finset.sum_add_distrib, step3, step4, add_zero]

end CSH

end Percolation.Continuity

end
