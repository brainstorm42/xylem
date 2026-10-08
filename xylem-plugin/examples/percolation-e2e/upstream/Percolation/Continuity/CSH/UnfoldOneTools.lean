import Percolation.Continuity.CSH.PhiMarkov
import Percolation.Continuity.HullPort.TAPv
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH: tools for Lemma U (reachability off a cut, the pointwise split of the level-1 form, world covariances, the Markov merge at `C_Y`)

Lemma U for k = 1, part 1 (tools).

Setting (sum level, `BHK2006.weight`): owner `x`, avoided set `Y`, ONE decoy `d`, observers `o, v` (all distinct), a functional `g`
of the open edge cluster of `x`; worlds = "delete the pairs meeting `Y ∪ V(C_Y(ω))`" (`HullPort.cut Y ω`); `D = {x ↮ Y}`,
`E = {d ↮ {x} ∪ Y}`.  For ARBITRARY real parameters `a, b_o, b_v, α, β` (in the application `a = μ(E)`, `b_u = μ(E, d↔u)`,
`α = μ(v↮{x,d}∪Y)`, `β = μ(v↮{x,d}∪Y, o↔v)`) put
`h = α·(a·1{x↔o} − b_o·1{x↔d}) − β·(a·1{x↔v} − b_v·1{x↔d})` (the polynomialised level-1 form).  LEMMA U (k = 1):

  `Σ_ω w 1_D(ω) Cov_{world(ω)}(g(C_x), h)
     = a·Σ_ω w 1_D(ω) [α·Cov_{world}(g(C_x), 1{o ↔ {x,d}}) − β·Cov_{world}(g(C_x), 1{v ↔ {x,d}})]        (H-part)
       + α·(a·P_o − b_o·P) − β·(a·P_v − b_v·P),                                                      (R̃-part)`
  `P_u = Σ_ζ w 1_E(ζ) 1{d↔u}(ζ) Φ(C_d(ζ))`, `P = Σ_ζ w 1_E(ζ) Φ(C_d(ζ))`, `Φ(K) = Σ_η w I_K(η)` (Lemma Φ's functional).

Ingredients: the pointwise split `a·1{x↔u} − b_u·1{x↔d} = a·1{u↔{x,d}} − b_u − 1{d↮x}(a·1{d↔u} − b_u)`; the Markov property at
`C_Y` (`HullPort.set_sum_cond_sdiff`) to merge the world double sum, the vanishing of the `C_Y`-measurable term against the residual
`g − ḡ`; the Markov property at `C_d` and Lemma Φ(a) (`CSH.sum_phiIntegrand_eq`).  With `CovTau.markerDominanceAvoid` (R̃-part ≥ 0, `Φ`
monotone by `CSH.phiFun_mono`) and the set-4PT + (Htw) for the H-part this gives the k = 1 case of CSH (put together separately).
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10); §1 display (10) (pp. 7–8) — corollaries]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical
open BHK2006 DecisionTree HullPort

namespace CSH

variable {V : Type*}

/-! ### Reachability bookkeeping off a cut -/

/-- The cut set of `{d}` is the set of pairs meeting the open vertex cluster of `d`. [folklore] -/
theorem cut_singleton_eq_edgesOf (d : V) (ω : Set (Sym2 V)) : cut {d} ω = edgesOf (openCluster ω d) := by
  ext e
  simp only [cut, edgesOf, openCluster, mem_setOf_eq, mem_singleton_iff, exists_eq_left]

/-- If no vertex of `X` is joined to `s`, deleting the cut set of `X` does not change the cluster of `s`. [folklore] -/
theorem openEdgeCluster_sdiff_cut_of_avoid {ω : Set (Sym2 V)} {X : Set V} {s : V} (h : ω ∈ avoidEv s X) :
    openEdgeCluster (ω \ cut X ω) s = openEdgeCluster ω s := by
  have hT : ∀ t ∈ ({s} : Set V), ¬ (t ∈ X ∨ ∃ e ∈ setCl ω X, t ∈ e) := by
    intro t ht; rw [mem_singleton_iff] at ht; subst ht
    exact (mem_avoidEv_iff_notMem_span t X ω).1 h
  have := setCl_eq_sdiff_barOf (rfl : setCl ω X = setCl ω X) hT
  rw [setCl_singleton, setCl_singleton, ← cut_eq_barOf] at this
  exact this.symm

/-- If no vertex of `X` is joined to `s`, deleting the cut set of `X` does not change the connections of `s`. [folklore] -/
theorem reachable_sdiff_cut_iff_of_avoid {ω : Set (Sym2 V)} {X : Set V} {s : V} (h : ω ∈ avoidEv s X) (t : V) :
    (openGraph (ω \ cut X ω)).Reachable s t ↔ (openGraph ω).Reachable s t := by
  rw [reachable_iff_exists_mem_openEdgeCluster, reachable_iff_exists_mem_openEdgeCluster,
    openEdgeCluster_sdiff_cut_of_avoid h]

/-- If some vertex of `X` is joined to `d`, then after deleting the cut set of `X` the vertex `d` is isolated: `d ↔ t` forces
`t = d`. [folklore] -/
theorem eq_of_reachable_sdiff_cut {ω : Set (Sym2 V)} {X : Set V} {d : V} (h : ω ∉ avoidEv d X) (η : Set (Sym2 V)) (t : V)
    (hdt : (openGraph (η \ cut X ω)).Reachable d t) : t = d := by
  have hy : ∃ y ∈ X, (openGraph ω).Reachable d y := by
    by_contra hc; exact h fun y hy hdy => hc ⟨y, hy, hdy⟩
  obtain ⟨y, hyX, hdy⟩ := hy
  have hiso : ∀ e ∈ η \ cut X ω, d ∉ e := fun e he hde => he.2 ⟨d, hde, y, hyX, hdy.symm⟩
  exact eq_of_reachable_of_isolated hiso t hdt

/-- The cut set of `Y` is unchanged by deleting the cut set of `{d}` when `d ↮ Y`. [folklore] -/
theorem cut_sdiff_cut_singleton_of_avoid {ζ : Set (Sym2 V)} {Y : Set V} {d : V} (h : ζ ∈ avoidEv d Y) :
    cut Y (ζ \ cut {d} ζ) = cut Y ζ := by
  ext e
  simp only [cut, mem_setOf_eq]
  constructor
  · rintro ⟨u, hue, y, hyY, hyu⟩
    exact ⟨u, hue, y, hyY, hyu.mono (SimpleGraph.fromEdgeSet_mono fun _ he => he.1)⟩
  · rintro ⟨u, hue, y, hyY, hyu⟩
    refine ⟨u, hue, y, hyY, ?_⟩
    have hdy : ¬ (openGraph ζ).Reachable d y := h y hyY
    exact (reachable_sdiff_cut_singleton_iff hdy u).2 hyu

/-! ### The pointwise split of the level-1 form -/

variable [Fintype V]

/-! ### World covariances -/

/-- The world covariance `Cov_{world(ω)}(φ, ψ) = ḡ(φψ) − ḡ(φ)ḡ(ψ)` (world = delete `cut Y ω`; sum level).
[folklore] -/
def wcovOff (w : Sym2 V → ℝ) (Y : Set V) (φ ψ : Set (Sym2 V) → ℝ) (ω : Set (Sym2 V)) : ℝ :=
  wmeanOff w Y (fun β => φ β * ψ β) ω - wmeanOff w Y φ ω * wmeanOff w Y ψ ω

/-- The world covariance as `Σ_η w (φ − ḡ(φ))·ψ`. [folklore] -/
theorem wcovOff_eq_sum (w : Sym2 V → ℝ) (Y : Set V) (φ ψ : Set (Sym2 V) → ℝ)
    (ω : Set (Sym2 V)) :
    wcovOff w Y φ ψ ω = ∑ η, weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * ψ (η \ cut Y ω)) := by
  have e : ∀ η, weight w η * ((φ (η \ cut Y ω) - wmeanOff w Y φ ω) * ψ (η \ cut Y ω)) =
      weight w η * (φ (η \ cut Y ω) * ψ (η \ cut Y ω)) - wmeanOff w Y φ ω * (weight w η * ψ (η \ cut Y ω)) := by
    intro η; ring
  rw [Finset.sum_congr rfl (fun η _ => e η), Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl

/-! ### Step C: merging the world double sum at `C_Y`, and the vanishing of `C_Y`-measurable terms -/

/-- **Markov merge at `C_Y`.** For any world test function `ψ`:
`Σ_ω w 1_D(ω) Σ_η w (g(C_x(η')) − ḡ(ω)) ψ(η') [η' = η ∖ cut_Y ω]  =  Σ_ζ w 1_D(ζ) (g(C_x ζ) − ḡ(ζ)) ψ(ζ ∖ cut_Y ζ)`
(`HullPort.set_sum_cond_sdiff` read backwards; on `D = {x ↮ Y}` the cluster of `x` off the cut is the cluster of `x`).
[cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) — corollary] -/
theorem markov_merge_Y (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (ψ : Set (Sym2 V) → ℝ) :
    ∑ ω, weight w ω * (ind (avoidEv x Y) ω *
        ∑ η, weight w η * ((g (openEdgeCluster (η \ cut Y ω) x) -
          wmeanOff w Y (fun β => g (openEdgeCluster β x)) ω) * ψ (η \ cut Y ω))) =
      ∑ ζ, weight w ζ * (ind (avoidEv x Y) ζ *
        ((g (openEdgeCluster ζ x) - wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ) * ψ (ζ \ cut Y ζ))) := by
  classical
  -- kernel: K(W, β) = 1{x ∉ Y ∪ V(W)} · (g(C_x β) − ḡ_W) · ψ(β), ḡ_W = Σ_η' w g(C_x(η' ∖ barOf Y W))
  set K : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun W β =>
    (if (x ∈ Y ∨ ∃ e ∈ W, x ∈ e) then 0 else 1) *
      ((g (openEdgeCluster β x) - ∑ η', weight w η' * g (openEdgeCluster (η' \ barOf Y W) x)) * ψ β) with hK
  have hind : ∀ ζ : Set (Sym2 V), ind (avoidEv x Y) ζ = (if (x ∈ Y ∨ ∃ e ∈ setCl ζ Y, x ∈ e) then 0 else 1) := by
    intro ζ
    by_cases h : (x ∈ Y ∨ ∃ e ∈ setCl ζ Y, x ∈ e)
    · rw [if_pos h, ind_of_not_mem (fun h' => (mem_avoidEv_iff_notMem_span x Y ζ).1 h' h)]
    · rw [if_neg h, ind_of_mem ((mem_avoidEv_iff_notMem_span x Y ζ).2 h)]
  have hmean : ∀ ζ : Set (Sym2 V), wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ =
      ∑ η', weight w η' * g (openEdgeCluster (η' \ barOf Y (setCl ζ Y)) x) := by
    intro ζ; rw [wmeanOff, cut_eq_barOf]
  have key := set_sum_cond_sdiff w hm Y K
  -- right-hand side of `key` is our left-hand side
  have hR : ∀ ω, weight w ω * ∑ η, weight w η * K (setCl ω Y) (η \ barOf Y (setCl ω Y)) =
      weight w ω * (ind (avoidEv x Y) ω * ∑ η, weight w η * ((g (openEdgeCluster (η \ cut Y ω) x) -
        wmeanOff w Y (fun β => g (openEdgeCluster β x)) ω) * ψ (η \ cut Y ω))) := by
    intro ω
    rw [hind, hmean, cut_eq_barOf]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun η _ => by simp only [hK]; ring
  -- left-hand side of `key` is our right-hand side (on `D` the cluster of `x` off the cut is the cluster of `x`)
  have hL : ∀ ζ, weight w ζ * K (setCl ζ Y) (ζ \ barOf Y (setCl ζ Y)) =
      weight w ζ * (ind (avoidEv x Y) ζ * ((g (openEdgeCluster ζ x) -
        wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ) * ψ (ζ \ cut Y ζ))) := by
    intro ζ
    simp only [hK]
    rw [hind, hmean, cut_eq_barOf]
    by_cases h : (x ∈ Y ∨ ∃ e ∈ setCl ζ Y, x ∈ e)
    · simp only [if_pos h, zero_mul, mul_zero]
    · have hζ : ζ ∈ avoidEv x Y := (mem_avoidEv_iff_notMem_span x Y ζ).2 h
      have hco := openEdgeCluster_sdiff_cut_of_avoid hζ
      rw [cut_eq_barOf] at hco
      rw [if_neg h, hco]
  calc _ = ∑ ω, weight w ω * ∑ η, weight w η * K (setCl ω Y) (η \ barOf Y (setCl ω Y)) :=
        Finset.sum_congr rfl fun ω _ => (hR ω).symm
    _ = ∑ ζ, weight w ζ * K (setCl ζ Y) (ζ \ barOf Y (setCl ζ Y)) := key.symm
    _ = _ := Finset.sum_congr rfl fun ζ _ => hL ζ

/-- **`C_Y`-measurable terms vanish against the residual**: for any function `κ` of the cluster of `Y`,
`Σ_ζ w 1_D(ζ) κ(C_Y ζ) (g(C_x ζ) − ḡ(ζ)) = 0`. [cite: VandenbergHaggstromKahn2005, §2.1 Lemma 2.4 (p. 10) — corollary] -/
theorem residual_orthogonal (w : Sym2 V → ℝ) (hm : ∑ ω, weight w ω = 1) (x : V) (Y : Set V) (g : Set (Sym2 V) → ℝ)
    (κ : Set (Sym2 V) → ℝ) :
    ∑ ζ, weight w ζ * (ind (avoidEv x Y) ζ * (κ (setCl ζ Y) *
      (g (openEdgeCluster ζ x) - wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ))) = 0 := by
  classical
  -- kernel with the extra factor κ(C_Y)
  set K : Set (Sym2 V) → Set (Sym2 V) → ℝ := fun W β =>
    (if (x ∈ Y ∨ ∃ e ∈ W, x ∈ e) then 0 else 1) * (κ W *
      (g (openEdgeCluster β x) - ∑ η', weight w η' * g (openEdgeCluster (η' \ barOf Y W) x))) with hK
  have hind : ∀ ζ : Set (Sym2 V), ind (avoidEv x Y) ζ = (if (x ∈ Y ∨ ∃ e ∈ setCl ζ Y, x ∈ e) then 0 else 1) := by
    intro ζ
    by_cases h : (x ∈ Y ∨ ∃ e ∈ setCl ζ Y, x ∈ e)
    · rw [if_pos h, ind_of_not_mem (fun h' => (mem_avoidEv_iff_notMem_span x Y ζ).1 h' h)]
    · rw [if_neg h, ind_of_mem ((mem_avoidEv_iff_notMem_span x Y ζ).2 h)]
  have hmean : ∀ ζ : Set (Sym2 V), wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ =
      ∑ η', weight w η' * g (openEdgeCluster (η' \ barOf Y (setCl ζ Y)) x) := by
    intro ζ; rw [wmeanOff, cut_eq_barOf]
  have key := set_sum_cond_sdiff w hm Y K
  have hL : ∀ ζ, weight w ζ * K (setCl ζ Y) (ζ \ barOf Y (setCl ζ Y)) =
      weight w ζ * (ind (avoidEv x Y) ζ * (κ (setCl ζ Y) *
        (g (openEdgeCluster ζ x) - wmeanOff w Y (fun β => g (openEdgeCluster β x)) ζ))) := by
    intro ζ
    simp only [hK]
    rw [hind, hmean]
    by_cases h' : (x ∈ Y ∨ ∃ e ∈ setCl ζ Y, x ∈ e)
    · simp only [if_pos h', zero_mul, mul_zero]
    · have hζ : ζ ∈ avoidEv x Y := (mem_avoidEv_iff_notMem_span x Y ζ).2 h'
      have hco := openEdgeCluster_sdiff_cut_of_avoid hζ
      rw [cut_eq_barOf] at hco
      rw [if_neg h', hco]
  have hR : ∀ ω, weight w ω * ∑ η, weight w η * K (setCl ω Y) (η \ barOf Y (setCl ω Y)) = 0 := by
    intro ω
    have e : ∀ η, weight w η * K (setCl ω Y) (η \ barOf Y (setCl ω Y)) =
        ((if (x ∈ Y ∨ ∃ e ∈ setCl ω Y, x ∈ e) then 0 else 1) * κ (setCl ω Y)) *
            (weight w η * g (openEdgeCluster (η \ barOf Y (setCl ω Y)) x)) -
          ((if (x ∈ Y ∨ ∃ e ∈ setCl ω Y, x ∈ e) then 0 else 1) * κ (setCl ω Y) *
            ∑ η', weight w η' * g (openEdgeCluster (η' \ barOf Y (setCl ω Y)) x)) * weight w η := by
      intro η; simp only [hK]; ring
    rw [Finset.sum_congr rfl (fun η _ => e η), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hm]
    ring
  calc _ = ∑ ζ, weight w ζ * K (setCl ζ Y) (ζ \ barOf Y (setCl ζ Y)) :=
        Finset.sum_congr rfl fun ζ _ => (hL ζ).symm
    _ = ∑ ω, weight w ω * ∑ η, weight w η * K (setCl ω Y) (η \ barOf Y (setCl ω Y)) := key
    _ = 0 := Finset.sum_eq_zero fun ω _ => hR ω

end CSH

end Percolation.Continuity
