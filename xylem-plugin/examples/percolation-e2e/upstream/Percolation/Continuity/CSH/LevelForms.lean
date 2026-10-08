import Percolation.Continuity.CSH.Defs
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy CSH: algebra of the level forms for GENERAL `k` (coefficient representation, sub-system lists, and the pointwise unfolding identity of Lemma U)

General `k`, pointwise part ((S5)_r for every `r` from the conditioned slack
hierarchy; Theorem 1 = `CSH.CSHHolds` for all data).  Everything here is ALGEBRA over the level forms
`CSH.slForm` / `CSH.cshMarg` of `Continuity/CSH/Defs.lean` — no measure theory:

* `CSH.slForm_eq_sum_single`, `CSH.cshMarg_eq_sum_single` — on a finite vertex type the level form and the margin are finite linear combinations
  `Marg[f] = Σ_u Λ(u)·f(u)` with `Λ(u) = Marg[δ_u]` (the shape of the multi-marker Lemma T `BHK2006_multiMarkerCov_nonneg_of_within`);
  `CSH.slForm_congr` — `sl_L[f](u)` only reads `f` at `u` and at the decoys.
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)] [cite: KozmaNitzan2024, Conj. 1 (p. 3)]
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

namespace CSH

variable {V : Type*}

/-! ### The level form only reads `f` at the argument and at the decoys -/

/-- `sl_L[f](u)` depends on `f` only through `f(u)` and the values `f(d)` at the decoys of `L`. [folklore] -/
theorem slForm_congr (L : List (V × (V → ℝ))) {f g : V → ℝ} {u : V} (hu : f u = g u)
    (hd : ∀ dc ∈ L, f dc.1 = g dc.1) : slForm L f u = slForm L g u := by
  induction L generalizing f g u with
  | nil => simpa using hu
  | cons dc L ih =>
      simp only [slForm_cons_eq]
      refine ih ?_ fun dc' hdc' => ?_
      · simp only [slStep, hu, hd dc (List.mem_cons_self)]
      · simp only [slStep, hd dc' (List.mem_cons_of_mem _ hdc'), hd dc (List.mem_cons_self)]

/-! ### Finite linear combinations -/

/-- `sl_L` commutes with finite sums. [folklore] -/
theorem slForm_finset_sum {ι : Type*} (L : List (V × (V → ℝ))) (s : Finset ι) (g : ι → V → ℝ) :
    slForm L (∑ i ∈ s, g i) = ∑ i ∈ s, slForm L (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [slForm_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, slForm_add, ih]

section Fin

variable [Fintype V]

/-- A function on a finite type is the combination of the unit vectors: `f = Σ_w f(w)·δ_w`. [folklore] -/
theorem eq_sum_smul_single (f : V → ℝ) : f = ∑ w, f w • (Pi.single w (1 : ℝ) : V → ℝ) := by
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single u (fun w _ hw => by simp [Ne.symm hw]) (fun h => absurd (Finset.mem_univ u) h)]
  simp

/-- **Coefficient representation of the level form**: `sl_L[f](u) = Σ_w sl_L[δ_w](u)·f(w)`. [folklore] -/
theorem slForm_eq_sum_single (L : List (V × (V → ℝ))) (f : V → ℝ) (u : V) :
    slForm L f u = ∑ w, slForm L (Pi.single w (1 : ℝ)) u * f w := by
  conv_lhs => rw [eq_sum_smul_single f]
  rw [slForm_finset_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun w _ => by rw [slForm_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Coefficient representation of the margin**: `Marg[f] = Σ_u Λ(u)·f(u)` with `Λ(u) = Marg[δ_u]` — the margin is a fixed finite
linear combination of the values of `f` (the shape consumed by the multi-marker reduction `BHK2006_multiMarkerCov_nonneg_of_within`).
[folklore] -/
theorem cshMarg_eq_sum_single (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f : V → ℝ) :
    cshMarg L p o v f = ∑ u, cshMarg L p o v (Pi.single u (1 : ℝ)) * f u := by
  simp only [cshMarg, slForm_eq_sum_single L f, sub_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => by ring

end Fin

/-! ### The sub-system lists -/

/-- The decoys of `decoyList w A D` are `D`. [folklore] -/
theorem map_fst_decoyList (w : Sym2 V → unitInterval) (A : Set V) (D : List V) :
    (decoyList w A D).map Prod.fst = D := by
  induction D generalizing A with
  | nil => rfl
  | cons d ds ih => simp [decoyList, ih]

/-! ### The pointwise unfolding identity -/

section Unfold

variable (R : V → V → Prop)

/-- `χ_d(u) = 1{u R d}` (in the application: `1{u ∈ C_d}` in the world). [folklore] -/
def chi (u d : V) : ℝ := if R u d then 1 else 0

/-- `J_S(u) = 1{∃ s ∈ S, u R s}` (`1{u ↔ S}` in the world). [folklore] -/
def jn (S : Set V) (u : V) : ℝ := if ∃ s ∈ S, R u s then 1 else 0

/-- `ε_S(d) = 1{∀ s ∈ S, ¬ d R s}` (`1{d ↮ S}` in the world: the indicator of the event `E_j`). [folklore] -/
def av (S : Set V) (d : V) : ℝ := if ∀ s ∈ S, ¬ R d s then 1 else 0

/-- The unfolded terms `Σ_j 1{E_j}·M^{(j,k)}_u`, as a recursion along the decoy list with a growing source set:
`unfoldT_S([]) = 0`, `unfoldT_S((d,c)::L') = ε_S(d)·sl_{L'}[χ_d − c] + unfoldT_{S∪{d}}(L')`.
[folklore] -/
def unfoldT : Set V → List (V × (V → ℝ)) → V → ℝ
  | _, [] => fun _ => 0
  | S, (d, c) :: L' => fun u => av R S d * slForm L' (fun w => chi R w d - c w) u + unfoldT (insert d S) L' u

/-- The CONFIGURATION-FREE remainder of the unfolding (depends on the constants only): `unfoldK([]) = 0`,
`unfoldK((d,c)::L') = unfoldK(L') − sl_{L'}[c]`. [folklore] -/
def unfoldK : List (V × (V → ℝ)) → V → ℝ
  | [] => fun _ => 0
  | (_, c) :: L' => fun u => unfoldK L' u - slForm L' c u

/-- `J_S(d) = 1 − ε_S(d)`. [folklore] -/
theorem jn_eq_one_sub_av (S : Set V) (d : V) : jn R S d = 1 - av R S d := by
  unfold jn av
  by_cases h : ∃ s ∈ S, R d s
  · rw [if_pos h, if_neg (fun h' => by obtain ⟨s, hs, hds⟩ := h; exact h' s hs hds)]; ring
  · rw [if_neg h, if_pos (fun s hs hds => h ⟨s, hs, hds⟩)]; ring

/-- The disjoint split `1{u ↔ S ∪ {d}} = 1{u ↔ S} + 1{u R d}·1{d ↮ S}` (symmetry + transitivity of `R`). [folklore] -/
theorem jn_insert (hRs : ∀ a b, R a b → R b a) (hRt : ∀ a b c, R a b → R b c → R a c) (S : Set V) (d u : V) :
    jn R (insert d S) u = jn R S u + chi R u d * av R S d := by
  unfold jn chi av
  by_cases h1 : ∃ s ∈ S, R u s
  · obtain ⟨s, hs, hus⟩ := h1
    rw [if_pos ⟨s, Set.mem_insert_of_mem _ hs, hus⟩, if_pos ⟨s, hs, hus⟩]
    by_cases h2 : R u d
    · rw [if_pos h2, if_neg (fun h' => h' s hs (hRt d u s (hRs u d h2) hus))]; ring
    · rw [if_neg h2]; ring
  · rw [if_neg h1]
    by_cases h2 : R u d
    · rw [if_pos ⟨d, Set.mem_insert _ _, h2⟩, if_pos h2,
        if_pos (fun s hs hds => h1 ⟨s, hs, hRt u d s h2 hds⟩)]
      ring
    · rw [if_neg h2, if_neg (by
        rintro ⟨s, hs, hus⟩
        rcases Set.mem_insert_iff.1 hs with rfl | hs
        · exact h2 hus
        · exact h1 ⟨s, hs, hus⟩)]
      ring

/-- **One level step on `J_S`**: `J_S(u) − c(u)·J_S(d) = J_{S∪{d}}(u) − c(u) − ε_S(d)·(χ_d(u) − c(u))`.
[folklore] -/
theorem slStep_jn (hRs : ∀ a b, R a b → R b a) (hRt : ∀ a b c, R a b → R b c → R a c) (S : Set V) (d : V) (c : V → ℝ) :
    slStep (d, c) (jn R S) = jn R (insert d S) - c - av R S d • (fun w => chi R w d - c w) := by
  funext u
  simp only [slStep, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [jn_insert R hRs hRt S d u, jn_eq_one_sub_av R S d]
  ring

/-- **THE POINTWISE CLAIM OF LEMMA U**: for a symmetric transitive relation `R`,
`sl_L[J_S](u) = J_{S ∪ decoys(L)}(u) − unfoldT_S(L)(u) + unfoldK(L)(u)`.
[folklore] -/
theorem slForm_jn (hRs : ∀ a b, R a b → R b a) (hRt : ∀ a b c, R a b → R b c → R a c) (L : List (V × (V → ℝ))) (S : Set V) (u : V) :
    slForm L (jn R S) u = jn R (S ∪ {d | d ∈ L.map Prod.fst}) u - unfoldT R S L u + unfoldK L u := by
  induction L generalizing S u with
  | nil => simp [unfoldT, unfoldK]
  | cons dc L ih =>
      obtain ⟨d, c⟩ := dc
      rw [slForm_cons_eq, slStep_jn R hRs hRt S d c, slForm_sub, slForm_sub, slForm_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ih (insert d S) u, unfoldT, unfoldK]
      have hset : insert d S ∪ {d' | d' ∈ L.map Prod.fst} = S ∪ {d' | d' ∈ ((d, c) :: L).map Prod.fst} := by
        ext a
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq, List.map_cons, List.mem_cons]
        tauto
      rw [hset]
      ring

/-- At the owner: `J_{{x}} = χ_x`, so the CLAIM unfolds `sl_L[χ_x] = L^k`. [folklore] -/
theorem jn_singleton (x u : V) : jn R {x} u = chi R u x := by
  unfold jn chi
  simp only [Set.mem_singleton_iff, exists_eq_left]

end Unfold

end CSH

end Percolation.Continuity

end
