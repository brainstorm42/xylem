import Percolation.Literature.ConstrainedClusters
import Percolation.Literature.GrimmettMarstrand
import Percolation.Literature.KozmaNitzanSteps
import Percolation.Literature.LatticeModels.ThermodynamicLimit
import Percolation.Literature.SlabCriticalityInputs
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 — the run of the exploration process: (29), (31), (32) and lawfulness

Twelfth proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, arXiv:2401.12397, §4 pp. 26–29): along the run of
the exploration process (`KSch.scheme`, `KozmaNitzanScheme.lean`) on a configuration `ω`, the explored
edges `F`, region `E_i = V` and pattern `ξ` evolve as KN describe ("declare `E_{i+1} = E_i ∪ E_{w,v} ∪
⋃_x H^{j_x}_{v,x}`", p. 27), and every history at which a macro-edge is chosen is VALID
(`KSch.valid_of_choice`): (29) and the cover property follow from the static geometry
(`KozmaNitzanSteps.lean`), and the estimate (32) is proved as on p. 28 — for `w ≠ 0` from the
success (30) of the examination of `w` (provenance from the driver, `exists_probe_of_det`) by Step I
((31): nothing explored later meets `E_{w,v}`), for `w = 0` from the wired cube `Q_0` (hypothesis
`hQ0`, the "definition of `m₂`", discharged from hittability in `KozmaNitzanTheorem6.lean`).
Consequently the scheme is LAWFUL (`KSch.lawful`) once the failure bound (33) is supplied (hypothesis
`hfail`, = `fail_bound` of `KozmaNitzanSteps.lean` at the chosen constants).

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 pp. 26–29 ((29)–(32), Step I).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem ProbeHistory Contour HSiteScheme

namespace KozmaNitzan

variable {d : ℕ}

/-- A vertex of the span of the lattice edges inside `X` has a lattice neighbour in `X`. [folklore] -/
theorem exists_adj_of_mem_span_edgesIn {X : Finset (Site d)} {y : Site d} (hy : y ∈ span (edgesIn (zdGraph d) X)) :
    ∃ z ∈ X, (zdGraph d).Adj y z := by
  obtain ⟨e, he, hye⟩ := mem_span_iff.1 hy
  revert he hye
  refine Sym2.ind (fun a b => ?_) e
  intro he hye
  rw [mem_edgesIn_iff] at he
  have hadj : (zdGraph d).Adj a b := (SimpleGraph.mem_edgeSet _).1 he.1
  rcases Sym2.mem_iff.1 hye with rfl | rfl
  · exact ⟨b, he.2 b (Sym2.mem_mk_right _ _), hadj⟩
  · exact ⟨a, he.2 a (Sym2.mem_mk_left _ _), hadj.symm⟩

namespace KSch

open Cells

variable (S : KSch d)

/-! ## Unfolding the scheme -/

/-- The explorer of the scheme is `nextProbe`. [folklore] -/
theorem scheme_next : S.scheme.E.next = S.nextProbe := rfl

/-- The history of the run after `n` steps. [folklore] -/
abbrev hst (ω : BondConfig (Site d)) (n : ℕ) : ProbeHistory (Site d) := S.scheme.E.hist n ω

/-- **The three cases of a step**: no probe, or a valid history with a chosen edge, examined by the probe.
[folklore] -/
theorem next_cases (ω : BondConfig (Site d)) (n : ℕ) :
    S.scheme.E.next (S.hst ω n) = none ∨
      ∃ e, (S.scheme.stN n ω).choice = some e ∧ S.Valid (S.hst ω n) e ∧ S.scheme.E.next (S.hst ω n) = some (S.probe (S.hst ω n) e) := by
  rw [scheme_next]
  cases hP : S.nextProbe (S.hst ω n) with
  | none => exact Or.inl rfl
  | some P =>
    obtain ⟨e, hc, hV, rfl⟩ := S.nextProbe_eq_some hP
    exact Or.inr ⟨e, hc, hV, rfl⟩

/-- If a probe is made then it is the examination of the chosen edge after a valid history. [folklore] -/
theorem of_next_some {ω : BondConfig (Site d)} {n : ℕ} {P : AProbe (Site d)} (hP : S.scheme.E.next (S.hst ω n) = some P) :
    ∃ e, (S.scheme.stN n ω).choice = some e ∧ S.Valid (S.hst ω n) e ∧ P = S.probe (S.hst ω n) e := by
  rw [scheme_next] at hP
  exact S.nextProbe_eq_some hP

/-! ## The evolution of `F`, `V`, `ξ` -/

/-- `U₀ ⊆ F`. [folklore] -/
theorem U₀_subset_F (h : ProbeHistory (Site d)) : S.U₀ ⊆ S.F h := Finset.subset_union_left

/-- A `none` step leaves `F` unchanged. [folklore] -/
theorem F_cons_none (h : ProbeHistory (Site d)) : S.F (none :: h) = S.F h := by
  unfold F; rw [supp_cons_none]

/-- A probe adds its examined edges to `F`. [folklore] -/
theorem F_cons_some (r : ProbeRecord (Site d)) (h : ProbeHistory (Site d)) : S.F (some r :: h) = S.F h ∪ r.1 := by
  unfold F; rw [supp_cons_some]
  ext x; simp only [Finset.mem_union]; tauto

/-- A `none` step leaves `ξ` unchanged. [folklore] -/
theorem ξ_cons_none (h : ProbeHistory (Site d)) : S.ξ (none :: h) = S.ξ h := by
  unfold ξ; rw [opens_cons_none]

/-- A probe adds its observation to `ξ`. [folklore] -/
theorem ξ_cons_some (r : ProbeRecord (Site d)) (h : ProbeHistory (Site d)) : S.ξ (some r :: h) = S.ξ h ∪ r.2 := by
  unfold ξ; rw [opens_cons_some]
  ext x; simp only [Finset.mem_union]; tauto

/-- `F` only grows along a history. [folklore] -/
theorem F_subset_cons (s : Option (ProbeRecord (Site d))) (h : ProbeHistory (Site d)) : S.F h ⊆ S.F (s :: h) :=
  Finset.union_subset_union le_rfl (supp_subset_cons s h)

/-- `F` only grows along the run. [folklore] -/
theorem F_mono (ω : BondConfig (Site d)) : Monotone fun n => S.F (S.hst ω n) := by
  refine monotone_nat_of_le_succ fun n => ?_
  show S.F (S.hst ω n) ⊆ S.F (S.hst ω (n + 1))
  exact S.F_subset_cons _ _

/-- `V` only grows along the run. [folklore] -/
theorem V_mono (ω : BondConfig (Site d)) : Monotone fun n => S.V (S.hst ω n) := fun _ _ hmn =>
  span_mono (S.F_mono ω hmn)

/-- No probe: `F`, `ξ` and the macro-state are unchanged. [folklore] -/
theorem step_none {ω : BondConfig (Site d)} {n : ℕ} (hD : S.scheme.E.next (S.hst ω n) = none) :
    S.F (S.hst ω (n + 1)) = S.F (S.hst ω n) ∧ S.ξ (S.hst ω (n + 1)) = S.ξ (S.hst ω n) ∧
      S.scheme.stN (n + 1) ω = S.scheme.stN n ω := by
  have h1 : S.hst ω (n + 1) = none :: S.hst ω n := by
    show S.scheme.E.hist (n + 1) ω = _
    rw [AExplorer.hist_succ, S.scheme.E.step_of_none hD]
  rw [h1, F_cons_none, ξ_cons_none]
  exact ⟨rfl, rfl, S.scheme.stN_succ_of_next_none hD⟩

/-- A probe along `e`: `F` gains the revealed edges, `ξ` the observed ones, and the macro-state is
updated by the success of the examination. [cite: KozmaNitzan2024, §4 p. 27 (E_{i+1}, G_{i+1}, X_{i+1})] -/
theorem step_some {ω : BondConfig (Site d)} {n : ℕ} {e : Site 2 × MDir} (hc : (S.scheme.stN n ω).choice = some e)
    (hD : S.scheme.E.next (S.hst ω n) = some (S.probe (S.hst ω n) e)) :
    S.F (S.hst ω (n + 1)) = S.F (S.hst ω n) ∪ S.revealOf (S.hst ω n) e (obs ω (S.env (S.hst ω n) e)) ∧
      S.ξ (S.hst ω (n + 1)) = S.ξ (S.hst ω n) ∪ obs ω (S.revealOf (S.hst ω n) e (obs ω (S.env (S.hst ω n) e))) ∧
      S.scheme.stN (n + 1) ω = (S.scheme.stN n ω).update e (S.succ (S.hst ω n) e ((S.probe (S.hst ω n) e).read ω)) := by
  have h1 : S.hst ω (n + 1) = some ((S.probe (S.hst ω n) e).record ω) :: S.hst ω n := by
    show S.scheme.E.hist (n + 1) ω = _
    rw [AExplorer.hist_succ, S.scheme.E.step_of_some hD]
  refine ⟨by rw [h1, F_cons_some]; rfl, by rw [h1, ξ_cons_some]; rfl, ?_⟩
  rw [S.scheme.stN_succ_of_next_some hD, hc]
  rfl

/-! ## The new region is covered by its own lattice edges -/

/-- Every vertex of the new region has a lattice neighbour in it. [folklore] -/
theorem exists_adj_of_mem_newRegion (h : ProbeHistory (Site d)) (e : Site 2 × MDir) (o : Finset (Sym2 (Site d)))
    {y : Site d} (hy : y ∈ S.newRegion h e o) : ∃ z ∈ S.newRegion h e o, (zdGraph d).Adj y z := by
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  have hd : 0 < d := by have := S.C.hd; omega
  rcases Finset.mem_union.1 hy with hy | hy
  · rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨z, hz, hadj⟩ := S.C.exists_adj_of_mem_sBox (by linarith) hy
      exact ⟨z, Finset.mem_union_left _ (Finset.mem_union_left _ hz), hadj⟩
    · obtain ⟨z, hz, hadj⟩ := exists_adj_of_mem_cIcc hd (by have := S.C.r_pos; omega) hy
      exact ⟨z, Finset.mem_union_left _ (Finset.mem_union_right _ hz), hadj⟩
  · obtain ⟨du, hdu, hy⟩ := Finset.mem_biUnion.1 hy
    obtain ⟨z, hz, hadj⟩ := S.C.exists_adj_of_mem_sBox (by linarith) hy
    exact ⟨z, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨du, hdu, hz⟩), hadj⟩

/-- Every vertex of `Q_0` has a lattice neighbour in it. [folklore] -/
theorem exists_adj_of_mem_Q (v : Site 2) {y : Site d} (hy : y ∈ S.C.Q v) : ∃ z ∈ S.C.Q v, (zdGraph d).Adj y z :=
  exists_adj_of_mem_cIcc (by have := S.C.hd; omega) (by have := S.C.r_pos; omega) hy

/-- `V` of the empty history is `Q_0`. [cite: KozmaNitzan2024, §4 p. 27 (E₁ = Q_{(0,0)})] -/
theorem V_nil : S.V [] = S.C.Q 0 := by
  unfold V F U₀
  rw [supp_nil, Finset.union_empty]
  exact span_edgesIn_eq fun y hy => S.exists_adj_of_mem_Q 0 hy

/-! ## The run invariant -/

/-- **The invariant of the run after `n` steps**: the explored edges are the lattice edges inside the
explored region; the recorded pattern is `ω` on the explored edges, with `U₀` recorded open; the
explored region consists of `Q_0` and the new regions of the probes made; the cube of every
determined macro-vertex is explored ((29)). [cite: KozmaNitzan2024, §4 pp. 26–27 ((29), E_{i+1})] -/
structure RunInv (ω : BondConfig (Site d)) (n : ℕ) : Prop where
  F_eq : S.F (S.hst ω n) = edgesIn (zdGraph d) (S.V (S.hst ω n))
  ξ_iff : ∀ x, x ∈ S.ξ (S.hst ω n) ↔ x ∈ S.F (S.hst ω n) ∧ (x ∈ ω ∨ x ∈ S.U₀)
  V_cases : ∀ y ∈ S.V (S.hst ω n), y ∈ S.C.Q 0 ∨ ∃ m < n, ∃ e, (S.scheme.stN m ω).choice = some e ∧
    S.Valid (S.hst ω m) e ∧ S.scheme.E.next (S.hst ω m) = some (S.probe (S.hst ω m) e) ∧
    y ∈ S.newRegion (S.hst ω m) e (obs ω (S.env (S.hst ω m) e))
  det_Q : ∀ x, (S.scheme.stN n ω).Det x → S.C.Q x ⊆ S.V (S.hst ω n)

/-- The step of the explored region at a probe: `E_{i+1} = E_i ∪ E_{w,v} ∪ ⋃_x H^{j_x}_{v,x}`, and the
explored edges stay the lattice edges inside. [cite: KozmaNitzan2024, §4 p. 27 (E_{i+1})] -/
theorem V_step {ω : BondConfig (Site d)} {n : ℕ} (hI : S.RunInv ω n) {e : Site 2 × MDir}
    (hc : (S.scheme.stN n ω).choice = some e) (hD : S.scheme.E.next (S.hst ω n) = some (S.probe (S.hst ω n) e)) :
    S.F (S.hst ω (n + 1)) = edgesIn (zdGraph d) (S.V (S.hst ω n) ∪ S.newRegion (S.hst ω n) e (obs ω (S.env (S.hst ω n) e))) ∧
      S.V (S.hst ω (n + 1)) = S.V (S.hst ω n) ∪ S.newRegion (S.hst ω n) e (obs ω (S.env (S.hst ω n) e)) := by
  obtain ⟨hF, -, -⟩ := S.step_some hc hD
  have hF' : S.F (S.hst ω (n + 1)) =
      edgesIn (zdGraph d) (S.V (S.hst ω n) ∪ S.newRegion (S.hst ω n) e (obs ω (S.env (S.hst ω n) e))) := by
    rw [hF, revealOf, Finset.union_sdiff_self_eq_union]
    refine Finset.union_eq_right.2 ?_
    rw [hI.F_eq]
    intro x hx
    rw [mem_edgesIn_iff] at hx ⊢
    exact ⟨hx.1, fun y hy => Finset.mem_union_left _ (hx.2 y hy)⟩
  refine ⟨hF', ?_⟩
  show span (S.F (S.hst ω (n + 1))) = _
  rw [hF']
  refine span_edgesIn_eq fun y hy => ?_
  rcases Finset.mem_union.1 hy with hy | hy
  · have hy' : y ∈ span (edgesIn (zdGraph d) (S.V (S.hst ω n))) := by
      rw [← hI.F_eq]; exact hy
    obtain ⟨z, hz, hadj⟩ := exists_adj_of_mem_span_edgesIn hy'
    exact ⟨z, Finset.mem_union_left _ hz, hadj⟩
  · obtain ⟨z, hz, hadj⟩ := S.exists_adj_of_mem_newRegion _ _ _ hy
    exact ⟨z, Finset.mem_union_right _ hz, hadj⟩

/-- **The invariant holds along the run.** [cite: KozmaNitzan2024, §4 pp. 26–27] -/
theorem runInv (ω : BondConfig (Site d)) : ∀ n, S.RunInv ω n
  | 0 => by
    have hV : S.V (S.hst ω 0) = S.C.Q 0 := S.V_nil
    have hF : S.F (S.hst ω 0) = S.U₀ := by
      show S.F [] = S.U₀
      unfold F; rw [supp_nil, Finset.union_empty]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hV, hF]; rfl
    · intro x
      have hξ : S.ξ (S.hst ω 0) = S.U₀ := by
        show S.ξ [] = S.U₀
        unfold ξ; rw [opens_nil, Finset.union_empty]
      rw [hξ, hF]; tauto
    · intro y hy; rw [hV] at hy; exact Or.inl hy
    · intro x hx
      have hx' : x = 0 := by
        rcases hx with hx | hx
        · simpa [HSiteScheme.stN, HSiteScheme.mst, HState.start] using hx
        · simp [HSiteScheme.stN, HSiteScheme.mst, HState.start] at hx
      rw [hx', hV]
  | n + 1 => by
    have hI := runInv ω n
    rcases S.next_cases ω n with hD | ⟨e, hc, hV, hD⟩
    · obtain ⟨hF, hξ, hst⟩ := S.step_none hD
      have hVV : S.V (S.hst ω (n + 1)) = S.V (S.hst ω n) := by
        show span _ = span _; rw [hF]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hF, hVV]; exact hI.F_eq
      · intro x; rw [hξ, hF]; exact hI.ξ_iff x
      · intro y hy
        rw [hVV] at hy
        rcases hI.V_cases y hy with h | ⟨m, hm, rest⟩
        · exact Or.inl h
        · exact Or.inr ⟨m, by omega, rest⟩
      · intro x hx
        rw [hst] at hx; rw [hVV]; exact hI.det_Q x hx
    · obtain ⟨hF1, hξ1, hst⟩ := S.step_some hc hD
      obtain ⟨hF2, hV2⟩ := S.V_step hI hc hD
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hF2, hV2]
      · intro x
        rw [hξ1, hF1, Finset.mem_union, Finset.mem_union, mem_obs_iff, hI.ξ_iff x]
        constructor
        · rintro (⟨hxF, h'⟩ | ⟨hxr, hxω⟩)
          · exact ⟨Or.inl hxF, h'⟩
          · exact ⟨Or.inr hxr, Or.inl hxω⟩
        · rintro ⟨hxF | hxr, h'⟩
          · exact Or.inl ⟨hxF, h'⟩
          · by_cases hxF : x ∈ S.F (S.hst ω n)
            · exact Or.inl ⟨hxF, h'⟩
            · rcases h' with h' | h'
              · exact Or.inr ⟨hxr, h'⟩
              · exact absurd (S.U₀_subset_F _ h') hxF
      · intro y hy
        rw [hV2] at hy
        rcases Finset.mem_union.1 hy with hy | hy
        · rcases hI.V_cases y hy with h | ⟨m, hm, rest⟩
          · exact Or.inl h
          · exact Or.inr ⟨m, by omega, rest⟩
        · exact Or.inr ⟨n, Nat.lt_succ_self n, e, hc, hV, hD, hy⟩
      · intro x hx
        rw [hst] at hx
        rw [hV2]
        rcases (HState.det_update_iff _ _ _).1 hx with rfl | hx
        · intro y hy
          refine Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
          exact hy
        · exact (hI.det_Q x hx).trans Finset.subset_union_left

/-! ## Consequences of the invariant -/

section Consequences

variable {S}
variable {ω : BondConfig (Site d)}

/-- `0 ∈ V`. [folklore] -/
theorem zero_mem_V (n : ℕ) : (0 : Site d) ∈ S.V (S.hst ω n) := by
  have h0 : (0 : Site d) ∈ S.V (S.hst ω 0) := by
    show (0 : Site d) ∈ S.V []
    rw [S.V_nil, Cells.Q, ← S.C.cen_zero]
    exact center_mem_cIcc _ _
  exact S.V_mono ω (Nat.zero_le n) h0

/-- The origin is always occupied. [folklore] -/
theorem zero_mem_occ (n : ℕ) : (0 : Site 2) ∈ (S.scheme.stN n ω).occ :=
  (S.scheme.inv_mst _).zero_mem

/-- A determined macro-vertex has its centre explored. [cite: KozmaNitzan2024, §4 p. 26 ((29))] -/
theorem cen_mem_V_of_det {n : ℕ} {x : Site 2} (hx : (S.scheme.stN n ω).Det x) : S.C.cen x ∈ S.V (S.hst ω n) :=
  (S.runInv ω n).det_Q x hx (center_mem_cIcc _ _)

/-- The new region of a probe lies in the explored region afterwards. [cite: KozmaNitzan2024, §4 p. 27 (E_{i+1})] -/
theorem newRegion_subset_V {m n : ℕ} (hmn : m < n) {e : Site 2 × MDir} (hc : (S.scheme.stN m ω).choice = some e)
    (hD : S.scheme.E.next (S.hst ω m) = some (S.probe (S.hst ω m) e)) :
    S.newRegion (S.hst ω m) e (obs ω (S.env (S.hst ω m) e)) ⊆ S.V (S.hst ω n) := by
  have h1 := (S.V_step (S.runInv ω m) hc hD).2
  intro y hy
  refine S.V_mono ω (Nat.succ_le_of_lt hmn) ?_
  show y ∈ S.V (S.hst ω (m + 1))
  rw [h1]; exact Finset.mem_union_right _ hy

/-- The target of a probe is determined afterwards. [folklore] -/
theorem det_tgt_of_probe {m n : ℕ} (hmn : m < n) {e : Site 2 × MDir} (hc : (S.scheme.stN m ω).choice = some e)
    (hD : S.scheme.E.next (S.hst ω m) = some (S.probe (S.hst ω m) e)) : (S.scheme.stN n ω).Det (tgt e) := by
  have hst := (S.step_some hc hD).2.2
  refine S.scheme.det_stN_mono ω (Nat.succ_le_of_lt hmn) ?_
  rw [hst]
  exact HState.det_update_tgt _ _ _

/-- **The explored region lies in the cover of the determined macro-vertices.**
[cite: KozmaNitzan2024, §4 pp. 26–27 ((29), (31))] -/
theorem V_subset_Cover (n : ℕ) : (↑(S.V (S.hst ω n)) : Set (Site d)) ⊆ S.C.Cover {x | (S.scheme.stN n ω).Det x} := by
  intro y hy
  rcases (S.runInv ω n).V_cases y (Finset.mem_coe.1 hy) with h | ⟨m, hm, e, hc, -, hD, h⟩
  · exact S.C.subset_cover (u := 0) (Or.inl (zero_mem_occ n)) (Or.inl (Finset.mem_coe.2 (S.C.Q_subset_Cell _ h)))
  · have hsrc : e.1 ∈ {x | (S.scheme.stN n ω).Det x} :=
      Or.inl (S.scheme.occ_stN_mono ω hm.le (HState.cand_of_choice hc).1)
    have htgt : tgt e ∈ {x | (S.scheme.stN n ω).Det x} := det_tgt_of_probe hm hc hD
    rcases Finset.mem_union.1 h with h | h
    · rcases Finset.mem_union.1 (S.C.Ewv_subset_Cells _ _ h) with h | h
      · exact S.C.subset_cover hsrc (Or.inl (Finset.mem_coe.2 h))
      · exact S.C.subset_cover htgt (Or.inl (Finset.mem_coe.2 h))
    · obtain ⟨du, -, h⟩ := Finset.mem_biUnion.1 h
      have hj : S.jOf (S.hst ω m) e du (obs ω (S.env (S.hst ω m) e)) + 1 ≤ S.C.K := S.jOf_lt _ _ _ _
      rcases Finset.mem_union.1 (S.C.Stub_subset_Cell_union_Zone _ _ hj h) with h | h
      · exact S.C.subset_cover htgt (Or.inl (Finset.mem_coe.2 h))
      · exact S.C.subset_cover htgt (Or.inr (Set.mem_iUnion.2 ⟨du, Finset.mem_coe.2 h⟩))

/-- **(29), converse half**: a macro-vertex whose centre is explored is determined. [cite: KozmaNitzan2024, §4 p. 26 ((29))] -/
theorem det_of_cen_mem_V {n : ℕ} {x : Site 2} (hx : S.C.cen x ∈ S.V (S.hst ω n)) : (S.scheme.stN n ω).Det x :=
  S.C.mem_of_cen_mem_Cover (V_subset_Cover n (Finset.mem_coe.2 hx))

/-- A probe's target is examined only once. [folklore] -/
theorem probe_time_unique {m m' : ℕ} {e e' : Site 2 × MDir} (hc : (S.scheme.stN m ω).choice = some e)
    (hD : S.scheme.E.next (S.hst ω m) = some (S.probe (S.hst ω m) e)) (hc' : (S.scheme.stN m' ω).choice = some e')
    (hD' : S.scheme.E.next (S.hst ω m') = some (S.probe (S.hst ω m') e')) (ht : tgt e' = tgt e) : m' = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := det_tgt_of_probe hlt hc' hD'
    rw [ht] at h1
    exact (HState.cand_of_choice hc).2 h1
  · have h1 := det_tgt_of_probe hlt hc hD
    rw [← ht] at h1
    exact (HState.cand_of_choice hc').2 h1

/-! ## (31): nothing explored later meets `E_{w,v}` -/

/-- The new region of an examination along `e'` avoids `Btw(w, du) ∪ Q_v`, `v = w + du`, whenever the
target of `e'` is neither `w` nor `v` and its source is not `v`. [cite: KozmaNitzan2024, §4 p. 27 ((31))] -/
theorem newRegion_disjoint (h : ProbeHistory (Site d)) (e' : Site 2 × MDir) (o : Finset (Sym2 (Site d)))
    {w : Site 2} {du : MDir} (hv' : tgt e' ≠ w + stepVec du) (hv'w : tgt e' ≠ w) (hw' : e'.1 ≠ w + stepVec du)
    {y : Site d} (hy : y ∈ S.newRegion h e' o) : y ∉ S.C.Btw w du ∧ y ∉ S.C.Q (w + stepVec du) := by
  have hQt : ∀ {z}, z ∈ S.C.Q (tgt e') → z ∉ S.C.Btw w du ∧ z ∉ S.C.Q (w + stepVec du) := fun hz =>
    ⟨Finset.disjoint_left.1 (S.C.Q_disjoint_Btw (tgt e') w du) hz, Finset.disjoint_left.1 (S.C.Q_disjoint_Q hv') hz⟩
  rcases Finset.mem_union.1 hy with hy | hy
  · rcases Finset.mem_union.1 hy with hy | hy
    · refine ⟨fun hy' => ?_, Finset.disjoint_right.1 (S.C.Q_disjoint_Btw (w + stepVec du) e'.1 e'.2) hy⟩
      refine Finset.disjoint_left.1 (S.C.Btw_disjoint_Btw (v := w) (δ := du) (v' := e'.1) (δ' := e'.2) ?_ ?_) hy' hy
      · intro heq
        apply hv'
        have h1 : e'.1 = w := congrArg Prod.fst heq
        have h2 : e'.2 = du := congrArg Prod.snd heq
        show e'.1 + stepVec e'.2 = w + stepVec du
        rw [h1, h2]
      · intro heq; exact hw' (congrArg Prod.fst heq)
    · exact hQt hy
  · obtain ⟨du'', -, hy⟩ := Finset.mem_biUnion.1 hy
    rcases Finset.mem_union.1 (S.C.Stub_subset_Q_union_Btw _ _ (S.jOf_lt _ _ _ _) hy) with hy | hy
    · exact hQt hy
    · refine ⟨fun hy' => ?_, Finset.disjoint_right.1 (S.C.Q_disjoint_Btw (w + stepVec du) (tgt e') du'') hy⟩
      refine Finset.disjoint_left.1 (S.C.Btw_disjoint_Btw (v := w) (δ := du) (v' := tgt e') (δ' := du'') ?_ ?_) hy' hy
      · intro heq; exact hv'w (congrArg Prod.fst heq)
      · intro heq; exact hv' (congrArg Prod.fst heq)

/-- An undetermined neighbour is an onward direction of every earlier history. [cite: KozmaNitzan2024, §4 p. 27 (X = X_v)] -/
theorem mem_onward_of_not_det {m n : ℕ} (hmn : m ≤ n) {w : Site 2} {du : MDir}
    (hv : ¬(S.scheme.stN n ω).Det (w + stepVec du)) : du ∈ S.onward (S.hst ω m) w :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => hv (S.scheme.det_stN_mono ω hmn (det_of_cen_mem_V h))⟩

/-- **(31)**: after the examination of `w` at time `m`, as long as `v = w + du` is undetermined, the
explored region meets `E_{w,v}` only inside the stub `H^{j_x}_{w,v}` revealed at time `m`.
[cite: KozmaNitzan2024, §4 p. 27 ((31))] -/
theorem mem_Stub_of_mem_V_of_mem_Efar {n m : ℕ} (hm : m < n) {e : Site 2 × MDir}
    (hc : (S.scheme.stN m ω).choice = some e) (hV : S.Valid (S.hst ω m) e)
    (hD : S.scheme.E.next (S.hst ω m) = some (S.probe (S.hst ω m) e)) {du : MDir}
    (hv : ¬(S.scheme.stN n ω).Det (tgt e + stepVec du)) {y : Site d} (hyV : y ∈ S.V (S.hst ω n))
    (hyE : y ∈ S.C.Efar (tgt e) du) :
    y ∈ S.C.Stub (tgt e) du (S.jOf (S.hst ω m) e du (obs ω (S.env (S.hst ω m) e))) := by
  have hdu : du ∈ S.onward (S.hst ω m) (tgt e) := mem_onward_of_not_det hm.le hv
  have hv0 : tgt e + stepVec du ≠ 0 := fun h => hv (by rw [h]; exact Or.inl (zero_mem_occ n))
  have hyE' := S.C.Efar_subset_Btw_union_Q _ _ hyE
  rcases (S.runInv ω n).V_cases y hyV with hy0 | ⟨m', hm', e', hc', hV', hD', hy'⟩
  · exfalso
    rcases Finset.mem_union.1 hyE' with h | h
    · exact Finset.disjoint_left.1 (S.C.Q_disjoint_Btw 0 (tgt e) du) hy0 h
    · exact Finset.disjoint_left.1 (S.C.Q_disjoint_Q hv0.symm) hy0 h
  · by_cases hmm : m' = m
    · subst hmm
      rw [hc] at hc'
      cases Option.some_injective _ hc'
      rcases Finset.mem_union.1 hy' with hy' | hy'
      · exact absurd hyE (Valid.Ewv_not_mem_Efar hV hdu hy')
      · obtain ⟨du'', -, hy'⟩ := Finset.mem_biUnion.1 hy'
        by_cases hdd : du'' = du
        · subst hdd; exact hy'
        · exfalso
          rcases Finset.mem_union.1 (S.C.Stub_subset_Q_union_Btw _ _ (S.jOf_lt _ _ _ _) hy') with h | h
          · exact S.C.Q_disjoint_Efar h hyE
          · exact (S.C.Btw_sep_Efar hdd).not_mem (Finset.mem_coe.2 h) (Finset.mem_coe.2 hyE)
    · exfalso
      have hv' : tgt e' ≠ tgt e + stepVec du := fun h => hv (h ▸ det_tgt_of_probe hm' hc' hD')
      have hv'w : tgt e' ≠ tgt e := fun h => hmm (probe_time_unique hc hD hc' hD' h)
      have hw' : e'.1 ≠ tgt e + stepVec du := fun h =>
        hv (h ▸ Or.inl (S.scheme.occ_stN_mono ω hm'.le (HState.cand_of_choice hc').1))
      obtain ⟨h1, h2⟩ := S.newRegion_disjoint _ _ _ hv' hv'w hw' hy'
      rcases Finset.mem_union.1 hyE' with h | h
      · exact h1 h
      · exact h2 h

/-- **(31) at the origin**: as long as `v = 0 + du` is undetermined, the explored region avoids
`E_{0,v}`. [cite: KozmaNitzan2024, §4 p. 28 ((E₁ ∪ E_{w,v}) ∩ E_i = E₁)] -/
theorem not_mem_Ewv_zero_of_mem_V {n : ℕ} {du : MDir} (hv : ¬(S.scheme.stN n ω).Det ((0 : Site 2) + stepVec du))
    {y : Site d} (hyV : y ∈ S.V (S.hst ω n)) : y ∉ S.C.Ewv 0 du := by
  have hv0 : (0 : Site 2) + stepVec du ≠ 0 := fun h => hv (by rw [h]; exact Or.inl (zero_mem_occ n))
  intro hyE
  rcases (S.runInv ω n).V_cases y hyV with hy0 | ⟨m', hm', e', hc', -, hD', hy'⟩
  · rcases Finset.mem_union.1 hyE with h | h
    · exact Finset.disjoint_left.1 (S.C.Q_disjoint_Btw 0 0 du) hy0 h
    · exact Finset.disjoint_left.1 (S.C.Q_disjoint_Q hv0.symm) hy0 h
  · have hv' : tgt e' ≠ 0 + stepVec du := fun h => hv (h ▸ det_tgt_of_probe hm' hc' hD')
    have hv'w : tgt e' ≠ 0 := fun h => (HState.cand_of_choice hc').2 (h ▸ Or.inl (zero_mem_occ m'))
    have hw' : e'.1 ≠ 0 + stepVec du := fun h =>
      hv (h ▸ Or.inl (S.scheme.occ_stN_mono ω hm'.le (HState.cand_of_choice hc').1))
    obtain ⟨h1, h2⟩ := S.newRegion_disjoint _ _ _ hv' hv'w hw' hy'
    rcases Finset.mem_union.1 hyE with h | h
    · exact h1 h
    · exact h2 h

/-! ## (32) -/

/-- Pinned weights agree at a coordinate pinned on both sides along equivalent patterns. [folklore] -/
theorem pinW_apply_eq_of_mem {ι : Type*} (w : ι → unitInterval) {F F' ξ ξ' : Set ι} {x : ι} (hx : x ∈ F) (hx' : x ∈ F')
    (h : x ∈ ξ ↔ x ∈ ξ') : pinW w F ξ x = pinW w F' ξ' x := by
  by_cases hξ : x ∈ ξ
  · rw [pinW_apply_of_mem_of_mem _ hx hξ, pinW_apply_of_mem_of_mem _ hx' (h.1 hξ)]
  · rw [pinW_apply_of_mem_of_not_mem _ hx hξ, pinW_apply_of_mem_of_not_mem _ hx' (fun h' => hξ (h.2 h'))]

/-- The recorded pattern is `ω ∪ U₀` on the explored edges: the two pinnings agree. [folklore] -/
theorem pinW_F_ξ_eq (n : ℕ) :
    pinW (lattW d S.p) ↑(S.F (S.hst ω n)) ↑(S.ξ (S.hst ω n)) = pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀) := by
  refine pinW_congr _ fun x hx => ?_
  rw [Finset.mem_coe, (S.runInv ω n).ξ_iff x, Set.mem_union, Finset.mem_coe]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_coe.1 hx, h⟩⟩

/-- `P[W₀](0 ↔ M_v) = P[pinned on ω ∪ U₀](0 ↔ M_v in E_i ∪ E_{w,v})`. [cite: KozmaNitzan2024, §4 p. 28 ((32))] -/
theorem real_W₀_eq (n : ℕ) (e : Site 2 × MDir) :
    (prodBernoulli (S.W₀ (S.hst ω n) e)).real (⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t) =
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M (tgt e)) : Set (Site d)), openConnIn (↑(S.V (S.hst ω n) ∪ S.C.Ewv e.1 e.2) : Set (Site d)) 0 t) := by
  have h0 : (0 : Site d) ∈ (↑(S.V (S.hst ω n) ∪ S.C.Ewv e.1 e.2) : Set (Site d)) :=
    Finset.mem_coe.2 (Finset.mem_union_left _ (zero_mem_V n))
  rw [W₀, ← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn _ _ h0, pinW_F_ξ_eq]

/-- **(32) for `w ≠ 0`** (KN p. 28 and Step I): if `w` was examined at time `m < n` and its connection to
the still undetermined `v = w + du` was good at level `j_x`, then `P(0 ↔ M_v in E_n ∪ E_{w,v} | ω|_{E_n}) > 1 - δ`.
[cite: KozmaNitzan2024, §4 p. 28 ((32) for w ≠ 0)] -/
theorem reach_of_probe {n m : ℕ} (hm : m < n) {e : Site 2 × MDir}
    (hc : (S.scheme.stN m ω).choice = some e) (hV : S.Valid (S.hst ω m) e)
    (hD : S.scheme.E.next (S.hst ω m) = some (S.probe (S.hst ω m) e)) {du : MDir}
    (hv : ¬(S.scheme.stN n ω).Det (tgt e + stepVec du))
    (hcond : S.cond (S.hst ω m) e du (S.jOf (S.hst ω m) e du (obs ω (S.env (S.hst ω m) e))) (obs ω (S.env (S.hst ω m) e))) :
    1 - S.δc < (prodBernoulli (S.W₀ (S.hst ω n) (tgt e, du))).real (⋃ t ∈ S.C.M (tgt (tgt e, du)), openConn (0 : Site d) t) := by
  set hm_ := S.hst ω m with hhm
  set o := obs ω (S.env hm_ e) with ho
  set j := S.jOf hm_ e du o with hjdef
  have hI := S.runInv ω n
  have hIm := S.runInv ω m
  have hdu : du ∈ S.onward hm_ (tgt e) := mem_onward_of_not_det hm.le hv
  have hjK : j < S.C.K := S.jOf_lt _ _ _ _
  -- `Fj_m ⊆ F_n`
  have hF1 : S.F (S.hst ω (m + 1)) = S.F hm_ ∪ S.revealOf hm_ e o := (S.step_some hc hD).1
  have hFjF : S.Fj hm_ e du j ⊆ S.F (S.hst ω n) := by
    intro x hx
    by_cases hxF : x ∈ S.F hm_
    · exact S.F_mono ω hm.le hxF
    · have h1 : x ∈ S.revealOf hm_ e o := S.Fj_sdiff_subset_revealOf hdu le_rfl (Finset.mem_sdiff.2 ⟨hx, hxF⟩)
      refine S.F_mono ω (Nat.succ_le_of_lt hm) ?_
      show x ∈ S.F (S.hst ω (m + 1))
      rw [hF1]; exact Finset.mem_union_right _ h1
  -- `F_n ∩ wireSet(Sx_m) ⊆ Fj_m` ((31))
  have hkey : ∀ x ∈ S.F (S.hst ω n), x ∈ wireSet (↑(S.Sx hm_ e du) : Set (Site d)) → x ∈ S.Fj hm_ e du j := by
    intro x hx hxS
    rw [hI.F_eq, mem_edgesIn_iff] at hx
    rw [Fj, mem_edgesIn_iff]
    refine ⟨hx.1, fun y hy => ?_⟩
    have hyV := hx.2 y hy
    have hyS := Finset.mem_coe.1 (hxS.1 y hy)
    rcases Finset.mem_union.1 hyS with hyS | hyS
    · exact Finset.mem_union_left _ hyS
    · exact Finset.mem_union_right _ (mem_Stub_of_mem_V_of_mem_Efar hm hc hV hD hv hyV hyS)
  -- the weights agree on `wireSet(Sx_m)`
  have hpq : ∀ x ∈ wireSet (↑(S.Sx hm_ e du) : Set (Site d)),
      pinW (lattW d S.p) ↑(S.Fj hm_ e du j) ↑(S.pat hm_ e du j o) x =
        pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀) x := by
    intro x hxS
    by_cases hxj : x ∈ S.Fj hm_ e du j
    · refine pinW_apply_eq_of_mem _ (Finset.mem_coe.2 hxj) (Finset.mem_coe.2 (hFjF hxj)) ?_
      rw [Finset.mem_coe, pat, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, ho, mem_obs_iff, Set.mem_union,
        Finset.mem_coe]
      by_cases hxF : x ∈ S.F hm_
      · rw [hIm.ξ_iff x]
        constructor
        · rintro (⟨-, h'⟩ | ⟨-, -, h'⟩)
          · exact h'
          · exact absurd hxF h'
        · intro h'; exact Or.inl ⟨hxF, h'⟩
      · have hxenv : x ∈ S.env hm_ e := S.Fj_sdiff_subset_env hm_ e hdu hjK (Finset.mem_sdiff.2 ⟨hxj, hxF⟩)
        have hxU : x ∉ S.U₀ := fun h' => hxF (S.U₀_subset_F _ h')
        constructor
        · rintro (h' | ⟨⟨-, h'⟩, -, -⟩)
          · exact absurd (hV.ξ_sub h') hxF
          · exact Or.inl h'
        · rintro (h' | h')
          · exact Or.inr ⟨⟨hxenv, h'⟩, hxj, hxF⟩
          · exact absurd h' hxU
    · have hxF : x ∉ S.F (S.hst ω n) := fun h' => hxj (hkey x h' hxS)
      rw [pinW_apply_of_not_mem _ _ (fun h' => hxj (Finset.mem_coe.1 h')),
        pinW_apply_of_not_mem _ _ (fun h' => hxF (Finset.mem_coe.1 h'))]
  -- `Sx_m ⊆ E_n ∪ E_{w,v}`
  have hSx : (↑(S.Sx hm_ e du) : Set (Site d)) ⊆ ↑(S.V (S.hst ω n) ∪ S.C.Ewv (tgt e) du) := by
    refine Finset.coe_subset.2 fun y hy => ?_
    rcases Finset.mem_union.1 hy with hy | hy
    · rcases Finset.mem_union.1 hy with hy | hy
      · exact Finset.mem_union_left _ (S.V_mono ω hm.le hy)
      · exact Finset.mem_union_left _ (newRegion_subset_V hm hc hD (Finset.mem_union_left _ hy))
    · exact Finset.mem_union_right _ (S.C.Efar_subset_Ewv _ _ hy)
  have h0S : (0 : Site d) ∈ (↑(S.Sx hm_ e du) : Set (Site d)) :=
    Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hV.zero_mem))
  -- the chain
  have e1 : (prodBernoulli (S.Wt hm_ e du j o)).real (S.Conn e du) =
      (prodBernoulli (pinW (lattW d S.p) ↑(S.Fj hm_ e du j) ↑(S.pat hm_ e du j o))).real
        (⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)), openConnIn (↑(S.Sx hm_ e du) : Set (Site d)) 0 t) := by
    rw [Conn, Wt, ← Finset.set_biUnion_coe, prodBernoulli_restrW_real_biUnion_openConn _ _ h0S]
  have e2 : (prodBernoulli (pinW (lattW d S.p) ↑(S.Fj hm_ e du j) ↑(S.pat hm_ e du j o))).real
        (⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)), openConnIn (↑(S.Sx hm_ e du) : Set (Site d)) 0 t) =
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)), openConnIn (↑(S.Sx hm_ e du) : Set (Site d)) 0 t) :=
    prodBernoulli_real_eq_of_determinedBy _ _ hpq (determinedBy_biUnion_openConnIn _ _ _ subset_rfl)
      (measurableSet_biUnion_openConnIn _ _ _)
  have e3 : (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)), openConnIn (↑(S.Sx hm_ e du) : Set (Site d)) 0 t) ≤
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)),
          openConnIn (↑(S.V (S.hst ω n) ∪ S.C.Ewv (tgt e) du) : Set (Site d)) 0 t) :=
    measureReal_mono (biUnion_openConnIn_mono hSx 0 subset_rfl) (measure_ne_top _ _)
  have hc' : 1 - S.δc < (prodBernoulli (S.Wt hm_ e du j o)).real (S.Conn e du) := hcond
  rw [real_W₀_eq]
  change 1 - S.δc < (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
    (⋃ t ∈ (↑(S.C.M (tgt e + stepVec du)) : Set (Site d)),
      openConnIn (↑(S.V (S.hst ω n) ∪ S.C.Ewv (tgt e) du) : Set (Site d)) 0 t)
  rw [e1, e2] at hc'
  exact lt_of_lt_of_le hc' e3

/-- **(32) for `w = 0`** (KN p. 28): the cube `Q_0` is wired open, and by the choice of `r` ("the
definition of `m₂`", hypothesis `hQ0`) `M_0` is joined to `M_v` inside `Q_0 ∪ E_{0,v}` with
probability `> 1 - δ`. [cite: KozmaNitzan2024, §4 p. 28 ((32) for w = 0)] -/
theorem reach_zero {n : ℕ} {du : MDir} (hv : ¬(S.scheme.stN n ω).Det ((0 : Site 2) + stepVec du))
    (hQ0 : 1 - S.δc < (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real
      (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
        openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t)) :
    1 - S.δc < (prodBernoulli (S.W₀ (S.hst ω n) ((0 : Site 2), du))).real
      (⋃ t ∈ S.C.M (tgt ((0 : Site 2), du)), openConn (0 : Site d) t) := by
  have hI := S.runInv ω n
  have hQ0V : S.C.Q 0 ⊆ S.V (S.hst ω n) := hI.det_Q 0 (Or.inl (zero_mem_occ n))
  -- `F_n ∩ wireSet(Q_0 ∪ E_{0,v}) ⊆ U₀`
  have hkey : ∀ x ∈ S.F (S.hst ω n), x ∈ wireSet (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) → x ∈ S.U₀ := by
    intro x hx hxS
    rw [hI.F_eq, mem_edgesIn_iff] at hx
    rw [U₀, mem_edgesIn_iff]
    refine ⟨hx.1, fun y hy => ?_⟩
    rcases Finset.mem_union.1 (Finset.mem_coe.1 (hxS.1 y hy)) with h | h
    · exact h
    · exact absurd h (not_mem_Ewv_zero_of_mem_V hv (hx.2 y hy))
  have hpq : ∀ x ∈ wireSet (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)),
      pinW (lattW d S.p) ↑S.U₀ ↑S.U₀ x = pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀) x := by
    intro x hxS
    by_cases hxF : x ∈ S.F (S.hst ω n)
    · have hxU : x ∈ S.U₀ := hkey x hxF hxS
      refine pinW_apply_eq_of_mem _ (Finset.mem_coe.2 hxU) (Finset.mem_coe.2 hxF) ?_
      simp only [Finset.mem_coe, Set.mem_union, hxU, or_true]
    · have hxU : x ∉ S.U₀ := fun h' => hxF (S.U₀_subset_F _ h')
      rw [pinW_apply_of_not_mem _ _ (fun h' => hxU (Finset.mem_coe.1 h')),
        pinW_apply_of_not_mem _ _ (fun h' => hxF (Finset.mem_coe.1 h'))]
  have hsub : (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) ⊆ ↑(S.V (S.hst ω n) ∪ S.C.Ewv 0 du) :=
    Finset.coe_subset.2 (Finset.union_subset_union hQ0V le_rfl)
  have e2 : (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real
        (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
          openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t) =
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
          openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t) :=
    prodBernoulli_real_eq_of_determinedBy _ _ hpq (determinedBy_biUnion_openConnIn _ _ _ subset_rfl)
      (measurableSet_biUnion_openConnIn _ _ _)
  have e3 : (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
          openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t) ≤
      (prodBernoulli (pinW (lattW d S.p) ↑(S.F (S.hst ω n)) (ω ∪ ↑S.U₀))).real
        (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
          openConnIn (↑(S.V (S.hst ω n) ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t) :=
    measureReal_mono (biUnion_openConnIn_mono hsub 0 subset_rfl) (measure_ne_top _ _)
  rw [real_W₀_eq]
  rw [e2] at hQ0
  exact lt_of_lt_of_le hQ0 e3

/-- **Every history of the run at which an edge is chosen is valid** ((29), the cover property and (32)).
[cite: KozmaNitzan2024, §4 pp. 26–28 ((29), (31), (32))] -/
theorem valid_of_choice
    (hQ0 : ∀ du : MDir, 1 - S.δc < (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real
      (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
        openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t))
    {n : ℕ} {e : Site 2 × MDir} (hc : (S.scheme.stN n ω).choice = some e) : S.Valid (S.hst ω n) e := by
  have hI := S.runInv ω n
  obtain ⟨he1, he2⟩ := HState.cand_of_choice hc
  refine ⟨hI.F_eq, fun x hx => ((hI.ξ_iff x).1 hx).1, zero_mem_V n, cen_mem_V_of_det (Or.inl he1), ?_, ?_⟩
  · refine ⟨{x | (S.scheme.stN n ω).Det x}, he2, fun du hdu hdet => ?_, V_subset_Cover n⟩
    exact (Finset.mem_filter.1 hdu).2 (cen_mem_V_of_det hdet)
  · obtain ⟨w, du⟩ := e
    rcases S.scheme.exists_probe_of_det ω n w (Or.inl he1) with hw0 | ⟨m, hm, e₀, P, hc₀, ht₀, hP, hocc⟩
    · subst hw0
      exact reach_zero he2 (hQ0 du)
    · obtain ⟨e₁, hc₁, hV₀, rfl⟩ := S.of_next_some hP
      rw [hc₀] at hc₁
      cases Option.some_injective _ hc₁
      subst ht₀
      have hsucc : S.succ (S.hst ω m) e₀ (obs ω (S.env (S.hst ω m) e₀)) := (S.succ_read_iff _ _ _).1 (hocc.1 he1)
      have hdu : du ∈ S.onward (S.hst ω m) (tgt e₀) := mem_onward_of_not_det hm.le he2
      exact reach_of_probe hm hc₀ hV₀ hP he2 (hsucc du hdu)

/-- **Kozma–Nitzan's exploration process is lawful**, given (32) at the origin (`hQ0`) and the
failure bound (33) after valid histories (`hfail`). [cite: KozmaNitzan2024, §4 pp. 25–31] -/
theorem lawful {ε : ℝ}
    (hQ0 : ∀ du : MDir, 1 - S.δc < (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real
      (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
        openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t))
    (hfail : ∀ h e, S.Valid h e → (bondPercolation (zdGraph d) S.p).real {ω | ¬S.succ h e ((S.probe h e).read ω)} ≤ ε) :
    S.scheme.Lawful (zdGraph d) S.p ε where
  fresh := by
    intro h P hP
    obtain ⟨e, -, -, rfl⟩ := S.nextProbe_eq_some hP
    constructor
    · rw [Set.disjoint_left]
      intro x hx hxU
      exact (Finset.mem_sdiff.1 (Finset.mem_coe.1 hx)).2 (S.U₀_subset_F _ (Finset.mem_coe.1 hxU))
    · rw [Finset.disjoint_left]
      intro x hx hxs
      exact (Finset.mem_sdiff.1 hx).2 (Finset.mem_union_right _ hxs)
  probes := by
    intro ω _ n hc
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hc
    have hV : S.Valid (S.hst ω n) e := valid_of_choice hQ0 he
    show S.nextProbe (S.hst ω n) ≠ none
    rw [S.nextProbe_of_valid he hV]
    exact Option.some_ne_none _
  fail := by
    intro h P e hP hc
    obtain ⟨e', hc', hV, rfl⟩ := S.nextProbe_eq_some hP
    have hcc : some e' = some e := hc'.symm.trans hc
    cases Option.some_injective _ hcc
    exact hfail h _ hV

end Consequences

end KSch

end KozmaNitzan

end Percolation.Literature

end

/-!
# Kozma–Nitzan, Theorem 6: Conjecture 3 and `θ(p) > 0` give percolation in a slab

Thirteenth and last proofs-only companion of
`KozmaNitzanReduction.lean` (G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a
conjectured inequality*, arXiv:2401.12397 (2024), §4 Theorem 6 pp. 25–31): the assembly.

* `KSch.exists_exit` — what an occupied macro-vertex certifies ("(3) For every `v ∈ G_i`,
  `0 ↔^{E_i}` …", p. 26): since (32) is a positive conditional probability given `ω|_{E_i}`, the
  configuration itself has an open path inside `E_i` from `0` to a lattice neighbour of `E_{w,v}`;
* `KSch.mem_percolatesVia_of_infinite`, `KSch.theta_slab_pos` — "the combination of (2) and (3)
  proves that the probability that there is percolation in `ℤ² × [-5r, 5r]^{d-2}` is positive"
  (pp. 26–27), with the lawful driver `HistorySiteRenormalization.lean` (`ε ≤ 2⁻³²` in place of
  `p_c(ℤ², site)`);
* `KSch.hQ0_of_hit` — (32) at the origin from the hittability of the elongated geometry of aspect
  `6` ("our definition of `m₂` implies `P(M_{(0,0)} ↔ M_v) > 1 - δ`", p. 28);
* `exists_KSch_theta_slab_pos` — the choice of the constants `ε, δ, δ₂, K, R, m₂, r` (pp. 25–26)
  and Theorem 6 in every `d ≥ 3`: `θ_{ℤ^d}(p) > 0`, `0 < p < 1` and Conjecture 3 give a slab
  `{|x_j| ≤ 5r, j ≠ 1, 2}` in which the origin percolates;

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024), §4 Theorem 6, pp. 25–31.
* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.2 [GrimmettPercolation1999].
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace Percolation.Literature

open LatticeModels SimpleGraph GadgetSystem ProbeHistory Contour HSiteScheme DCT16

namespace KozmaNitzan

variable {d : ℕ}

/-- The unit of the sign of a macro-direction. [folklore] -/
def σu (δ : MDir) : ℤˣ := if Cells.sgOf δ = 1 then 1 else -1

/-- Its value is the sign. [folklore] -/
theorem σu_val (δ : MDir) : (σu δ : ℤ) = Cells.sgOf δ := units_of_sign_val (Cells.sgOf_sign δ)

namespace KSch

open Cells

variable (S : KSch d)

/-! ## The slab -/

/-- **The slab** `ℤ² × [-5r, 5r]^{d-2}` of the exploration (KN p. 26: "`E_i ⊂ ℤ² × [-5r, 5r]^{d-2}`").
[cite: KozmaNitzan2024, §4 p. 26] -/
def slab : Set (Site d) := {x | ∀ j, j ≠ S.C.ax0 → j ≠ S.C.ax1 → |x j| ≤ 5 * S.C.r}

/-- The origin lies in the slab. [folklore] -/
theorem zero_mem_slab : (0 : Site d) ∈ S.slab := fun j _ _ => by simp

/-- The cover of any set of macro-vertices lies in the slab. [cite: KozmaNitzan2024, §4 p. 26] -/
theorem Cover_subset_slab (det : Set (Site 2)) : S.C.Cover det ⊆ S.slab := by
  intro y hy j h0 h1
  simp only [Cells.Cover, Set.mem_iUnion, Set.mem_union, exists_prop, Finset.mem_coe] at hy
  obtain ⟨u, -, hy | ⟨δ, hy⟩⟩ := hy
  · rw [Cells.Cell, mem_Icc_iff] at hy
    have := hy j
    have hw : S.C.wC j = 5 * S.C.r := by unfold Cells.wC; rw [if_neg]; push Not; exact ⟨h0, h1⟩
    simp only [Pi.sub_apply, Pi.add_apply, hw, S.C.cen_of_ne u h0 h1] at this
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · rw [Cells.Zone, mem_sBox_iff (sgOf_sign δ)] at hy
    have hne : j ≠ S.C.axOf δ := by
      unfold Cells.axOf Cells.pax; split_ifs
      · exact h0
      · exact h1
    have := hy.2 j hne
    rw [S.C.cen_of_ne u h0 h1] at this
    have hr : (0 : ℤ) ≤ S.C.r := by positivity
    rw [abs_le]; constructor <;> linarith [this.1, this.2]

/-- The explored region lies in the slab. [cite: KozmaNitzan2024, §4 p. 26] -/
theorem V_subset_slab (ω : BondConfig (Site d)) (n : ℕ) : (↑(S.V (S.hst ω n)) : Set (Site d)) ⊆ S.slab :=
  (V_subset_Cover n).trans (S.Cover_subset_slab _)

/-- `M_v ⊆ Q_v`. [folklore] -/
theorem M_subset_Q (v : Site 2) : S.C.M v ⊆ S.C.Q v := by
  intro y hy
  rw [Cells.M, mem_cIcc_iff] at hy
  rw [Cells.Q, mem_cIcc_iff]
  intro i; have := hy i; push_cast at this ⊢; constructor <;> linarith [this.1, this.2]

/-- The macro-vertices whose cell is near a given vertex form a finite set. [folklore] -/
theorem finite_setOf_near (a : Site d) :
    {b : Site 2 | ∀ i : Fin 2, |20 * (S.C.r : ℤ) * b i - a (S.C.pax i)| ≤ 16 * S.C.r}.Finite := by
  set B : Site 2 := fun i => |a (S.C.pax i)| + 1 with hB
  refine (Finset.Icc (-B) B).finite_toSet.subset fun b hb => ?_
  rw [Finset.coe_Icc, Set.mem_Icc, Pi.le_def, Pi.le_def]
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  have key : ∀ i, |b i| ≤ |a (S.C.pax i)| + 1 := by
    intro i
    have h1 := hb i
    have h2 : |20 * (S.C.r : ℤ) * b i| ≤ 16 * S.C.r + |a (S.C.pax i)| := by
      have := abs_sub_abs_le_abs_sub (20 * (S.C.r : ℤ) * b i) (a (S.C.pax i)); linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ 20 * S.C.r)] at h2
    by_contra hlt
    push Not at hlt
    have h3 : |a (S.C.pax i)| + 2 ≤ |b i| := by omega
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℤ) ≤ 20 * S.C.r)
    nlinarith [abs_nonneg (a (S.C.pax i))]
  constructor <;> intro i <;> have := key i <;> simp only [hB, Pi.neg_apply] <;> rw [abs_le] at this
  · linarith [this.1]
  · linarith [this.2]

/-! ## What an occupied macro-vertex certifies -/

variable {S}

/-- **The certificate of (32)** (KN p. 26, (3)): after a valid history the configuration itself has
an open path inside the explored region from the origin to a lattice neighbour of `E_{w,v}` — (32) is
a positive probability under the weighting pinned on the recorded pattern, which on the initial event
is the configuration's own. [cite: KozmaNitzan2024, §4 p. 26 ((3)) and p. 28 ((32))] -/
theorem exists_exit (hδc : S.δc ≤ 1) {ω : BondConfig (Site d)} (hA : ω ∈ initEvent S.scheme)
    {n : ℕ} {e : Site 2 × MDir} (hV : S.Valid (S.hst ω n) e) :
    ∃ a ∈ S.V (S.hst ω n), PathIn (openGraph ω) (↑(S.V (S.hst ω n)) : Set (Site d)) 0 a ∧
      ∃ b ∈ S.C.Ewv e.1 e.2, (zdGraph d).Adj a b := by
  set W := S.W₀ (S.hst ω n) e with hW
  have hI := S.runInv ω n
  have hpos : 0 < (prodBernoulli W).real (⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t) :=
    lt_of_le_of_lt (by linarith) hV.reach
  -- almost surely no pair of weight zero is open
  have hae : ∀ᵐ η ∂prodBernoulli W, ∀ x ∈ {x : Sym2 (Site d) | W x = 0}, x ∉ η :=
    prodBernoulli_ae_forall_notMem _ (Set.to_countable _) fun x hx => hx
  have hne : ((⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t) ∩ {η | ∀ x : Sym2 (Site d), W x = 0 → x ∉ η}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h1 : (prodBernoulli W).real ((⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t) ∩
        {η | ∀ x : Sym2 (Site d), W x = 0 → x ∉ η}) = (prodBernoulli W).real (⋃ t ∈ S.C.M (tgt e), openConn (0 : Site d) t) := by
      refine measureReal_congr ?_
      filter_upwards [hae] with η hη
      exact propext ⟨fun h' => h'.1, fun h' => ⟨h', fun x hx => hη x hx⟩⟩
    rw [h, measureReal_empty] at h1
    linarith
  obtain ⟨η, hηA, hη0⟩ := hne
  simp only [Set.mem_iUnion, exists_prop] at hηA
  obtain ⟨t, ht, hreach⟩ := hηA
  have hopen : ∀ x y, (openGraph η).Adj x y → W s(x, y) ≠ 0 := fun x y hxy h0 =>
    hη0 _ h0 ((openGraph_adj _ _ _).1 hxy).1
  -- the open path from `0` to `M_v` inside `E_i ∪ E_{w,v}` and its first exit from `E_i`
  have hηwire : ∀ x ∈ η, x ∈ wireSet (↑(S.V (S.hst ω n) ∪ S.C.Ewv e.1 e.2) : Set (Site d)) := by
    intro x hx
    by_contra hxS
    exact hη0 x (by rw [hW, W₀]; exact restrW_apply_of_not_mem _ hxS) hx
  have hpath := pathIn_of_reachable_of_forall_mem_wireSet hηwire
    (Finset.mem_coe.2 (Finset.mem_union_left _ hV.zero_mem)) hreach
  have htV : t ∉ (↑(S.V (S.hst ω n)) : Set (Site d)) := fun h =>
    (Valid.sep_Q hV).not_mem h (Finset.mem_coe.2 (S.M_subset_Q _ ht))
  obtain ⟨a, b, ha, hb, hbU, hab, hpa⟩ := hpath.exit (R := (↑(S.V (S.hst ω n)) : Set (Site d)))
    (Finset.mem_coe.2 hV.zero_mem) htV
  have hbE : b ∈ S.C.Ewv e.1 e.2 := by
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hbU) with h | h
    · exact absurd (Finset.mem_coe.2 h) hb
    · exact h
  have haU : a ∈ (↑(S.V (S.hst ω n) ∪ S.C.Ewv e.1 e.2) : Set (Site d)) :=
    Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha))
  -- the exit edge is a lattice edge
  have hab' : (zdGraph d).Adj a b := by
    have h1 := hopen a b hab
    rw [hW, W₀, restrW_apply_of_mem _ (mk_mem_wireSet_iff.2 ⟨haU, hbU, hab.ne⟩)] at h1
    have hF : s(a, b) ∉ (↑(S.F (S.hst ω n)) : Set (Sym2 (Site d))) := by
      intro h
      rw [Finset.mem_coe, hI.F_eq, mem_edgesIn_iff] at h
      exact hb (Finset.mem_coe.2 (h.2 b (Sym2.mem_mk_right _ _)))
    rw [pinW_apply_of_not_mem _ _ hF, lattW_mk] at h1
    by_contra hnadj
    rw [if_neg hnadj] at h1
    exact h1 rfl
  -- the initial segment is `ω`-open
  have hpa' : PathIn (openGraph ω) (↑(S.V (S.hst ω n)) : Set (Site d)) 0 a := by
    refine (pathIn_congrGraph (fun x y hx hy hxy => ?_) hpa).mono Set.inter_subset_left
    have hxV : x ∈ S.V (S.hst ω n) := Finset.mem_coe.1 hx.1
    have hyV : y ∈ S.V (S.hst ω n) := Finset.mem_coe.1 hy.1
    have h1 := hopen x y hxy
    have hne := hxy.ne
    rw [hW, W₀, restrW_apply_of_mem _ (mk_mem_wireSet_iff.2 ⟨hx.2, hy.2, hne⟩)] at h1
    by_cases hF : s(x, y) ∈ (↑(S.F (S.hst ω n)) : Set (Sym2 (Site d)))
    · have hξ : s(x, y) ∈ (↑(S.ξ (S.hst ω n)) : Set (Sym2 (Site d))) := by
        by_contra hξ
        rw [pinW_apply_of_mem_of_not_mem _ hF hξ] at h1
        exact h1 rfl
      rw [openGraph_adj]
      rcases ((hI.ξ_iff _).1 (Finset.mem_coe.1 hξ)).2 with h | h
      · exact ⟨h, hne⟩
      · exact ⟨hA (Finset.mem_coe.2 h), hne⟩
    · exfalso
      rw [pinW_apply_of_not_mem _ _ hF, lattW_mk] at h1
      by_cases hadj : (zdGraph d).Adj x y
      · apply hF
        rw [Finset.mem_coe, hI.F_eq, mem_edgesIn_iff]
        refine ⟨(SimpleGraph.mem_edgeSet _).2 hadj, fun z hz => ?_⟩
        rcases Sym2.mem_iff.1 hz with rfl | rfl
        · exact hxV
        · exact hyV
      · rw [if_neg hadj] at h1
        exact h1 rfl
  exact ⟨a, Finset.mem_coe.1 ha, hpa', b, hbE, hab'⟩

/-- **An infinite macro-cluster forces an infinite open cluster of the origin inside the slab**
(KN pp. 26–27: "the combination of (2) and (3)"): every occupied macro-vertex `v ≠ 0` was examined
after a valid history, whose certificate ends within `16r` of the centre of `v`; a vertex is that close
to boundedly many centres only. [cite: KozmaNitzan2024, §4 pp. 26–27] -/
theorem mem_percolatesVia_of_infinite (hδc : S.δc ≤ 1) {ω : BondConfig (Site d)}
    (hωE : ω ⊆ (zdGraph d).edgeSet) (hA : ω ∈ initEvent S.scheme) (hinf : (S.scheme.occFinal ω).Infinite) :
    ω ∈ percolatesVia (withinGraph (zdGraph d) S.slab) (0 : Site d) := by
  set Cl := openClusterIn (withinGraph (zdGraph d) S.slab) ω 0 with hCl
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  have hnear : ∀ b ∈ S.scheme.occFinal ω, b ≠ 0 →
      ∃ a ∈ Cl, ∀ i : Fin 2, |20 * (S.C.r : ℤ) * b i - a (S.C.pax i)| ≤ 16 * S.C.r := by
    intro b hb hb0
    obtain ⟨n, hbn⟩ := Set.mem_iUnion.1 hb
    rcases S.scheme.exists_probe_of_det ω n b (Or.inl hbn) with h | ⟨m, -, e, P, hc, hte, hP, -⟩
    · exact absurd h hb0
    obtain ⟨e', hc', hV, rfl⟩ := S.of_next_some hP
    rw [hc] at hc'
    cases Option.some_injective _ hc'
    obtain ⟨a, haV, hpa, b', hb', hab⟩ := exists_exit hδc hA hV
    refine ⟨a, ?_, fun i => ?_⟩
    · rw [hCl, mem_openClusterIn_iff]
      refine DCT16.reachable_of_pathIn (pathIn_congrGraph (fun x y hx hy hxy => ?_) hpa)
      rw [SimpleGraph.inf_adj]
      refine ⟨hxy, withinGraph_adj.2 ⟨?_, S.V_subset_slab ω m hx, S.V_subset_slab ω m hy⟩⟩
      exact (SimpleGraph.mem_edgeSet _).1 (hωE ((openGraph_adj _ _ _).1 hxy).1)
    · -- `b'` is within `15r` of `cen b`, and `a ∼ b'`
      subst hte
      have htgt : tgt e = e.1 + stepVec e.2 := rfl
      rw [htgt]
      have hab1 := abs_sub_le_one_of_adj hab (S.C.pax i)
      have hb'c : |b' (S.C.pax i) - 20 * S.C.r * (e.1 + stepVec e.2) i| ≤ 15 * S.C.r := by
        rcases Finset.mem_union.1 hb' with h | h
        · obtain ⟨⟨hl1, hl2⟩, ht1, ht2⟩ := S.C.planar_of_mem_sBox h
          by_cases hi : i = e.2.1
          · subst hi
            have hta : (e.1 + stepVec e.2) e.2.1 = e.1 e.2.1 + sgOf e.2 := by
              rw [Pi.add_apply, stepVec_apply_fst]
            rw [hta, abs_le]
            rcases sgOf_sign e.2 with hs | hs <;> rw [hs] at hl1 hl2 ⊢ <;> constructor <;> nlinarith
          · have hi' : i = oth e.2.1 := eq_oth_of_ne hi
            subst hi'
            have hta : (e.1 + stepVec e.2) (oth e.2.1) = e.1 (oth e.2.1) := by
              rw [Pi.add_apply, stepVec_apply_oth, add_zero]
            rw [hta, abs_le]; constructor <;> linarith
        · have := S.C.planar_of_mem_cIcc h i
          push_cast at this
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
      have := abs_sub_abs_le_abs_sub (20 * (S.C.r : ℤ) * (e.1 + stepVec e.2) i - a (S.C.pax i))
        (20 * S.C.r * (e.1 + stepVec e.2) i - b' (S.C.pax i))
      have e1 : 20 * (S.C.r : ℤ) * (e.1 + stepVec e.2) i - a (S.C.pax i) - (20 * S.C.r * (e.1 + stepVec e.2) i - b' (S.C.pax i)) =
          b' (S.C.pax i) - a (S.C.pax i) := by ring
      rw [e1] at this
      rw [abs_sub_comm] at hb'c
      linarith
  by_contra hfin
  have hClfin : Cl.Finite := Set.not_infinite.1 hfin
  have hF : (⋃ a ∈ Cl, {b : Site 2 | ∀ i : Fin 2, |20 * (S.C.r : ℤ) * b i - a (S.C.pax i)| ≤ 16 * S.C.r}).Finite :=
    hClfin.biUnion fun a _ => S.finite_setOf_near a
  refine hinf ((hF.union (Set.finite_singleton 0)).subset fun b hb => ?_)
  by_cases hb0 : b = 0
  · exact Or.inr hb0
  · obtain ⟨a, ha, hnr⟩ := hnear b hb hb0
    exact Or.inl (Set.mem_biUnion ha hnr)

variable (S) in
/-- **Percolation in the slab**: if the scheme is lawful with `ε ≤ 2⁻³²`, `p > 0` and `δ ≤ 1`, then
`θ_{slab}(0, p) > 0` (with probability `≥ P_p(A₀)/3 > 0` the macro-cluster is infinite).
[cite: KozmaNitzan2024, §4 pp. 25–27 (proof of Theorem 6)] -/
theorem theta_slab_pos {ε : ℝ} (hL : S.scheme.Lawful (zdGraph d) S.p ε) (hε : ε ≤ (1 / 2) ^ 32)
    (hp0 : 0 < (S.p : ℝ)) (hδc : S.δc ≤ 1) :
    0 < theta ((zdGraph d).induce S.slab) ⟨0, S.zero_mem_slab⟩ S.p := by
  have hsub : initEvent S.scheme ∩ {ω | (S.scheme.occFinal ω).Infinite} ⊆
      percolatesVia (withinGraph (zdGraph d) S.slab) (0 : Site d) ∪ {ω | ¬ω ⊆ (zdGraph d).edgeSet} := by
    rintro ω ⟨hA, hinf⟩
    by_cases hωE : ω ⊆ (zdGraph d).edgeSet
    · exact Or.inl (mem_percolatesVia_of_infinite hδc hωE hA hinf)
    · exact Or.inr hωE
  have h3 := HSiteScheme.measureReal_le_three_mul_of_subset hL hε hsub
  have hU : (↑S.scheme.U₀ : Set (Sym2 (Site d))) ⊆ (zdGraph d).edgeSet := fun x hx =>
    (mem_edgesIn_iff.1 (Finset.mem_coe.1 hx)).1
  have hA0 := HSiteScheme.initEvent_pos (p := S.p) hU hp0
  have hN0 : (bondPercolation (zdGraph d) S.p).real {ω | ¬ω ⊆ (zdGraph d).edgeSet} = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    left
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [(ProbabilityTheory.setBernoulli_ae_subset :
      ∀ᵐ ω ∂(bondPercolation (zdGraph d) S.p), ω ⊆ (zdGraph d).edgeSet)] with ω hω using fun h => h hω
  have hUn := measureReal_union_le (μ := bondPercolation (zdGraph d) S.p)
    (percolatesVia (withinGraph (zdGraph d) S.slab) (0 : Site d)) {ω | ¬ω ⊆ (zdGraph d).edgeSet}
  rw [hN0, add_zero] at hUn
  rw [theta_induce_eq_real_percolatesVia]
  nlinarith [hA0, h3, hUn]

/-! ## (32) at the origin from hittability -/

variable (S) in
/-- **(32) for `w = 0`, from the hittability of the elongated geometry of aspect `6` at scale `3r`**
("our definition of `m₂` implies `P(M_{(0,0)} ↔^{Q_{(0,0)} ∪ E_{(0,0),v}} M_v) > 1 - δ` … positively
correlated [with] the event that all edges of `Q_{(0,0)}` are open", p. 28): under the lattice weighting
with the edges of `Q_0` wired open, `0` is joined to `M_v` inside `Q_0 ∪ E_{0,v}` with probability
`> 1 - δ`. [cite: KozmaNitzan2024, §4 p. 28 ((32) for w = 0)] -/
theorem hQ0_of_hit (du : MDir)
    (hhit : 1 - S.δc < (bondPercolation (zdGraph d) S.p).real
      (linkIn (↑((elongGeom (S.C.axOf du) (σu du) 6 (by norm_num)).Qset (3 * S.C.r) 0)) (box d (3 * S.C.r))
        ((elongGeom (S.C.axOf du) (σu du) 6 (by norm_num)).Fset (3 * S.C.r) 0))) :
    1 - S.δc < (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real
      (⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
        openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t) := by
  set g := elongGeom (S.C.axOf du) (σu du) 6 (by norm_num) with hg
  have hσ := sgOf_sign du
  have hr1 : (1 : ℤ) ≤ S.C.r := by exact_mod_cast S.C.r_pos
  -- geometry
  have hQset : g.Qset (3 * S.C.r) 0 ⊆ S.C.Q 0 ∪ S.C.Ewv 0 du := by
    intro y hy
    have hy' : y ∈ S.C.bigD 0 du := by
      rw [hg, elongGeom_Qset_eq, σu_val] at hy
      rw [Cells.bigD, S.C.cen_zero]
      refine sBox_mono hσ 0 ?_ ?_ ?_ hy <;> push_cast <;> linarith
    rcases S.C.mem_Q_or_Efar_of_mem_bigD hy' with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (S.C.Efar_subset_Ewv _ _ h)
  have hFset : g.Fset (3 * S.C.r) 0 ⊆ S.C.M ((0 : Site 2) + stepVec du) := by
    intro y hy
    rw [hg, elongGeom_Fset_eq, σu_val, mem_sBox_iff hσ] at hy
    obtain ⟨⟨h1, h2⟩, ht⟩ := hy
    push_cast at h1 h2 ht
    rw [Cells.M, mem_cIcc_iff]
    intro i
    rw [S.C.cen_add_stepVec, S.C.cen_zero]
    push_cast
    by_cases hi : i = S.C.axOf du
    · subst hi
      rw [if_pos rfl]
      have hsq := sign_mul_self hσ
      have hb : -(3 * (S.C.r : ℤ)) ≤ sgOf du * (y (S.C.axOf du) - ((0 : Site d) (S.C.axOf du) + 20 * S.C.r * sgOf du)) ∧
          sgOf du * (y (S.C.axOf du) - ((0 : Site d) (S.C.axOf du) + 20 * S.C.r * sgOf du)) ≤ 3 * S.C.r := by
        have e1 : sgOf du * (y (S.C.axOf du) - ((0 : Site d) (S.C.axOf du) + 20 * S.C.r * sgOf du)) =
            sgOf du * (y (S.C.axOf du) - (0 : Site d) (S.C.axOf du)) - 20 * S.C.r * (sgOf du * sgOf du) := by ring
        rw [e1, hsq]
        constructor <;> linarith
      have := abs_bounds_of_level hσ hb.1 hb.2
      constructor <;> linarith [this.1, this.2]
    · rw [if_neg hi]
      have := ht i hi
      simp only [Pi.zero_apply] at this ⊢
      constructor <;> linarith [this.1, this.2]
  have hbox : box d (3 * S.C.r) ⊆ S.C.Q 0 := by
    intro y hy
    rw [mem_box] at hy
    rw [Cells.Q, S.C.cen_zero, mem_cIcc_iff]
    intro i; have := hy i; simp only [Pi.zero_apply]; push_cast at this ⊢; constructor <;> linarith [this.1, this.2]
  have h0Q : (0 : Site d) ∈ S.C.Q 0 := by
    rw [Cells.Q, ← S.C.cen_zero]; exact center_mem_cIcc _ _
  -- probability
  set E1 := linkIn (↑(g.Qset (3 * S.C.r) 0) : Set (Site d)) (box d (3 * S.C.r)) (g.Fset (3 * S.C.r) 0) with hE1
  have hE1up : IsUpperSet E1 := by
    rw [hE1, linkIn_eq_biUnion]
    exact isUpperSet_iUnion₂ fun s _ => isUpperSet_iUnion₂ fun t _ => isUpperSet_openConnIn _ s t
  have hE1m : MeasurableSet E1 := measurableSet_linkIn _ _ _
  have hle : lattW d S.p ≤ pinW (lattW d S.p) ↑S.U₀ ↑S.U₀ := by
    intro x
    by_cases hx : x ∈ (↑S.U₀ : Set (Sym2 (Site d)))
    · rw [pinW_apply_of_mem_of_mem _ hx hx]; exact le_top
    · rw [pinW_apply_of_not_mem _ _ hx]
  have h1 : (bondPercolation (zdGraph d) S.p).real E1 ≤ (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real E1 := by
    rw [← prodBernoulli_lattW]; exact prodBernoulli_real_mono_of_isUpperSet hle hE1up hE1m
  have h2 : (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real E1 =
      (prodBernoulli (pinW (lattW d S.p) ↑S.U₀ ↑S.U₀)).real (E1 ∩ localCylinder (↑S.U₀ : Set (Sym2 (Site d))) ↑S.U₀) :=
    (prodBernoulli_pinW_real_inter_localCylinder _ S.U₀.finite_toSet.countable _ E1).symm
  have h3 : E1 ∩ localCylinder (↑S.U₀ : Set (Sym2 (Site d))) ↑S.U₀ ⊆
      ⋃ t ∈ (↑(S.C.M ((0 : Site 2) + stepVec du)) : Set (Site d)),
        openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 t := by
    rintro η ⟨hη, hcyl⟩
    obtain ⟨s, hs, t, ht, hst⟩ := mem_linkIn_iff.1 hη
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨t, Finset.mem_coe.2 (hFset ht), ?_⟩
    have hU₀open : ∀ x ∈ S.U₀, x ∈ η := fun x hx => (hcyl x (Finset.mem_coe.2 hx)).2 (Finset.mem_coe.2 hx)
    have h0s : η ∈ openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) 0 s := by
      rw [mem_openConnIn_iff_pathIn]
      have hp := exists_pathIn_Icc h0Q (hbox hs)
      refine (pathIn_congrGraph (fun x y hx hy hxy => ?_) hp).mono (Finset.coe_subset.2 Finset.subset_union_left)
      rw [openGraph_adj]
      refine ⟨hU₀open _ ?_, hxy.ne⟩
      rw [U₀, mem_edgesIn_iff]
      refine ⟨(SimpleGraph.mem_edgeSet _).2 hxy, fun z hz => ?_⟩
      rcases Sym2.mem_iff.1 hz with rfl | rfl
      · exact Finset.mem_coe.1 hx
      · exact Finset.mem_coe.1 hy
    have hst' : η ∈ openConnIn (↑(S.C.Q 0 ∪ S.C.Ewv 0 du) : Set (Site d)) s t := by
      rw [mem_openConnIn_iff_pathIn] at hst ⊢
      exact hst.mono (Finset.coe_subset.2 hQset)
    exact SlabCriticality.openConnIn_trans h0s hst'
  calc 1 - S.δc < (bondPercolation (zdGraph d) S.p).real E1 := hhit
    _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := measureReal_mono h3 (measure_ne_top _ _)

end KSch

/-! ## The constants and Theorem 6 -/

/-- [cite: KozmaNitzan2024, §4 Theorem 6 (pp. 25–31)] -/
theorem exists_KSch_theta_slab_pos_of_target [NeZero d] (hd : 3 ≤ d) (p : unitInterval)
    (hT : TargetProperty d p) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) :
    ∃ S : KSch d, S.p = p ∧ 0 < theta ((zdGraph d).induce S.slab) ⟨0, S.zero_mem_slab⟩ p := by
  -- `ε`
  set ε : ℝ := (1 / 2) ^ 32 with hε
  have hε0 : 0 < ε := by positivity
  -- Lemma 12 at `ε / 8`
  obtain ⟨δ, hδ0, m, hcorr⟩ := CData.corridorLemma_of_target p hT hp1 hθ (ε := ε / 8) (by positivity)
  set δc : ℝ := min δ (1 / 2) with hδc
  have hδc0 : 0 < δc := lt_min hδ0 (by norm_num)
  have hδc1 : δc ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδcδ : δc ≤ δ := min_le_left _ _
  -- Lemma 10 at `δc`
  obtain ⟨δ₂, hδ₂0, htgt0⟩ := hT hδc0
  set δ₂' : ℝ := min δ₂ 1 with hδ₂'
  have hδ₂'0 : 0 < δ₂' := lt_min hδ₂0 one_pos
  have hδ₂'1 : δ₂' ≤ 1 := min_le_right _ _
  have hδ₂'2 : δ₂' ≤ δ₂ := min_le_left _ _
  -- `K`
  obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 8 by positivity) (show 1 - δ₂' < 1 by linarith)
  set K : ℕ := max K₀ 20 with hK
  have hK20 : 20 ≤ K := le_max_right _ _
  have hKε : (1 - δ₂') ^ K + ε / 8 ≤ ε / 4 := by
    have : (1 - δ₂') ^ K ≤ (1 - δ₂') ^ K₀ := pow_le_pow_of_le_one (by linarith) (by linarith) (le_max_left _ _)
    linarith
  -- `R`
  have hK2 : 2 ≤ 2 * K := by omega
  obtain ⟨R, hR⟩ := htgt0 (elongList d (2 * K) (by omega)) (isHittable_of_mem_elongList_of_target p hT hp1 hθ (2 * K) hK2)
  -- the hittability thresholds for (32) at the origin
  set C₀ : Cells d := ⟨hd, 20, 1, le_rfl, le_rfl⟩ with hC₀
  have hhit6 : ∀ du : MDir, ∃ kℓ : ℕ, ∀ m', kℓ ≤ m' → ∀ ℓ, kℓ ≤ ℓ →
      1 - δc < (bondPercolation (zdGraph d) p).real
        (linkIn (↑((elongGeom (C₀.axOf du) (σu du) 6 (by norm_num)).Qset ℓ 0)) (box d m')
          ((elongGeom (C₀.axOf du) (σu du) 6 (by norm_num)).Fset ℓ 0)) := by
    intro du
    obtain ⟨k, ℓ₀, h⟩ := (isHittable_elongGeom_of_target p hT hp1 hθ (C₀.axOf du) (σu du) 6 (by norm_num)).hit δc hδc0
    exact ⟨max k ℓ₀, fun m' hm' ℓ hℓ => h m' ((le_max_left _ _).trans hm') ℓ ((le_max_right _ _).trans hℓ)⟩
  choose kℓ hkℓ using hhit6
  set kmax : ℕ := Finset.univ.sup kℓ with hkmax
  have hkmax' : ∀ du, kℓ du ≤ kmax := fun du => Finset.le_sup (f := kℓ) (Finset.mem_univ du)
  -- `s` and the scheme
  set s : ℕ := max (max (max 1 (2 * R)) m) kmax with hs
  have hs1 : 1 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hsR : 2 * R ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hsm : m ≤ s := le_trans (le_max_right _ _) (le_max_left _ _)
  have hsk : kmax ≤ s := le_max_right _ _
  set C : Cells d := ⟨hd, K, s, hK20, hs1⟩ with hCdef
  set S : KSch d := ⟨C, p, δc⟩ with hSdef
  refine ⟨S, rfl, ?_⟩
  have hsr : s ≤ C.r := by
    show s ≤ K * s
    exact Nat.le_mul_of_pos_left s (by omega)
  -- lawfulness
  have hL : S.scheme.Lawful (zdGraph d) p ε := by
    refine S.lawful (fun du => ?_) (fun h e hV => ?_)
    · refine S.hQ0_of_hit du (hkℓ du (3 * C.r) ?_ (3 * C.r) ?_) <;> linarith [hkmax' du]
    · refine KSch.fail_bound hV hε0.le hδ₂'1 (R := R) (fun T hT hTr hyp => ?_)
        (fun W Sfin D lo hi T o h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => ?_) hsR hKε
      · refine hcorr T hT ?_ (lt_of_le_of_lt (by show 1 - δ ≤ 1 - S.δc; linarith) hyp)
        rw [hTr]; exact hsm.trans hsr
      · exact hR W Sfin D lo hi T o h1 h2 h3 h4 h5 h6 h7 h8 h9
          (lt_of_le_of_lt (by show 1 - δ₂ ≤ 1 - δ₂'; linarith) h10)
  exact S.theta_slab_pos hL le_rfl hp0 hδc1

/-- **Theorem 6 of Kozma–Nitzan in `d ≥ 3`, slab form**: if Conjecture 3 holds, `0 < p < 1` and
`θ_{ℤ^d}(p) > 0`, then for the exploration process with suitable constants the origin percolates in
the slab `ℤ² × [-5r, 5r]^{d-2}` with positive probability. The constants (pp. 25–26): `ε = 2⁻³²`;
`δ, m` from Lemma 12 at `ε/8` (and `δ ≤ 1/2`); `δ₂` from Lemma 10 at `δ` (and `δ₂ ≤ 1`); `K ≥ 20` with
`(1 - δ₂)^K ≤ ε/8`; `R` from Lemma 10 for the elongated geometries of aspect `2K`; `s ≥ 2R, m` and the
hittability thresholds of the aspect-`6` geometries at `δ`; `r = Ks`.
[cite: KozmaNitzan2024, §4 Theorem 6 (pp. 25–31)] -/
theorem exists_KSch_theta_slab_pos [NeZero d] (hC : KozmaNitzan2024_conjecture3) (hd : 3 ≤ d)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) (0 : Site d) p) :
    ∃ S : KSch d, S.p = p ∧ 0 < theta ((zdGraph d).induce S.slab) ⟨0, S.zero_mem_slab⟩ p := by
  exact exists_KSch_theta_slab_pos_of_target hd p (targetProperty_of_conjecture3 hC p hp0 hp1 hθ) hp0 hp1 hθ

end KozmaNitzan

end Percolation.Literature

end
