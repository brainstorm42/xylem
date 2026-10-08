import Percolation.Literature.FlatDisjD
import Percolation.Util.Linter

/-!
# The flat gait, XIV–XV

This module gathers 2 consecutive parts of the flat-gait development, in order:
XIV: assembling disjointness, II — the forks, the later trunk, the branches ·
XV: assembling disjointness, III — the branches; all plates pairwise disjoint.
Part 1 follows; the later parts keep their own headers below.

# Part 1 (The flat gait, XIV): assembling disjointness, II — the forks, the later trunk, the branches

Continuing `FlatDisjD.lean` (Grimmett, *Percolation*,
2nd ed. (1999), §7.3 pp. 171–174, case `H < L`): the frames of the forks and of the continuing
trunk (`FlatInv.g1frame`, `FlatInv.cframe`), the profile of everything before the first fork seen
from its start (`FlatInv.far_beforeG1`: behind along the fork's kept coordinate, or — for the jog
side when the fork flips the jog's kept coordinate — far behind along the flipped one), and the
disjointness of the first fork and of the second trunk stretch from everything earlier
(`FlatInv.disj_seg7`, `FlatInv.disj_seg8`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174, (C), Fig. 7.11.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## Frames of the first trunk stretch, the first fork and the continuing trunk -/

/-- **The first trunk stretch, extended by `T₀`**, is a diagonal leg of the signs of `e`. [folklore] -/
theorem FlatInv.frame_T1 (hI : FlatInv hd Y a e τ st) (h6 : st.segs 6 ≠ []) :
    ∃ T₀, (st.segs 5).head? = some T₀ ∧ (st.segs 5).length = 2 ∧ legOf (st.segs 5) 1 = T₀.1 ∧
      DiagLeg hd Y e (dsg e) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 6 ++ [T₀]) ∧
      (∀ k, (hk : k < (st.segs 6).length) → legOf (st.segs 6 ++ [T₀]) (k + 1) = legOf (st.segs 6) k) ∧
      legOf (st.segs 6 ++ [T₀]) 0 = T₀.1 := by
  have hK6 : SegOK hd Y e τ (eJOf hd Y a e τ st) 6 (st.segs 6) (st.segs (startOf 6)) := hI.segOK 6
  simp only [startOf, Matrix.cons_val] at hK6
  obtain ⟨s, hs, hD6, hD60⟩ := hK6 h6
  obtain ⟨T₀, hT₀, hlen5, -⟩ := hI.frame_trunk h6
  have hsT : s = T₀ := by rw [hT₀] at hs; simpa using hs.symm
  subst hsT
  obtain ⟨tl5, hl5⟩ : ∃ tl, st.segs 5 = s :: tl := by
    rcases hl : st.segs 5 with _ | ⟨r0, tl⟩
    · rw [hl] at hT₀; simp at hT₀
    · rw [hl] at hT₀; simp only [List.head?_cons, Option.some.injEq] at hT₀; subst hT₀; exact ⟨tl, rfl⟩
  have htl5 : tl5.length = 1 := by rw [hl5] at hlen5; simp at hlen5; omega
  exact ⟨s, hT₀, hlen5, by rw [hl5]; exact legOf_head' htl5, diagLeg_snoc hD6 hD60, fun k hk => legOf_append_singleton_succ _ _ k,
    legOf_snoc_zero _ _⟩

/-- **The frame of the first fork**: the first trunk stretch has at least three plates, its head `r6`
is the extended stretch's last plate, of axis `1`, and the fork is the turn off it towards the first
branch. [folklore] -/
theorem FlatInv.g1frame (hI : FlatInv hd Y a e τ st) (h7 : st.segs 7 ≠ []) :
    ∃ r6, (st.segs 6).head? = some r6 ∧ 3 ≤ (st.segs 6).length ∧ ∃ T₀, (st.segs 5).head? = some T₀ ∧ (st.segs 5).length = 2 ∧
      legOf (st.segs 5) 1 = T₀.1 ∧
      DiagLeg hd Y e (dsg e) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 6 ++ [T₀]) ∧
      (∀ k, (hk : k < (st.segs 6).length) → legOf (st.segs 6 ++ [T₀]) (k + 1) = legOf (st.segs 6) k) ∧
      legOf (st.segs 6 ++ [T₀]) 0 = T₀.1 ∧
      legOf (st.segs 6 ++ [T₀]) ((st.segs 6 ++ [T₀]).length - 1) = r6.1 ∧ r6.1.a = pl hd 1 ∧
      Turn hd Y e (dsg e) (dsg (eB1 e)) 1 (legOf (st.segs 6 ++ [T₀]) ((st.segs 6 ++ [T₀]).length - 1)) (st.segs 7) := by
  obtain ⟨r6, hr6, h3, hax, hT⟩ := hI.frame_fork.1 h7
  have h6 : st.segs 6 ≠ [] := by intro h; rw [h] at h3; simp at h3
  obtain ⟨T₀, hT₀, hlen5, h51, hle, hsucc, hle0⟩ := hI.frame_T1 h6
  obtain ⟨tl6, hl6⟩ : ∃ tl, st.segs 6 = r6 :: tl := by
    rcases hl : st.segs 6 with _ | ⟨r0, tl⟩
    · rw [hl] at hr6; simp at hr6
    · rw [hl] at hr6; simp only [List.head?_cons, Option.some.injEq] at hr6; subst hr6; exact ⟨tl, rfl⟩
  have hlast := legOf_append_singleton_last hl6 T₀
  have hp1 : p1 e = 1 := by unfold p1 keepIdx; rw [(flipIdx_eB e).1]; rfl
  rw [hp1] at hax hT
  exact ⟨r6, hr6, h3, T₀, hT₀, hlen5, h51, hle, hsucc, hle0, hlast, hax, by rw [hlast]; exact hT⟩

/-- **The frame of the continuing trunk** after the first fork: the second and third stretches,
extended by the first stretch's head `r6`, form a diagonal leg of the signs of `e` off `r6`, first
index `0`. [folklore] -/
theorem FlatInv.cframe (hI : FlatInv hd Y a e τ st) (h8 : st.segs 8 ≠ []) :
    ∃ r6, (st.segs 6).head? = some r6 ∧ DiagLeg hd Y e (dsg e) none 1 (st.segs 10 ++ st.segs 8 ++ [r6]) ∧
      legOf (st.segs 10 ++ st.segs 8 ++ [r6]) 0 = r6.1 ∧
      (∀ k, (hk : k < (st.segs 8).length) → legOf (st.segs 10 ++ st.segs 8 ++ [r6]) (k + 1) = legOf (st.segs 8) k) ∧
      (∀ k, (hk : k < (st.segs 10).length) → legOf (st.segs 10 ++ st.segs 8 ++ [r6]) ((st.segs 8).length + 1 + k) = legOf (st.segs 10) k) := by
  have hK8 : SegOK hd Y e τ (eJOf hd Y a e τ st) 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
  simp only [startOf, Matrix.cons_val] at hK8
  obtain ⟨r6, hr6, q8, hD8, hD80⟩ := hK8 h8
  simp only [Option.mem_def] at hr6
  have h7 : st.segs 7 ≠ [] := by
    have := hI.order 8 7 (by decide) h8; intro h; rw [h] at this; simp [complete'] at this
  obtain ⟨r6', hr6', -, hax, -⟩ := hI.frame_fork.1 h7
  have hr66 : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
  rw [hr66] at hax
  -- the first index: `r6` has axis `1 = pl (oth q8)`
  have hp1 : p1 e = 1 := by unfold p1 keepIdx; rw [(flipIdx_eB e).1]; rfl
  have hq : oth q8 = 1 := by
    have h1 := hD80.srcAxis
    rw [hp1] at hax; rw [hax] at h1; exact (pl_injective hd h1).symm
  have hE8 : DiagLeg hd Y e (dsg e) none 1 (st.segs 8 ++ [r6]) := by rw [← hq]; exact diagLeg_snoc hD8 hD80
  refine ⟨r6, hr6, ?_, by rw [List.append_assoc, legOf_append_of_lt _ _ (by simp), legOf_snoc_zero],
    fun k hk => by rw [List.append_assoc, legOf_append_of_lt _ _ (by simp; omega), legOf_append_singleton_succ],
    fun k hk => by rw [List.append_assoc, show (st.segs 8).length + 1 + k = (st.segs 8 ++ [r6]).length + k by simp, legOf_append_of_ge]⟩
  by_cases h10 : st.segs 10 = []
  · rw [h10, List.nil_append]; exact hE8
  · have hK10 : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
    simp only [startOf, Matrix.cons_val] at hK10
    obtain ⟨s10, hs10, q10, hD10, hD100⟩ := hK10 h10
    obtain ⟨r8, tl8, hl8, hh8⟩ := exists_head_of_ne_nil h8
    rw [hh8] at hs10; simp only [Option.mem_def, Option.some.injEq] at hs10; subst hs10
    rw [List.append_assoc]
    refine diagLeg_append hD10 hE8 ?_
    rw [legOf_append_singleton_last hl8]; exact hD100

/-! ## Everything before the first fork, seen from its start -/

omit [NeZero d] in
/-- The axis class only depends on the sign at the index. [folklore] -/
theorem AxCl.congr {σ σ' : Fin 2 → ℤˣ} {i : Fin 2} (h : σ' i = σ i) {X : BrickPos d} (hX : AxCl hd σ i X) : AxCl hd σ' i X := by
  rcases hX with hX | ⟨ha, hs⟩
  · exact Or.inl hX
  · exact Or.inr ⟨ha, by rw [hs, h]⟩

/-- The sign relations of the forks. [folklore] -/
theorem flip_keep_B (e : MDir) :
    (dsg (eB1 e) (oth 1) = -dsg e (oth 1) ∧ dsg (eB1 e) 1 = dsg e 1) ∧ (dsg (eB2 e) (oth 0) = -dsg e (oth 0) ∧ dsg (eB2 e) 0 = dsg e 0) := by
  have h1 := dsg_lat e (!e.2); have h2 := dsg_lat e e.2
  have f1 : flipIdx e (eB1 e) = 0 := (flipIdx_eB e).1
  have f2 : flipIdx e (eB2 e) = 1 := (flipIdx_eB e).2
  unfold keepIdx at h1 h2
  change dsg (eB1 e) (oth (flipIdx e (eB1 e))) = dsg e (oth (flipIdx e (eB1 e))) ∧ dsg (eB1 e) (flipIdx e (eB1 e)) = -dsg e (flipIdx e (eB1 e)) at h1
  change dsg (eB2 e) (oth (flipIdx e (eB2 e))) = dsg e (oth (flipIdx e (eB2 e))) ∧ dsg (eB2 e) (flipIdx e (eB2 e)) = -dsg e (flipIdx e (eB2 e)) at h2
  rw [f1] at h1; rw [f2] at h2
  exact ⟨⟨h1.2, h1.1⟩, ⟨h2.2, h2.1⟩⟩

/-- **Profile of everything before the first fork, from its start `r6`**: a plate of the extended
first stretch (by index); or far behind `r6` along the fork's kept coordinate `1`; or — a plate of
the jog side when the jog's kept coordinate is `0` — in the axis class along `0` and at least `U`
behind the jog's head along `0`, the jog's head being at least `2U + H + 2m + 3` behind `r6`
there. [folklore] -/
theorem FlatInv.far_beforeG1 (hI : FlatInv hd Y a e τ st) (hY : Y.OK)
    {T₀ : BrickRec d} (hlen5 : (st.segs 5).length = 2) (h51 : legOf (st.segs 5) 1 = T₀.1)
    (hle : DiagLeg hd Y e (dsg e) none (oth (pJ e (eJOf hd Y a e τ st))) (st.segs 6 ++ [T₀])) (h3 : 3 ≤ (st.segs 6).length)
    {x : BrickRec d} (hx : ((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) :
    (∃ k < (st.segs 6 ++ [T₀]).length, x.1 = legOf (st.segs 6 ++ [T₀]) k) ∨
      FarB hd Y (dsg e) 1 (legOf (st.segs 6 ++ [T₀]) ((st.segs 6 ++ [T₀]).length - 1)) x.1 ∨
      (pJ e (eJOf hd Y a e τ st) = 0 ∧ AxCl hd (dsg e) 0 x.1 ∧ ∃ B : ℤ, ox hd (dsg e) 0 x.1.b + Y.U ≤ B ∧
        B + 2 * Y.U + Y.H + 2 * Y.m + 3 ≤ ox hd (dsg e) 0 (legOf (st.segs 6 ++ [T₀]) ((st.segs 6 ++ [T₀]).length - 1)).b) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  set ej := eJOf hd Y a e τ st with hej
  obtain ⟨hflipJ, hkeepJ, hflipT⟩ := flip_keep_J hd Y a e τ st
  rw [← hej] at hflipJ hkeepJ hflipT
  have h5ne : st.segs 5 ≠ [] := by intro h; rw [h] at hlen5; simp at hlen5
  obtain ⟨γ, hγ, hlen3, h31, hJE, h2, hsuccJ, hJ0, hax, hsx, hT⟩ := hI.tframe h5ne
  rw [← hej] at hJE hax hsx hT
  set le := st.segs 6 ++ [T₀] with hledef
  set n := le.length - 1 with hn
  have hlen : le.length = (st.segs 6).length + 1 := by simp [hledef]
  have hn3 : 3 ≤ n := by omega
  have hle0 : legOf le 0 = legOf (st.segs 5) 1 := by rw [hledef, legOf_snoc_zero, h51]
  -- the kept coordinate `pJ` advances: `rJ + H + 1 + U + m + 1 ≤ le[k+1]`
  set rJ := legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1) with hrJ
  have hkept : ∀ k, (hk : k + 1 < le.length) → ox hd (dsg e) (pJ e ej) rJ.b + ((Y.H : ℤ) + 1) + Y.U + Y.m + 1 ≤ ox hd (dsg e) (pJ e ej) (legOf le (k + 1)).b := by
    intro k hk
    have := (leg_after_turn_kept hY hT hlen5 hle hle0 hk).1
    have oxe : ∀ b : Site d, ox hd (dsg ej) (pJ e ej) b = ox hd (dsg e) (pJ e ej) b := fun b => by unfold ox; rw [hkeepJ]
    rw [oxe, oxe] at this; exact this
  -- both coordinates are monotone along `le`
  have hmono : ∀ (i : Fin 2) k, (hk : k < le.length) → ox hd (dsg e) i (legOf le k).b ≤ ox hd (dsg e) i (legOf le n).b :=
    fun i k hk => (hle.mono (k := k) (k' := n) (by omega) (by omega) i).1
  -- the turn back: top stacking `r'_T = legOf (segs 5) 0`, hop `T₀ = le[0]`
  have hT0 := hT.h0 (by omega); have hT1 := hT.h1 (by omega)
  -- segment 5: `T₀` is on `le`, `r'_T` is far behind along `1`
  rcases hx with hx | hx
  swap
  · obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [hlen5] at hm
    interval_cases m
    · -- the top stacking `r'_T`: thin along `pJ` at `rJ + H + 1`, wide along `oth pJ` pushed forward
      right; left; rw [← hmx]
      have hface : ox hd (dsg e) (pJ e ej) (legOf (st.segs 5) 0).b = ox hd (dsg e) (pJ e ej) rJ.b + ((Y.H : ℤ) + 1) := by
        unfold ox; rw [hT0.face, hT.sSign, hkeepJ, mul_add, ← mul_assoc, units_sq, one_mul]
      rcases Fin.exists_fin_two.1 ⟨pJ e ej, rfl⟩ with hp0 | hp1
      · -- `pJ = 0`: wide along `1 = oth pJ`; `T₀` is `+U` along `1`, then `le[1]` drifts, `le[2]` is `+U`
        have ho : oth (pJ e ej) = 1 := by rw [hp0]; rfl
        have hT0f : ox hd (dsg e) 1 (legOf le 0).b = ox hd (dsg e) 1 (legOf (st.segs 5) 0).b + Y.U := by
          rw [hle0]; unfold ox; rw [← ho, hT1.face, mul_add, ← mul_assoc, units_sq, one_mul]
        have hd1 := ((hle.step_either (k := 0) (by omega) 1).2 (by
          rw [show (0:ℕ) + 1 = 1 from rfl, show qAt (oth (pJ e ej)) 1 = qAt (oth (pJ e ej)) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth, hp0]; decide)).1
        have hs2 := (hle.step (k := 1) (by omega)).1
        rw [show (1:ℕ) + 1 = 2 from rfl, show qAt (oth (pJ e ej)) 2 = qAt (oth (pJ e ej)) (0 + 2) from rfl, qAt_add_two, qAt_zero, ho] at hs2
        have hm2 := hmono 1 2 (by omega)
        refine ⟨Or.inl (by rw [hT0.axis, hp0]; exact pl_ne_pl hd (by decide)), ?_, fun _ => ?_⟩ <;> linarith
      · -- `pJ = 1`: thin along `1` with the sign of `e`, `U` behind `le[1]`
        have hk1 := hkept 0 (by omega)
        have hm1 := hmono 1 1 (by omega)
        rw [hp1] at hface hk1 hT0
        refine ⟨Or.inr ⟨hT0.axis, by rw [hT0.sign, hT.sSign, hkeepJ, hp1]⟩, by linarith, fun hw => absurd hT0.axis hw⟩
    · left; exact ⟨0, by omega, by rw [← hmx, hle0]⟩
  -- segments 0–4: far behind `rJ` along `pJ`, or on the extended jog
  have hfar := hI.far_beforeT hY h5ne hlen3 h31 (by rw [← hej]; exact hJE) hx
  rw [← hej, ← hrJ] at hfar
  rcases Fin.exists_fin_two.1 ⟨pJ e ej, rfl⟩ with hp0 | hp1
  · -- `pJ = 0`: the jog's head `rJ` is wide along `1` and far behind `r6`; everything else goes by `0`
    have ho : oth (pJ e ej) = 1 := by rw [hp0]; rfl
    -- `rJ` along `1`: behind the top stacking (pushed forward), which is `U` behind `T₀`, …
    have hpush : ox hd (dsg e) 1 rJ.b ≤ ox hd (dsg e) 1 (legOf (st.segs 5) 0).b := by
      have := hT0.push.1; rw [ho] at this; unfold ox
      linarith [mul_sub (dsg e 1 : ℤ) ((legOf (st.segs 5) 0).b (pl hd 1)) (rJ.b (pl hd 1))]
    have hT0f : ox hd (dsg e) 1 (legOf le 0).b = ox hd (dsg e) 1 (legOf (st.segs 5) 0).b + Y.U := by
      rw [hle0]; unfold ox; rw [← ho, hT1.face, mul_add, ← mul_assoc, units_sq, one_mul]
    have hd1 := ((hle.step_either (k := 0) (by omega) 1).2 (by
      rw [show (0:ℕ) + 1 = 1 from rfl, show qAt (oth (pJ e ej)) 1 = qAt (oth (pJ e ej)) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth, hp0]; decide)).1
    have hs2 := (hle.step (k := 1) (by omega)).1
    rw [show (1:ℕ) + 1 = 2 from rfl, show qAt (oth (pJ e ej)) 2 = qAt (oth (pJ e ej)) (0 + 2) from rfl, qAt_add_two, qAt_zero, ho] at hs2
    have hm2 := hmono 1 2 (by omega)
    -- along `0`: `le[1] = T₀ + U`, `le[2]` drifts, `le[3] = + U`
    have hs1 := (hle.step (k := 0) (by omega)).1
    rw [show (0:ℕ) + 1 = 1 from rfl, show qAt (oth (pJ e ej)) 1 = qAt (oth (pJ e ej)) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth, hp0] at hs1
    have hd2 := ((hle.step_either (k := 1) (by omega) 0).2 (by
      rw [show (1:ℕ) + 1 = 2 from rfl, show qAt (oth (pJ e ej)) 2 = qAt (oth (pJ e ej)) (0 + 2) from rfl, qAt_add_two, qAt_zero, ho]; decide)).1
    have hs3 := (hle.step (k := 2) (by omega)).1
    rw [show (2:ℕ) + 1 = 3 from rfl, show qAt (oth (pJ e ej)) 3 = qAt (oth (pJ e ej)) (1 + 2) from rfl, qAt_add_two,
      show qAt (oth (pJ e ej)) 1 = qAt (oth (pJ e ej)) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth, hp0] at hs3
    have hm3 := hmono 0 3 (by omega)
    have hT0p : ox hd (dsg e) 0 (legOf le 0).b = ox hd (dsg e) 0 rJ.b + ((Y.H : ℤ) + 1) +
        (ox hd (dsg e) 0 (legOf le 0).b - ox hd (dsg e) 0 (legOf (st.segs 5) 0).b) := by
      have hface : ox hd (dsg e) 0 (legOf (st.segs 5) 0).b = ox hd (dsg e) 0 rJ.b + ((Y.H : ℤ) + 1) := by
        unfold ox; rw [← hp0, hT0.face, hT.sSign, hkeepJ, mul_add, ← mul_assoc, units_sq, one_mul]
      linarith
    have hdr0 : (Y.m : ℤ) + 1 ≤ ox hd (dsg e) 0 (legOf le 0).b - ox hd (dsg e) 0 (legOf (st.segs 5) 0).b := by
      have := hT1.drift.1; rw [oth_oth, hp0] at this; rw [hle0]; unfold ox
      linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 5) 1).b (pl hd 0)) ((legOf (st.segs 5) 0).b (pl hd 0))]
    have hB : ox hd (dsg e) 0 rJ.b + 2 * Y.U + Y.H + 2 * Y.m + 3 ≤ ox hd (dsg e) 0 (legOf le n).b := by linarith
    rcases hfar with hf | ⟨k, hk, hkx⟩
    · -- far behind `rJ` along `0`
      obtain ⟨hcl, hf1, -⟩ := hf
      right; right
      refine ⟨hp0, ?_, ox hd (dsg e) 0 rJ.b, ?_, hB⟩
      · rw [hp0] at hcl; exact AxCl.congr (by rw [← hp0, hkeepJ]) hcl
      · have oxe : ox hd (dsg ej) (pJ e ej) x.1.b = ox hd (dsg e) 0 x.1.b := by unfold ox; rw [hkeepJ, hp0]
        have oxe' : ox hd (dsg ej) (pJ e ej) rJ.b = ox hd (dsg e) 0 rJ.b := by unfold ox; rw [hkeepJ, hp0]
        rw [oxe, oxe'] at hf1; exact hf1
    · -- on the extended jog: the head by `1`, the rest by `0`
      rcases hJE.prof_feed hY hax hk with hlast | ⟨_, ha, hs, hox, -⟩ | ⟨_, hcl, h1, -⟩
      · right; left
        rw [hkx, hlast, ← hrJ]
        refine ⟨Or.inl (by rw [hax, hp0]; exact pl_ne_pl hd (by decide)), by linarith, fun _ => by linarith⟩
      · right; right
        refine ⟨hp0, Or.inl (by rw [hkx, ha, ho]; exact pl_ne_pl hd (by decide)), ox hd (dsg e) 0 rJ.b, ?_, hB⟩
        have oxe : ∀ b : Site d, ox hd (dsg ej) (pJ e ej) b = ox hd (dsg e) 0 b := fun b => by unfold ox; rw [hkeepJ, hp0]
        rw [oxe, oxe, ← hrJ] at hox; rw [hkx]; linarith
      · right; right
        refine ⟨hp0, ?_, ox hd (dsg e) 0 rJ.b, ?_, hB⟩
        · rw [hkx]; rw [hp0] at hcl; exact AxCl.congr (by rw [← hp0, hkeepJ]) hcl
        · have oxe : ∀ b : Site d, ox hd (dsg ej) (pJ e ej) b = ox hd (dsg e) 0 b := fun b => by unfold ox; rw [hkeepJ, hp0]
          rw [oxe, oxe, ← hrJ] at h1; rw [hkx]; linarith
  · -- `pJ = 1`: everything far behind `rJ` along `1`, which is far behind `r6`
    have hk1 := hkept 0 (by omega)
    have hm1 := hmono 1 1 (by omega)
    rw [hp1] at hk1
    have hH0 : (0 : ℤ) ≤ Y.H := by positivity
    have hrJle : ox hd (dsg e) 1 rJ.b + Y.U ≤ ox hd (dsg e) 1 (legOf le n).b := by linarith
    right; left
    rcases hfar with hf | ⟨k, hk, hkx⟩
    · rw [hp1] at hf; exact (FarB.congr (by rw [← hp1, hkeepJ]) hf).mono (by linarith)
    · rw [hkx]
      have := farB_feed_of_next hY hJE (by rw [hax, hp1]) (s' := legOf le n) (by rw [hsx, hp1])
        (by have oxe : ∀ b : Site d, ox hd (dsg ej) 1 b = ox hd (dsg e) 1 b := fun b => by unfold ox; rw [← hp1, hkeepJ]
            rw [oxe, oxe, ← hrJ]; exact hrJle) hk
      exact FarB.congr (by rw [← hp1, hkeepJ]) this

/-! ## The first fork and the second trunk stretch against everything earlier -/

/-- **First fork against everything earlier.** [folklore] -/
theorem FlatInv.disj_seg7 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : (((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6)
    (hy : y ∈ st.segs 7) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨⟨hflip1, hkeep1⟩, -⟩ := flip_keep_B e
  obtain ⟨r6, hr6, h3, T₀, hT₀, hlen5, h51, hle, hsucc, hle0, hlast, hax, hT⟩ := hI.g1frame (List.ne_nil_of_mem hy)
  obtain ⟨jj, hjj, hjy⟩ := exists_legOf_of_mem hy
  rw [← hjy]
  have hjj2 : jj < 2 := by have := hT.len; omega
  rcases hx with hx | hx
  · rcases hI.far_beforeG1 hY hlen5 h51 hle h3 hx with ⟨k, hk, hkx⟩ | hfar | ⟨hp0, hcl, B, hB1, hB2⟩
    · rw [hkx]; exact disj_feed_turn hY hle hT hflip1 hk hjj
    · exact disj_far_turn hY hT hfar hjj
    · interval_cases jj
      · refine disj_turntop_flipped hY hT hjj hflip1 hcl ⟨fun _ => ?_, fun _ => ?_⟩ <;>
          simp only [show oth (1 : Fin 2) = 0 from rfl] <;> linarith
      · refine disj_turnhop_flipped hY hT hjj hflip1 hcl ⟨fun _ => ?_, fun _ => ?_⟩ <;>
          simp only [show oth (1 : Fin 2) = 0 from rfl] <;> nlinarith [hB1, hB2, hHU, hLpe, hUe, hm0, hmH]
  · obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc m hm]
    exact disj_feed_turn hY hle hT hflip1 (by simp; omega) hjj

/-- **Second trunk stretch against everything earlier.** [folklore] -/
theorem FlatInv.disj_seg8 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : ((((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6) ∨ x ∈ st.segs 7)
    (hy : y ∈ st.segs 8) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨⟨hflip1, hkeep1⟩, -⟩ := flip_keep_B e
  have h8 : st.segs 8 ≠ [] := List.ne_nil_of_mem hy
  have h7 : st.segs 7 ≠ [] := by
    have := hI.order 8 7 (by decide) h8; intro h; rw [h] at this; simp [complete'] at this
  obtain ⟨r6, hr6, h3, T₀, hT₀, hlen5, h51, hle, hsucc, hle0, hlast, hax, hT⟩ := hI.g1frame h7
  obtain ⟨r6', hr6', hC, hc0, hsucc8, -⟩ := hI.cframe h8
  have hr66 : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
  rw [hr66] at hC hc0 hsucc8
  -- the turn back and the full trunk, for the earlier structures
  have h5ne : st.segs 5 ≠ [] := by intro h; rw [h] at hlen5; simp at hlen5
  obtain ⟨γ, hγ, hlen3, h31, hJE, h2, hsuccJ, hJ0, haxJ, hsxJ, hTT⟩ := hI.tframe h5ne
  obtain ⟨T₀', hT₀', -, hTE⟩ := hI.frame_trunk (by intro h; rw [h] at h3; simp at h3)
  have hTT0 : T₀' = T₀ := by rw [hT₀] at hT₀'; simpa using hT₀'.symm
  rw [hTT0] at hTE
  have hTE' : st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀] = (st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀]) := by simp
  rw [hTE'] at hTE
  have hTE0 : legOf ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])) 0 = legOf (st.segs 5) 1 := by
    rw [legOf_append_of_lt _ _ (by simp), hle0, h51]
  -- `y` as a plate of the continuing trunk and of the full trunk
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  have hyc : y.1 = legOf (st.segs 10 ++ st.segs 8 ++ [r6]) (k + 1) := by rw [hsucc8 k hk, hky]
  have hyT : y.1 = legOf ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])) ((st.segs 6 ++ [T₀]).length + k) := by
    rw [legOf_append_of_ge, legOf_append_of_lt _ _ hk, hky]
  have hkc : k + 1 < (st.segs 10 ++ st.segs 8 ++ [r6]).length := by simp; omega
  have hkT : (st.segs 6 ++ [T₀]).length + k < ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])).length := by simp; omega
  rcases hx with ((hx | hx) | hx) | hx
  · -- the jog side and the entry: far behind the jog's head, or on the extended jog
    rw [hyT, show (st.segs 6 ++ [T₀]).length + k = ((st.segs 6 ++ [T₀]).length + k - 1) + 1 by simp; omega]
    exact disj_farfeed_legafter hY hJE hTT hlen5 hTE hTE0 (hI.far_beforeT hY h5ne hlen3 h31 hJE hx)
      (by simp; omega)
  · -- the turn back: the top stacking and `T₀`
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, hyT]
    rw [hlen5] at hm
    interval_cases m
    · rw [show (st.segs 6 ++ [T₀]).length + k = ((st.segs 6 ++ [T₀]).length + k - 1) + 1 by simp; omega]
      exact disj_leg_after_turn_top hY hTT hlen5 hTE hTE0 (by simp; omega)
    · rw [← hTE0]; exact hTE.disj hY (by simp) hkT
  · -- the first stretch: on the full trunk
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc m hm, hyT, ← legOf_append_of_lt (st.segs 10 ++ st.segs 8) (st.segs 6 ++ [T₀]) (k := m + 1) (by simp; omega)]
    exact hTE.disj hY (by simp; omega) hkT
  · -- the fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, hyc]
    have hm2 : m < 2 := by have := hT.len; omega
    rw [hlast] at hT
    interval_cases m
    · exact disj_cont_forktop hY hT hm hflip1 hC hc0 hkc
    · exact disj_cont_forkhop hY hT hm hflip1 hC hc0 hkc

/-! ## Profiles along the continuing trunk and along a branch -/

section Profiles

variable {σ : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {c je : List (BrickRec d)}

/-- **The continuing leg lies above its start along the flipped coordinate**: every plate after the
start `s = legOf c 0` (axis `p`) of a diagonal leg `c` of signs `σ` is, along `oth p` read along
`σ`, thin-forwards at least `U` on, or wide more than `U` on. [folklore] -/
theorem cont_above (hY : Y.OK) (hC : DiagLeg hd Y e σ none p c) (hc0 : legOf c 0 = s) {k : ℕ} (hk : k + 1 < c.length) :
    ((legOf c (k + 1)).a = pl hd (oth p) ∧ (legOf c (k + 1)).s = σ (oth p) ∧ ox hd σ (oth p) s.b + Y.U ≤ ox hd σ (oth p) (legOf c (k + 1)).b) ∨
      ((legOf c (k + 1)).a ≠ pl hd (oth p) ∧ ox hd σ (oth p) s.b + Y.U < ox hd σ (oth p) (legOf c (k + 1)).b) := by
  obtain ⟨hU, -, -, -, -, -, -, -, hm0⟩ := hY.facts
  have e1 : qAt p 1 = oth p := by rw [show qAt p 1 = qAt p (0 + 1) from rfl, qAt_succ, qAt_zero]
  have e2 : qAt p 2 = p := by rw [show qAt p 2 = qAt p (0 + 2) from rfl, qAt_add_two, qAt_zero]
  have hst1 := (hC.step (k := 0) (by omega)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, e1, hc0] at hst1
  obtain ⟨hak, hsk⟩ := hC.axis_sign (k := k + 1) hk
  by_cases hax : (legOf c (k + 1)).a = pl hd (oth p)
  · have hs' : (legOf c (k + 1)).s = σ (oth p) := by rw [hak] at hax; have := pl_injective hd hax; rw [hsk, this]
    refine Or.inl ⟨hax, hs', ?_⟩
    have hmono := (hC.mono (k := 1) (k' := k + 1) (by omega) hk (oth p)).1
    linarith
  · refine Or.inr ⟨hax, ?_⟩
    have hk1 : 1 ≤ k := by
      by_contra h'; have : k = 0 := by omega
      subst this; rw [show (0 : ℕ) + 1 = 1 from rfl, e1] at hak; exact hax hak
    have hdr2 := ((hC.step_either (k := 1) (by omega) (oth p)).2 (by rw [show (1 : ℕ) + 1 = 2 from rfl, e2]; exact oth_ne p)).1
    have hmono := (hC.mono (k := 2) (k' := k + 1) (by omega) hk (oth p)).1
    linarith

/-- **A branch lies below its turn plate along the flipped coordinate** (read the old way): the
extended branch `je` (signs `σB`, opposite to `σ` on the flipped index `f`, first index `f`, first
plate `γ`) has its plates of axis `f` thin-backwards no further on than `γ`, and its other plates
wide at least `m + 1` behind `γ`. [folklore] -/
theorem branch_below (hY : Y.OK) {σB : Fin 2 → ℤˣ} {f : Fin 2} (hJ : DiagLeg hd Y e σB none f je) (hflip : σB f = -σ f) {k : ℕ} (hk : k < je.length) :
    ((legOf je k).a = pl hd f ∧ (legOf je k).s = -σ f ∧ ox hd σ f (legOf je k).b ≤ ox hd σ f (legOf je 0).b) ∨
      ((legOf je k).a ≠ pl hd f ∧ ox hd σ f (legOf je k).b + Y.m + 1 ≤ ox hd σ f (legOf je 0).b) := by
  obtain ⟨hU, -, -, -, -, -, -, -, hm0⟩ := hY.facts
  -- read along `σB`, the coordinate `f` increases; read along `σ`, it decreases
  have oxe : ∀ b : Site d, ox hd σ f b = -ox hd σB f b := fun b => by unfold ox; rw [hflip]; simp
  obtain ⟨hak, hsk⟩ := hJ.axis_sign hk
  have hmono := (hJ.mono (k := 0) (k' := k) (Nat.zero_le _) hk f).1
  by_cases hax : (legOf je k).a = pl hd f
  · have hs' : (legOf je k).s = -σ f := by rw [hak] at hax; have := pl_injective hd hax; rw [hsk, this, hflip]
    exact Or.inl ⟨hax, hs', by rw [oxe, oxe]; linarith⟩
  · refine Or.inr ⟨hax, ?_⟩
    have hk1 : 1 ≤ k := by
      by_contra h'; have : k = 0 := by omega
      subst this; rw [qAt_zero] at hak; exact hax hak
    have e1 : qAt f 1 = oth f := by rw [show qAt f 1 = qAt f (0 + 1) from rfl, qAt_succ, qAt_zero]
    have hdr := ((hJ.step_either (k := 0) (by omega) f).2 (by rw [show (0 : ℕ) + 1 = 1 from rfl, e1]; exact (oth_ne f).symm)).1
    have hmono1 := (hJ.mono (k := 1) (k' := k) hk1 hk f).1
    rw [oxe, oxe]; rw [show (0 : ℕ) + 1 = 1 from rfl] at hdr; linarith

end Profiles

/-! ## The frame of the second fork and the profile before it -/

/-- **The frame of the second fork**: the second stretch has at least three plates, its head `r8`
is the last plate of the stretch extended by `r6`, of axis `0`, and the fork is the turn off it
towards the second branch. [folklore] -/
theorem FlatInv.g2frame (hI : FlatInv hd Y a e τ st) (h9 : st.segs 9 ≠ []) :
    ∃ r8, (st.segs 8).head? = some r8 ∧ 3 ≤ (st.segs 8).length ∧ ∃ r6, (st.segs 6).head? = some r6 ∧
      DiagLeg hd Y e (dsg e) none 1 (st.segs 8 ++ [r6]) ∧
      (∀ k, (hk : k < (st.segs 8).length) → legOf (st.segs 8 ++ [r6]) (k + 1) = legOf (st.segs 8) k) ∧
      legOf (st.segs 8 ++ [r6]) 0 = r6.1 ∧
      legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1) = r8.1 ∧ r8.1.a = pl hd 0 ∧
      Turn hd Y e (dsg e) (dsg (eB2 e)) 0 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)) (st.segs 9) := by
  obtain ⟨r8, hr8, h3, hax, hT⟩ := hI.frame_fork.2 h9
  have h8 : st.segs 8 ≠ [] := by intro h; rw [h] at h3; simp at h3
  have hK8 : SegOK hd Y e τ (eJOf hd Y a e τ st) 8 (st.segs 8) (st.segs (startOf 8)) := hI.segOK 8
  simp only [startOf, Matrix.cons_val] at hK8
  obtain ⟨r6, hr6, q8, hD8, hD80⟩ := hK8 h8
  simp only [Option.mem_def] at hr6
  have h7 : st.segs 7 ≠ [] := by
    have := hI.order 8 7 (by decide) h8; intro h; rw [h] at this; simp [complete'] at this
  obtain ⟨r6', hr6', -, hax6, -⟩ := hI.frame_fork.1 h7
  have hr66 : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
  rw [hr66] at hax6
  have hp1 : p1 e = 1 := by unfold p1 keepIdx; rw [(flipIdx_eB e).1]; rfl
  have hp2 : p2 e = 0 := by unfold p2 keepIdx; rw [(flipIdx_eB e).2]; rfl
  have hq : oth q8 = 1 := by
    have h1 := hD80.srcAxis; rw [hp1] at hax6; rw [hax6] at h1; exact (pl_injective hd h1).symm
  have hE8 : DiagLeg hd Y e (dsg e) none 1 (st.segs 8 ++ [r6]) := by rw [← hq]; exact diagLeg_snoc hD8 hD80
  obtain ⟨tl8, hl8⟩ : ∃ tl, st.segs 8 = r8 :: tl := by
    rcases hl : st.segs 8 with _ | ⟨r0, tl⟩
    · rw [hl] at hr8; simp at hr8
    · rw [hl] at hr8; simp only [List.head?_cons, Option.some.injEq] at hr8; subst hr8; exact ⟨tl, rfl⟩
  have hlast := legOf_append_singleton_last hl8 r6
  rw [hp2] at hax hT
  exact ⟨r8, hr8, h3, r6, hr6, hE8, fun k hk => legOf_append_singleton_succ _ _ k, legOf_snoc_zero _ _, hlast, hax,
    by rw [hlast]; exact hT⟩

/-- **Profile of everything before the second fork, from its start `r8`**: a plate of the second
stretch extended by `r6` (by index); or far behind `r8` along the fork's kept coordinate `0`; or —
when the jog's kept coordinate is `1` — in the axis class along `1` and far enough behind `r8`
there for the flipped-coordinate lemmas; or the first fork's hop `γ₁`, thin-backwards along `0` at
least `U` behind `r6`. [folklore] -/
theorem FlatInv.far_beforeG2 (hI : FlatInv hd Y a e τ st) (hY : Y.OK)
    {r6 : BrickRec d} (hr6 : (st.segs 6).head? = some r6) (hle8 : DiagLeg hd Y e (dsg e) none 1 (st.segs 8 ++ [r6])) (h83 : 3 ≤ (st.segs 8).length)
    (hle80 : legOf (st.segs 8 ++ [r6]) 0 = r6.1) (hax8 : (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)).a = pl hd 0)
    {x : BrickRec d}
    (hx : (((((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6) ∨ x ∈ st.segs 7) ∨ x ∈ st.segs 8) :
    (∃ k < (st.segs 8 ++ [r6]).length, x.1 = legOf (st.segs 8 ++ [r6]) k) ∨
      FarB hd Y (dsg e) 0 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)) x.1 ∨
      (AxCl hd (dsg e) 1 x.1 ∧
        (x.1.a ≠ pl hd 1 → ox hd (dsg e) 1 x.1.b + 2 * Y.U + Y.H + 1 + Y.Lp < ox hd (dsg e) 1 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)).b) ∧
        (x.1.a = pl hd 1 → ox hd (dsg e) 1 x.1.b + Y.U + 2 * Y.H + 2 + Y.Lp < ox hd (dsg e) 1 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)).b)) ∨
      (x.1.a = pl hd 0 ∧ x.1.s = -dsg e 0 ∧ ox hd (dsg e) 0 x.1.b + Y.U ≤ ox hd (dsg e) 0 r6.1.b) := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  set ej := eJOf hd Y a e τ st with hej
  obtain ⟨hflipJ, hkeepJ, hflipT⟩ := flip_keep_J hd Y a e τ st
  rw [← hej] at hflipJ hkeepJ hflipT
  obtain ⟨⟨hflip1, hkeep1⟩, -⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  -- the first fork's frame and the turn back
  have h8ne : st.segs 8 ≠ [] := by intro h; rw [h] at h83; simp at h83
  have h7 : st.segs 7 ≠ [] := by
    have := hI.order 8 7 (by decide) h8ne; intro h; rw [h] at this; simp [complete'] at this
  obtain ⟨r6', hr6', h63, T₀, hT₀, hlen5, h51, hle6, hsucc6, hle60, hlast6, hax6, hT1⟩ := hI.g1frame h7
  have hr66 : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
  rw [hr66] at hlast6 hax6
  rw [← hej] at hle6
  have h5ne : st.segs 5 ≠ [] := by intro h; rw [h] at hlen5; simp at hlen5
  obtain ⟨γ, hγ, hlen3, h31, hJE, h2, hsuccJ, hJ0, haxJ, hsxJ, hTT⟩ := hI.tframe h5ne
  rw [← hej] at hJE haxJ hsxJ hTT
  set le8 := st.segs 8 ++ [r6] with hle8def
  set n8 := le8.length - 1 with hn8
  set le6 := st.segs 6 ++ [T₀] with hle6def
  set n6 := le6.length - 1 with hn6
  set rJ := legOf (st.segs 4 ++ [γ]) ((st.segs 4 ++ [γ]).length - 1) with hrJ
  have hlen8 : le8.length = (st.segs 8).length + 1 := by simp [hle8def]
  have hlen6 : le6.length = (st.segs 6).length + 1 := by simp [hle6def]
  have hle60' : legOf le6 0 = legOf (st.segs 5) 1 := by rw [hle60, h51]
  -- along `le8`: `0`: `r8 ≥ r6 + U`; `1`: `r8 ≥ r6 + U + 2m + 2`
  have e81 : qAt (1 : Fin 2) 1 = 0 := by rw [show qAt (1 : Fin 2) 1 = qAt 1 (0 + 1) from rfl, qAt_succ, qAt_zero]; rfl
  have e82 : qAt (1 : Fin 2) 2 = 1 := by rw [show qAt (1 : Fin 2) 2 = qAt 1 (0 + 2) from rfl, qAt_add_two, qAt_zero]
  have hs81 := (hle8.step (k := 0) (by omega)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, e81, hle80] at hs81
  have hm80 : ∀ (i : Fin 2) k, (hk : k < le8.length) → ox hd (dsg e) i (legOf le8 k).b ≤ ox hd (dsg e) i (legOf le8 n8).b :=
    fun i k hk => (hle8.mono (k := k) (k' := n8) (by omega) (by omega) i).1
  have hd81 := ((hle8.step_either (k := 0) (by omega) 1).2 (by rw [show (0 : ℕ) + 1 = 1 from rfl, e81]; decide)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, hle80] at hd81
  have hs82 := (hle8.step (k := 1) (by omega)).1
  rw [show (1 : ℕ) + 1 = 2 from rfl, e82] at hs82
  have hd83 := ((hle8.step_either (k := 2) (by omega) 1).2 (by
    rw [show (2 : ℕ) + 1 = 3 from rfl, show qAt (1 : Fin 2) 3 = qAt 1 (1 + 2) from rfl, qAt_add_two, e81]; decide)).1
  rw [show (2 : ℕ) + 1 = 3 from rfl] at hd83
  have hr8_1 : ox hd (dsg e) 1 r6.1.b + Y.U + 2 * Y.m + 2 ≤ ox hd (dsg e) 1 (legOf le8 n8).b := by have := hm80 1 3 (by omega); linarith
  -- along `le6`: both coordinates monotone; the kept one of the jog advances
  have hm6 : ∀ (i : Fin 2) k, (hk : k < le6.length) → ox hd (dsg e) i (legOf le6 k).b ≤ ox hd (dsg e) i r6.1.b :=
    fun i k hk => by have := (hle6.mono (k := k) (k' := n6) (by omega) (by omega) i).1; rw [hlast6] at this; exact this
  have hkept : ∀ k, (hk : k + 1 < le6.length) → ox hd (dsg e) (pJ e ej) rJ.b + ((Y.H : ℤ) + 1) + Y.U + Y.m + 1 ≤ ox hd (dsg e) (pJ e ej) (legOf le6 (k + 1)).b := by
    intro k hk
    have := (leg_after_turn_kept hY hTT hlen5 hle6 hle60' hk).1
    have oxe : ∀ b : Site d, ox hd (dsg ej) (pJ e ej) b = ox hd (dsg e) (pJ e ej) b := fun b => by unfold ox; rw [hkeepJ]
    rw [oxe, oxe] at this; exact this
  -- everything at most level with `r6` along `0` is far behind `r8` (since `r6` is wide along `0`)
  have hfar0 : ∀ {X : BrickPos d}, AxCl hd (dsg e) 0 X → ox hd (dsg e) 0 X.b ≤ ox hd (dsg e) 0 r6.1.b → FarB hd Y (dsg e) 0 (legOf le8 n8) X := by
    intro X hcl hle
    refine farB_of_le_first hY hle8 hax8 (by omega) hcl (Or.inr (Or.inr ⟨?_, by rw [hle80]; exact hle⟩))
    rw [hle80, hax6]; exact pl_ne_pl hd (by decide)
  -- the turn back: `r'_T` and `T₀`
  have hTT0 := hTT.h0 (by omega); have hTT1 := hTT.h1 (by omega)
  rcases hx with (((hx | hx) | hx) | hx) | hx
  rotate_left
  · -- segment 5
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [hlen5] at hm
    rw [← hmx]
    interval_cases m
    · -- `r'_T`
      rcases Fin.exists_fin_two.1 ⟨pJ e ej, rfl⟩ with hp0 | hp1
      · -- thin along `0` with the sign of `e`, at most level with `T₀ = le6[0]` (a drift on)
        right; left
        have hdr : (Y.m : ℤ) + 1 ≤ ox hd (dsg e) 0 (legOf le6 0).b - ox hd (dsg e) 0 (legOf (st.segs 5) 0).b := by
          have := hTT1.drift.1; rw [oth_oth, hp0] at this; rw [hle60']; unfold ox
          linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 5) 1).b (pl hd 0)) ((legOf (st.segs 5) 0).b (pl hd 0))]
        refine hfar0 (Or.inr ⟨by rw [hTT0.axis, hp0], by rw [hTT0.sign, hTT.sSign, hkeepJ, hp0]⟩) ?_
        have := hm6 0 0 (by omega); linarith
      · -- thin along `1` at `rJ + H + 1`, far enough behind `r8` for the flipped lemmas
        right; right; left
        have hface : ox hd (dsg e) 1 (legOf (st.segs 5) 0).b = ox hd (dsg e) 1 rJ.b + ((Y.H : ℤ) + 1) := by
          unfold ox; rw [← hp1, hTT0.face, hTT.sSign, hkeepJ, mul_add, ← mul_assoc, units_sq, one_mul]
        -- `rJ + H + 3U + 4m + 5 ≤ r8` along `1`
        have hk1 := hkept 0 (by omega); rw [hp1] at hk1
        have hg := (hle6.gaps (k := 1)).1 (by omega)
        rw [show qAt (oth (pJ e ej)) 1 = qAt (oth (pJ e ej)) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth, hp1] at hg
        have hm3 := hm6 1 3 (by omega)
        refine ⟨Or.inr ⟨by rw [hTT0.axis, hp1], by rw [hTT0.sign, hTT.sSign, hkeepJ, hp1]⟩, fun hw => absurd (by rw [hTT0.axis, hp1]) hw, fun _ => ?_⟩
        linarith [hface, hk1, hg, hm3, hr8_1, hHU, hLpe, hUe, hm0, hmH, hflat]
    · -- `T₀ = le6[0]`
      right; left
      rw [← hle60']
      exact hfar0 (hle6.axCl (by omega) 0) (hm6 0 0 (by omega))
  · -- segment 6: on `le6`
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    right; left
    rw [← hmx, ← hsucc6 m hm]
    exact hfar0 (hle6.axCl (by omega) 0) (hm6 0 (m + 1) (by omega))
  · -- the first fork: the top stacking is pushed back along `0`, the hop is below along `0`
    have hT10 := hT1.h0 (List.length_pos_of_ne_nil (List.ne_nil_of_mem hx))
    have hpush : ox hd (dsg e) 0 (legOf (st.segs 7) 0).b ≤ ox hd (dsg e) 0 r6.1.b := by
      have h0 := hT10.push.1
      rw [hlast6] at h0
      change 0 ≤ (dsg (eB1 e) 0 : ℤ) * ((legOf (st.segs 7) 0).b (pl hd 0) - r6.1.b (pl hd 0)) at h0; rw [hflip1] at h0
      unfold ox; simp only [Units.val_neg, neg_mul] at h0
      linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 7) 0).b (pl hd 0)) (r6.1.b (pl hd 0))]
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    have hm2 : m < 2 := by have := hT1.len; omega
    rw [← hmx]
    interval_cases m
    · right; left
      rw [hlast6] at hT10
      exact hfar0 (Or.inl (by rw [hT10.axis]; exact pl_ne_pl hd (by decide))) hpush
    · right; right; right
      have hT11 := hT1.h1 hm
      refine ⟨hT11.axis, by rw [hT11.sign]; exact hflip1, ?_⟩
      have hγ : ox hd (dsg e) 0 (legOf (st.segs 7) 1).b = ox hd (dsg e) 0 (legOf (st.segs 7) 0).b - Y.U := by
        have hf := hT11.face; change (legOf (st.segs 7) 1).b (pl hd 0) = (legOf (st.segs 7) 0).b (pl hd 0) + (dsg (eB1 e) 0 : ℤ) * Y.U at hf
        unfold ox; rw [hf, hflip1]
        simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
      linarith
  · -- the second stretch: on `le8`
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    left; exact ⟨m + 1, by omega, by rw [hle8def, legOf_append_singleton_succ, hmx]⟩
  -- segments 0–4: the jog side and the entry
  have hfar := hI.far_beforeT hY h5ne hlen3 h31 (by rw [← hej]; exact hJE) hx
  rw [← hej, ← hrJ] at hfar
  rcases Fin.exists_fin_two.1 ⟨pJ e ej, rfl⟩ with hp0 | hp1
  · -- `pJ = 0`: at most level with `rJ ≤ r6` along `0`
    right; left
    have hk1 := hkept 0 (by omega); rw [hp0] at hk1
    have hm1 := hm6 0 1 (by omega)
    have hH0 : (0 : ℤ) ≤ Y.H := by positivity
    have oxe : ∀ b : Site d, ox hd (dsg ej) (pJ e ej) b = ox hd (dsg e) 0 b := fun b => by unfold ox; rw [hkeepJ, hp0]
    rcases hfar with ⟨hcl, hf1, -⟩ | ⟨k, hk, hkx⟩
    · rw [hp0] at hcl; rw [oxe, oxe] at hf1
      exact hfar0 (AxCl.congr (by rw [← hp0, hkeepJ]) hcl) (by linarith)
    · rw [hkx]
      have hmJ := (hJE.mono (k := k) (k' := (st.segs 4 ++ [γ]).length - 1) (by omega) (by omega) 0).1
      have oxe' : ∀ b : Site d, ox hd (dsg ej) 0 b = ox hd (dsg e) 0 b := fun b => by unfold ox; rw [← hp0, hkeepJ]
      rw [oxe', oxe', ← hrJ] at hmJ
      have hcl := hJE.axCl hk 0
      have hk0 : dsg e 0 = dsg ej 0 := by rw [← hp0, hkeepJ]
      exact hfar0 (AxCl.congr hk0 hcl) (by linarith)
  · -- `pJ = 1`: along `1`, `rJ + H + 3U + 4m + 5 ≤ r8`; the jog's head itself goes by `0`
    have hk1 := hkept 0 (by omega); rw [hp1] at hk1
    have hg := (hle6.gaps (k := 1)).1 (by omega)
    rw [show qAt (oth (pJ e ej)) 1 = qAt (oth (pJ e ej)) (0 + 1) from rfl, qAt_succ, qAt_zero, oth_oth, hp1] at hg
    have hm3 := hm6 1 3 (by omega)
    have hr8 : ox hd (dsg e) 1 rJ.b + Y.H + 3 * Y.U + 4 * Y.m + 5 ≤ ox hd (dsg e) 1 (legOf le8 n8).b := by linarith
    have oxe : ∀ b : Site d, ox hd (dsg ej) (pJ e ej) b = ox hd (dsg e) 1 b := fun b => by unfold ox; rw [hkeepJ, hp1]
    rcases hfar with ⟨hcl, hf1, hf2⟩ | ⟨k, hk, hkx⟩
    · right; right; left
      rw [hp1] at hcl; rw [oxe, oxe] at hf1 hf2
      refine ⟨AxCl.congr (by rw [← hp1, hkeepJ]) hcl, fun hw => ?_, fun _ => ?_⟩
      · have := hf2 (by rw [hp1]; exact hw); linarith [this, hr8, hHU, hLpe, hUe, hm0, hmH, hflat]
      · linarith [hf1, hr8, hHU, hLpe, hUe, hm0, hmH, hflat]
    · rw [hkx]
      rcases hJE.prof_feed hY haxJ hk with hlast | ⟨_, ha, hs, hox, -⟩ | ⟨_, hcl, h1, h2⟩
      · -- the jog's head: wide along `0` (axis `1`), along `0` behind `r'_T ≤ T₀ - U ≤ r6 - U`
        right; left
        rw [hlast, ← hrJ]
        have hpush : ox hd (dsg e) 0 rJ.b ≤ ox hd (dsg e) 0 (legOf (st.segs 5) 0).b := by
          have := hTT0.push.1; rw [show oth (pJ e ej) = 0 by rw [hp1]; rfl] at this; unfold ox
          linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 5) 0).b (pl hd 0)) (rJ.b (pl hd 0))]
        have hT0f : ox hd (dsg e) 0 (legOf le6 0).b = ox hd (dsg e) 0 (legOf (st.segs 5) 0).b + Y.U := by
          have hf := hTT1.face; rw [show oth (pJ e ej) = 0 by rw [hp1]; rfl] at hf
          rw [hle60']; unfold ox; rw [hf, mul_add, ← mul_assoc, units_sq, one_mul]
        have hm0' := hm6 0 0 (by omega)
        exact hfar0 (Or.inl (by rw [haxJ, hp1]; exact pl_ne_pl hd (by decide))) (by linarith)
      · right; right; left
        rw [hp1] at ha hs; rw [oxe, oxe, ← hrJ] at hox
        refine ⟨Or.inl (by rw [ha]; exact pl_ne_pl hd (by decide)), fun _ => ?_, fun hw => absurd hw (by rw [ha]; exact pl_ne_pl hd (by decide))⟩
        linarith [hox, hr8, hHU, hLpe, hUe, hm0, hmH, hflat]
      · right; right; left
        rw [hp1] at hcl; rw [oxe, oxe, ← hrJ] at h1 h2
        refine ⟨AxCl.congr (by rw [← hp1, hkeepJ]) hcl, fun hw => ?_, fun _ => ?_⟩
        · have := h2 (by rw [hp1]; exact hw); linarith [this, hr8, hHU, hLpe, hUe, hm0, hmH, hflat]
        · linarith [h1, hr8, hHU, hLpe, hUe, hm0, hmH, hflat]

/-! ## The second fork and the third trunk stretch against everything earlier -/

/-- **Second fork against everything earlier.** [folklore] -/
theorem FlatInv.disj_seg9 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : (((((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6) ∨ x ∈ st.segs 7) ∨ x ∈ st.segs 8)
    (hy : y ∈ st.segs 9) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨-, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  obtain ⟨r8, hr8, h83, r6, hr6, hle8, hsucc8, hle80, hlast8, hax8, hT⟩ := hI.g2frame (List.ne_nil_of_mem hy)
  obtain ⟨jj, hjj, hjy⟩ := exists_legOf_of_mem hy
  rw [← hjy]
  have hjj2 : jj < 2 := by have := hT.len; omega
  have hax8' : (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)).a = pl hd 0 := by rw [hlast8]; exact hax8
  rcases hI.far_beforeG2 hY hr6 hle8 h83 hle80 hax8' hx with ⟨k, hk, hkx⟩ | hfar | ⟨hcl, hw1, hw2⟩ | ⟨ha, hs, hle⟩
  · rw [hkx]; exact disj_feed_turn hY hle8 hT hflip2 hk hjj
  · exact disj_far_turn hY hT hfar hjj
  · have hH0 : (0 : ℤ) ≤ Y.H := by positivity
    interval_cases jj
    · refine disj_turntop_flipped hY hT hjj hflip2 hcl ⟨fun hw => ?_, fun hw => ?_⟩ <;>
        simp only [show oth (0 : Fin 2) = 1 from rfl] at hw ⊢
      · have := hw1 hw; linarith
      · have := hw2 hw; linarith
    · exact disj_turnhop_flipped hY hT hjj hflip2 hcl ⟨hw1, hw2⟩
  · -- `γ₁` below `r6` along `0`; the fork's plates above
    have hT0 := hT.h0 (by omega)
    -- `r8 ≥ r6 + U` along `0`
    have e81 : qAt (1 : Fin 2) 1 = 0 := by rw [show qAt (1 : Fin 2) 1 = qAt 1 (0 + 1) from rfl, qAt_succ, qAt_zero]; rfl
    have hs81 := (hle8.step (k := 0) (by simp; omega)).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, e81, hle80] at hs81
    have hm81 := (hle8.mono (k := 1) (k' := (st.segs 8 ++ [r6]).length - 1) (by simp; omega) (by simp) 0).1
    have hface : ox hd (dsg e) 0 (legOf (st.segs 9) 0).b = ox hd (dsg e) 0 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)).b + ((Y.H : ℤ) + 1) := by
      unfold ox; rw [hT0.face, hT.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
    have hH0 : (0 : ℤ) ≤ Y.H := by positivity
    refine disj_across hY (dsg e 0) (pl hd 0) (ox hd (dsg e) 0 r6.1.b - Y.U) (Or.inr ⟨ha, hs, by unfold ox at hle ⊢; linarith⟩) ?_
    interval_cases jj
    · refine Or.inl ⟨hT0.axis, by rw [hT0.sign, hT.sSign], ?_⟩
      unfold ox at hface hs81 hm81 ⊢; linarith
    · have hT1 := hT.h1 hjj
      refine Or.inr ⟨by rw [hT1.axis]; exact pl_ne_pl hd (by decide), ?_⟩
      have hdr := hT1.drift.1
      change (Y.m : ℤ) + 1 ≤ (dsg (eB2 e) 0 : ℤ) * ((legOf (st.segs 9) 1).b (pl hd 0) - (legOf (st.segs 9) 0).b (pl hd 0)) at hdr
      rw [hkeep2] at hdr
      unfold ox at hface hs81 hm81 ⊢
      linarith [hdr, hface, hs81, hm81, hm0, hU, hH0, mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 9) 1).b (pl hd 0)) ((legOf (st.segs 9) 0).b (pl hd 0))]

/-- **Third trunk stretch against everything earlier.** [folklore] -/
theorem FlatInv.disj_seg10 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) {x y : BrickRec d}
    (hx : ((((((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6) ∨ x ∈ st.segs 7) ∨ x ∈ st.segs 8) ∨ x ∈ st.segs 9)
    (hy : y ∈ st.segs 10) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨⟨hflip1, hkeep1⟩, hflip2, hkeep2⟩ := flip_keep_B e
  have h10 : st.segs 10 ≠ [] := List.ne_nil_of_mem hy
  have h9 : st.segs 9 ≠ [] := by
    have := hI.order 10 9 (by decide) h10; intro h; rw [h] at this; simp [complete'] at this
  obtain ⟨r8, hr8, h83, r6, hr6, hle8, hsucc8l, hle80, hlast8, hax8, hT2⟩ := hI.g2frame h9
  have h8 : st.segs 8 ≠ [] := by intro h; rw [h] at h83; simp at h83
  have h7 : st.segs 7 ≠ [] := by
    have := hI.order 8 7 (by decide) h8; intro h; rw [h] at this; simp [complete'] at this
  obtain ⟨r6', hr6', h63, T₀, hT₀, hlen5, h51, hle6, hsucc6, hle60, hlast6, hax6, hT1⟩ := hI.g1frame h7
  have hr66 : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
  rw [hr66] at hlast6 hax6
  obtain ⟨r6'', hr6'', hC, hc0, hsucc8, hsucc10⟩ := hI.cframe h8
  have hr666 : r6'' = r6 := by rw [hr6] at hr6''; simpa using hr6''.symm
  rw [hr666] at hC hc0 hsucc8 hsucc10
  -- the continuing leg off `r8`
  have hK10 : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
  simp only [startOf, Matrix.cons_val] at hK10
  obtain ⟨r8', hr8', q10, hD10, hD100⟩ := hK10 h10
  have hr88 : r8' = r8 := by rw [hr8] at hr8'; simpa using hr8'.symm
  rw [hr88] at hD100
  have hq10 : oth q10 = 0 := by have h1 := hD100.srcAxis; rw [hax8] at h1; exact (pl_injective hd h1).symm
  have hC10 : DiagLeg hd Y e (dsg e) none 0 (st.segs 10 ++ [r8]) := by rw [← hq10]; exact diagLeg_snoc hD10 hD100
  have hc100 : legOf (st.segs 10 ++ [r8]) 0 = r8.1 := legOf_snoc_zero _ _
  -- the turn back and the full trunk
  have h5ne : st.segs 5 ≠ [] := by intro h; rw [h] at hlen5; simp at hlen5
  obtain ⟨γ, hγ, hlen3, h31, hJE, h2, hsuccJ, hJ0, haxJ, hsxJ, hTT⟩ := hI.tframe h5ne
  obtain ⟨T₀', hT₀', -, hTE⟩ := hI.frame_trunk (by intro h; rw [h] at h63; simp at h63)
  have hTT0 : T₀' = T₀ := by rw [hT₀] at hT₀'; simpa using hT₀'.symm
  rw [hTT0] at hTE
  have hTE' : st.segs 10 ++ st.segs 8 ++ st.segs 6 ++ [T₀] = (st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀]) := by simp
  rw [hTE'] at hTE
  have hTE0 : legOf ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])) 0 = legOf (st.segs 5) 1 := by
    rw [legOf_append_of_lt _ _ (by simp), hle60, h51]
  -- `y` in the three legs
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  have hyc : y.1 = legOf (st.segs 10 ++ st.segs 8 ++ [r6]) ((st.segs 8).length + 1 + k) := by rw [hsucc10 k hk, hky]
  have hyc10 : y.1 = legOf (st.segs 10 ++ [r8]) (k + 1) := by rw [legOf_append_singleton_succ, hky]
  have hyT : y.1 = legOf ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])) ((st.segs 6 ++ [T₀]).length + ((st.segs 8).length + k)) := by
    rw [legOf_append_of_ge, legOf_append_of_ge, hky]
  have hkc : (st.segs 8).length + 1 + k < (st.segs 10 ++ st.segs 8 ++ [r6]).length := by simp; omega
  have hkc10 : k + 1 < (st.segs 10 ++ [r8]).length := by simp; omega
  have hkT : (st.segs 6 ++ [T₀]).length + ((st.segs 8).length + k) < ((st.segs 10 ++ st.segs 8) ++ (st.segs 6 ++ [T₀])).length := by simp; omega
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · -- the jog side and the entry
    rw [hyT, show (st.segs 6 ++ [T₀]).length + ((st.segs 8).length + k) = ((st.segs 6 ++ [T₀]).length + ((st.segs 8).length + k) - 1) + 1 by simp; omega]
    exact disj_farfeed_legafter hY hJE hTT hlen5 hTE hTE0 (hI.far_beforeT hY h5ne hlen3 h31 hJE hx) (by simp; omega)
  · -- the turn back
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, hyT]
    rw [hlen5] at hm
    interval_cases m
    · rw [show (st.segs 6 ++ [T₀]).length + ((st.segs 8).length + k) = ((st.segs 6 ++ [T₀]).length + ((st.segs 8).length + k) - 1) + 1 by simp; omega]
      exact disj_leg_after_turn_top hY hTT hlen5 hTE hTE0 (by simp; omega)
    · rw [← hTE0]; exact hTE.disj hY (by simp) hkT
  · -- the first stretch
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc6 m hm, hyT, ← legOf_append_of_lt (st.segs 10 ++ st.segs 8) (st.segs 6 ++ [T₀]) (k := m + 1) (by simp; omega)]
    exact hTE.disj hY (by simp; omega) hkT
  · -- the first fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, hyc]
    have hm2 : m < 2 := by have := hT1.len; omega
    rw [hlast6] at hT1
    rw [show (st.segs 8).length + 1 + k = ((st.segs 8).length + k) + 1 by ring] at hkc ⊢
    interval_cases m
    · exact disj_cont_forktop hY hT1 hm hflip1 hC hc0 hkc
    · exact disj_cont_forkhop hY hT1 hm hflip1 hC hc0 hkc
  · -- the second stretch: on the continuing leg
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc8 m hm, hyc]
    exact hC.disj hY (by omega) hkc
  · -- the second fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, hyc10]
    have hm2 : m < 2 := by have := hT2.len; omega
    rw [hlast8] at hT2
    interval_cases m
    · exact disj_cont_forktop hY hT2 hm hflip2 hC10 hc100 hkc10
    · exact disj_cont_forkhop hY hT2 hm hflip2 hC10 hc100 hkc10

end BGNd

end Percolation.Literature

end

/-!
# Part 2 (The flat gait, XV): assembling disjointness, III — the branches; all plates pairwise disjoint

The last two segments of the flat gait (Grimmett,
*Percolation*, 2nd ed. (1999), §7.3 pp. 171–174, case `H < L`), the branches, against everything
earlier (`FlatInv.disj_seg11`, `FlatInv.disj_seg12`): structurally against the trunk and the forks
(the two sides of a fork, the leg after a turn), and — against the entry and the jog side, which a
branch may approach again in one plane coordinate — by the quantitative separation `PsiFar` of
the forward diagonal coordinate (`disj_of_upar_gap`), established from the stopping rules in
`FlatBoundsG.lean`. Finally all plates of an invariant state are pairwise disjoint
(`FlatInv.pairwise`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Springer 1999, §7.3 pp. 171–174.
-/

noncomputable section

namespace Percolation.Literature

open LatticeModels Contour
open scoped Classical

namespace BGNd

variable {d : ℕ} [NeZero d] {hd : 3 ≤ d} {Y : FlatLayout} {a : Site 2} {e : MDir} {τ : TTok d} {st : FS d}

/-! ## The quantitative separation -/

/-- **A gap of more than `4U` in the forward diagonal coordinate separates two plates**: one of
the two oriented plane coordinates differs by more than `2U`. [folklore] -/
theorem disj_of_upar_gap (hY : Y.OK) (σ : Fin 2 → ℤˣ) {X Z : BrickPos d} (h : upar hd σ X.b + 4 * Y.U < upar hd σ Z.b) : PlateDisj Y.L Y.H X Z := by
  obtain ⟨hU, hUe, -, -, -, hHU, -⟩ := hY.facts
  unfold upar at h
  unfold PlateDisj
  have hUH : (Y.H : ℤ) + 1 ≤ (Y.L : ℤ) + 1 := by linarith
  by_cases h0 : 2 * Y.U < ox hd σ 0 Z.b - ox hd σ 0 X.b
  · refine sep_any hUH (σ 0) (pl hd 0) ?_; unfold ox at h0; linarith
  · refine sep_any hUH (σ 1) (pl hd 1) ?_; unfold ox at h0 h; push Not at h0; linarith

/-- **The branches are far from the entry and the jog side** in the forward diagonal coordinate:
the quantitative input from the stopping rules (`FlatBoundsG.lean`). [folklore] -/
def PsiFar (hd : 3 ≤ d) (Y : FlatLayout) (e : MDir) (st : FS d) : Prop :=
  ∀ y, (y ∈ st.segs 11 ∨ y ∈ st.segs 12) → ∀ x : BrickRec d,
    (((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) →
      upar hd (dsg e) x.1.b + 4 * Y.U < upar hd (dsg e) y.1.b

/-! ## The first branch -/

/-- **First branch against everything earlier.** [folklore] -/
theorem FlatInv.disj_seg11 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hΨ : PsiFar hd Y e st) {x y : BrickRec d}
    (hx : (((((((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6) ∨ x ∈ st.segs 7) ∨ x ∈ st.segs 8) ∨ x ∈ st.segs 9) ∨ x ∈ st.segs 10)
    (hy : y ∈ st.segs 11) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨⟨hflip1, hkeep1⟩, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  have h11 : st.segs 11 ≠ [] := List.ne_nil_of_mem hy
  obtain ⟨γ₁, hγ₁, hlen7, hBE⟩ := hI.frame_branch.1 h11
  have hp1 : oth (p1 e) = 0 := (oth_p1_p2 e).1.trans (flipIdx_eB e).1
  rw [hp1] at hBE
  have h7 : st.segs 7 ≠ [] := by intro h; rw [h] at hlen7; simp at hlen7
  obtain ⟨r6, hr6, h63, T₀, hT₀, hlen5, h51, hle6, hsucc6, hle60, hlast6, hax6, hT1⟩ := hI.g1frame h7
  obtain ⟨tl7, hl7⟩ : ∃ tl, st.segs 7 = γ₁ :: tl := by
    rcases hl : st.segs 7 with _ | ⟨r0, tl⟩
    · rw [hl] at hγ₁; simp at hγ₁
    · rw [hl] at hγ₁; simp only [List.head?_cons, Option.some.injEq] at hγ₁; subst hγ₁; exact ⟨tl, rfl⟩
  have htl7 : tl7.length = 1 := by rw [hl7] at hlen7; simp at hlen7; omega
  have hBE0 : legOf (st.segs 11 ++ [γ₁]) 0 = legOf (st.segs 7) 1 := by
    rw [legOf_snoc_zero, hl7]; exact (legOf_head' htl7).symm
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  rw [← hky, ← legOf_append_singleton_succ (st.segs 11) γ₁ k]
  have hk' : k + 1 < (st.segs 11 ++ [γ₁]).length := by simp; exact hk
  -- the first fork's plates: `γ₁ = r'₁ - U` along `0`, `r'₁ ≤ r6` along `0`
  have hT10 := hT1.h0 (by omega); have hT11 := hT1.h1 (by omega)
  rw [hlast6] at hT10
  have hpush : ox hd (dsg e) 0 (legOf (st.segs 7) 0).b ≤ ox hd (dsg e) 0 r6.1.b := by
    have h0 := hT10.push.1
    change 0 ≤ (dsg (eB1 e) 0 : ℤ) * ((legOf (st.segs 7) 0).b (pl hd 0) - r6.1.b (pl hd 0)) at h0; rw [hflip1] at h0
    unfold ox; simp only [Units.val_neg, neg_mul] at h0
    linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 7) 0).b (pl hd 0)) (r6.1.b (pl hd 0))]
  have hγ : ox hd (dsg e) 0 (legOf (st.segs 7) 1).b = ox hd (dsg e) 0 (legOf (st.segs 7) 0).b - Y.U := by
    have hf := hT11.face; change (legOf (st.segs 7) 1).b (pl hd 0) = (legOf (st.segs 7) 0).b (pl hd 0) + (dsg (eB1 e) 0 : ℤ) * Y.U at hf
    unfold ox; rw [hf, hflip1]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · -- the entry, the jog side and the turn back: far in the forward diagonal coordinate
    rw [legOf_append_singleton_succ, hky]; exact disj_of_upar_gap hY (dsg e) (hΨ y (Or.inl hy) x hx)
  · -- the first stretch: on the feeding leg of the first fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc6 m hm]
    exact disj_farfeed_legafter hY hle6 hT1 hlen7 hBE hBE0 (Or.inr ⟨m + 1, by simp; omega, rfl⟩) hk'
  · -- the first fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    rw [hlen7] at hm
    interval_cases m
    · exact disj_leg_after_turn_top hY hT1 hlen7 hBE hBE0 hk'
    · rw [← hBE0]; exact hBE.disj hY (by omega) hk'
  all_goals
    -- the trunk after the fork and the second fork: above `r6` along `0`, the branch below
    have h8 : st.segs 8 ≠ [] := by
      first
        | exact List.ne_nil_of_mem hx
        | (have h9 : st.segs 9 ≠ [] := by first | exact List.ne_nil_of_mem hx | (have := hI.order 10 9 (by decide) (List.ne_nil_of_mem hx); intro h; rw [h] at this; simp [complete'] at this)
           have := hI.order 9 8 (by decide) h9; intro h; rw [h] at this; simp [complete'] at this)
    obtain ⟨r6'', hr6'', hC, hc0, hsucc8, hsucc10⟩ := hI.cframe h8
    have hr666 : r6'' = r6 := by rw [hr6] at hr6''; simpa using hr6''.symm
    rw [hr666] at hC hc0 hsucc8 hsucc10
    have hbelow := branch_below (σ := dsg e) hY hBE hflip1 hk'
    rw [hBE0] at hbelow
    refine (disj_across hY (dsg e 0) (pl hd 0) (ox hd (dsg e) 0 r6.1.b - Y.m - 1) (β := legOf (st.segs 11 ++ [γ₁]) (k + 1)) ?_ ?_).symm
    · rcases hbelow with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩
      · exact Or.inr ⟨ha, hs, by unfold ox at hle hγ hpush ⊢; linarith⟩
      · exact Or.inl ⟨ha, by unfold ox at hle hγ hpush ⊢; linarith⟩
  · -- the second stretch
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc8 m hm]
    rcases cont_above hY hC hc0 (k := m) (by simp; omega) with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩ <;>
      simp only [show oth (1 : Fin 2) = 0 from rfl] at ha hle ⊢
    · exact Or.inl ⟨ha, hs, by unfold ox at hle ⊢; linarith⟩
    · exact Or.inr ⟨ha, by unfold ox at hle ⊢; linarith⟩
  · -- the second fork: `r'₂ = r8 + H + 1` thin along `0`, `γ₂` wide beyond
    obtain ⟨r8, hr8, h83, r6', hr6', hle8, hsucc8l, hle80, hlast8, hax8, hT2⟩ := hI.g2frame (List.ne_nil_of_mem hx)
    have hr66' : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
    rw [hr66'] at hle8 hle80 hlast8 hT2
    have e81 : qAt (1 : Fin 2) 1 = 0 := by rw [show qAt (1 : Fin 2) 1 = qAt 1 (0 + 1) from rfl, qAt_succ, qAt_zero]; rfl
    have hs81 := (hle8.step (k := 0) (by simp; omega)).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, e81, hle80] at hs81
    have hm81 := (hle8.mono (k := 1) (k' := (st.segs 8 ++ [r6]).length - 1) (by simp; omega) (by simp) 0).1
    rw [hlast8] at hm81
    have hT20 := hT2.h0 (by have := hT2.len; have := List.length_pos_of_ne_nil (List.ne_nil_of_mem hx); omega)
    rw [hlast8] at hT20
    have hface : ox hd (dsg e) 0 (legOf (st.segs 9) 0).b = ox hd (dsg e) 0 r8.1.b + ((Y.H : ℤ) + 1) := by
      unfold ox; rw [hT20.face, ← hlast8, hT2.sSign, mul_add, ← mul_assoc, units_sq, one_mul]
    have hH0 : (0 : ℤ) ≤ Y.H := by positivity
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    have hm2 : m < 2 := by have := hT2.len; omega
    interval_cases m
    · refine Or.inl ⟨hT20.axis, by rw [hT20.sign, ← hlast8, hT2.sSign], ?_⟩
      unfold ox at hface hs81 hm81 ⊢; linarith
    · have hT21 := hT2.h1 hm
      refine Or.inr ⟨by rw [hT21.axis]; exact pl_ne_pl hd (by decide), ?_⟩
      have hdr := hT21.drift.1
      change (Y.m : ℤ) + 1 ≤ (dsg (eB2 e) 0 : ℤ) * ((legOf (st.segs 9) 1).b (pl hd 0) - (legOf (st.segs 9) 0).b (pl hd 0)) at hdr
      rw [hkeep2] at hdr
      unfold ox at hface hs81 hm81 ⊢
      linarith [hdr, mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 9) 1).b (pl hd 0)) ((legOf (st.segs 9) 0).b (pl hd 0))]
  · -- the third stretch
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc10 m hm, show (st.segs 8).length + 1 + m = ((st.segs 8).length + m) + 1 by ring]
    rcases cont_above hY hC hc0 (k := (st.segs 8).length + m) (by simp; omega) with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩ <;>
      simp only [show oth (1 : Fin 2) = 0 from rfl] at ha hle ⊢
    · exact Or.inl ⟨ha, hs, by unfold ox at hle ⊢; linarith⟩
    · exact Or.inr ⟨ha, by unfold ox at hle ⊢; linarith⟩

/-! ## The second branch -/

/-- **Second branch against everything earlier.** [folklore] -/
theorem FlatInv.disj_seg12 (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hΨ : PsiFar hd Y e st) {x y : BrickRec d}
    (hx : ((((((((((x ∈ st.segs 0 ∨ x ∈ st.segs 1) ∨ x ∈ st.segs 2) ∨ x ∈ st.segs 3) ∨ x ∈ st.segs 4) ∨ x ∈ st.segs 5) ∨ x ∈ st.segs 6) ∨ x ∈ st.segs 7) ∨ x ∈ st.segs 8) ∨ x ∈ st.segs 9) ∨ x ∈ st.segs 10) ∨ x ∈ st.segs 11)
    (hy : y ∈ st.segs 12) : PlateDisj Y.L Y.H x.1 y.1 := by
  obtain ⟨hU, hUe, hLpe, hLp0, hULp, hHU, hmH, hflat, hm0⟩ := hY.facts
  obtain ⟨⟨hflip1, hkeep1⟩, hflip2, hkeep2⟩ := flip_keep_B e
  change dsg (eB1 e) 0 = -dsg e 0 at hflip1
  change dsg (eB2 e) 1 = -dsg e 1 at hflip2
  have h12 : st.segs 12 ≠ [] := List.ne_nil_of_mem hy
  obtain ⟨γ₂, hγ₂, hlen9, hBE⟩ := hI.frame_branch.2 h12
  have hp2 : oth (p2 e) = 1 := (oth_p1_p2 e).2.trans (flipIdx_eB e).2
  rw [hp2] at hBE
  have h9 : st.segs 9 ≠ [] := by intro h; rw [h] at hlen9; simp at hlen9
  obtain ⟨r8, hr8, h83, r6, hr6, hle8, hsucc8l, hle80, hlast8, hax8, hT2⟩ := hI.g2frame h9
  have h8 : st.segs 8 ≠ [] := by intro h; rw [h] at h83; simp at h83
  have h7 : st.segs 7 ≠ [] := by
    have := hI.order 8 7 (by decide) h8; intro h; rw [h] at this; simp [complete'] at this
  have hlen7' : 2 ≤ (st.segs 7).length := by
    have hc := hI.order 8 7 (by decide) h8
    obtain ⟨r, tl, hl, -⟩ := exists_head_of_ne_nil h7
    rw [hl] at hc ⊢; simp only [complete', kindOf, Matrix.cons_val] at hc; simpa using hc
  obtain ⟨r6', hr6', h63, T₀, hT₀, hlen5, h51, hle6, hsucc6, hle60, hlast6, hax6, hT1⟩ := hI.g1frame h7
  have hr66 : r6' = r6 := by rw [hr6] at hr6'; simpa using hr6'.symm
  rw [hr66] at hlast6 hax6
  obtain ⟨tl9, hl9⟩ : ∃ tl, st.segs 9 = γ₂ :: tl := by
    rcases hl : st.segs 9 with _ | ⟨r0, tl⟩
    · rw [hl] at hγ₂; simp at hγ₂
    · rw [hl] at hγ₂; simp only [List.head?_cons, Option.some.injEq] at hγ₂; subst hγ₂; exact ⟨tl, rfl⟩
  have htl9 : tl9.length = 1 := by rw [hl9] at hlen9; simp at hlen9; omega
  have hBE0 : legOf (st.segs 12 ++ [γ₂]) 0 = legOf (st.segs 9) 1 := by
    rw [legOf_snoc_zero, hl9]; exact (legOf_head' htl9).symm
  obtain ⟨k, hk, hky⟩ := exists_legOf_of_mem hy
  rw [← hky, ← legOf_append_singleton_succ (st.segs 12) γ₂ k]
  have hk' : k + 1 < (st.segs 12 ++ [γ₂]).length := by simp; exact hk
  -- along `0` on `le8`: `r8 ≥ le8[1] = r6 + U`
  have e81 : qAt (1 : Fin 2) 1 = 0 := by rw [show qAt (1 : Fin 2) 1 = qAt 1 (0 + 1) from rfl, qAt_succ, qAt_zero]; rfl
  have hs81 := (hle8.step (k := 0) (by simp; omega)).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, e81, hle80] at hs81
  have hm8 : ∀ (i : Fin 2) j, (hj : j < (st.segs 8 ++ [r6]).length) → ox hd (dsg e) i (legOf (st.segs 8 ++ [r6]) j).b ≤ ox hd (dsg e) i r8.1.b := by
    intro i j hj; have := (hle8.mono (k := j) (k' := (st.segs 8 ++ [r6]).length - 1) (by omega) (by simp) i).1; rw [hlast8] at this; exact this
  have hm81 := hm8 0 1 (by simp; omega)
  -- the two plates of the second fork along `0` and `1`
  have hT20 := hT2.h0 (by omega); have hT21 := hT2.h1 (by omega)
  rw [hlast8] at hT20
  have hface : ox hd (dsg e) 0 (legOf (st.segs 9) 0).b = ox hd (dsg e) 0 r8.1.b + ((Y.H : ℤ) + 1) := by
    unfold ox; rw [hT20.face]; have := hT2.sSign; rw [hlast8] at this; rw [this, mul_add, ← mul_assoc, units_sq, one_mul]
  have hdr9 : (Y.m : ℤ) + 1 ≤ ox hd (dsg e) 0 (legOf (st.segs 9) 1).b - ox hd (dsg e) 0 (legOf (st.segs 9) 0).b := by
    have hdr := hT21.drift.1
    change (Y.m : ℤ) + 1 ≤ (dsg (eB2 e) 0 : ℤ) * ((legOf (st.segs 9) 1).b (pl hd 0) - (legOf (st.segs 9) 0).b (pl hd 0)) at hdr
    rw [hkeep2] at hdr; unfold ox
    linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 9) 1).b (pl hd 0)) ((legOf (st.segs 9) 0).b (pl hd 0))]
  have hpush2 : ox hd (dsg e) 1 (legOf (st.segs 9) 0).b ≤ ox hd (dsg e) 1 r8.1.b := by
    have h0 := hT20.push.1
    change 0 ≤ (dsg (eB2 e) 1 : ℤ) * ((legOf (st.segs 9) 0).b (pl hd 1) - r8.1.b (pl hd 1)) at h0; rw [hflip2] at h0
    unfold ox; simp only [Units.val_neg, neg_mul] at h0
    linarith [mul_sub (dsg e 1 : ℤ) ((legOf (st.segs 9) 0).b (pl hd 1)) (r8.1.b (pl hd 1))]
  have hγ2 : ox hd (dsg e) 1 (legOf (st.segs 9) 1).b = ox hd (dsg e) 1 (legOf (st.segs 9) 0).b - Y.U := by
    have hf := hT21.face; change (legOf (st.segs 9) 1).b (pl hd 1) = (legOf (st.segs 9) 0).b (pl hd 1) + (dsg (eB2 e) 1 : ℤ) * Y.U at hf
    unfold ox; rw [hf, hflip2]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
  have hH0 : (0 : ℤ) ≤ Y.H := by positivity
  -- everything at most level with `r6` along `0` is far behind `r8`
  have hax8' : (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)).a = pl hd 0 := by rw [hlast8]; exact hax8
  have hfar0 : ∀ {X : BrickPos d}, AxCl hd (dsg e) 0 X → ox hd (dsg e) 0 X.b ≤ ox hd (dsg e) 0 r6.1.b →
      FarB hd Y (dsg e) 0 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)) X := by
    intro X hcl hle
    refine farB_of_le_first hY hle8 hax8' (by simp; omega) hcl (Or.inr (Or.inr ⟨?_, by rw [hle80]; exact hle⟩))
    rw [hle80, hax6]; exact pl_ne_pl hd (by decide)
  have hT2' : Turn hd Y e (dsg e) (dsg (eB2 e)) 0 (legOf (st.segs 8 ++ [r6]) ((st.segs 8 ++ [r6]).length - 1)) (st.segs 9) := hT2
  -- the above profile of the extended second branch along `0`, and its below profile along `1`
  have hBabove : ∀ j, (hj : j < (st.segs 12 ++ [γ₂]).length) →
      ((legOf (st.segs 12 ++ [γ₂]) j).a = pl hd 0 ∧ (legOf (st.segs 12 ++ [γ₂]) j).s = dsg e 0 ∧ ox hd (dsg e) 0 r6.1.b - Y.m - 1 + Y.U ≤ ox hd (dsg e) 0 (legOf (st.segs 12 ++ [γ₂]) j).b) ∨
      ((legOf (st.segs 12 ++ [γ₂]) j).a ≠ pl hd 0 ∧ ox hd (dsg e) 0 r6.1.b - Y.m - 1 + Y.U < ox hd (dsg e) 0 (legOf (st.segs 12 ++ [γ₂]) j).b) := by
    intro j hj
    rcases j with _ | j
    · right; rw [hBE0]; exact ⟨by rw [hT21.axis]; exact pl_ne_pl hd (by decide), by unfold ox at hface hdr9 hs81 hm81 ⊢; linarith⟩
    · rcases cont_above (σ := dsg (eB2 e)) (p := 1) hY hBE rfl (k := j) hj with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩
      · simp only [show oth (1 : Fin 2) = 0 from rfl, hkeep2] at ha hs hle
        left; refine ⟨ha, hs, ?_⟩; rw [hBE0] at hle; unfold ox at hface hdr9 hs81 hm81 hle ⊢; rw [hkeep2] at hle; linarith
      · simp only [show oth (1 : Fin 2) = 0 from rfl] at ha hle
        right; refine ⟨ha, ?_⟩; rw [hBE0] at hle; unfold ox at hface hdr9 hs81 hm81 hle ⊢; rw [hkeep2] at hle; linarith
  rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
  · -- the entry, the jog side and the turn back
    rw [legOf_append_singleton_succ, hky]; exact disj_of_upar_gap hY (dsg e) (hΨ y (Or.inr hy) x hx)
  · -- the first stretch: at most level with `r6` along `0`
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc6 m hm]
    have hm' : m + 1 < (st.segs 6 ++ [T₀]).length := by simp; exact hm
    refine disj_farfeed_legafter hY hle8 hT2' hlen9 hBE hBE0 (Or.inl (hfar0 (hle6.axCl hm' 0) ?_)) hk'
    have := (hle6.mono (k := m + 1) (k' := (st.segs 6 ++ [T₀]).length - 1) (by omega) (by simp) 0).1
    rw [hlast6] at this; exact this
  · -- the first fork: the top stacking far behind `r8` along `0`, the hop below `r6`
    have hT10 := hT1.h0 (by omega); have hT11 := hT1.h1 (by omega)
    rw [hlast6] at hT10
    have hpush : ox hd (dsg e) 0 (legOf (st.segs 7) 0).b ≤ ox hd (dsg e) 0 r6.1.b := by
      have h0 := hT10.push.1
      change 0 ≤ (dsg (eB1 e) 0 : ℤ) * ((legOf (st.segs 7) 0).b (pl hd 0) - r6.1.b (pl hd 0)) at h0; rw [hflip1] at h0
      unfold ox; simp only [Units.val_neg, neg_mul] at h0
      linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 7) 0).b (pl hd 0)) (r6.1.b (pl hd 0))]
    have hγ : ox hd (dsg e) 0 (legOf (st.segs 7) 1).b = ox hd (dsg e) 0 (legOf (st.segs 7) 0).b - Y.U := by
      have hf := hT11.face; change (legOf (st.segs 7) 1).b (pl hd 0) = (legOf (st.segs 7) 0).b (pl hd 0) + (dsg (eB1 e) 0 : ℤ) * Y.U at hf
      unfold ox; rw [hf, hflip1]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    have hm2 : m < 2 := by have := hT1.len; omega
    interval_cases m
    · exact disj_farfeed_legafter hY hle8 hT2' hlen9 hBE hBE0 (Or.inl (hfar0 (Or.inl (by rw [hT10.axis]; exact pl_ne_pl hd (by decide))) hpush)) hk'
    · exact disj_across hY (dsg e 0) (pl hd 0) (ox hd (dsg e) 0 r6.1.b - Y.m - 1)
        (Or.inr ⟨hT11.axis, by rw [hT11.sign]; exact hflip1, by unfold ox at hγ hpush ⊢; linarith⟩) (hBabove (k + 1) hk')
  · -- the second stretch: on the feeding leg of the second fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← hsucc8l m hm]
    exact disj_farfeed_legafter hY hle8 hT2' hlen9 hBE hBE0 (Or.inr ⟨m + 1, by simp; omega, rfl⟩) hk'
  · -- the second fork
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx]
    rw [hlen9] at hm
    interval_cases m
    · exact disj_leg_after_turn_top hY hT2' hlen9 hBE hBE0 hk'
    · rw [← hBE0]; exact hBE.disj hY (by omega) hk'
  · -- the third stretch: above `r8` along `1`, the branch below
    have h10 : st.segs 10 ≠ [] := List.ne_nil_of_mem hx
    have hK10 : SegOK hd Y e τ (eJOf hd Y a e τ st) 10 (st.segs 10) (st.segs (startOf 10)) := hI.segOK 10
    simp only [startOf, Matrix.cons_val] at hK10
    obtain ⟨r8', hr8', q10, hD10, hD100⟩ := hK10 h10
    have hr88 : r8' = r8 := by rw [hr8] at hr8'; simpa using hr8'.symm
    rw [hr88] at hD100
    have hq10 : oth q10 = 0 := by have h1 := hD100.srcAxis; rw [hax8] at h1; exact (pl_injective hd h1).symm
    have hC10 : DiagLeg hd Y e (dsg e) none 0 (st.segs 10 ++ [r8]) := by rw [← hq10]; exact diagLeg_snoc hD10 hD100
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← legOf_append_singleton_succ (st.segs 10) r8 m]
    have hbelow := branch_below (σ := dsg e) hY hBE hflip2 hk'
    rw [hBE0] at hbelow
    refine (disj_across hY (dsg e 1) (pl hd 1) (ox hd (dsg e) 1 r8.1.b - Y.m - 1) (β := legOf (st.segs 12 ++ [γ₂]) (k + 1)) ?_ ?_).symm
    · rcases hbelow with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩
      · exact Or.inr ⟨ha, hs, by unfold ox at hle hγ2 hpush2 ⊢; linarith⟩
      · exact Or.inl ⟨ha, by unfold ox at hle hγ2 hpush2 ⊢; linarith⟩
    · rcases cont_above hY hC10 (legOf_snoc_zero _ _) (k := m) (by simp; omega) with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩
      · simp only [show oth (0 : Fin 2) = 1 from rfl] at ha hs hle
        exact Or.inl ⟨ha, hs, by unfold ox at hle ⊢; linarith⟩
      · simp only [show oth (0 : Fin 2) = 1 from rfl] at ha hle
        exact Or.inr ⟨ha, by unfold ox at hle ⊢; linarith⟩
  · -- the first branch: below `r6` along `0`, the second branch above
    obtain ⟨γ₁, hγ₁, hlen7, hBE1⟩ := hI.frame_branch.1 (List.ne_nil_of_mem hx)
    have hp1 : oth (p1 e) = 0 := (oth_p1_p2 e).1.trans (flipIdx_eB e).1
    rw [hp1] at hBE1
    obtain ⟨tl7, hl7⟩ : ∃ tl, st.segs 7 = γ₁ :: tl := by
      rcases hl : st.segs 7 with _ | ⟨r0, tl⟩
      · rw [hl] at hγ₁; simp at hγ₁
      · rw [hl] at hγ₁; simp only [List.head?_cons, Option.some.injEq] at hγ₁; subst hγ₁; exact ⟨tl, rfl⟩
    have htl7 : tl7.length = 1 := by rw [hl7] at hlen7; simp at hlen7; omega
    have hBE10 : legOf (st.segs 11 ++ [γ₁]) 0 = legOf (st.segs 7) 1 := by
      rw [legOf_snoc_zero, hl7]; exact (legOf_head' htl7).symm
    have hT10 := hT1.h0 (by omega); have hT11 := hT1.h1 (by omega)
    rw [hlast6] at hT10
    have hpush : ox hd (dsg e) 0 (legOf (st.segs 7) 0).b ≤ ox hd (dsg e) 0 r6.1.b := by
      have h0 := hT10.push.1
      change 0 ≤ (dsg (eB1 e) 0 : ℤ) * ((legOf (st.segs 7) 0).b (pl hd 0) - r6.1.b (pl hd 0)) at h0; rw [hflip1] at h0
      unfold ox; simp only [Units.val_neg, neg_mul] at h0
      linarith [mul_sub (dsg e 0 : ℤ) ((legOf (st.segs 7) 0).b (pl hd 0)) (r6.1.b (pl hd 0))]
    have hγ : ox hd (dsg e) 0 (legOf (st.segs 7) 1).b = ox hd (dsg e) 0 (legOf (st.segs 7) 0).b - Y.U := by
      have hf := hT11.face; change (legOf (st.segs 7) 1).b (pl hd 0) = (legOf (st.segs 7) 0).b (pl hd 0) + (dsg (eB1 e) 0 : ℤ) * Y.U at hf
      unfold ox; rw [hf, hflip1]; simp only [Units.val_neg, neg_mul, mul_add, mul_neg, ← mul_assoc, units_sq, one_mul]; ring
    obtain ⟨m, hm, hmx⟩ := exists_legOf_of_mem hx
    rw [← hmx, ← legOf_append_singleton_succ (st.segs 11) γ₁ m]
    have hbelow := branch_below (σ := dsg e) hY hBE1 hflip1 (k := m + 1) (by simp; omega)
    rw [hBE10] at hbelow
    refine disj_across hY (dsg e 0) (pl hd 0) (ox hd (dsg e) 0 r6.1.b - Y.m - 1) ?_ (hBabove (k + 1) hk')
    rcases hbelow with ⟨ha, hs, hle⟩ | ⟨ha, hle⟩
    · exact Or.inr ⟨ha, hs, by unfold ox at hle hγ hpush ⊢; linarith⟩
    · exact Or.inl ⟨ha, by unfold ox at hle hγ hpush ⊢; linarith⟩

/-! ## All plates pairwise disjoint -/

/-- **Plates of different segments are disjoint.** [folklore] -/
theorem FlatInv.disj_cross (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hΨ : PsiFar hd Y e st)
    {i j : Fin 13} (hij : i < j) {x y : BrickRec d} (hx : x ∈ st.segs i) (hy : y ∈ st.segs j) : PlateDisj Y.L Y.H x.1 y.1 := by
  have hival := Fin.lt_def.1 hij
  fin_cases j <;> simp at hy hival ⊢ <;> fin_cases i <;> simp at hx hival
  · exact hI.disj_seg1 hY hx hy
  · exact hI.disj_seg2 hY (Or.inl (hx)) hy
  · exact hI.disj_seg2 hY (Or.inr hx) hy
  · exact hI.disj_seg3 hY (Or.inl (Or.inl (hx))) hy
  · exact hI.disj_seg3 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg3 hY (Or.inr hx) hy
  · exact hI.disj_seg4 hY (Or.inl (Or.inl (Or.inl (hx)))) hy
  · exact hI.disj_seg4 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg4 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg4 hY (Or.inr hx) hy
  · exact hI.disj_seg5 hY (Or.inl (Or.inl (Or.inl (Or.inl (hx))))) hy
  · exact hI.disj_seg5 hY (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg5 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg5 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg5 hY (Or.inr hx) hy
  · exact hI.disj_seg6 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx)))))) hy
  · exact hI.disj_seg6 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg6 hY (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg6 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg6 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg6 hY (Or.inr hx) hy
  · exact hI.disj_seg7 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx))))))) hy
  · exact hI.disj_seg7 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) hy
  · exact hI.disj_seg7 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg7 hY (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg7 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg7 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg7 hY (Or.inr hx) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx)))))))) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg8 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg8 hY (Or.inr hx) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx))))))))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg9 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg9 hY (Or.inr hx) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx)))))))))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg10 hY (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg10 hY (Or.inr hx) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx))))))))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg11 hY hΨ (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg11 hY hΨ (Or.inr hx) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hx)))))))))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx))))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inl (Or.inr hx)))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inl (Or.inr hx))) hy
  · exact hI.disj_seg12 hY hΨ (Or.inl (Or.inr hx)) hy
  · exact hI.disj_seg12 hY hΨ (Or.inr hx) hy

/-- The records of a riser are pairwise disjoint. [folklore] -/
theorem Riser.pairwise (hY : Y.OK) {σ : Fin 2 → ℤˣ} {u : ℤˣ} {q₀ : Fin 2} {s : BrickPos d} {l : List (BrickRec d)} (h : Riser hd Y σ u q₀ s l) :
    l.Pairwise (fun r r' => PlateDisj Y.L Y.H r.1 r'.1) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have key : ∀ i (hi : i < l.length), (l[i]).1 = legOf l (l.length - 1 - i) := by
    intro i hi
    unfold legOf recOf
    rw [List.getElem?_reverse (by omega), show l.length - 1 - (l.length - 1 - i) = i by omega, List.getElem?_eq_getElem hi]
    rfl
  rw [key i hi, key j hj]
  exact ((h.disj hY).2 (l.length - 1 - j) (l.length - 1 - i) (by omega) (by omega)).symm

/-- The records of a turn are pairwise disjoint. [folklore] -/
theorem Turn.pairwise (hY : Y.OK) {σ σ' : Fin 2 → ℤˣ} {p : Fin 2} {s : BrickPos d} {l : List (BrickRec d)} (h : Turn hd Y e σ σ' p s l) :
    l.Pairwise (fun r r' => PlateDisj Y.L Y.H r.1 r'.1) := by
  have hlen := h.len
  rcases l with _ | ⟨r, _ | ⟨r', _ | ⟨r'', tl⟩⟩⟩
  · exact List.Pairwise.nil
  · exact List.pairwise_singleton _ _
  · rw [List.pairwise_pair]
    have e0 : legOf [r, r'] 0 = r'.1 := by
      rw [show [r, r'] = r :: [r'] from rfl, legOf_cons_of_lt _ _ (by simp)]
      have := legOf_cons_length r' ([] : List (BrickRec d)); rwa [List.length_nil] at this
    have e1 : legOf [r, r'] 1 = r.1 := legOf_cons_length r [r']
    have := h.disj_top_hop hY (by simp)
    rw [e0, e1] at this; exact this.symm
  · simp at hlen

/-- **All plates of an invariant state are pairwise disjoint.** [cite: GrimmettPercolation1999, §7.3 pp. 172–174 (C)] -/
theorem FlatInv.pairwise (hI : FlatInv hd Y a e τ st) (hY : Y.OK) (hΨ : PsiFar hd Y e st) :
    st.all.Pairwise (fun r r' => PlateDisj Y.L Y.H r.1 r'.1) := by
  unfold FS.all
  rw [List.pairwise_flatMap]
  constructor
  · -- within a segment
    intro k _
    have hK := hI.segOK k
    fin_cases k
    · -- segment 0: the lead-in
      simp only [SegOK, Fin.zero_eta, Fin.isValue] at hK ⊢
      by_cases hne : st.segs 0 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨hD, -, -⟩ := hK hne; exact hD.pairwise hY
    · simp only [SegOK, Fin.mk_one, Fin.isValue] at hK ⊢
      by_cases hne : st.segs 1 = []
      · rw [hne]; exact List.Pairwise.nil
      · exact Riser.pairwise hY (hK hne)
    all_goals simp only [SegOK, Fin.isValue, Fin.reduceFinMk] at hK ⊢
    · by_cases hne : st.segs 2 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, _, hD, _⟩ := hK hne; exact hD.pairwise hY
    · by_cases hne : st.segs 3 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hT⟩ := hK hne; exact hT.pairwise hY
    · by_cases hne : st.segs 4 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hD, _⟩ := hK hne; exact hD.pairwise hY
    · by_cases hne : st.segs 5 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hT⟩ := hK hne; exact hT.pairwise hY
    · by_cases hne : st.segs 6 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hD, _⟩ := hK hne; exact hD.pairwise hY
    · by_cases hne : st.segs 7 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hT⟩ := hK hne; exact hT.pairwise hY
    · by_cases hne : st.segs 8 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, _, hD, _⟩ := hK hne; exact hD.pairwise hY
    · by_cases hne : st.segs 9 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hT⟩ := hK hne; exact hT.pairwise hY
    · by_cases hne : st.segs 10 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, _, hD, _⟩ := hK hne; exact hD.pairwise hY
    · by_cases hne : st.segs 11 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hD, _⟩ := hK hne; exact hD.pairwise hY
    · by_cases hne : st.segs 12 = []
      · rw [hne]; exact List.Pairwise.nil
      · obtain ⟨_, _, hD, _⟩ := hK hne; exact hD.pairwise hY
  · -- across segments
    refine (List.pairwise_lt_finRange 13).imp (fun {i j} hij => ?_)
    intro x hx y hy
    exact hI.disj_cross hY hΨ hij hx hy

end BGNd

end Percolation.Literature

end
