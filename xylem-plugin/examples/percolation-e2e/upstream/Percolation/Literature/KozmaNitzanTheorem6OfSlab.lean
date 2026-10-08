import Percolation.Literature.HalfSpaceHighDim
import Percolation.Literature.KozmaNitzanReduction
import Percolation.Literature.KozmaNitzanTheorem6
import Percolation.Literature.SlabGluingFact2
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 (`KozmaNitzan2024_thm6`) split at its two printed steps: same-`p` slab percolation (§4) and "a percolating slab means `p > p_c`" (Aizenman–Grimmett)

The statement `Percolation.Literature.KozmaNitzan2024_thm6` (`KozmaNitzanReduction.lean`;
G. Kozma, S. Nitzan, *A reduction of the `θ(p_c) = 0` problem to a conjectured inequality*,
arXiv:2401.12397, Thm 6, p. 15: "If conjecture 3 holds then `P(|C(0)| = ∞) = 0` at the critical
probability for `ℤ^d` for any `d ≥ 2`"; `KozmaNitzan2024_conjecture3 → ∀ d ≥ 2, PercolationContinuity d`)
is proved here through its two printed steps.

The printed proof (p. 25): "**Proof of theorem 6.** Let `p` be such that `θ(p) > 0`. We will show
that at `p` there is percolation in some slab, which will imply, by Aizenman–Grimmett
[Grimmett 1999, §§3.2–3.3], that `p > p_c`. Since `p` was arbitrary with `θ(p) > 0`, this will show
the claim." — followed by six pages (pp. 25–31: the parameter cascade through Lemmas 10–12, the
`(20r)`-block exploration process `(Eᵢ, Gᵢ, Xᵢ)`, Steps I–III) proving that under Conjecture 3 the
block process dominates a supercritical two-dimensional site exploration, "this gives that there
is an infinite cluster in the slab with positive probability (hence with probability `1`)" (p. 31),
the slab being `ℤ² × [-5r, 5r]^{d-2}`; `d = 2` is Harris–Kesten (p. 15: "[Grimmett 1999, §11]").
Accordingly the statement is cut into two steps

and `KozmaNitzan2024_thm6_holds_of` puts the two steps together: `d = 2` by the Harris and Kesten
theorems (`percolationContinuity_two kesten_criticalProb_Z2_holds harris_theta_half_holds`), `d ≥ 3`
by contradiction from the two steps. Neither step restates Theorem 6 (the first is a same-`p`
statement with no critical point in it, the second a statement about `p_c` with no Conjecture 3 in
it); the first step alone gives `PercolationContinuity 3`.

## Proof of the first step

`KozmaNitzan2024_slabPercolation_holds` proves the first step for every `d ≥ 3`, from the formalised
§4 (`KozmaNitzan.exists_KSch_theta_slab_pos`, `KozmaNitzanTheorem6.lean`: under Conjecture 3, for `0
< p < 1` with `θ_{ℤ^d}(p) > 0` the origin percolates at `p` inside KN's slab `{x | |x_j| ≤ 5r for j
≠ 1, 2}`) by the lattice symmetry announced in its docstring: translate by `5r e₀` into `S_{10r} =
{0 ≤ x₀ ≤ 10r}` (`induceShiftIso`, `theta_iso`), enlarge the vertex set (`theta_induce_mono_holds`),
and carry positivity back to the origin of `S_{10r}` along the axis `ℤ e₀` (`theta_pos_of_adj`,
Grimmett 1999 p. 35); the endpoints `p = 0` (`theta_bot`) and `p = 1` (every slab percolates: the
open axis `ℤ e₁`) are elementary.

## Proof of the second step — Theorem 6 is unconditional

`theta_slab_criticalProb_zd_eq_zero_holds` (`KozmaNitzanTheorem6SlabCritical.lean`, which imports
this file) proves the second step for every `d ≥ 3` (indeed `θ_{S_k}(p_c(ℤ^d)) = 0` for every `d ≥
2` and every `k`, `theta_slab_criticalProbI_eq_zero_of_two_le`): `S_k ⊆ ℍ = {0 ≤ x₀}`, monotonicity
of `θ` under inclusion (`theta_induce_mono_holds`, Grimmett 1999 (7.1) p. 146), and the proved
Barsky–Grimmett–Newman theorem `θ_ℍ(p_c) = 0` (`BarskyGrimmettNewman1991_holds`, Grimmett 1999 Thm
(7.35) p. 163). Neither proof uses the consecutive-slab inequality `p_c(S_{k+1}) < p_c(S_k)` of §3.3
item C; that inequality is the subject of the files under `AizenmanGrimmett1991/`, and Grimmett's
literal slabs `ℤ² × {0, …, k}^{d-2}` (equal to `S_k` up to a coordinate permutation when `d = 3`,
strictly thinner when `d ≥ 4`) are treated under `GrimmettMarstrand1990/`.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024): Conjecture 3 and Thm 6 (p. 15), §4 Lemmas 7–12
  (pp. 15–25), proof of Thm 6 (pp. 25–31). [KozmaNitzan2024]
* G. Grimmett, *Percolation*, 2nd ed. (1999): §3.3 Thm (3.16) and item C "Slabs" (pp. 65–66),
  §7.2 p. 148 (`p_c(A)`), §7.3 (7.38) p. 165, §11 (`d = 2`). [GrimmettPercolation1999]
* M. Aizenman, G. Grimmett, *Strict monotonicity for critical points in percolation and
  ferromagnetic models*, J. Stat. Phys. 63 (1991) 817–835. [AizenmanGrimmett1991]
* H. Duminil-Copin, V. Sidoravicius, V. Tassion, Comm. Pure Appl. Math. 69 (2016), Thm 1.
  [DuminilCopinSidoraviciusTassion2016]
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory Percolation.Literature.LatticeModels

/-- **Kozma–Nitzan 2024, §4 (proof of Thm 6, pp. 25–31): under the near-one gluing hypothesis
of Thm 6 (its antecedent, KN's inequality (3) p. 15 — the same antecedent as in
`KozmaNitzan2024_thm6`), an infinite cluster at `p` forces percolation in a slab at the SAME `p`.**
For `d ≥ 3`: if the antecedent holds and `θ_{ℤ^d}(p) > 0` (bond percolation on `zdGraph d`, origin
`0`), then for some `k ≥ 1` the slab `S_k = {x ∈ ℤ^d | 0 ≤ x₀ ≤ k}` (`slabGraph d k`, rooted at
`slabOrigin d k`) percolates at `p`: `θ_{S_k}(p) > 0`. This is a THEOREM in print (an implication,
exactly as Thm 6 itself): Lemma 12 with `ε < 1 - p_c(ℤ², site)`, Lemma 10 ("`δ` does not depend on
the hittable geometry"), Lemma 11 with `K ≥ 20`, `r ≥ 2K max{m, m₂, R}`; the cubes
`M_v = 20vr + [-3r,3r]^d ⊂ Q_v = 20vr + [-5r,5r]^d`, `v ∈ ℤ²`, edges `E_{v,x}`, narrowed `H_{v,x}`;
the exploration `(Eᵢ, Gᵢ, Xᵢ)` with `Eᵢ ⊂ ℤ² × [-5r,5r]^{d-2}` is "a two-dimensional, supercritical
exploration process" (clauses (1)–(3), (28)), Steps I–III ((33)–(37)), hence "there is an infinite
cluster in the slab with positive probability" (p. 31). KN's slab `ℤ² × [-5r,5r]^{d-2}` lies in
`S_{10r}` after a lattice symmetry (bound the coordinate `x₀` only), and positivity transfers to
the origin of the connected graph `S_k` (Harris–FKG), so this rendering is implied by the printed
statement. Proved below for every `d ≥ 3`: `KozmaNitzan2024_slabPercolation_holds` (Lemmas 10–12
in `KozmaNitzanTargetLemma.lean` / `KozmaNitzanCorridor.lean`, the exploration process in
`KozmaNitzanTheorem6.lean`).
[cite: KozmaNitzan2024, Thm 6, proof pp. 25–31 (with Lemmas 10–12)] -/
def KozmaNitzan2024_slabPercolation : Prop :=
  KozmaNitzan2024_conjecture3 →
    ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ p : unitInterval,
      0 < theta (zdGraph d) (0 : Site d) p →
        ∃ k : ℕ, 0 < k ∧ 0 < theta (slabGraph d k) (slabOrigin d k) p

/-- **No slab of `ℤ^d` percolates at `p_c(ℤ^d)`** (`d ≥ 3`, `k ≥ 1`): `θ_{S_k}(p_c(ℤ^d)) = 0` for `S_k
 = {0 ≤ x₀ ≤ k}` (`slabGraph d k`, `criticalProbI d = p_c(zdGraph d)`). Grimmett 1999, (7.38) (p.
 165, there `d = 3`: "`P_{p_c}(b(0) ↔ ∞ in S_h) = 0` for all `h`", read off "`p_c(S_h) > p_c` from
 the discussion following Theorem (3.16)"), i.e. the Aizenman–Grimmett strict inequality for the
 essential enhancement `S_k ⊂ S_{k+1}` (§3.3 item C "Slabs", pp. 65–66; Aizenman–Grimmett 1991):
 `p_c(ℤ^d) ≤ p_c(S_{k+1}) < p_c(S_k)`, and `θ_{S_k}` vanishes below `p_c(S_k)`. This is the step
 "percolation in some slab at `p` will imply, by Aizenman–Grimmett, that `p > p_c`" of the proof of
 KN Thm 6 (p. 25). [cite: GrimmettPercolation1999, §7.3 (7.38) p. 165 and §3.3 Thm (3.16) with item
 C, pp. 65–66] [cite: AizenmanGrimmett1991, Thm 1 (essential enhancements)]
-/
def theta_slab_criticalProb_zd_eq_zero : Prop :=
  ∀ (d : ℕ) [NeZero d], 3 ≤ d → ∀ k : ℕ, 0 < k →
    theta (slabGraph d k) (slabOrigin d k) (criticalProbI d) = 0

/-- **Kozma–Nitzan's Theorem 6 from its two steps.** `d = 2` is
Harris–Kesten (`percolationContinuity_two` with `kesten_criticalProb_Z2_holds`,
`harris_theta_half_holds`; KN p. 15); for `d ≥ 3`, if `θ_{ℤ^d}(p_c) > 0` then the first step
gives a slab percolating at `p_c(ℤ^d)`, contradicting the second.
[cite: KozmaNitzan2024, Thm 6 (proof, p. 25)] -/
theorem KozmaNitzan2024_thm6_holds_of (hslab : KozmaNitzan2024_slabPercolation)
    (hAG : theta_slab_criticalProb_zd_eq_zero) : KozmaNitzan2024_thm6 := by
  intro hC d hd
  rcases Nat.lt_or_ge d 3 with h2 | h3
  · obtain rfl : d = 2 := by omega
    exact percolationContinuity_two kesten_criticalProb_Z2_holds harris_theta_half_holds
  · haveI : NeZero d := ⟨by omega⟩
    change theta (zdGraph d) 0 (criticalProbI d) = 0
    by_contra hne
    have hpos : 0 < theta (zdGraph d) 0 (criticalProbI d) :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    obtain ⟨k, hk, hθ⟩ := hslab hC d h3 _ hpos
    exact hθ.ne' (hAG d h3 k hk)

/-! ## Proof of the first step: from KN's slab `ℤ² × [-5r, 5r]^{d-2}` to `S_{10r}` -/

section SlabTransfer

variable {d : ℕ}

/-- Consecutive points of a coordinate axis of `ℤ^d` are adjacent. [folklore] -/
theorem zdGraph_adj_single_succ (i : Fin d) (n : ℤ) :
    (zdGraph d).Adj (Pi.single i n) (Pi.single i (n + 1)) := by
  rw [zdGraph_adj_iff]
  refine ⟨i, Or.inl ?_⟩
  rw [← Pi.single_add]

/-- The axis point `n e₀`, `n ≤ k`, lies in the slab `S_k = {0 ≤ x₀ ≤ k}`. [folklore] -/
theorem single_zero_natCast_mem_slab [NeZero d] {k n : ℕ} (hn : n ≤ k) :
    (Pi.single 0 (n : ℤ) : Site d) ∈ slab d k :=
  ⟨by simp, by simpa using hn⟩

/-- **Positivity of `θ` in a slab passes from the axis `ℤ e₀ ∩ S_k` to the origin**: if
`θ_{S_k}(n e₀, p) > 0` for some `n ≤ k` then `θ_{S_k}(0, p) > 0` — `n` applications of "positivity
passes between adjacent roots" (Grimmett 1999, p. 35, `theta_pos_of_adj`) along the path
`n e₀, (n-1) e₀, …, 0` inside `S_k`. [cite: GrimmettPercolation1999, §2.2 p. 35 (before Thm. (2.8))] -/
theorem theta_slabOrigin_pos_of_axis [NeZero d] {k : ℕ} (p : unitInterval) :
    ∀ n : ℕ, ∀ hn : n ≤ k,
      0 < theta (slabGraph d k) ⟨Pi.single 0 (n : ℤ), single_zero_natCast_mem_slab hn⟩ p →
        0 < theta (slabGraph d k) (slabOrigin d k) p
  | 0, _, h => by
    have h0 : (⟨Pi.single 0 ((0 : ℕ) : ℤ), single_zero_natCast_mem_slab (Nat.zero_le k)⟩ :
        slab d k) = slabOrigin d k :=
      Subtype.ext (by simp [slabOrigin])
    rwa [h0] at h
  | n + 1, hn, h => by
    refine theta_slabOrigin_pos_of_axis p n (Nat.le_of_succ_le hn) ?_
    refine theta_pos_of_adj (slabGraph d k) ?_ p h
    change (zdGraph d).Adj (Pi.single 0 (n : ℤ)) (Pi.single 0 ((n + 1 : ℕ) : ℤ))
    push_cast
    exact zdGraph_adj_single_succ 0 n

/-- **Every slab percolates at `p = 1`** (`d ≥ 2`): under `P_1` every edge of `S_k` is open and the
axis `ℤ e₁` lies in `S_k`, so the open cluster of the origin is infinite, `θ_{S_k}(0, 1) > 0`
(indeed `= 1`). [folklore] -/
theorem theta_slabGraph_one_pos_of_two_le [NeZero d] (hd : 2 ≤ d) (k : ℕ) :
    0 < theta (slabGraph d k) (slabOrigin d k) 1 := by
  have hmeas : bondPercolation (slabGraph d k) 1 = Measure.dirac (slabGraph d k).edgeSet := by
    rw [bondPercolation]; exact ProbabilityTheory.setBernoulli_one _
  rw [theta, hmeas, measureReal_def, Measure.dirac_apply_of_mem, ENNReal.toReal_one]
  · exact one_pos
  -- the axis `ℤ e₁` through the origin lies in the open cluster of `E(S_k)`
  set i : Fin d := ⟨1, hd⟩ with hi
  have hi0 : (0 : Fin d) ≠ i := by simp [hi, Fin.ext_iff]
  have hmem : ∀ z : ℤ, (Pi.single i z : Site d) ∈ slab d k := fun z =>
    ⟨by simp [Pi.single_eq_of_ne hi0], by simp [Pi.single_eq_of_ne hi0]⟩
  set f : ℕ → slab d k := fun n => ⟨Pi.single i (n : ℤ), hmem n⟩ with hf
  have hadj : ∀ n, (openGraph ((slabGraph d k).edgeSet)).Adj (f n) (f (n + 1)) := by
    intro n
    have hzd : (slabGraph d k).Adj (f n) (f (n + 1)) := by
      change (zdGraph d).Adj (Pi.single i (n : ℤ)) (Pi.single i ((n + 1 : ℕ) : ℤ))
      push_cast
      exact zdGraph_adj_single_succ i n
    exact (openGraph_adj _ _ _).2 ⟨(SimpleGraph.mem_edgeSet _).2 hzd, hzd.ne⟩
  have hreach : ∀ n, f n ∈ openCluster ((slabGraph d k).edgeSet) (slabOrigin d k) := by
    intro n
    induction n with
    | zero =>
      have h0 : f 0 = slabOrigin d k := Subtype.ext (by simp [hf, slabOrigin])
      rw [h0]; exact mem_openCluster_self _ _
    | succ n ih => exact SimpleGraph.Reachable.trans ih (hadj n).reachable
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    have := congrFun h1 i
    simpa [hf] using this
  exact Set.infinite_of_injective_forall_mem hinj hreach

/-- **Theorem 6 of Kozma–Nitzan in `d ≥ 3`, in the slabs `S_k`** (the interior `0 < p < 1`): Conjecture
 3 and `θ_{ℤ^d}(p) > 0` give `k > 0` with `θ_{S_k}(0, p) > 0`, `S_k = {0 ≤ x₀ ≤ k}`. From
 `KozmaNitzan.exists_KSch_theta_slab_pos` (percolation at `p` of the origin inside KN's slab `{|x_j|
 ≤ 5r, j ≠ 1, 2} ⊇ ℤ² × [-5r, 5r]^{d-2}`, pp. 25–31): the translate by `5r e₀` of that slab lies in
 `S_{10r}` (`induceShiftIso`, `theta_iso`, `theta_induce_mono_holds`), and positivity returns to the
 origin along `ℤ e₀` (`theta_slabOrigin_pos_of_axis`). [cite: KozmaNitzan2024, §4 Theorem 6 (pp.
 25–31)]
-/
theorem KozmaNitzan.exists_slab_theta_pos_of_three_le [NeZero d] (hC : KozmaNitzan2024_conjecture3)
    (hd : 3 ≤ d) (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hθ : 0 < theta (zdGraph d) (0 : Site d) p) :
    ∃ k : ℕ, 0 < k ∧ 0 < theta (slabGraph d k) (slabOrigin d k) p := by
  obtain ⟨S, rfl, hθ'⟩ := KozmaNitzan.exists_KSch_theta_slab_pos hC hd p hp0 hp1 hθ
  have hr := S.C.r_pos
  refine ⟨10 * S.C.r, by omega, ?_⟩
  set v : Site d := Pi.single 0 ((5 * S.C.r : ℕ) : ℤ) with hv
  set T : Set (Site d) := {x | x - v ∈ S.slab} with hT
  have hiff : ∀ x : Site d, x ∈ S.slab ↔ x + v ∈ T := fun x => by
    show x ∈ S.slab ↔ x + v - v ∈ S.slab
    rw [add_sub_cancel_right]
  have hvT : v ∈ T := by
    show v - v ∈ S.slab
    rw [sub_self]; exact S.zero_mem_slab
  have h1 : theta ((zdGraph d).induce T) ⟨v, hvT⟩ S.p =
      theta ((zdGraph d).induce S.slab) ⟨0, S.zero_mem_slab⟩ S.p := by
    have h := theta_iso (induceShiftIso v hiff) ⟨0, S.zero_mem_slab⟩ S.p
    have heq : (induceShiftIso v hiff ⟨0, S.zero_mem_slab⟩ : T) = ⟨v, hvT⟩ :=
      Subtype.ext (zero_add _)
    rw [heq] at h
    exact h
  have h5 : 5 * S.C.r ≤ 10 * S.C.r := by omega
  have hTslab : T ⊆ slab d (10 * S.C.r) := by
    intro x hx
    have h0 : (0 : Fin d) ≠ S.C.ax0 := by simp [Cells.ax0, Fin.ext_iff]
    have h0' : (0 : Fin d) ≠ S.C.ax1 := by simp [Cells.ax1, Fin.ext_iff]
    have := hx 0 h0 h0'
    simp only [hv, Pi.sub_apply, Pi.single_eq_same] at this
    rw [abs_le] at this
    push_cast at this
    refine ⟨by linarith [this.1], ?_⟩
    push_cast; linarith [this.2]
  have h2 : theta ((zdGraph d).induce T) ⟨v, hvT⟩ S.p ≤
      theta (slabGraph d (10 * S.C.r)) ⟨v, hTslab hvT⟩ S.p :=
    theta_induce_mono_holds (zdGraph d) hTslab v hvT S.p
  have hpos : 0 < theta (slabGraph d (10 * S.C.r))
      ⟨Pi.single 0 ((5 * S.C.r : ℕ) : ℤ), single_zero_natCast_mem_slab h5⟩ S.p := by
    have hle := h2
    linarith
  exact theta_slabOrigin_pos_of_axis S.p (5 * S.C.r) h5 hpos

end SlabTransfer

/-- **`KozmaNitzan2024_slabPercolation` holds** (Kozma–Nitzan 2024, §4: under
Conjecture 3, in every `d ≥ 3`, an infinite cluster at `p` forces a slab `S_k`, `k > 0`, to
percolate at the same `p`). Interior `0 < p < 1`: `KozmaNitzan.exists_slab_theta_pos_of_three_le`
(the formalised exploration process of pp. 25–31 on top of Lemmas 7–12); `p = 0` is excluded by
`θ(0) = 0`; at `p = 1` every slab percolates. [cite: KozmaNitzan2024, Thm 6, proof pp. 25–31 (with Lemmas 10–12)] -/
theorem KozmaNitzan2024_slabPercolation_holds : KozmaNitzan2024_slabPercolation := by
  intro hC d _ hd p hθ
  rcases eq_or_lt_of_le p.2.1 with hp0 | hp0
  · -- `p = 0`: `θ_{ℤ^d}(0) = 0`, contradicting `hθ`
    exfalso
    obtain rfl : p = 0 := Subtype.ext hp0.symm
    exact hθ.ne' (theta_bot (zdGraph d) (0 : Site d))
  rcases eq_or_lt_of_le p.2.2 with hp1 | hp1
  · -- `p = 1`: every slab percolates
    obtain rfl : p = 1 := Subtype.ext hp1
    exact ⟨1, one_pos, theta_slabGraph_one_pos_of_two_le (by omega) 1⟩
  exact KozmaNitzan.exists_slab_theta_pos_of_three_le hC hd p hp0 hp1 hθ

/-- **Theorem 6 in every `d ≥ 2`, modulo the Aizenman–Grimmett slab statement alone**: with the first
step proved, `KozmaNitzan2024_thm6` follows from `theta_slab_criticalProb_zd_eq_zero`
(`θ_{S_k}(p_c(ℤ^d)) = 0`; proved for every `d ≥ 3` by `theta_slab_criticalProb_zd_eq_zero_holds`,
whence the unconditional `KozmaNitzan2024_thm6_holds` — both in `KozmaNitzanTheorem6SlabCritical.lean`).
[cite: KozmaNitzan2024, Thm 6 (proof, p. 25)] -/
theorem KozmaNitzan2024_thm6_of_slabCritical (hAG : theta_slab_criticalProb_zd_eq_zero) :
    KozmaNitzan2024_thm6 :=
  KozmaNitzan2024_thm6_holds_of KozmaNitzan2024_slabPercolation_holds hAG

end Percolation.Literature

end
