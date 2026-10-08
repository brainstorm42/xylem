import Percolation.Literature.CriticalContinuityProofs
import Percolation.Literature.DynamicSiteRenormalization
import Percolation.Literature.FlatKit
import Percolation.Literature.HalfSpaceLemma752
import Percolation.Literature.TallKit
import Percolation.Util.Linter

/-!
# The Barsky–Grimmett–Newman theorem `θ_ℍ(p_c) = 0` in every dimension `d ≥ 2`

Proof of the statement `Percolation.Literature.BarskyGrimmettNewman1991` of `HalfSpace.lean` — Grimmett, *Percolation*, 2nd ed. (1999), Theorem (7.35), p. 162, `θ_ℍ(p_c) = 0` (Barsky–Grimmett–Newman 1991, Thm. 1.1 (i)), for every `d ≥ 2` — (`BarskyGrimmettNewman1991_holds`) by the same argument in
`ℤ^d`, `d ≥ 3` (`BGNd.theta_halfSpace_criticalProbI_eq_zero`; Grimmett p. 163: "a similar
argument is valid when `d > 3`"; Barsky–Grimmett–Newman 1991 work in `ℤ^d` throughout), the case
`d = 2` being Harris–Kesten (`BarskyGrimmettNewman1991_dim_two`, `HalfSpaceHighDim.lean`):

* Lemma (7.36) for clean seeds in `ℤ^d` at every density (`BGNd.lemma_7_36C`,
  `HalfSpaceHighDimClean.lean`; its slab input is the almost sure unboundedness of the height of an
  infinite `ℍ*`-cluster, `HalfSpaceHighDimBounded.lean`, so that no slab theorem is needed): were
  `θ_ℍ(p_c) > 0`, `P_{p_c}(goodC d m L H) > 1 - ν/2` for some `m ≥ 1`, `L ≥ m + 2`, `H ≥ 2m + 3`;
* continuity of `p ↦ P_p(goodC d m L H)` (`BGNd.determinedBy_goodC`), whence `> 1 - ν` at some
  `p' < p_c`;
* Lemma (7.52) in quantitative form in `ℤ^d`: the dynamic renormalization of pp. 170–176 as a good
  block kit (`BlockKit.lean`), by the tall gait when `L + 1 ≤ 8 (H + 1)` (`BGNd.theta_pos_tall`,
  `TallKit.lean`, `R = 2²²` bricks per attempt with `P = 8`) and by the flat gait when
  `8 (H + 1) ≤ L + 1` (`BGNd.theta_pos_flat`, `FlatKit.lean`, `R = 2¹⁵`), with `ν = 1/(64 · 2²²)`:
  `θ(p') > 0` on `ℤ^d`;
* contradicting `θ(p') = 0` for `p' < p_c`.

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2 Thm. (7.8),
  §7.3 Thm. (7.35), Lemmas (7.36), (7.52), pp. 146–176.
* D. J. Barsky, G. R. Grimmett, C. M. Newman, Percolation in half-spaces: equality of critical
  densities and continuity of the percolation probability, Probab. Theory Related Fields 90
  (1991), 111–148, Thm. 1.1.
* H. Duminil-Copin, V. Sidoravicius, V. Tassion, Absence of infinite cluster for critical
  Bernoulli percolation on slabs, Comm. Pure Appl. Math. 69 (2016), 1397–1411.
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory LatticeModels unitInterval

/-- **Theorem (7.35) of Grimmett 1999 in `ℤ^d`, `d ≥ 3`: `θ_ℍ(p_c(ℤ^d)) = 0`** — by Lemma (7.36)
for clean seeds at `p_c`, continuity of `P_p(goodC)` in `p`, and the block construction of Lemma
(7.52) in `ℤ^d` (tall or flat gait according as `L + 1 ≤ 8 (H + 1)` or not), which would make
`θ(p') > 0` at some `p' < p_c`. [cite: GrimmettPercolation1999, Thm. (7.35) p. 163, proof p. 169; Lemmas (7.36), (7.52)] -/
theorem BGNd.theta_halfSpace_criticalProbI_eq_zero {d : ℕ} [NeZero d] (hd : 3 ≤ d) :
    theta (halfSpaceGraph d) (halfSpaceOrigin d) (criticalProbI d) = 0 := by
  by_contra hne
  set p : unitInterval := criticalProbI d with hpdef
  have hθ : 0 < theta (halfSpaceGraph d) (halfSpaceOrigin d) p :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  have hp0 : 0 < (p : ℝ) := by rw [hpdef, coe_criticalProbI]; exact criticalProb_zd_pos d (by omega)
  have hp1 : (p : ℝ) < 1 := by rw [hpdef, coe_criticalProbI]; exact criticalProb_zd_lt_one (by omega)
  -- the constant of Lemma (7.52): `ν = 1/(64 R)` with `R = 2²²` bricks per attempt (tall gait, `P = 8`;
  -- the flat gait uses `2¹⁵`)
  set ν : ℝ := 1 / (64 * 2 ^ 22) with hν
  have hν0 : 0 < ν := by positivity
  -- Lemma (7.36) for clean seeds at `p_c`, with `η = ν / 2`
  obtain ⟨m, H₀, L, H, hm1, hH₀, hH₀H, hLm, -, hgood, -⟩ :=
    BGNd.lemma_7_36C (d := d) (by omega) (fun _ _ => 0) p hp0 hp1 hθ (half_pos hν0)
  have hH1 : 1 ≤ H := by omega
  have hmL : m < L := by omega
  -- `p ↦ P_p(goodC)` is continuous (a cylinder event)
  have hf : Continuous fun q : unitInterval => (bondPercolation (zdGraph d) q).real (BGNd.goodC d m L H) :=
    continuous_bondPercolation_real_of_determinedBy _ (F := BGNd.suppCF d m L H)
      (by rw [BGNd.coe_suppCF]; exact BGNd.determinedBy_goodC hH1 hmL)
  -- below `p_c` the probability of `goodC` is at most `1 - ν`, by the block construction
  have key : ∀ q : unitInterval, 0 < (q : ℝ) → (q : ℝ) < p →
      (bondPercolation (zdGraph d) q).real (BGNd.goodC d m L H) ≤ 1 - ν := by
    intro q hq0 hqp
    by_contra hlt
    push Not at hlt
    have hsmall : 1 - (bondPercolation (zdGraph d) q).real (BGNd.goodC d m L H) < 1 / (64 * 2 ^ 22) := by
      rw [hν] at hlt; linarith
    have hpos : 0 < theta (zdGraph d) 0 q := by
      by_cases hreg : (L : ℤ) + 1 ≤ 8 * ((H : ℤ) + 1)
      · -- tall bricks: the tall gait with `P = 8`, `R = 2¹³ · 8³ = 2²²`
        have hY : BGNd.TallLayout.OK ⟨m, L, H, 8⟩ := by
          refine ⟨?_, ?_, ?_, ?_⟩
          · change m + 1 ≤ L; omega
          · change 2 * m + 2 ≤ H; omega
          · change (L : ℤ) + 1 ≤ ((8 : ℕ) : ℤ) * (((H + 1 : ℕ)) : ℤ); push_cast; linarith
          · change 8 ≤ 8; exact le_rfl
        refine BGNd.theta_pos_tall ⟨m, L, H, 8⟩ hd hY q hq0 ?_
        change ((2 ^ 13 * 8 ^ 3 : ℕ) : ℝ) * (1 - (bondPercolation (zdGraph d) q).real (BGNd.goodC d m L H)) ≤ 1 / 64
        norm_num at hsmall ⊢
        linarith
      · -- flat bricks: the flat gait, `R = 2¹⁵`
        have hY : BGNd.FlatLayout.OK ⟨m, L, H⟩ := by
          refine ⟨?_, ?_, ?_⟩
          · change m + 1 ≤ L; omega
          · change 2 * m + 2 ≤ H; omega
          · change 8 * ((H : ℤ) + 1) ≤ (L : ℤ) + 1; linarith
        refine BGNd.theta_pos_flat ⟨m, L, H⟩ hd hY q hq0 ?_
        change ((2 ^ 15 : ℕ) : ℝ) * (1 - (bondPercolation (zdGraph d) q).real (BGNd.goodC d m L H)) ≤ 1 / 64
        norm_num at hsmall ⊢
        linarith
    have hqc : (q : ℝ) < criticalProb (zdGraph d) (0 : Site d) := by rwa [hpdef, coe_criticalProbI] at hqp
    have hzero := theta_eq_zero_of_lt_criticalProb_holds (zdGraph d) (0 : Site d) q hqc
    linarith
  have hle := le_of_forall_pos_lt_le hf hp0 key
  -- but at `p_c` it exceeds `1 - ν / 2`
  have h1 : (bondPercolation (zdGraph d) p).real (BGNd.goodC d m L H) ≤ 1 - ν := hle
  have h2 : 1 - ν / 2 < (bondPercolation (zdGraph d) p).real (BGNd.goodC d m L H) := hgood
  have h3 : 1 - ν / 2 < 1 - ν := h2.trans_le h1
  rw [hν] at h3
  norm_num at h3

/-- **Theorem (7.35) of Grimmett 1999 (Barsky–Grimmett–Newman 1991, Thm. 1.1 (i)) in every
dimension: for `d ≥ 2`, `θ_ℍ(p_c(ℤ^d)) = 0`** — the statement `BarskyGrimmettNewman1991` of
`HalfSpace.lean`, proved here: `d = 2` by Harris–Kesten (`BarskyGrimmettNewman1991_dim_two`), `d ≥ 3`
by `BGNd.theta_halfSpace_criticalProbI_eq_zero`.
[cite: GrimmettPercolation1999, Thm. (7.35) p. 163 ("Let `d ≥ 2`. We have that `θ_ℍ(p_c) = 0`"), proof pp. 163–176, notes p. 196 (`d = 2`)] -/
theorem BarskyGrimmettNewman1991_holds : BarskyGrimmettNewman1991 := by
  intro d _ hd
  rcases hd.eq_or_lt with rfl | hlt
  · exact BarskyGrimmettNewman1991_dim_two
  · exact BGNd.theta_halfSpace_criticalProbI_eq_zero hlt

end Percolation.Literature
