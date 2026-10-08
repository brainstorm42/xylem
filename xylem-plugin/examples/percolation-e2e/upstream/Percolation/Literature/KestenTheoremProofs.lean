import Percolation.Literature.BernoulliPercolationProofs
import Percolation.Literature.ConnectivityProofs
import Percolation.Literature.HarrisTheorem
import Percolation.Literature.KestenTheorem
import Percolation.Literature.RSWLemma
import Percolation.Literature.SharpnessDCTProofs
import Percolation.Util.Linter

/-!
# Kesten's theorem `p_c(ℤ²) = 1/2`: final assembly

This file proves the statement
`Percolation.Literature.kesten_criticalProb_Z2 : criticalProb (zdGraph 2) 0 = 1/2`
(`BernoulliPercolation.lean`; Kesten, *Comm. Math. Phys.* 74 (1980) 41–59,
Thm. 1: "the critical probability of bond percolation on the square lattice equals 1/2"; lower
bound `p_c ≥ 1/2` by Harris, *Proc. Camb. Phil. Soc.* 56 (1960) 13) by plugging the proved
inputs of the DAG of `KestenTheorem.lean` into
`kesten_criticalProb_Z2_of_sharpness` (Grimmett, *Percolation* (1999), Thm. (11.11), second
proof, p. 294):

* `p_c ≤ 1/2`: sharpness of the phase transition on `ℤ^d` (`perc_sharpness`, Duminil-Copin–Tassion
  2016, Thm. 1.1(1); `DCT16.perc_sharpness_holds` of `SharpnessDCTProofs.lean`) and the
  self-duality `h_{1/2}(n + 1, n) = 1/2` (`crossingProb_half_succ_self_holds`, `RSWProofs.lean`,
  Grimmett Lemma (11.21)), combined in `criticalProb_Z2_le_half_of_sharpness`
  (`KestenTheorem.lean`): if `p_c > 1/2` then `1/2 = h_{1/2}(n + 1, n) ≤ (n + 1) e^{-c n} → 0`.

Also proved here: Kesten's Thm. 2 (1.5), `θ(p) > 0` for `p > 1/2` (`Kesten1980_theta_pos_holds`, from `p_c ≤ 1/2` and
`theta_pos_of_criticalProb_lt_holds` of `BernoulliPercolationProofs.lean`), (1.6), `θ(p) = 0` for
`p ≤ 1/2` (`Kesten1980_theta_eq_zero`) and (1.7), exponential decay of the one-arm probability
for `p < 1/2` (`Kesten1980_expDecay`); and the three remaining
statements of `KestenTheorem.lean` along Bollobás–Riordan's Ch. 3 approach — Thm. 10
(`P_p(E_∞) = 1` for `p > 1/2`, from Thm. 2 (1.5) and the zero–one law
`Grimmett1999_prob_exists_percolatesAt_holds`, `ConnectivityProofs.lean`), Lemma 8 (sharp
threshold `h_p(ρ n, n) ≥ 1 - n^{-γ}`, here with `γ = 1`, from duality
`crossingProb_add_crossingProb_symm_holds`, the union bound `crossingProb_succ_le` and sharpness
at the dual parameter `1 - p < 1/2 = p_c`: `1 - h_p(ρ n, n) = h_{1-p}(n, ρ n - 1) ≤ ρ n e^{-c (n - 1)}
≤ n^{-1}` for large `n`) and its qualitative form Lemma 9 (`BollobasRiordan2006_ch3_lemma9_of_lemma8`).
Bollobás–Riordan prove Lemma 8 (with some `γ(p) > 0`) by the Friedgut–Kalai
sharp-threshold theorem *before* `p_c = 1/2` is known (Ch. 3, p. 58); here it is derived
*after* Kesten's theorem, from exponential decay in the subcritical phase `p < 1/2` (the
conclusion of Bollobás–Riordan's Ch. 3, Thm. 12, p. 63, there deduced from Lemma 9; here the
input `perc_sharpness`), which gives the printed statement with `γ = 1`; the union-bound step
is that of Grimmett 1999, Thm. (11.11), second proof, p. 294 (`crossingProb_succ_le`).

## References
* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980) 41–59, Thm. 1, Thm. 2 (1.5)–(1.7), proof of Thm. 2 p. 54
  [KestenCMP1980].
* T. E. Harris, *A lower bound for the critical probability in a certain percolation process*,
  Proc. Camb. Phil. Soc. 56 (1960) 13–20 [HarrisPCPS1960].
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), Thm. (11.11) (second proof, p. 294),
  Thm. (11.12), Thm. (1.11) [GrimmettPercolation1999].
* B. Bollobás, O. Riordan, *Percolation*, CUP (2006), Ch. 3, Thm. 6, Lemma 8, Lemma 9, Thm. 10
  [BollobasRiordanPercolation2006].
* H. Duminil-Copin, V. Tassion, L'Enseignement Math. 62 (2016) 199–206, Thm. 1.1
  [DuminilCopinTassionEM2016].
-/

namespace Percolation.Literature

open LatticeModels MeasureTheory Filter Topology unitInterval

noncomputable section

/-! ### Kesten's theorem -/

/-- **Kesten's theorem** (Kesten, *Comm. Math. Phys.* 74 (1980), Thm. 1): the critical
probability of bond percolation on the square lattice is `p_c(ℤ²) = 1/2`; proof of the statement
`kesten_criticalProb_Z2` along Grimmett 1999, Thm. (11.11), second proof (Harris' theorem +
sharpness + self-duality), via `kesten_criticalProb_Z2_of_sharpness` (`KestenTheorem.lean`). [cite: KestenCMP1980, Thm. 1] [cite: GrimmettPercolation1999, Thm. 11.11 (second proof)] -/
theorem kesten_criticalProb_Z2_holds : kesten_criticalProb_Z2 :=
  kesten_criticalProb_Z2_of_sharpness harris_theta_half_holds DCT16.perc_sharpness_holds
    crossingProb_half_succ_self_holds

/-- **Kesten 1980, Thm. 2 (1.5)**: `θ(p) > 0` for `p > 1/2` on `ℤ²`, proving the statement
`Kesten1980_theta_pos` (`KestenTheorem.lean`) from `p_c ≤ 1/2`
(`criticalProb_Z2_le_half_of_sharpness`) and `θ > 0` above `p_c`
(`theta_pos_of_criticalProb_lt_holds`, `BernoulliPercolationProofs.lean`). [cite: KestenCMP1980, Thm. 2 (1.5)] -/
theorem Kesten1980_theta_pos_holds : Kesten1980_theta_pos :=
  Kesten1980_theta_pos_of_sharpness DCT16.perc_sharpness_holds crossingProb_half_succ_self_holds
    theta_pos_of_criticalProb_lt_holds

/-- **Kesten 1980, Thm. 2 (1.6)**: `θ(p) = 0` for every `p ≤ 1/2` on `ℤ²` (Kesten, p. 54:
"(1.5) and (1.6) are immediate from the definition of `p_H` and Theorem 1, except when
`p = 1/2`. But `θ(1/2) = 0` was already proved by Harris"): from Harris' theorem
`harris_theta_half_holds` and the monotonicity of `θ` (`theta_mono_holds`). [cite: KestenCMP1980, Thm. 2 (1.6)] -/
theorem Kesten1980_theta_eq_zero (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    theta (zdGraph 2) (0 : Site 2) p = 0 := by
  refine le_antisymm ?_ measureReal_nonneg
  have hle : p ≤ half := Subtype.coe_le_coe.1 (by simpa using hp)
  have hH : theta (zdGraph 2) (0 : Site 2) half = 0 := harris_theta_half_holds
  exact hH ▸ theta_mono_holds (zdGraph 2) (0 : Site 2) hle

/-- **Kesten 1980, Thm. 2 (1.7), one-arm form** (exponential decay below `1/2`: Kesten states
that for any `p < 1/2` there is a constant `C₁(p) > 0` such that, for all `n ≥ 1`, the
probability `P_p{W contains vertices at distance ≥ n from the origin}` is exponentially small
in `n`; proof on p. 54: "(1.7) is a special case of Theorem 1 of [10] … now that we know
`p_T = p_H = 1/2`"). Here in the form of `perc_sharpness`: for `p < 1/2` there is `c > 0`
with `P_p(0 ↔ ∂B(n) in B(n)) ≤ e^{-c n}` for all `n`; from sharpness on `ℤ²`
(`DCT16.perc_sharpness_holds`, Duminil-Copin–Tassion 2016, Thm. 1.1(1)) and `p_c = 1/2`
(`kesten_criticalProb_Z2_holds`). (Bollobás–Riordan 2006, Ch. 3, Thm. 12 is the cluster-size
form.) [cite: KestenCMP1980, Thm. 2 (1.7)] [cite: DuminilCopinTassionEM2016, Thm. 1.1(1)] -/
theorem Kesten1980_expDecay (p : unitInterval) (hp : (p : ℝ) < 1 / 2) :
    ∃ c > 0, ∀ n : ℕ,
      (bondPercolation (zdGraph 2) p).real (siteToBoundary 2 n) ≤ Real.exp (-c * n) :=
  DCT16.perc_sharpness_holds (d := 2) le_rfl p (by rw [kesten_criticalProb_Z2_holds]; exact hp)

/-! ### Bollobás–Riordan's Ch. 3 approach, a posteriori -/

/-- **Bollobás–Riordan 2006, Ch. 3, Thm. 10 from Kesten's Thm. 2 (1.5) and the zero–one law**
("Recall that `P_p(E_∞) > 0` implies that `P_p(E_∞) = 1` and `θ(p) > 0`"; conversely
`θ(p) > 0 ⟹ P_p(E_∞) = 1`, Grimmett 1999, Thm. (1.11), second clause of
`Grimmett1999_prob_exists_percolatesAt`). [cite: BollobasRiordanPercolation2006, Ch. 3, Thm. 10] [cite: GrimmettPercolation1999, Thm. 1.11] -/
theorem BollobasRiordan2006_ch3_thm10_of_theta_pos (hK : Kesten1980_theta_pos)
    (h01 : Grimmett1999_prob_exists_percolatesAt) : BollobasRiordan2006_ch3_thm10 :=
  fun p hp => (h01 2 p).2 (hK p hp)

/-- **Bollobás–Riordan 2006, Ch. 3, Thm. 10**: for bond percolation on `ℤ²` and `p > 1/2`,
`P_p(E_∞) = 1`; proof of the statement `BollobasRiordan2006_ch3_thm10` from
`Kesten1980_theta_pos_holds` and the zero–one law `Grimmett1999_prob_exists_percolatesAt_holds`
(`ConnectivityProofs.lean`). [cite: BollobasRiordanPercolation2006, Ch. 3, Thm. 10] -/
theorem BollobasRiordan2006_ch3_thm10_holds : BollobasRiordan2006_ch3_thm10 :=
  BollobasRiordan2006_ch3_thm10_of_theta_pos Kesten1980_theta_pos_holds
    Grimmett1999_prob_exists_percolatesAt_holds

/-- `ρ n² e^{-c (n - 1)} → 0` as `n → ∞` for `c > 0` (polynomial times decaying exponential;
Mathlib's `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`). [folklore] -/
theorem tendsto_const_mul_sq_mul_exp_neg (ρ c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ρ * (n : ℝ) ^ 2 * Real.exp (-(c * ((n : ℝ) - 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hcn : Tendsto (fun n : ℕ => c * n) atTop atTop :=
    (tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have h2 : Tendsto (fun n : ℕ => (c * n) ^ 2 * Real.exp (-(c * n))) atTop (𝓝 0) := h1.comp hcn
  have h3 : Tendsto (fun n : ℕ => (ρ * Real.exp c / c ^ 2) * ((c * n) ^ 2 * Real.exp (-(c * n))))
      atTop (𝓝 0) := by simpa using h2.const_mul (ρ * Real.exp c / c ^ 2)
  refine h3.congr fun n => ?_
  have : -(c * ((n : ℝ) - 1)) = c + -(c * n) := by ring
  rw [this, Real.exp_add]
  field_simp

/-- **Bollobás–Riordan 2006, Ch. 3, Lemma 8 from sharpness, `p_c = 1/2` and duality** (with
`γ = 1`). For `p > 1/2` the dual parameter `1 - p < 1/2 = p_c` is subcritical
(`kesten_criticalProb_Z2`), so `P_{1-p}(0 ↔ ∂B(n)) ≤ e^{-c n}` (`perc_sharpness`); by duality
(`crossingProb_add_crossingProb_symm`, Bollobás–Riordan Ch. 3, Cor. 3(i)) and the union bound of
Grimmett's second proof of Thm. (11.11) (`crossingProb_succ_le`),
`1 - h_p(ρ n, n) = h_{1-p}(n, ρ n - 1) ≤ ρ n · P_{1-p}(0 ↔ ∂B(n - 1)) ≤ ρ n e^{-c (n - 1)} ≤ n^{-1}`
for `n ≥ n₀(p, ρ)`. (Bollobás–Riordan obtain some `γ(p) > 0` via Friedgut–Kalai before `p_c` is
identified; the statement vendored in `KestenTheorem.lean` only asks for some `γ > 0`.) [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 8] [cite: GrimmettPercolation1999, Thm. 11.11 (second proof, p. 294)] -/
theorem BollobasRiordan2006_ch3_lemma8_of_sharpness (hS : perc_sharpness)
    (hK : kesten_criticalProb_Z2) (hdual : crossingProb_add_crossingProb_symm) :
    BollobasRiordan2006_ch3_lemma8 := by
  intro p hp
  -- the dual parameter `1 - p < 1/2 = p_c` is subcritical
  have hsub : ((σ p : unitInterval) : ℝ) < criticalProb (zdGraph 2) 0 := by
    rw [hK, coe_symm_eq]; linarith
  obtain ⟨c, hc, hdecay⟩ := hS (d := 2) le_rfl (σ p) hsub
  refine ⟨1, one_pos, fun ρ hρ => ?_⟩
  -- `ρ n² e^{-c (n - 1)} → 0`, so it is eventually `≤ 1`
  have hev : ∀ᶠ n : ℕ in atTop, (ρ : ℝ) * (n : ℝ) ^ 2 * Real.exp (-(c * ((n : ℝ) - 1))) ≤ 1 :=
    (tendsto_const_mul_sq_mul_exp_neg ρ c hc).eventually (eventually_le_nhds one_pos)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 hev
  refine ⟨max n₁ 1, le_max_right _ _, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hnn₁ : n₁ ≤ n := le_of_max_le_left hn
  -- indices: `n = m + 1`, `ρ n - 1 = (ρ n - 2) + 1`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have h2 : 2 ≤ ρ * n := by nlinarith
  have hρn : ρ * n - 1 = (ρ * n - 2) + 1 := by omega
  -- duality: `h_p(ρ n, n) = 1 - h_{1-p}(n, ρ n - 1)`
  have hdual' : crossingProb p (ρ * n - 1) (n - 1) =
      1 - crossingProb (σ p) (m + 1) (ρ * n - 2) := by
    have h := hdual p (ρ * n - 2) m
    rw [hρn, show n - 1 = m by omega]
    linarith
  rw [hdual', Real.rpow_neg_one]
  -- union bound and sharpness: `h_{1-p}(n, ρ n - 1) ≤ (ρ n - 1) e^{-c (n - 1)}`
  have hle : crossingProb (σ p) (m + 1) (ρ * n - 2) ≤
      (((ρ * n - 2 : ℕ) : ℝ) + 1) * Real.exp (-c * m) :=
    calc crossingProb (σ p) (m + 1) (ρ * n - 2)
        ≤ (((ρ * n - 2 : ℕ) : ℝ) + 1) *
            (bondPercolation (zdGraph 2) (σ p)).real (siteToBoundary 2 m) :=
          crossingProb_succ_le (σ p) m (ρ * n - 2)
      _ ≤ (((ρ * n - 2 : ℕ) : ℝ) + 1) * Real.exp (-c * m) := by gcongr; exact hdecay m
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hm' : (m : ℝ) = n - 1 := by rw [hm]; push_cast; ring
  have hcast : ((ρ * n - 2 : ℕ) : ℝ) + 1 ≤ (ρ : ℝ) * n := by
    rw [Nat.cast_sub h2]; push_cast; linarith
  have hX : crossingProb (σ p) (m + 1) (ρ * n - 2) ≤
      (ρ : ℝ) * n * Real.exp (-(c * ((n : ℝ) - 1))) := by
    refine hle.trans ?_
    rw [show -c * (m : ℝ) = -(c * ((n : ℝ) - 1)) by rw [hm']; ring]
    gcongr
  -- `ρ n e^{-c (n - 1)} ≤ n⁻¹` since `ρ n² e^{-c (n - 1)} ≤ 1`
  have hfin : (ρ : ℝ) * n * Real.exp (-(c * ((n : ℝ) - 1))) ≤ (n : ℝ)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hn0]
    calc (ρ : ℝ) * n * Real.exp (-(c * ((n : ℝ) - 1))) * n
        = ρ * (n : ℝ) ^ 2 * Real.exp (-(c * ((n : ℝ) - 1))) := by ring
      _ ≤ 1 := hn₁ n hnn₁
  linarith

/-- **Bollobás–Riordan 2006, Ch. 3, Lemma 8** ("Let `p > 1/2` and an integer `ρ > 1` be fixed.
There are constants `γ = γ(p) > 0` and `n₀ = n₀(p, ρ)` such that `h_p(ρ n, n) ≥ 1 - n^{-γ}` for
all `n ≥ n₀`"), proved with `γ = 1` from `DCT16.perc_sharpness_holds`,
`kesten_criticalProb_Z2_holds` and `crossingProb_add_crossingProb_symm_holds`. [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 8] -/
theorem BollobasRiordan2006_ch3_lemma8_holds : BollobasRiordan2006_ch3_lemma8 :=
  BollobasRiordan2006_ch3_lemma8_of_sharpness DCT16.perc_sharpness_holds
    kesten_criticalProb_Z2_holds crossingProb_add_crossingProb_symm_holds

/-- **Bollobás–Riordan 2006, Ch. 3, Lemma 9** ("Let `p > 1/2` be fixed. If `R_n` is a `3n` by `n`
rectangle in `ℤ²`, then `P_p(H(R_n)) → 1` as `n → ∞`"), proved from Lemma 8
(`BollobasRiordan2006_ch3_lemma9_of_lemma8`, `KestenTheorem.lean`). [cite: BollobasRiordanPercolation2006, Ch. 3, Lemma 9] -/
theorem BollobasRiordan2006_ch3_lemma9_holds : BollobasRiordan2006_ch3_lemma9 :=
  BollobasRiordan2006_ch3_lemma9_of_lemma8 BollobasRiordan2006_ch3_lemma8_holds

end

end Percolation.Literature
