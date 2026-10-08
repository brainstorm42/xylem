/-
Finite-grid approximation for the empirical Rockafellar--Uryasev CVaR objective.

The useful estimate is a threshold estimate, rather than a separate estimate for
the threshold term and the hinge term.  If `s ≤ t`, each hinge decreases by an
amount in `[0, t - s]`.  Consequently the objective difference has the form
`(t - s) - c A`, with `0 ≤ A ≤ q (t - s)` and
`c = 1 / (q (1 - α))`.  Since `0 ≤ α < 1`, both possible slopes are bounded in
absolute value by `1 / (1 - α)`.  Applying this at an attained sample threshold
and then taking the finite grid minimum gives the stated grid error.
-/
import Ctrllib.CvarInfForm

open scoped BigOperators

namespace Ctrllib

variable {q : ℕ}

/-- The empirical CVaR objective is Lipschitz in its auxiliary threshold, with the
global bound `1 / (1 - α)`.  The proof uses the ordered hinge
differences, so it does not lose an additional `1` by applying the triangle
inequality to the two summands of `cvarObj`. -/
theorem cvarObj_threshold_lipschitz (α : ℝ) (Z : Fin q → ℝ)
    (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1) (s t : ℝ) :
    |cvarObj α Z s - cvarObj α Z t| ≤ |s - t| / (1 - α) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hρ : (0 : ℝ) < 1 - α := by linarith
  have hc : (0 : ℝ) ≤ 1 / ((q : ℝ) * (1 - α)) := by
    exact le_of_lt (div_pos one_pos (mul_pos hq' hρ))
  have hone : ∀ {u v : ℝ}, u ≤ v →
      |cvarObj α Z u - cvarObj α Z v| ≤ (v - u) / (1 - α) := by
    intro u v huv
    have hdu : 0 ≤ v - u := sub_nonneg.mpr huv
    have hhinge : ∀ k : Fin q,
        0 ≤ max (Z k - u) 0 - max (Z k - v) 0 := by
      intro k
      have hmono : max (Z k - v) 0 ≤ max (Z k - u) 0 := by
        exact max_le_max (by linarith) le_rfl
      linarith
    have hhinge_le : ∀ k : Fin q,
        max (Z k - u) 0 - max (Z k - v) 0 ≤ v - u := by
      intro k
      calc
        max (Z k - u) 0 - max (Z k - v) 0 ≤
            max ((Z k - u) - (Z k - v)) (0 - 0) :=
          max_sub_max_le_max (Z k - u) 0 (Z k - v) 0
        _ = v - u := by
          rw [sub_self, max_eq_left]
          · ring
          · linarith
    let A : ℝ := ∑ k, (max (Z k - u) 0 - max (Z k - v) 0)
    have hA0 : 0 ≤ A := by
      dsimp [A]
      exact Finset.sum_nonneg (fun k _ => hhinge k)
    have hA_le : A ≤ (q : ℝ) * (v - u) := by
      dsimp [A]
      calc
        (∑ k, (max (Z k - u) 0 - max (Z k - v) 0)) ≤
            ∑ _ : Fin q, (v - u) :=
          Finset.sum_le_sum (fun k _ => hhinge_le k)
        _ = (q : ℝ) * (v - u) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcA : (1 / ((q : ℝ) * (1 - α))) * A ≤
        (v - u) / (1 - α) := by
      have hmul := mul_le_mul_of_nonneg_left hA_le hc
      calc
        (1 / ((q : ℝ) * (1 - α))) * A ≤
            (1 / ((q : ℝ) * (1 - α))) * ((q : ℝ) * (v - u)) := hmul
        _ = (v - u) / (1 - α) := by
          field_simp [ne_of_gt hq', ne_of_gt hρ]
    have hsum : (∑ k, max (Z k - v) 0) - (∑ k, max (Z k - u) 0) = -A := by
      dsimp [A]
      rw [← Finset.sum_sub_distrib]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    have hdiff : cvarObj α Z v - cvarObj α Z u =
        (v - u) - (1 / ((q : ℝ) * (1 - α))) * A := by
      calc
        cvarObj α Z v - cvarObj α Z u = (v - u) +
            (1 / ((q : ℝ) * (1 - α))) *
              ((∑ k, max (Z k - v) 0) - (∑ k, max (Z k - u) 0)) := by
          simp only [cvarObj]
          ring
        _ = (v - u) - (1 / ((q : ℝ) * (1 - α))) * A := by rw [hsum]; ring
    have hlow : -((v - u) / (1 - α)) ≤ cvarObj α Z v - cvarObj α Z u := by
      rw [hdiff]
      nlinarith [hcA, hdu]
    have hupp : cvarObj α Z v - cvarObj α Z u ≤ (v - u) / (1 - α) := by
      have hratio : v - u ≤ (v - u) / (1 - α) := by
        apply (le_div_iff₀ hρ).2
        nlinarith [mul_nonneg hdu hα0]
      rw [hdiff]
      exact le_trans (sub_le_self (v - u) (mul_nonneg hc hA0)) hratio
    have habs : |cvarObj α Z v - cvarObj α Z u| ≤ (v - u) / (1 - α) :=
      (abs_le).2 ⟨hlow, hupp⟩
    rw [abs_sub_comm] at habs
    exact habs
  rcases le_total s t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst)]
    convert hone hst using 1
    ring
  · have h := hone hts
    rw [abs_sub_comm] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    exact h

/-- Finite-grid approximation of empirical CVaR.  Every sample value lies in
`[a,b]`, and every threshold in that interval is within `h` of a grid point.
The grid itself need not be restricted to the interval: only its nonemptiness
and the stated cover are used. -/
theorem cvarGrid_approximation (α : ℝ) (Z : Fin q → ℝ) (G : Finset ℝ)
    (a b h : ℝ) (hq : 0 < q) (hα0 : 0 ≤ α) (hα : α < 1)
    (hZ : ∀ k, Z k ∈ Set.Icc a b) (hG : G.Nonempty)
    (hcover : ∀ t ∈ Set.Icc a b, ∃ g ∈ G, |t - g| ≤ h) (_hh : 0 ≤ h) :
    0 ≤ G.inf' hG (fun g => cvarObj α Z g) - cvarSAA α Z ∧
      G.inf' hG (fun g => cvarObj α Z g) - cvarSAA α Z ≤ h / (1 - α) := by
  have hlower : cvarSAA α Z ≤ G.inf' hG (fun g => cvarObj α Z g) := by
    apply Finset.le_inf' hG
    intro g hg
    exact cvarSAA_le_obj α Z hq hα0 hα g
  constructor
  · linarith
  · obtain ⟨k, hk⟩ := cvarSAA_eq_obj_sample α Z hq hα0 hα
    obtain ⟨g, hgG, hdist⟩ := hcover (Z k) (hZ k)
    have hL := cvarObj_threshold_lipschitz α Z hq hα0 hα g (Z k)
    have hdist0 : |g - Z k| ≤ h := by rw [abs_sub_comm]; exact hdist
    have hdist' : |g - Z k| / (1 - α) ≤ h / (1 - α) :=
      div_le_div_of_nonneg_right hdist0 (le_of_lt (by linarith : (0 : ℝ) < 1 - α))
    have hobj : cvarObj α Z g - cvarObj α Z (Z k) ≤ h / (1 - α) := by
      exact le_trans (le_trans (le_abs_self _) hL) hdist'
    have hmin := Finset.inf'_le (fun g => cvarObj α Z g) hgG
    rw [hk]
    linarith

#print axioms Ctrllib.cvarObj_threshold_lipschitz
#print axioms Ctrllib.cvarGrid_approximation

end Ctrllib
