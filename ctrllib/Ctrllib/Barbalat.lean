/-
Barbalat's lemma and its Lyapunov-like corollary (proof rung R3).

Slotine & Li, *Applied Nonlinear Control*, Lemma 4.2 (Barbalat) and Lemma 4.3
("Lyapunov-like lemma"). Neither is in Mathlib v4.31.0 (searched: no `barbalat`
identifier, no `UniformContinuous … → Tendsto … 0` shape) -- both are proved here
from the Mean Value Theorem.

No SymPy pin: Barbalat is a pure analysis limit result with no algebraic identity
to machine-check (the pin pattern is for algebraic identities, not limits).

Human derivation: the corresponding derivation record (not bundled).
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Filter.AtTopBot.Field

open Set Filter Topology

namespace Ctrllib

/-- **Barbalat's lemma** (derivative form; Slotine & Li Lemma 4.2). If a
differentiable `f : ℝ → ℝ` has a finite limit as `t → ∞` and its derivative `f'`
is uniformly continuous, then `f' t → 0` as `t → ∞`.

The derivative is carried as an explicit witness `f'` (via `HasDerivAt`) rather
than `deriv f`, sidestepping the total-`deriv` junk-value trap and matching the
house idiom.

Proof idea (direct, no contradiction): fix `ε`. Uniform continuity gives `δ` with
`|f' a − f' b| < ε/2` whenever `dist a b < δ`. On `[t, t+δ]` the Mean Value Theorem
gives `c` with `f' c = (f (t+δ) − f t)/δ`; since `f` converges, the increment
`f (t+δ) − f t → 0`, so `|f' c| < ε/2` for large `t`, whence
`|f' t| ≤ |f' t − f' c| + |f' c| < ε`. -/
theorem barbalat {f f' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hlim : ∃ L, Tendsto f atTop (𝓝 L)) (huc : UniformContinuous f') :
    Tendsto f' atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := hlim
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  -- uniform continuity of `f'` supplies the interval width `δ`
  obtain ⟨δ, hδ, hucδ⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (half_pos hε)
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  -- `f` converges, so the shifted increment `f (·+δ) − f ·` tends to `0`
  have hshiftmap : Tendsto (fun s : ℝ => s + δ) atTop atTop :=
    tendsto_atTop_add_const_right atTop δ tendsto_id
  have hshift : Tendsto (fun s => f (s + δ)) atTop (𝓝 L) := hL.comp hshiftmap
  have hdiff : Tendsto (fun s => f (s + δ) - f s) atTop (𝓝 0) := by
    have h := hshift.sub hL
    rwa [sub_self] at h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdiff (ε / 2 * δ) (mul_pos (half_pos hε) hδ)
  filter_upwards [eventually_ge_atTop N] with s hs
  have hab : s < s + δ := by linarith
  -- Mean Value Theorem on `[s, s+δ]`
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    exists_hasDerivAt_eq_slope f f' hab hcont.continuousOn (fun x _ => hderiv x)
  rw [show s + δ - s = δ from by ring] at hc_eq
  have hincr : |f (s + δ) - f s| < ε / 2 * δ := by
    have h := hN s hs
    simpa [Real.dist_eq] using h
  have hfc_bound : |f' c| < ε / 2 := by
    rw [hc_eq, abs_div, abs_of_pos hδ, div_lt_iff₀ hδ]
    exact hincr
  have hcdist : dist s c < δ := by
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hc_mem.2], by linarith [hc_mem.1]⟩
  have huc_bound : |f' s - f' c| < ε / 2 := by
    have h := hucδ hcdist
    rwa [Real.dist_eq] at h
  rw [Real.norm_eq_abs]
  calc |f' s| = |(f' s - f' c) + f' c| := by congr 1; ring
    _ ≤ |f' s - f' c| + |f' c| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add huc_bound hfc_bound
    _ = ε := by ring

/-- **Lyapunov-like lemma** (Slotine & Li Lemma 4.3). If a scalar `V : ℝ → ℝ` is
lower bounded, non-increasing (`V' ≤ 0`, so `V̇` is negative semidefinite), and its
derivative `V'` is uniformly continuous, then `V' t → 0` as `t → ∞`.

`V` is antitone and bounded below, hence converges to `⨅ t, V t` by monotone
convergence; this half needs no uniform continuity. Barbalat's lemma then forces
`V' → 0`. -/
theorem barbalat_lyapunov {V V' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt V (V' x) x)
    (hlb : ∃ m, ∀ t, m ≤ V t) (hnonpos : ∀ t, V' t ≤ 0)
    (huc : UniformContinuous V') :
    Tendsto V' atTop (𝓝 0) := by
  refine barbalat hderiv ?_ huc
  have hdV : Differentiable ℝ V := fun x => (hderiv x).differentiableAt
  have hanti : Antitone V :=
    antitone_of_deriv_nonpos hdV fun x => by rw [(hderiv x).deriv]; exact hnonpos x
  obtain ⟨m, hm⟩ := hlb
  have hbdd : BddBelow (Set.range V) := ⟨m, by rintro _ ⟨x, rfl⟩; exact hm x⟩
  exact ⟨⨅ t, V t, tendsto_atTop_ciInf hanti hbdd⟩

end Ctrllib

#print axioms Ctrllib.barbalat
#print axioms Ctrllib.barbalat_lyapunov
