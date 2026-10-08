import Ctrllib.RoverPoseGeometry

/-! Translation and heading motion interfaces for a two-segment piecewise-affine path.

The useful contract is derived from the segment velocities.  In particular, the
global Lipschitz bound below is not an assumption about the whole path: it is
proved by splitting a pair of times at the knot when necessary.
-/

namespace Ctrllib

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous two-segment affine path, with its knot at `b`.

The second branch starts at the value reached by the first branch, so the two
pieces agree at the knot.  The definition is intended for times in `[a,c]`
with `a ≤ b ≤ c`.
-/
noncomputable def twoSegmentAffine (x₀ v₁ v₂ : E) (a b t : ℝ) : E :=
  if t ≤ b then x₀ + (t - a) • v₁ else (x₀ + (b - a) • v₁) + (t - b) • v₂

private theorem affine_segment_bound
    {x v : E} {u t a V : ℝ}
    (hv : ‖v‖ ≤ V) :
    ‖(x + (t - a) • v) - (x + (u - a) • v)‖ ≤ V * |t - u| := by
  rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul]
  have htu : t - a - (u - a) = t - u := by ring
  rw [htu]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hv (abs_nonneg (t - u))

/-- Two affine segments with bounded velocities give a global displacement bound.

The proof explicitly handles pairs on the same segment and pairs separated by
the knot; the latter case uses the triangle inequality through the common knot.
-/
theorem two_segment_affine_lipschitz
    {x₀ v₁ v₂ : E} {a b c V : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hv₁ : ‖v₁‖ ≤ V) (hv₂ : ‖v₂‖ ≤ V)
    (hV : 0 ≤ V) :
    ∀ s ∈ Set.Icc a c, ∀ t ∈ Set.Icc a c,
      ‖twoSegmentAffine x₀ v₁ v₂ a b s - twoSegmentAffine x₀ v₁ v₂ a b t‖ ≤
        V * |s - t| := by
  have _ := hab
  have _ := hbc
  have _ := hV
  intro s hs t ht
  by_cases hsK : s ≤ b
  · by_cases htK : t ≤ b
    · simp only [twoSegmentAffine, hsK, htK, ↓reduceIte]
      exact affine_segment_bound hv₁
    · have hsb : s ≤ b := hsK
      have htb : b ≤ t := le_of_not_ge htK
      have hfirst := affine_segment_bound (x := x₀) (v := v₁) (u := s) (t := b)
        (a := a) hv₁
      have hsecond := affine_segment_bound
        (x := x₀ + (b - a) • v₁) (v := v₂) (u := b) (t := t) (a := b) hv₂
      have hst : 0 ≤ t - s := sub_nonneg.mpr (le_trans hsb htb)
      have hsb' : 0 ≤ b - s := sub_nonneg.mpr hsb
      have hbt' : 0 ≤ t - b := sub_nonneg.mpr htb
      have hsum : (b - s) + (t - b) = t - s := by ring
      simp only [twoSegmentAffine, hsK, htK, ↓reduceIte]
      calc
        ‖(x₀ + (s - a) • v₁) -
            ((x₀ + (b - a) • v₁) + (t - b) • v₂)‖ ≤
            ‖(x₀ + (s - a) • v₁) - (x₀ + (b - a) • v₁)‖ +
              ‖(x₀ + (b - a) • v₁) -
                ((x₀ + (b - a) • v₁) + (t - b) • v₂)‖ := by
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ V * (b - s) + V * (t - b) := by
          gcongr
          · simpa [sub_self, abs_of_nonneg hsb', norm_sub_rev] using hfirst
          · simpa [sub_self, abs_of_nonneg hbt'] using hsecond
        _ = V * ((b - s) + (t - b)) := by ring
        _ = V * (t - s) := by rw [hsum]
        _ = V * |s - t| := by rw [abs_sub_comm, abs_of_nonneg hst]
  · have hsb : b ≤ s := le_of_not_ge hsK
    by_cases htK : t ≤ b
    · have htb : t ≤ b := htK
      have hst : 0 ≤ s - t := sub_nonneg.mpr (le_trans htb hsb)
      have hfirst := affine_segment_bound (x := x₀) (v := v₁) (u := t) (t := b)
        (a := a) hv₁
      have hsecond := affine_segment_bound
        (x := x₀ + (b - a) • v₁) (v := v₂) (u := b) (t := s) (a := b) hv₂
      have htb' : 0 ≤ b - t := sub_nonneg.mpr htb
      have hbs' : 0 ≤ s - b := sub_nonneg.mpr hsb
      have hsum : (b - t) + (s - b) = s - t := by ring
      simp only [twoSegmentAffine, hsK, htK, ↓reduceIte]
      calc
        ‖((x₀ + (b - a) • v₁) + (s - b) • v₂) -
            (x₀ + (t - a) • v₁)‖ ≤
            ‖((x₀ + (b - a) • v₁) + (s - b) • v₂) -
                (x₀ + (b - a) • v₁)‖ +
              ‖(x₀ + (b - a) • v₁) - (x₀ + (t - a) • v₁)‖ := by
          exact norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ V * (s - b) + V * (b - t) := by
          gcongr
          · simpa [sub_self, abs_of_nonneg hbs'] using hsecond
          · simpa [abs_of_nonneg htb'] using hfirst
        _ = V * ((s - b) + (b - t)) := by ring
        _ = V * (s - t) := by ring
        _ = V * |s - t| := by rw [abs_of_nonneg hst]
    · have htb : b ≤ t := le_of_not_ge htK
      simp only [twoSegmentAffine, hsK, htK, ↓reduceIte]
      exact affine_segment_bound hv₂

end

/-! A reusable finite gluing step.  Repeated use gives the corresponding
statement for any finite ordered waypoint list. -/

theorem one_knot_lipschitz_of_segment_bounds
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b c V : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hV : 0 ≤ V)
    (hleft : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      ‖f s - f t‖ ≤ V * |s - t|)
    (hright : ∀ s ∈ Set.Icc b c, ∀ t ∈ Set.Icc b c,
      ‖f s - f t‖ ≤ V * |s - t|) :
    ∀ s ∈ Set.Icc a c, ∀ t ∈ Set.Icc a c,
      ‖f s - f t‖ ≤ V * |s - t| := by
  have _ := hV
  intro s hs t ht
  by_cases hsK : s ≤ b
  · by_cases htK : t ≤ b
    · exact hleft s ⟨hs.1, hsK⟩ t ⟨ht.1, htK⟩
    · have htb : b ≤ t := le_of_not_ge htK
      have h₁ := hleft s ⟨hs.1, hsK⟩ b ⟨hab, le_rfl⟩
      have h₂ := hright b ⟨le_rfl, hbc⟩ t ⟨htb, ht.2⟩
      have hst : 0 ≤ t - s := sub_nonneg.mpr (le_trans hsK htb)
      have htri := norm_sub_le_norm_sub_add_norm_sub (f s) (f b) (f t)
      have hsum : (b - s) + (t - b) = t - s := by ring
      have h₁' : ‖f s - f b‖ ≤ V * (b - s) := by
        simpa [abs_of_nonpos (sub_nonpos.mpr hsK)] using h₁
      have h₂' : ‖f b - f t‖ ≤ V * (t - b) := by
        simpa [abs_of_nonpos (sub_nonpos.mpr htb)] using h₂
      rw [abs_sub_comm, abs_of_nonneg hst]
      linarith
  · have hsb : b ≤ s := le_of_not_ge hsK
    by_cases htK : t ≤ b
    · have htb : t ≤ b := htK
      have h₁ := hright s ⟨hsb, hs.2⟩ b ⟨le_rfl, hbc⟩
      have h₂ := hleft b ⟨hab, le_rfl⟩ t ⟨ht.1, htb⟩
      have hst : 0 ≤ s - t := sub_nonneg.mpr (le_trans htb hsb)
      have htri := norm_sub_le_norm_sub_add_norm_sub (f s) (f b) (f t)
      have hsum : (s - b) + (b - t) = s - t := by ring
      have h₁' : ‖f s - f b‖ ≤ V * (s - b) := by
        simpa [abs_of_nonneg (sub_nonneg.mpr hsb)] using h₁
      have h₂' : ‖f b - f t‖ ≤ V * (b - t) := by
        simpa [abs_of_nonneg (sub_nonneg.mpr htb)] using h₂
      rw [abs_of_nonneg hst]
      linarith
    · have htb : b ≤ t := le_of_not_ge htK
      exact hright s ⟨hsb, hs.2⟩ t ⟨htb, ht.2⟩

/-! Finite ordered waypoint gluing.  Each segment is affine with its own
velocity; induction uses the preceding theorem at the final waypoint. -/

theorem finite_piecewise_affine_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {T : ℕ → ℝ} {f : ℝ → E} {v : ℕ → E} {V : ℝ}
    (hT : Monotone T)
    (hmodel : ∀ k < N, ∀ t ∈ Set.Icc (T k) (T (k + 1)),
      f t = f (T k) + (t - T k) • v k)
    (hvel : ∀ k < N, ‖v k‖ ≤ V) (hV : 0 ≤ V) :
    ∀ s ∈ Set.Icc (T 0) (T N), ∀ t ∈ Set.Icc (T 0) (T N),
      ‖f s - f t‖ ≤ V * |s - t| := by
  induction N with
  | zero =>
      intro s hs t ht
      have hs0 : s = T 0 := le_antisymm hs.2 hs.1
      have ht0 : t = T 0 := le_antisymm ht.2 ht.1
      simp [hs0, ht0]
  | succ N ih =>
      have hleft : ∀ s ∈ Set.Icc (T 0) (T N), ∀ t ∈ Set.Icc (T 0) (T N),
          ‖f s - f t‖ ≤ V * |s - t| := by
        apply ih
        · intro k hk
          exact hmodel k (Nat.lt_trans hk (Nat.lt_succ_self N))
        · intro k hk
          exact hvel k (Nat.lt_trans hk (Nat.lt_succ_self N))
      have hright : ∀ s ∈ Set.Icc (T N) (T (N + 1)),
          ∀ t ∈ Set.Icc (T N) (T (N + 1)),
          ‖f s - f t‖ ≤ V * |s - t| := by
        intro s hs t ht
        rw [hmodel N (Nat.lt_succ_self N) s hs,
          hmodel N (Nat.lt_succ_self N) t ht]
        simpa only [norm_sub_rev, abs_sub_comm] using
          (affine_segment_bound (x := f (T N)) (v := v N)
            (u := s) (t := t) (a := T N) (hvel N (Nat.lt_succ_self N)))
      exact one_knot_lipschitz_of_segment_bounds
        (hT (Nat.zero_le N)) (hT (Nat.le_succ N)) hV hleft hright

/-! Concrete aliases used by the rover contracts. -/

theorem piecewise_affine_translation_lipschitz
    {x₀ v₁ v₂ : Point3} {a b c V : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hv₁ : ‖v₁‖ ≤ V) (hv₂ : ‖v₂‖ ≤ V) (hV : 0 ≤ V) :
    ∀ s ∈ Set.Icc a c, ∀ t ∈ Set.Icc a c,
      ‖twoSegmentAffine x₀ v₁ v₂ a b s - twoSegmentAffine x₀ v₁ v₂ a b t‖ ≤
        V * |s - t| :=
  two_segment_affine_lipschitz hab hbc hv₁ hv₂ hV

theorem piecewise_affine_heading_lipschitz
    {θ₀ ω₁ ω₂ a b c Ω : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hω₁ : |ω₁| ≤ Ω) (hω₂ : |ω₂| ≤ Ω)
    (hΩ : 0 ≤ Ω) :
    ∀ s ∈ Set.Icc a c, ∀ t ∈ Set.Icc a c,
      |twoSegmentAffine θ₀ ω₁ ω₂ a b s - twoSegmentAffine θ₀ ω₁ ω₂ a b t| ≤
        Ω * |s - t| := by
  simpa only [Real.norm_eq_abs] using
    (two_segment_affine_lipschitz (E := ℝ) hab hbc hω₁ hω₂ hΩ)

end Ctrllib

#print axioms Ctrllib.two_segment_affine_lipschitz
#print axioms Ctrllib.one_knot_lipschitz_of_segment_bounds
#print axioms Ctrllib.finite_piecewise_affine_lipschitz
#print axioms Ctrllib.piecewise_affine_translation_lipschitz
#print axioms Ctrllib.piecewise_affine_heading_lipschitz
