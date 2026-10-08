/-
Comparison-function library (TARGET 12 of the ctrllib stream).

The definitional substrate for the Panteley cascade theorems and ISS: the classes
`𝒦`, `𝒦∞`, `𝒦ℒ` of comparison functions. Confirmed ABSENT from Mathlib v4.31.0
(a potential upstream contribution, like the house LaSalle layer).

Provenance. The definitions are read verbatim from the rendered sources on disk:
  - panteley1998global (Notation, p.1): `α ∈ 𝒦` iff `α : ℝ≥0 → ℝ≥0` continuous,
    strictly increasing, `α 0 = 0`; `α ∈ 𝒦∞` iff in addition `α x → ∞` as `x → ∞`.
  - panteley2001growth (Notation, p.3): identical `𝒦`, `𝒦∞`; adds class `ℒ`
    (continuous, strictly DECREASING, `α s → 0` as `s → ∞`) and gives the
    Khalil-ordered `𝒦ℒ`: `β(·,t) ∈ 𝒦` for each fixed `t`, `β(s,·) ∈ ℒ` for each `s`.
  - Khalil, Nonlinear Systems 3rd ed. (2002), §4.4 "Comparison Functions"
    (render line 4584): Definition 4.2 (render line 4588; classes 𝒦 and 𝒦∞) and
    Definition 4.3 (render line 4590; class 𝒦ℒ). Confirmed against the corpus
    render 2026-07-11 (the corresponding local note).

Carrier. Functions `ℝ → ℝ` with the defining properties asserted on `Set.Ici 0`
(the ray `[0,∞)`). This matches the paper's `ℝ≥0 → ℝ≥0` while composing directly
with the real-valued norms `‖x‖` and Lyapunov values `V` that the ISS/cascade
rungs manipulate -- and it reuses the `ContinuousOn _ (Ici 0)` idiom already
carried by TimeVaryingComparison.lean. Nonnegativity of the output on the ray is
a THEOREM (`IsClassK.nonneg`), not a hypothesis: `f 0 = 0` plus monotonicity give it.

Human derivation: the corresponding derivation record (not bundled).
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Hom.Set

open Set Filter Topology Function

namespace Ctrllib

variable {f g : ℝ → ℝ}

/-! ### Definitions -/

/-- A function is of **class 𝒦** if, on the ray `[0,∞)`, it is continuous, strictly
increasing, and vanishes at the origin. (panteley1998global / panteley2001growth,
Notation; Khalil (2002) §4.4 Def 4.2, render line 4588.) -/
structure IsClassK (f : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn f (Ici 0)
  strictMonoOn : StrictMonoOn f (Ici 0)
  map_zero : f 0 = 0

/-- A function is of **class 𝒦∞** if it is class 𝒦 and unbounded: `f x → ∞` as
`x → ∞`. (panteley1998global / panteley2001growth, Notation;
Khalil (2002) §4.4 Def 4.2, render line 4588.) -/
structure IsClassKInfinity (f : ℝ → ℝ) : Prop extends IsClassK f where
  tendsto_atTop : Tendsto f atTop atTop

/-- A function `β : ℝ → ℝ → ℝ` is of **class 𝒦ℒ** if, on the ray `[0,∞)`, the map
`r ↦ β r s` is class 𝒦 for each fixed `s ≥ 0`, and for each fixed `r > 0` the map
`s ↦ β r s` is strictly decreasing to `0`. (panteley2001growth, Notation, in the
Khalil `β(r,s)` ordering; Khalil (2002) §4.4 Def 4.3, render line 4590.)

The restriction to `r > 0` in the decreasing clause is deliberate: class 𝒦 in the
first argument forces `β 0 s = 0` for all `s`, so `β 0 ·` is identically `0` and
cannot be *strictly* decreasing. The literature (panteley2001growth) writes
`β(s,·) ∈ ℒ for each s ≥ 0`, glossing this degenerate `r = 0` slice; we pin it. -/
structure IsClassKL (β : ℝ → ℝ → ℝ) : Prop where
  isClassK_fst : ∀ s, 0 ≤ s → IsClassK (fun r => β r s)
  strictAntiOn_snd : ∀ r, 0 < r → StrictAntiOn (fun s => β r s) (Ici 0)
  tendsto_snd : ∀ r, 0 < r → Tendsto (fun s => β r s) atTop (𝓝 0)

/-! ### Class 𝒦: monotonicity and sign -/

/-- On the ray, a class-𝒦 function is monotone. -/
theorem IsClassK.monotoneOn (hf : IsClassK f) : MonotoneOn f (Ici 0) :=
  hf.strictMonoOn.monotoneOn

/-- The shape the ISS sandwich `α₁(‖x‖) ≤ V ≤ α₂(‖x‖)` consumes: `0 ≤ a ≤ b`
implies `f a ≤ f b`. -/
theorem IsClassK.le_of_le (hf : IsClassK f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    f a ≤ f b :=
  hf.monotoneOn (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hab)) hab

/-- Strict version of `IsClassK.le_of_le`. -/
theorem IsClassK.lt_of_lt (hf : IsClassK f) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    f a < f b :=
  hf.strictMonoOn (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hab.le)) hab

/-- A class-𝒦 function is nonnegative on the ray. This is a theorem, not part of
the definition: it follows from `f 0 = 0` and monotonicity. -/
theorem IsClassK.nonneg (hf : IsClassK f) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have := hf.le_of_le le_rfl hx
  rwa [hf.map_zero] at this

/-- A class-𝒦 function is strictly positive off the origin. -/
theorem IsClassK.pos_of_pos (hf : IsClassK f) {x : ℝ} (hx : 0 < x) : 0 < f x := by
  have := hf.lt_of_lt le_rfl hx
  rwa [hf.map_zero] at this

/-- A class-𝒦 function maps the ray into the ray. -/
theorem IsClassK.mapsTo (hf : IsClassK f) : MapsTo f (Ici 0) (Ici 0) :=
  fun _ hx => mem_Ici.mpr (hf.nonneg (mem_Ici.mp hx))

/-- On the ray, a class-𝒦 function vanishes exactly at the origin. -/
theorem IsClassK.eq_zero_iff (hf : IsClassK f) {x : ℝ} (hx : 0 ≤ x) :
    f x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ hf.map_zero⟩
  by_contra hne
  exact (hf.pos_of_pos (hx.lt_of_ne (Ne.symm hne))).ne' h

/-! ### Class 𝒦: constructions -/

/-- The identity is class 𝒦. -/
theorem isClassK_id : IsClassK (id : ℝ → ℝ) where
  continuousOn := continuousOn_id
  strictMonoOn := strictMono_id.strictMonoOn _
  map_zero := rfl

/-- A positive scalar multiple of a class-𝒦 function is class 𝒦. -/
theorem IsClassK.const_mul (hf : IsClassK f) {c : ℝ} (hc : 0 < c) :
    IsClassK (fun x => c * f x) where
  continuousOn := continuousOn_const.mul hf.continuousOn
  strictMonoOn := fun a ha b hb hab =>
    mul_lt_mul_of_pos_left (hf.strictMonoOn ha hb hab) hc
  map_zero := by simp [hf.map_zero]

/-- The composition of two class-𝒦 functions is class 𝒦. -/
theorem IsClassK.comp (hg : IsClassK g) (hf : IsClassK f) : IsClassK (g ∘ f) where
  continuousOn := hg.continuousOn.comp hf.continuousOn hf.mapsTo
  strictMonoOn := hg.strictMonoOn.comp hf.strictMonoOn hf.mapsTo
  map_zero := by simp only [comp_apply, hf.map_zero, hg.map_zero]

/-- The sum of two class-𝒦 functions is class 𝒦. -/
theorem IsClassK.add (hf : IsClassK f) (hg : IsClassK g) :
    IsClassK (fun x => f x + g x) where
  continuousOn := hf.continuousOn.add hg.continuousOn
  strictMonoOn := fun a ha b hb hab =>
    add_lt_add (hf.strictMonoOn ha hb hab) (hg.strictMonoOn ha hb hab)
  map_zero := by simp [hf.map_zero, hg.map_zero]

/-- The pointwise minimum of two class-𝒦 functions is class 𝒦. -/
theorem IsClassK.min (hf : IsClassK f) (hg : IsClassK g) :
    IsClassK (fun x => min (f x) (g x)) where
  continuousOn := continuous_min.comp_continuousOn (hf.continuousOn.prodMk hg.continuousOn)
  strictMonoOn := fun a ha b hb hab =>
    lt_min ((min_le_left _ _).trans_lt (hf.strictMonoOn ha hb hab))
      ((min_le_right _ _).trans_lt (hg.strictMonoOn ha hb hab))
  map_zero := by simp [hf.map_zero, hg.map_zero]

/-- The pointwise maximum of two class-𝒦 functions is class 𝒦. -/
theorem IsClassK.max (hf : IsClassK f) (hg : IsClassK g) :
    IsClassK (fun x => max (f x) (g x)) where
  continuousOn := continuous_max.comp_continuousOn (hf.continuousOn.prodMk hg.continuousOn)
  strictMonoOn := fun a ha b hb hab =>
    max_lt ((hf.strictMonoOn ha hb hab).trans_le (le_max_left _ _))
      ((hg.strictMonoOn ha hb hab).trans_le (le_max_right _ _))
  map_zero := by simp [hf.map_zero, hg.map_zero]

/-! ### Class 𝒦∞: constructions -/

/-- The identity is class 𝒦∞. -/
theorem isClassKInfinity_id : IsClassKInfinity (id : ℝ → ℝ) where
  toIsClassK := isClassK_id
  tendsto_atTop := tendsto_id

/-- A positive scalar multiple of a class-𝒦∞ function is class 𝒦∞. -/
theorem IsClassKInfinity.const_mul (hf : IsClassKInfinity f) {c : ℝ} (hc : 0 < c) :
    IsClassKInfinity (fun x => c * f x) where
  toIsClassK := hf.toIsClassK.const_mul hc
  tendsto_atTop := Tendsto.const_mul_atTop hc hf.tendsto_atTop

/-- The composition of two class-𝒦∞ functions is class 𝒦∞. -/
theorem IsClassKInfinity.comp (hg : IsClassKInfinity g) (hf : IsClassKInfinity f) :
    IsClassKInfinity (g ∘ f) where
  toIsClassK := hg.toIsClassK.comp hf.toIsClassK
  tendsto_atTop := hg.tendsto_atTop.comp hf.tendsto_atTop

/-! ### Class 𝒦∞: bijectivity of the carrier -/

/-- A class-𝒦∞ function is surjective from the ray onto the ray: continuity plus
`f 0 = 0` plus `f → ∞` cover `[0,∞)` by the intermediate value theorem. -/
theorem IsClassKInfinity.surjOn (hf : IsClassKInfinity f) : SurjOn f (Ici 0) (Ici 0) := by
  have h := isPreconnected_Ici.intermediate_value_Ici (a := (0 : ℝ))
    (mem_Ici.mpr le_rfl) (le_principal_iff.mpr (Ici_mem_atTop 0))
    hf.toIsClassK.continuousOn hf.tendsto_atTop
  rwa [hf.toIsClassK.map_zero] at h

/-- A class-𝒦∞ function is a bijection of the ray onto itself. -/
theorem IsClassKInfinity.bijOn (hf : IsClassKInfinity f) : BijOn f (Ici 0) (Ici 0) :=
  ⟨hf.toIsClassK.mapsTo, hf.toIsClassK.strictMonoOn.injOn, hf.surjOn⟩

/-! ### Class 𝒦∞: the inverse -/

/-- The inverse of a class-𝒦∞ function on the ray, as the partial inverse
`Function.invFunOn` restricted to `[0,∞)`. For a class-𝒦∞ `f` this is a genuine
two-sided inverse on the ray (`classKInv_leftInvOn`, `classKInv_rightInvOn`). -/
noncomputable def classKInv (f : ℝ → ℝ) : ℝ → ℝ := invFunOn f (Ici 0)

/-- `classKInv f` is a left inverse of `f` on the ray: `classKInv f (f x) = x`. -/
theorem IsClassKInfinity.classKInv_leftInvOn (hf : IsClassKInfinity f) :
    LeftInvOn (classKInv f) f (Ici 0) :=
  hf.bijOn.invOn_invFunOn.1

/-- `classKInv f` is a right inverse of `f` on the ray: `f (classKInv f y) = y`.
This is the equivalence `α(‖x‖) ≤ V ↔ ‖x‖ ≤ α⁻¹(V)` the ISS bounds rest on. -/
theorem IsClassKInfinity.classKInv_rightInvOn (hf : IsClassKInfinity f) :
    RightInvOn (classKInv f) f (Ici 0) :=
  hf.bijOn.invOn_invFunOn.2

/-- The inverse of a class-𝒦∞ function is itself class 𝒦∞. The continuity of the
inverse comes from `OrderIso.continuous`: `f` restricts to an order isomorphism of
`[0,∞)` onto itself, whose inverse is automatically continuous (the carrier is
order-connected, hence carries the order topology). -/
theorem IsClassKInfinity.classKInv_isClassKInfinity (hf : IsClassKInfinity f) :
    IsClassKInfinity (classKInv f) := by
  change IsClassKInfinity (invFunOn f (Ici 0))
  set g := invFunOn f (Ici 0) with hg
  have hleft : LeftInvOn g f (Ici 0) := hf.bijOn.invOn_invFunOn.1
  have hright : RightInvOn g f (Ici 0) := hf.bijOn.invOn_invFunOn.2
  have hmaps : MapsTo g (Ici 0) (Ici 0) := hf.surjOn.mapsTo_invFunOn
  -- vanishes at the origin
  have hz : g 0 = 0 := by
    have h := hleft (mem_Ici.mpr le_rfl)
    rwa [hf.toIsClassK.map_zero] at h
  -- strictly increasing (order-reverse the strict monotonicity of `f`)
  have hmono : StrictMonoOn g (Ici 0) := by
    intro a ha b hb hab
    by_contra h
    rw [not_lt] at h
    have hfle : f (g b) ≤ f (g a) := hf.toIsClassK.le_of_le (mem_Ici.mp (hmaps hb)) h
    rw [hright hb, hright ha] at hfle
    exact absurd hfle (not_le.mpr hab)
  -- unbounded: `g x ≥ M` once `x ≥ f (max M 0)`
  have htop : Tendsto g atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun M => ⟨f (max M 0), fun x hx => ?_⟩
    have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
    have hfM0 : (0 : ℝ) ≤ f (max M 0) := hf.toIsClassK.nonneg hM0
    have hx0 : (0 : ℝ) ≤ x := hfM0.trans hx
    have hle : g (f (max M 0)) ≤ g x :=
      hmono.monotoneOn (mem_Ici.mpr hfM0) (mem_Ici.mpr hx0) hx
    rw [hleft (mem_Ici.mpr hM0)] at hle
    exact (le_max_left _ _).trans hle
  -- continuity via the order isomorphism `f` induces on the ray
  have hcont : ContinuousOn g (Ici 0) := by
    set f' : Ici (0 : ℝ) → Ici (0 : ℝ) := fun x => ⟨f x.1, hf.toIsClassK.mapsTo x.2⟩ with hf'
    have hf'_mono : StrictMono f' := fun a b hab => hf.toIsClassK.strictMonoOn a.2 b.2 hab
    have hf'_surj : Function.Surjective f' := by
      intro y
      obtain ⟨x, hx, hxy⟩ := hf.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hsymm : Continuous (StrictMono.orderIsoOfSurjective f' hf'_mono hf'_surj).symm :=
      (StrictMono.orderIsoOfSurjective f' hf'_mono hf'_surj).symm.continuous
    rw [continuousOn_iff_continuous_domRestrict]
    have hbridge : (Ici (0 : ℝ)).domRestrict g =
        fun x => ((StrictMono.orderIsoOfSurjective f' hf'_mono hf'_surj).symm x : ℝ) := by
      funext x
      apply hf.toIsClassK.strictMonoOn.injOn (hmaps x.2)
        ((StrictMono.orderIsoOfSurjective f' hf'_mono hf'_surj).symm x).2
      rw [hright x.2]
      exact (congrArg Subtype.val
        (StrictMono.orderIsoOfSurjective_self_symm_apply f' hf'_mono hf'_surj x)).symm
    rw [hbridge]
    exact continuous_subtype_val.comp hsymm
  exact ⟨⟨hcont, hmono, hz⟩, htop⟩

/-! ### Class 𝒦ℒ: sign -/

/-- A class-𝒦ℒ function is nonnegative on the closed first quadrant of the ray. -/
theorem IsClassKL.nonneg {β : ℝ → ℝ → ℝ} (hβ : IsClassKL β) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) : 0 ≤ β r s :=
  (hβ.isClassK_fst s hs).nonneg hr

end Ctrllib

#print axioms Ctrllib.IsClassK.monotoneOn
#print axioms Ctrllib.IsClassK.le_of_le
#print axioms Ctrllib.IsClassK.lt_of_lt
#print axioms Ctrllib.IsClassK.nonneg
#print axioms Ctrllib.IsClassK.pos_of_pos
#print axioms Ctrllib.IsClassK.mapsTo
#print axioms Ctrllib.IsClassK.eq_zero_iff
#print axioms Ctrllib.isClassK_id
#print axioms Ctrllib.IsClassK.const_mul
#print axioms Ctrllib.IsClassK.comp
#print axioms Ctrllib.IsClassK.add
#print axioms Ctrllib.IsClassK.min
#print axioms Ctrllib.IsClassK.max
#print axioms Ctrllib.isClassKInfinity_id
#print axioms Ctrllib.IsClassKInfinity.const_mul
#print axioms Ctrllib.IsClassKInfinity.comp
#print axioms Ctrllib.IsClassKInfinity.surjOn
#print axioms Ctrllib.IsClassKInfinity.bijOn
#print axioms Ctrllib.classKInv
#print axioms Ctrllib.IsClassKInfinity.classKInv_leftInvOn
#print axioms Ctrllib.IsClassKInfinity.classKInv_rightInvOn
#print axioms Ctrllib.IsClassKInfinity.classKInv_isClassKInfinity
#print axioms Ctrllib.IsClassKL.nonneg
