import Mathlib

open MeasureTheory
open scoped Interval

namespace NewPG03C01

theorem shifted_endpoint_bound
    {V d s : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hV : ContinuousOn V (Set.Icc a b))
    (hd : ContinuousOn d (Set.Icc a b))
    (hs : ContinuousOn s (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt V (d t) t)
    (hbound : ∀ t ∈ Set.Icc a b, d t ≤ s t) :
    V b - V a ≤ ∫ t in a..b, s t := by
  have hVu : ContinuousOn V (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hV
  have hdu : ContinuousOn d (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hd
  have hsu : ContinuousOn s (Set.uIcc a b) := by
    simpa only [Set.uIcc_of_le hab] using hs
  have hdi : IntervalIntegrable d volume a b :=
    hdu.intervalIntegrable
  have hsi : IntervalIntegrable s volume a b :=
    hsu.intervalIntegrable
  have hderiv' :
      ∀ t ∈ Set.Ioo (min a b) (max a b),
        HasDerivAt V (d t) t := by
    simpa only [min_eq_left hab, max_eq_right hab] using hderiv
  have hFTC : (∫ t in a..b, d t) = V b - V a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hV hderiv hdi
  calc
    V b - V a = ∫ t in a..b, d t := hFTC.symm
    _ ≤ ∫ t in a..b, s t :=
      intervalIntegral.integral_mono_on hab hdi hsi hbound

theorem origin_endpoint_bound
    {V d s : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hV : ContinuousOn V (Set.Icc 0 T))
    (hd : ContinuousOn d (Set.Icc 0 T))
    (hs : ContinuousOn s (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt V (d t) t)
    (hbound : ∀ t ∈ Set.Icc 0 T, d t ≤ s t) :
    V T - V 0 ≤ ∫ t in (0 : ℝ)..T, s t := by
  exact shifted_endpoint_bound
    (V := V) (d := d) (s := s) (a := 0) (b := T)
    hT hV hd hs hderiv hbound

end NewPG03C01
