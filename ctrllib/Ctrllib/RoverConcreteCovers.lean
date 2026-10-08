import Ctrllib.RoverPoseGeometry
import Mathlib.Algebra.Order.Floor.Semifield

/-!
Concrete finite covers for the rover geometry contract.

The rectangular body is planar and is sampled at the centres of a finite
`nx`-by-`ny` grid. The proof uses the floor of the normalized coordinate to
select a cell; it therefore establishes an actual finite cover rather than
assuming that a nearby sample exists. A centred disc is represented by its
centre sample together with its radius as the cover radius.
-/

namespace Ctrllib

private lemma scalar_cell_cover
    {A : ℝ} {n : ℕ} (hA : 0 < A) (hn : 0 < n) {x : ℝ}
    (hx₁ : -A ≤ x) (hx₂ : x ≤ A) :
    ∃ i : Fin n,
      |x - (-A + (2 * (i : ℝ) + 1) * A / n)| ≤ A / n := by
  by_cases hright : x = A
  · refine ⟨⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt hn) (by omega)⟩, ?_⟩
    rw [hright]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn1 : 1 ≤ n := by omega
    have hcalc :
        A - (-A + (2 * ((n - 1 : ℕ) : ℝ) + 1) * A / n) = A / n := by
      rw [Nat.cast_sub hn1]
      field_simp
      ring_nf
    rw [hcalc, abs_of_nonneg (by positivity : 0 ≤ A / (n : ℝ))]
  · have hlt : x < A := lt_of_le_of_ne hx₂ hright
    let z : ℝ := (x + A) * n / (2 * A)
    have hz : 0 ≤ z := by
      dsimp [z]
      have hxA : 0 ≤ x + A := by linarith
      positivity
    let k : ℕ := ⌊z⌋₊
    have hklt : k < n := by
      apply (Nat.floor_lt' (Nat.ne_of_gt hn)).2
      dsimp [z]
      field_simp
      ring_nf at *
      nlinarith
    refine ⟨⟨k, hklt⟩, ?_⟩
    have hk_le : (k : ℝ) ≤ z := Nat.floor_le hz
    have hz_lt : z < k + 1 := Nat.lt_floor_add_one z
    have hleft : -A + 2 * (k : ℝ) * A / n ≤ x := by
      dsimp [z] at hk_le
      field_simp at hk_le
      ring_nf at hk_le
      field_simp
      have hnR : (0 : ℝ) < n := by positivity
      nlinarith [hk_le, mul_pos hA hnR]
    have hright' : x < -A + 2 * ((k : ℝ) + 1) * A / n := by
      dsimp [z] at hz_lt
      field_simp at hz_lt
      ring_nf at hz_lt
      field_simp
      have hnR : (0 : ℝ) < n := by positivity
      nlinarith [hz_lt, mul_pos hA hnR]
    have hleft' : -A + (2 * (k : ℝ) + 1) * A / n - A / n ≤ x := by
      calc
        -A + (2 * (k : ℝ) + 1) * A / n - A / n =
            -A + 2 * (k : ℝ) * A / n := by field_simp; ring
        _ ≤ x := hleft
    have hright'' : x ≤ -A + (2 * (k : ℝ) + 1) * A / n + A / n := by
      have htemp : x < -A + (2 * (k : ℝ) + 1) * A / n + A / n := by
        calc
        x < -A + 2 * ((k : ℝ) + 1) * A / n := hright'
        _ = -A + (2 * (k : ℝ) + 1) * A / n + A / n := by field_simp; ring
      exact htemp.le
    change |x - (-A + (2 * (k : ℝ) + 1) * A / n)| ≤ A / n
    rw [abs_le]
    constructor <;> linarith

private lemma scalar_cell_cover_zero
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x = 0) :
    ∃ i : Fin n,
      |x - (-(0 : ℝ) + (2 * (i : ℝ) + 1) * 0 / n)| ≤ 0 := by
  subst x
  refine ⟨⟨0, hn⟩, ?_⟩
  simp

/-- The centre samples of a positive-width interval cover that interval with
radius half its cell width. -/
theorem scalar_cell_centre_cover
    {A : ℝ} {n : ℕ} (hA : 0 ≤ A) (hn : 0 < n) {x : ℝ}
    (hx₁ : -A ≤ x) (hx₂ : x ≤ A) :
    ∃ i : Fin n,
      |x - (-A + (2 * (i : ℝ) + 1) * A / n)| ≤ A / n := by
  by_cases hAz : A = 0
  · subst A
    simpa using (scalar_cell_cover_zero hn (by linarith))
  · exact scalar_cell_cover (lt_of_le_of_ne hA (Ne.symm hAz)) hn hx₁ hx₂

noncomputable def rectangleCellCentre (A B : ℝ) (nx ny : ℕ)
    (ij : Fin nx × Fin ny) : Point3 :=
  WithLp.toLp 2 (![(-A + (2 * (ij.1 : ℝ) + 1) * A / nx),
    (-B + (2 * (ij.2 : ℝ) + 1) * B / ny), 0] : Fin 3 → ℝ)

def planarRectangle (A B : ℝ) : Set Point3 :=
  {x | x 0 ∈ Set.Icc (-A) A ∧ x 1 ∈ Set.Icc (-B) B ∧ x 2 = 0}

private lemma rect_cover_exists
    {A B : ℝ} {nx ny : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnx : 0 < nx) (hny : 0 < ny) {x : Point3} (hx : x ∈ planarRectangle A B) :
    ∃ ij : Fin nx × Fin ny,
      ‖x - rectangleCellCentre A B nx ny ij‖ ≤
        Real.sqrt ((A / nx) ^ 2 + (B / ny) ^ 2) := by
  obtain ⟨ix, hix⟩ := scalar_cell_centre_cover hA hnx hx.1.1 hx.1.2
  have hy : x 1 ∈ Set.Icc (-B) B := hx.2.1
  obtain ⟨iy, hiy⟩ := scalar_cell_centre_cover hB hny hy.1 hy.2
  refine ⟨(ix, iy), ?_⟩
  rw [EuclideanSpace.norm_eq]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, rectangleCellCentre]
  have hz : x 2 - 0 = 0 := by linarith [hx.2.2]
  have hsq : (x 0 - (-A + (2 * (ix : ℝ) + 1) * A / nx)) ^ 2 ≤ (A / nx) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : 0 ≤ A / (nx : ℝ))] using hix
  have hsqy : (x 1 - (-B + (2 * (iy : ℝ) + 1) * B / ny)) ^ 2 ≤ (B / ny) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by positivity : 0 ≤ B / (ny : ℝ))] using hiy
  have hnonneg : 0 ≤ (A / nx) ^ 2 + (B / ny) ^ 2 := by positivity
  have hzsq : (x 2) ^ 2 = 0 := by rw [show x 2 = 0 by linarith [hx.2.2]]; simp
  apply Real.sqrt_le_sqrt
  simp [Real.norm_eq_abs, Fin.sum_univ_succ, rectangleCellCentre,
    WithLp.ofLp_toLp] at ⊢
  nlinarith [hsq, hsqy]

/-- Cell-centre samples cover a planar rectangle. The third coordinate is
zero, so the cover radius is the Euclidean diagonal of a half-cell. -/
theorem planar_rectangle_cell_centre_cover
    {A B : ℝ} {nx ny : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnx : 0 < nx) (hny : 0 < ny) :
    ∀ x ∈ planarRectangle A B, ∃ ij : Fin nx × Fin ny,
      ‖x - rectangleCellCentre A B nx ny ij‖ ≤
        Real.sqrt ((A / nx) ^ 2 + (B / ny) ^ 2) := by
  intro x hx
  exact rect_cover_exists hA hB hnx hny hx

/-- Every rectangular-body sample has lever arm at most the rectangle's
corner radius. -/
theorem planar_rectangle_cell_centre_lever_arm
    {A B : ℝ} {nx ny : ℕ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnx : 0 < nx) (hny : 0 < ny) (ij : Fin nx × Fin ny) :
    ‖rectangleCellCentre A B nx ny ij‖ ≤ Real.sqrt (A ^ 2 + B ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [rectangleCellCentre]
  have hix : (0 : ℝ) ≤ (ij.1 : ℝ) := by positivity
  have hiy : (0 : ℝ) ≤ (ij.2 : ℝ) := by positivity
  have hix' : (ij.1 : ℝ) < nx := by exact_mod_cast ij.1.isLt
  have hiy' : (ij.2 : ℝ) < ny := by exact_mod_cast ij.2.isLt
  have hxbound : |(-A + (2 * (ij.1 : ℝ) + 1) * A / nx)| ≤ A := by
    rw [abs_le]
    constructor
    · field_simp
      nlinarith [hix]
    · field_simp
      have hsucc : (ij.1 : ℝ) + 1 ≤ nx := by
        exact_mod_cast Nat.succ_le_of_lt ij.1.isLt
      have hbase : -(nx : ℝ) + (2 * (ij.1 : ℝ) + 1) ≤ nx := by nlinarith [hsucc]
      have hmul := mul_le_mul_of_nonneg_left hbase hA
      nlinarith
  have hybound : |(-B + (2 * (ij.2 : ℝ) + 1) * B / ny)| ≤ B := by
    rw [abs_le]
    constructor
    · field_simp
      nlinarith [hiy]
    · field_simp
      have hsucc : (ij.2 : ℝ) + 1 ≤ ny := by
        exact_mod_cast Nat.succ_le_of_lt ij.2.isLt
      have hbase : -(ny : ℝ) + (2 * (ij.2 : ℝ) + 1) ≤ ny := by nlinarith [hsucc]
      have hmul := mul_le_mul_of_nonneg_left hbase hB
      nlinarith
  have hsqx : (-A + (2 * (ij.1 : ℝ) + 1) * A / nx) ^ 2 ≤ A ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hA] using hxbound
  have hsqy : (-B + (2 * (ij.2 : ℝ) + 1) * B / ny) ^ 2 ≤ B ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hB] using hybound
  apply Real.sqrt_le_sqrt
  simpa [Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] using add_le_add hsqx hsqy

/-- A centred planar disc is covered by its centre sample with radius `a`. -/
def planarDisc (a : ℝ) : Set Point3 :=
  {x | ‖x‖ ≤ a ∧ x 2 = 0}

theorem centred_disc_singleton_cover
    {a : ℝ} :
    ∀ x ∈ planarDisc a, ∃ _ : Unit, ‖x - (0 : Point3)‖ ≤ a := by
  intro x hx
  exact ⟨(), by simpa using hx.1⟩

end Ctrllib

#print axioms Ctrllib.scalar_cell_centre_cover
#print axioms Ctrllib.planar_rectangle_cell_centre_cover
#print axioms Ctrllib.planar_rectangle_cell_centre_lever_arm
#print axioms Ctrllib.centred_disc_singleton_cover
