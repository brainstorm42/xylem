import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.ProjIcc
import Percolation.Literature.BernoulliPercolation
import Percolation.Util.Linter

/-!
# Sharpness of the phase transition for Bernoulli percolation on `ℤ^d` (Duminil-Copin–Tassion 2016): the quantities `φ_p(S)`, `p̃_c` and the named steps

This file records the
architecture of the Duminil-Copin–Tassion proof of the sharpness of the percolation phase
transition on the hypercubic lattice, in the nearest-neighbour `p`-parametrisation of the
companion note

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for
  Bernoulli percolation on `ℤ^d`*, L'Enseignement Math. 62 (2016) 199–206 (arXiv:1502.03051)
  [DuminilCopinTassionEM2016], Thm. 1.1, §2.1, Lemma 2.1, §2.2;

which is the `ℤ^d`, `J_{x,y} = 𝟙_{x ∼ y}`, `p = 1 - e^{-β}` case of H. Duminil-Copin, V. Tassion,
*Comm. Math. Phys.* 343 (2016) 725–745 [DuminilCopinTassionCMP2016], Thm. 1.1 (see §1.2 there,
"Nearest-neighbor percolation", which refers to the note for this parametrisation).

## Contents

* `DCT16.phi p S = φ_p(S) := p · Σ_{x ∈ S} Σ_{y ∉ S, y ∼ x} P_p[0 ⟷ x in S]` (note, §1, definition of `φ_p(S)`);
* `DCT16.tildeCriticalProb d = p̃_c := sup {p ∈ [0,1] | ∃ finite S ∋ 0, φ_p(S) < 1}` (note, §1, definition of `p̃_c`);
* `DCT16.originSets d n`, the finite collection `{S | 0 ∈ S ⊆ Λ_n}` over which the infimum of
  Lemma 2.1 is taken, and `DCT16.thetaN d n q = P_q[0 ⟷ ∂Λ_n]` as a function of a real parameter
  (constant extension outside `[0, 1]` via `Set.projIcc`, the convention of `russo_formula`);
* the objects of §2 of the note: the translated one-arm event `DCT16.armEvent`, the cluster `DCT16.clusterSet` of `0` inside `S` with the events `DCT16.clusterEvent` (`{𝒞 = C}`),
  `DCT16.exitEvent` (`{y ⟷ ∂Λ_N in Λ_N ∖ C}`) and the pairs `DCT16.clusterPairs` (§2.1), and
  `DCT16.BdryConn` (`z ⟷ ∂Λ_n`), the random set `DCT16.blockSet` (`𝒮`) with the events
  `DCT16.blockEvent` (`{𝒮 = S}`) (proof of Lemma 2.1);

## Conventions

* `Λ_n = box d n = {-n, …, n}^d`, `∂Λ_n = innerBoundary (zdGraph d) (box d n)` (for `n ≥ 1` this
  is `Λ_n ∖ Λ_{n-1}`, the note's `∂Λ_n`), and `{0 ⟷ ∂Λ_n} = siteToBoundary d n` (connection inside
  `Λ_n`; an open path from `0` to `∂Λ_n` stopped at its first visit to `∂Λ_n` lies in `Λ_n`, so this
  is the note's event). `{0 ⟷ x in S} = openConnIn ↑S 0 x` (`Literature/Basic.lean`).
* The edge boundary `ΔS = {{x, y} : x ∈ S, y ∉ S}` is summed as the double sum over `x ∈ S` and
  the neighbours `y ∉ S` of `x` (each boundary edge has exactly one endpoint in `S`, so this is the
  note's `Σ_{{x,y} ∈ ΔS}`).
* Lemma 2.1 is printed for `p ∈ [0, 1]`; the right-hand side `1/(p(1-p))` is only meaningful on
  `(0, 1)`, where we state it, for the real-parameter map `DCT16.thetaN` and in the form
  "`∃ D, HasDerivAt … D p ∧ RHS ≤ D`" (the derivative exists by Russo's formula).
* All statements are over `d : ℕ` without the note's standing assumption `d ≥ 2` when they hold
  verbatim for every `d` (for `d = 0` they are vacuous or trivial); `perc_sharpness` itself carries
  `2 ≤ d`.
-/

namespace Percolation.Literature

open MeasureTheory LatticeModels
open scoped ProbabilityTheory

variable {d : ℕ}

namespace DCT16

/-- `φ_p(S) := p · Σ_{x ∈ S} Σ_{y ∉ S, {x,y} ∈ E} P_p[0 ⟷ x in S]`, the expected number of open
edges of the edge boundary of `S` whose inner endpoint is joined to `0` inside `S`
(Duminil-Copin–Tassion 2016, §1, display defining `φ_p(S)`; CMP 343 (2016), §1.2 "Nearest-neighbor percolation").
Defined for every finite `S ⊆ ℤ^d` (the note only uses `S ∋ 0`).
[cite: DuminilCopinTassionEM2016, §1 (definition of φ_p(S))] -/
noncomputable def phi (p : unitInterval) (S : Finset (Site d)) : ℝ :=
  p * ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
    (bondPercolation (zdGraph d) p).real (openConnIn (↑S : Set (Site d)) 0 x)

/-- `φ_p(S)` unfolded. [cite: DuminilCopinTassionEM2016, §1 (definition of φ_p(S))] -/
theorem phi_def (p : unitInterval) (S : Finset (Site d)) :
    phi p S = p * ∑ x ∈ S, ∑ y ∈ (zdGraph d).neighborFinset x with y ∉ S,
      (bondPercolation (zdGraph d) p).real (openConnIn (↑S : Set (Site d)) 0 x) := rfl

/-- `φ_p(S) ≥ 0`. [folklore] -/
theorem phi_nonneg (p : unitInterval) (S : Finset (Site d)) : 0 ≤ phi p S :=
  mul_nonneg p.2.1 (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => measureReal_nonneg)

/-- `φ_0(S) = 0`. [folklore] -/
@[simp] theorem phi_zero (S : Finset (Site d)) : phi 0 S = 0 := by
  simp [phi]

/-- The finite collection `{S | 0 ∈ S ⊆ Λ_n}` indexing the infimum in Lemma 2.1 of
Duminil-Copin–Tassion 2016. [cite: DuminilCopinTassionEM2016, Lemma 2.1] -/
noncomputable def originSets (d n : ℕ) : Finset (Finset (Site d)) :=
  (box d n).powerset.filter fun S => (0 : Site d) ∈ S

/-- Membership in `originSets`. [cite: DuminilCopinTassionEM2016, Lemma 2.1] -/
theorem mem_originSets {n : ℕ} {S : Finset (Site d)} :
    S ∈ originSets d n ↔ S ⊆ box d n ∧ (0 : Site d) ∈ S := by
  simp [originSets]

/-- `{0} ∈ originSets d n`, so the family is nonempty. [folklore] -/
theorem originSets_nonempty (d n : ℕ) : (originSets d n).Nonempty :=
  ⟨{0}, mem_originSets.2 ⟨by simp, by simp⟩⟩

/-- [cite: DuminilCopinTassionEM2016, Lemma 2.1] -/
noncomputable def thetaN (d n : ℕ) (q : ℝ) : ℝ :=
  (bondPercolation (zdGraph d) (Set.projIcc 0 1 zero_le_one q)).real (siteToBoundary d n)

/-- `θ_n` at a genuine parameter `p ∈ [0, 1]`. [folklore] -/
theorem thetaN_coe (d n : ℕ) (p : unitInterval) :
    thetaN d n p = (bondPercolation (zdGraph d) p).real (siteToBoundary d n) := by
  rw [thetaN, Set.projIcc_val]

/-! ### Objects of the proof

The events and random sets manipulated in §2 of Duminil-Copin–Tassion 2016, defined here (with
their informal meaning and locator) so that the proof files `SharpnessDCTProofs.lean` /
`BernoulliPercolationProofs.lean` are pure proofs. All connection events are phrased through
`openConnIn S x y = {x ⟷ y in S}`; the set of pairs inside a set `S` of sites (the
coordinates an event "inside `S`" depends on) is Mathlib's `Set.sym2 S`. -/

section Objects

/-- The translated one-arm event `{v ⟷ v + ∂Λ_n in v + Λ_n}`: some `a` with `a - v ∈ ∂Λ_n` is
joined to `v` inside `v + Λ_n`. For `v = 0` this is `siteToBoundary d n`. (Duminil-Copin–Tassion
2016, §2.1: "since `y ∈ Λ_L`, one can bound `P_p[y ⟷ ∂Λ_{kL}]` by `P_p[0 ⟷ ∂Λ_{(k-1)L}]`", i.e.
translation invariance applied to this event.) [cite: DuminilCopinTassionEM2016, §2.1] -/
def armEvent (v : Site d) (n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∃ a, a - v ∈ innerBoundary (zdGraph d) (box d n) ∧
    ω ∈ openConnIn {z : Site d | z - v ∈ box d n} v a}

/-- `𝒞(ω) = {z ∈ S : 0 ⟷ z in S}`, the cluster of the origin in the configuration restricted to
`S` (Duminil-Copin–Tassion 2016, §2.1). It is a subset of `S`. [cite: DuminilCopinTassionEM2016, §2.1] -/
def clusterSet (S : Finset (Site d)) (ω : BondConfig (Site d)) : Set (Site d) :=
  {z | ω ∈ openConnIn (↑S : Set (Site d)) 0 z}

/-- The event `{𝒞 = C}` (Duminil-Copin–Tassion 2016, §2.1, "decomposition with respect to
possible values of `𝒞`"). [cite: DuminilCopinTassionEM2016, §2.1] -/
def clusterEvent (S C : Finset (Site d)) : Set (BondConfig (Site d)) :=
  {ω | clusterSet S ω = ↑C}

/-- The pairs inside `S` with at least one member in `C`: the pairs whose states determine the
event `{𝒞 = C}` (Duminil-Copin–Tassion 2016, §2.1, "the three events depend on different sets of
edges"). [cite: DuminilCopinTassionEM2016, §2.1] -/
def clusterPairs (S C : Finset (Site d)) : Finset (Sym2 (Site d)) := S.sym2 \ (S \ C).sym2

/-- The event `{y ⟷ ∂Λ_N in Λ_N ∖ C}` (Duminil-Copin–Tassion 2016, §2.1: `y ⟷ ∂Λ_{kL}` off `𝒞`;
an open path off `𝒞` to `∂Λ_N`, stopped at its first visit to `∂Λ_N`, lies in `Λ_N ∖ 𝒞`).
[cite: DuminilCopinTassionEM2016, §2.1] -/
def exitEvent (N : ℕ) (C : Finset (Site d)) (y : Site d) : Set (BondConfig (Site d)) :=
  {ω | ∃ z, z ∈ innerBoundary (zdGraph d) (box d N) ∧
    ω ∈ openConnIn ((↑(box d N) : Set (Site d)) \ ↑C) y z}

/-- `z ⟷ ∂Λ_n` (inside `Λ_n`): `z` is joined inside `Λ_n` by an open path to a site of `∂Λ_n`; for
`z = 0` this is literally `siteToBoundary d n` (Duminil-Copin–Tassion 2016, proof of Lemma 2.1).
[cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
def BdryConn (n : ℕ) (ω : BondConfig (Site d)) (z : Site d) : Prop :=
  ∃ w ∈ innerBoundary (zdGraph d) (box d n), ω ∈ openConnIn (↑(box d n) : Set (Site d)) z w

/-- `{0 ⟷ ∂Λ_n} = siteToBoundary d n` is `BdryConn n · 0`. [folklore] -/
theorem mem_siteToBoundary_iff_bdryConn {n : ℕ} {ω : BondConfig (Site d)} :
    ω ∈ siteToBoundary d n ↔ BdryConn n ω 0 := Iff.rfl

open Classical in
/-- `𝒮(ω) := {z ∈ Λ_n : z ⟷̸ ∂Λ_n}` (Duminil-Copin–Tassion 2016, proof of Lemma 2.1: "the boundary
of `𝒮` corresponds to the outmost blocking surface"). [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
noncomputable def blockSet (n : ℕ) (ω : BondConfig (Site d)) : Finset (Site d) :=
  (box d n).filter fun z => ¬BdryConn n ω z

open Classical in
/-- Membership in `𝒮(ω)`. [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
theorem mem_blockSet_iff {n : ℕ} {ω : BondConfig (Site d)} {z : Site d} :
    z ∈ blockSet n ω ↔ z ∈ box d n ∧ ¬BdryConn n ω z := by
  unfold blockSet
  rw [Finset.mem_filter]

/-- The event `{𝒮 = S}` (Duminil-Copin–Tassion 2016, proof of Lemma 2.1, "by summing over the
possible values for `𝒮`"). [cite: DuminilCopinTassionEM2016, §2.2 (proof of Lemma 2.1)] -/
def blockEvent (n : ℕ) (S : Finset (Site d)) : Set (BondConfig (Site d)) := {ω | blockSet n ω = S}

end Objects

end DCT16

/-! ### The steps of the proof, as statements -/

/-- **Monotonicity of `φ_p(S)` in `p`** (used implicitly in the first sentence of §2.1 of
Duminil-Copin–Tassion 2016, "by definition, one can fix a finite set `S` containing the origin such
that `φ_p(S) < 1`" for `p < p̃_c`): `p ≤ q ⟹ φ_p(S) ≤ φ_q(S)`, since `{0 ⟷ x in S}` is increasing
and `P_p(A) ≤ P_q(A)` for increasing events (Grimmett, *Percolation* (1999), Thm. 2.1).
[cite: DuminilCopinTassionEM2016, §2.1] [cite: GrimmettPercolation1999, Thm. 2.1] -/
def DCT16_phi_mono : Prop :=
  ∀ {d : ℕ} (S : Finset (Site d)) {p q : unitInterval}, p ≤ q → DCT16.phi p S ≤ DCT16.phi q S

/-- **Duminil-Copin–Tassion 2016, §2.1 (proof of item 1 of Thm. 1.1).** If some finite `S ∋ 0`
has `φ_p(S) < 1` (and `p < 1`, automatic in the note where `p < p̃_c ≤ 1`), then there is
`c = c(p) > 0` with `P_p[0 ⟷ ∂Λ_n] ≤ e^{-cn}` for all `n` (the note states `n ≥ 1`; `n = 0` is
trivial). Printed proof: with `S ⊆ Λ_{L-1}`, an exploration of the cluster of `0` in `S` and
independence give `P_p[0 ⟷ ∂Λ_{kL}] ≤ φ_p(S) P_p[0 ⟷ ∂Λ_{(k-1)L}]`, whence `≤ φ_p(S)^{k-1}` by
induction. [cite: DuminilCopinTassionEM2016, §2.1] -/
def DCT16_expDecay_of_phi_lt_one : Prop :=
  ∀ {d : ℕ} (p : unitInterval) (S : Finset (Site d)), (0 : Site d) ∈ S → DCT16.phi p S < 1 →
    (p : ℝ) < 1 →
      ∃ c > 0, ∀ n : ℕ, (bondPercolation (zdGraph d) p).real (siteToBoundary d n) ≤
        Real.exp (-c * n)

/-- **Duminil-Copin–Tassion 2016, Lemma 2.1** (differential inequality). For `n ≥ 1` and
`p ∈ (0, 1)`,
`d/dp P_p[0 ⟷ ∂Λ_n] ≥ 1/(p(1-p)) · inf_{0 ∈ S ⊆ Λ_n} φ_p(S) · (1 - P_p[0 ⟷ ∂Λ_n])` (2.1);
here in the form: the real-parameter map `θ_n = DCT16.thetaN d n` has a derivative `D` at `p`
(Russo's formula) and `D` dominates the right-hand side. (Printed for `p ∈ [0, 1]`; the factor
`1/(p(1-p))` restricts it to the open interval.) [cite: DuminilCopinTassionEM2016, Lemma 2.1] -/
def DCT16_lemma21 : Prop :=
  ∀ {d : ℕ} (n : ℕ), 1 ≤ n → ∀ (p : ℝ), p ∈ Set.Ioo (0 : ℝ) 1 →
    ∃ D : ℝ, HasDerivAt (DCT16.thetaN d n) D p ∧
      1 / (p * (1 - p)) *
          (DCT16.originSets d n).inf' (DCT16.originSets_nonempty d n)
            (fun S => DCT16.phi (Set.projIcc 0 1 zero_le_one p) S) *
          (1 - DCT16.thetaN d n p) ≤ D

/-- **Duminil-Copin–Tassion 2016, §2.2 (proof of item 2 of Thm. 1.1 from Lemma 2.1).** If
`φ_q(S) ≥ 1` for every finite `S ∋ 0` and every parameter `q ≥ p₁`, then for `p₁ < p < 1`,
`θ(p) ≥ (p - p₁)/(p(1 - p₁))`: "integrating the differential inequality (2.1) between `p₁` and
`p` implies `P_p[0 ⟷ ∂Λ_n] ≥ (p - p₁)/(p(1 - p₁))` for every `n ≥ 1`; letting `n → ∞` gives the
lower bound on `P_p[0 ⟷ ∞]`" (printed with `p₁ = p̃_c`: for `q > p̃_c` the hypothesis holds by
the definition of `p̃_c`, and for `q = p̃_c` by Remark 3 of the note). [cite: DuminilCopinTassionEM2016, §2.2] -/
def DCT16_meanField_of_phi_ge_one : Prop :=
  ∀ {d : ℕ} (p₁ : unitInterval),
    (∀ q : unitInterval, p₁ ≤ q → ∀ S : Finset (Site d), (0 : Site d) ∈ S → 1 ≤ DCT16.phi q S) →
    ∀ p : unitInterval, (p₁ : ℝ) < p → (p : ℝ) < 1 →
      ((p : ℝ) - p₁) / (p * (1 - p₁)) ≤ theta (zdGraph d) 0 p

/-! ### Conclusion (Duminil-Copin–Tassion 2016, §2, first sentence) -/

/-- **Sharpness of the percolation transition on `ℤ^d` from the Duminil-Copin–Tassion steps**
(Duminil-Copin–Tassion 2016, §2: "it is sufficient to show items 1 and 2 with `p_c` replaced by
`p̃_c`"). Given `p < p_c`: either some finite `S ∋ 0` has `φ_p(S) < 1`, and §2.1
(`DCT16_expDecay_of_phi_lt_one`) gives the exponential decay; or `φ_p(S) ≥ 1` for all `S ∋ 0`,
hence (monotonicity, `DCT16_phi_mono`) `φ_q(S) ≥ 1` for all `q ≥ p`, and §2.2
(`DCT16_meanField_of_phi_ge_one`) at the midpoint `r` of `p` and `p_c` gives `θ(r) > 0`,
contradicting `θ(r) = 0` for `r < p_c` (`theta_eq_zero_of_lt_criticalProb_holds`).
[cite: DuminilCopinTassionEM2016, Thm. 1.1(1) and §2] -/
theorem perc_sharpness_of_DCT16 (h0 : DCT16_phi_mono) (h1 : DCT16_expDecay_of_phi_lt_one)
    (h3 : DCT16_meanField_of_phi_ge_one) : perc_sharpness := by
  intro d _hd p hp
  obtain ⟨-, hpc1⟩ := criticalProb_mem_Icc (zdGraph d) (0 : Site d)
  have hp1 : (p : ℝ) < 1 := hp.trans_le hpc1
  by_cases hS : ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ DCT16.phi p S < 1
  · obtain ⟨S, h0S, hφ⟩ := hS
    exact h1 p S h0S hφ hp1
  · exfalso
    push Not at hS
    have hp0 : (0 : ℝ) ≤ p := p.2.1
    set r : ℝ := ((p : ℝ) + criticalProb (zdGraph d) 0) / 2 with hr
    have hpr : (p : ℝ) < r := by rw [hr]; linarith
    have hrc : r < criticalProb (zdGraph d) 0 := by rw [hr]; linarith
    have hr01 : r ∈ unitInterval := ⟨by linarith, by linarith⟩
    have hφ : ∀ q : unitInterval, p ≤ q → ∀ S : Finset (Site d), (0 : Site d) ∈ S →
        1 ≤ DCT16.phi q S :=
      fun q hq S h0S => (hS S h0S).trans (h0 S hq)
    have hθ := h3 p hφ ⟨r, hr01⟩ hpr (hrc.trans_le hpc1)
    have hzero : theta (zdGraph d) 0 ⟨r, hr01⟩ = 0 :=
      theta_eq_zero_of_lt_criticalProb_holds (zdGraph d) 0 ⟨r, hr01⟩ hrc
    have hpos : 0 < (r - p) / (r * (1 - p)) :=
      div_pos (by linarith) (mul_pos (by linarith) (by linarith))
    have hθ' : (r - p) / (r * (1 - p)) ≤ theta (zdGraph d) 0 ⟨r, hr01⟩ := hθ
    linarith

end Percolation.Literature
