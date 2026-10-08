import Percolation.Literature.Connectivity
import Percolation.Literature.PercolationProofs
import Percolation.Literature.ZeroOneLaw
import Percolation.Util.Linter

/-!
# The zero–one law for the existence of an infinite open cluster (Grimmett 1999, Thm. (1.11))

Sibling proof file of `Connectivity.lean`. We
prove the statement `Percolation.Literature.Grimmett1999_prob_exists_percolatesAt` stated there
(Grimmett, *Percolation*, 2nd ed. (1999), §1.4, Thm. (1.11), p. 14: "The probability `ψ(p)` that
there exists an infinite open cluster satisfies `ψ(p) = 0` if `θ(p) = 0`, `ψ(p) = 1` if
`θ(p) > 0`"), following the printed proof (§1.4, p. 19, "Proof of Theorem (1.11)"):

> "First, we note that the event {`ℤ^d` contains an infinite open cluster} does not depend upon
> the states of any finite collection of edges. By the usual zero–one law (see, for example,
> Grimmett and Stirzaker (1992, p. 290)), `ψ` takes the values 0 and 1 only. If `θ(p) = 0` then
> `ψ(p) ≤ Σ_{x ∈ ℤ^d} P_p(|C(x)| = ∞) = 0`. On the other hand, if `θ(p) > 0` then
> `ψ(p) ≥ P_p(|C| = ∞) > 0` so that `ψ(p) = 1` by the zero–one law, as required."

The zero–one input is taken in the translation-invariant form of
(`bondPercolation_zero_one_of_relabel_shift`, `ZeroOneLaw.lean`: an event invariant under the
shift of configurations by a non-zero `v ∈ ℤ^d` has `P_p`-probability `0` or `1`; Grimmett uses
this form of the law in §8.2, p. 198: "Since `N` is a translation-invariant function on `Ω`, it is
a.s. constant"), the event `E_∞ = {∃ x, |C(x)| = ∞}` being invariant under
every translation (`preimage_relabel_shift_setOf_exists_percolatesAt`). The inequality
`ψ ≤ Σ_x θ_x = Σ_x θ_0` uses the translation invariance `θ_x(p) = θ_0(p)`
(`theta_zdGraph_eq_theta_zero`, from `bondPercolation_real_preimage_shift`,
`BondPercolationSymmetry.lean`; Grimmett §1.3 p. 12: "By the translation invariance of the
lattice and of the probability measure `P_p`, the distribution of `C(x)` is independent of the
choice of `x`", and §1.4 p. 13) and countable subadditivity. For `d = 0`
(one site, no edges) every cluster is finite, `θ ≡ 0`, and the second clause is vacuous.

Mathlib anchors: `SimpleGraph.Iso.reachable_iff`, `MeasureTheory.measure_iUnion_null_iff`,
`PreErgodic.prob_eq_zero_or_one` (through `bondPercolation_zero_one_of_relabel_shift`).

## References
* G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §1.3 p. 12; §1.4 p. 13, Thm. (1.11)
  p. 14 with its proof p. 19; §8.2 p. 198 [GrimmettPercolation1999].
-/

namespace Percolation.Literature

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The shift `ω ↦ ω + v` carries the open cluster of `x` onto the open cluster of `x + v`:
`C_{ω + v}(x + v) = C_ω(x) + v` (the open graph of `ω + v` is isomorphic to that of `ω` along
`z ↦ z + v`, `openGraph_relabel_adj_iff`; Grimmett 1999, §1.3 p. 12: "the distribution of `C(x)`
is independent of the choice of `x`"). [cite: GrimmettPercolation1999, §1.3 p. 12] -/
theorem openCluster_relabel_shift (v : LatticeModels.Site d) (ω : BondConfig (LatticeModels.Site d)) (x : LatticeModels.Site d) :
    openCluster (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ω) (x + v) =
      (· + v) '' openCluster ω x := by
  let φ : openGraph ω ≃g openGraph (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ω) :=
    { toEquiv := LatticeModels.Site.shift v
      map_rel_iff' := fun {a b} => openGraph_relabel_adj_iff (LatticeModels.Site.shift v) ω a b }
  ext y
  simp only [openCluster, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨y - v, ?_, sub_add_cancel y v⟩
    have h' : (openGraph (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ω)).Reachable
        (φ x) (φ (y - v)) := by
      change (openGraph (BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ω)).Reachable
        (x + v) (y - v + v)
      rwa [sub_add_cancel]
    exact φ.reachable_iff.1 h'
  · rintro ⟨z, hz, rfl⟩
    exact φ.reachable_iff.2 hz

/-- `(ω ↦ ω + v)⁻¹' {|C(x + v)| = ∞} = {|C(x)| = ∞}`: translating a configuration translates
its infinite clusters (Grimmett 1999, §1.3 p. 12). [cite: GrimmettPercolation1999, §1.3 p. 12] -/
theorem preimage_relabel_shift_percolatesAt (v x : LatticeModels.Site d) :
    BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ⁻¹'
        (percolatesAt (x + v) : Set (BondConfig (LatticeModels.Site d))) = percolatesAt x := by
  ext ω
  simp only [Set.mem_preimage, percolatesAt, Set.mem_setOf_eq, openCluster_relabel_shift]
  exact Set.infinite_image_iff (add_left_injective v).injOn

/-- **Translation invariance of the percolation probability**: `θ_x(p) = θ_0(p)` on `ℤ^d`
(Grimmett 1999, §1.4, p. 13: "By the translation invariance of the lattice and probability
measure, we lose no generality by taking" the vertex to be the origin). [cite: GrimmettPercolation1999, §1.4 p. 13] -/
theorem theta_zdGraph_eq_theta_zero (p : unitInterval) (x : LatticeModels.Site d) :
    theta (LatticeModels.zdGraph d) x p = theta (LatticeModels.zdGraph d) (0 : LatticeModels.Site d) p := by
  have h := preimage_relabel_shift_percolatesAt x (0 : LatticeModels.Site d)
  rw [zero_add] at h
  simp only [theta]
  rw [← h, bondPercolation_real_preimage_shift]

/-- The event `E_∞ = {some open cluster is infinite}` is invariant under every translation of
`ℤ^d` (Grimmett 1999, p. 19: it "does not depend upon the states of any finite collection of
edges"; §8.2 p. 198, translation-invariant functions on `Ω`). [cite: GrimmettPercolation1999, §1.4 p. 19 (proof of Thm. 1.11)] -/
theorem preimage_relabel_shift_setOf_exists_percolatesAt (v : LatticeModels.Site d) :
    BondConfig.relabel (sym2Equiv (LatticeModels.Site.shift v)) ⁻¹'
        {ω : BondConfig (LatticeModels.Site d) | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} =
      {ω | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x - v, ?_⟩
    rw [← preimage_relabel_shift_percolatesAt v (x - v), Set.mem_preimage, sub_add_cancel]
    exact hx
  · rintro ⟨x, hx⟩
    refine ⟨x + v, ?_⟩
    rw [← preimage_relabel_shift_percolatesAt v x, Set.mem_preimage] at hx
    exact hx

/-- On `ℤ⁰` (a single site, no edges) no cluster is infinite: `θ ≡ 0` — the degenerate instance
`d = 0` of the definition `θ(p) = P_p(|C| = ∞)`. [cite: GrimmettPercolation1999, §1.4 (1.6) p. 13 (degenerate case d = 0)] -/
theorem theta_zdGraph_zero (x : LatticeModels.Site 0) (p : unitInterval) : theta (LatticeModels.zdGraph 0) x p = 0 := by
  have h : (percolatesAt x : Set (BondConfig (LatticeModels.Site 0))) = ∅ := by
    ext ω
    simp only [percolatesAt, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact Set.not_infinite.2 (Set.toFinite _)
  simp [theta, h]

/-- **Grimmett 1999, Thm. (1.11), proved** (zero–one law for the existence of an infinite
open cluster, nearest-neighbour bond percolation on `ℤ^d`, every `d` and `p`): with
`ψ(p) = P_p(∃ x, |C(x)| = ∞)`, `θ(p) = 0 ⟹ ψ(p) = 0` and `θ(p) > 0 ⟹ ψ(p) = 1`. Proof as
printed (p. 19): `ψ(p) ≤ Σ_x θ_x(p) = 0` by translation invariance and countable subadditivity;
and `ψ ∈ {0, 1}` by the zero–one law for the translation-invariant event `E_∞`
(`bondPercolation_zero_one_of_relabel_shift` with `v = e₀ ≠ 0`, which needs `d ≥ 1`; for `d = 0`
the hypothesis `θ > 0` is impossible), while `ψ(p) ≥ θ(p) > 0` excludes `0`. [cite: GrimmettPercolation1999, §1.4 Thm. (1.11) p. 14, proof p. 19] -/
theorem Grimmett1999_prob_exists_percolatesAt_holds : Grimmett1999_prob_exists_percolatesAt := by
  intro d p
  set μ := bondPercolation (LatticeModels.zdGraph d) p with hμ
  have hE : {ω : BondConfig (LatticeModels.Site d) | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} =
      ⋃ x : LatticeModels.Site d, percolatesAt x := by
    ext ω; simp
  have hEm : MeasurableSet {ω : BondConfig (LatticeModels.Site d) | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} := by
    rw [hE]; exact MeasurableSet.iUnion fun x => measurableSet_percolatesAt_holds x
  refine ⟨fun h0 => ?_, fun hpos => ?_⟩
  · -- `ψ(p) ≤ Σ_x θ_x(p) = Σ_x θ_0(p) = 0`
    have hx : ∀ x : LatticeModels.Site d, μ (percolatesAt x) = 0 := fun x =>
      (measureReal_eq_zero_iff (measure_ne_top μ _)).1
        ((theta_zdGraph_eq_theta_zero p x).trans h0)
    have h : μ {ω : BondConfig (LatticeModels.Site d) | ∃ x : LatticeModels.Site d, ω ∈ percolatesAt x} = 0 := by
      rw [hE]; exact (measure_iUnion_null_iff).2 hx
    simp [Measure.real, h]
  · cases d with
    | zero => exact absurd (theta_zdGraph_zero 0 p) hpos.ne'
    | succ d =>
      -- the zero–one law for the translation-invariant event `E_∞`, shift by `e₀ ≠ 0`
      set v : LatticeModels.Site (d + 1) := Pi.single 0 1 with hv_def
      have hv : v ≠ 0 := by
        intro h
        have := congrFun h 0
        simp [hv_def] at this
      rcases bondPercolation_zero_one_of_relabel_shift p hv hEm
          (preimage_relabel_shift_setOf_exists_percolatesAt v) with h0 | h1
      · -- `ψ(p) ≥ θ(p) > 0` excludes `ψ(p) = 0`
        exfalso
        have hle : theta (LatticeModels.zdGraph (d + 1)) (0 : LatticeModels.Site (d + 1)) p ≤
            μ.real {ω : BondConfig (LatticeModels.Site (d + 1)) | ∃ x : LatticeModels.Site (d + 1), ω ∈ percolatesAt x} :=
          measureReal_mono (fun ω hω => ⟨0, hω⟩) (measure_ne_top μ _)
        have h0' : μ.real {ω : BondConfig (LatticeModels.Site (d + 1)) | ∃ x : LatticeModels.Site (d + 1),
            ω ∈ percolatesAt x} = 0 := by
          rw [← hμ] at h0
          simp [Measure.real, h0]
        exact absurd (hle.trans_eq h0') (not_le.2 hpos)
      · rw [← hμ] at h1
        simp [Measure.real, h1]

end

end Percolation.Literature
