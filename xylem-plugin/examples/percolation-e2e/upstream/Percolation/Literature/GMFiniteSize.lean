import Percolation.Literature.HalfSpaceBrickSymmetry
import Percolation.Literature.SeedLemma
import Percolation.Literature.UniformPercolation
import Percolation.Literature.UniquenessZone
import Percolation.Util.Linter

/-!
# The finite-size criterion of the Grimmett–Marstrand renormalisation, Martineau–Tassion form

For bond percolation on `ℤ^d` with `θ(p) > 0` and `p < 1` we PROVE:

* `orthantFace a τ n` — the face orthant `{x ∈ ∂Λ_n : x_a = τ_a n, τ_j x_j ≥ 0 (j ≠ a)}` of the
  box `Λ_n` (Grimmett's `T(n)` and its `2^d d!` images, (7.6) p. 150; `= GM.piece g n` for the
  signed permutation `g = (swap 0 a, τ ∘ swap 0 a)`, `orthantFace_eq_piece`);
* `exists_forall_lt_real_linked_orthantFace` — for every `η > 0`, `k₀`: some `k ≥ k₀` and `n₁`
  such that for all `n ≥ n₁` and every face orthant, `P_p(Λ_k ↔ orthantFace a τ n in Λ_n) > 1 - η`
  (Grimmett (7.14)–(7.16) with `ℓ' = 1`: `SeedLemma.lean`'s square-root trick, symmetry and
  finite-energy estimate);

## References

* S. Martineau, V. Tassion, *Locality of percolation for abelian Cayley graphs*, Ann. Probab. 45
  (2017) 1247–1277, arXiv:1312.1946, §3.3 Lemma 3.7, §3.4 (finite-size criterion)
  [MartineauTassion2017].
* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999, §7.2, (7.6) p. 150,
  (7.14)–(7.16) p. 151 [GrimmettPercolation1999].
-/

noncomputable section

namespace Percolation.Literature

open MeasureTheory ProbabilityTheory Filter LatticeModels DCT16 GM
open scoped _root_.Topology ENNReal

variable {d : ℕ}

/-! ## Face orthants -/

/-- The **face orthant** of `Λ_n` on the face `x_a = τ_a n`, with transverse signs `τ_j`:
`{x ∈ Λ_n : τ_a x_a = n, τ_j x_j ≥ 0 (j ≠ a)}` (Grimmett 1999, (7.6): `T(n)` and its images under
the symmetries of `B(n)`). [cite: GrimmettPercolation1999, §7.2 (7.6) p. 150] -/
def orthantFace (a : Fin d) (τ : Fin d → ℤˣ) (n : ℕ) : Finset (Site d) :=
  (box d n).filter fun x => (τ a : ℤ) * x a = n ∧ ∀ j, j ≠ a → 0 ≤ (τ j : ℤ) * x j

/-- Membership in a face orthant. [folklore] -/
theorem mem_orthantFace {a : Fin d} {τ : Fin d → ℤˣ} {n : ℕ} {x : Site d} :
    x ∈ orthantFace a τ n ↔ x ∈ box d n ∧ (τ a : ℤ) * x a = n ∧ ∀ j, j ≠ a → 0 ≤ (τ j : ℤ) * x j :=
  Finset.mem_filter

/-- **Face orthants are symmetric images of `T(n)`**: `orthantFace a τ n = GM.piece g n` for
`g = (swap 0 a, τ ∘ swap 0 a)`. [cite: GrimmettPercolation1999, §7.2 p. 151 (24 copies of T(n))] -/
theorem orthantFace_eq_piece [NeZero d] (a : Fin d) (τ : Fin d → ℤˣ) (n : ℕ) :
    orthantFace a τ n = piece ((Equiv.swap 0 a, fun j => τ (Equiv.swap 0 a j)) : HOct d) n := by
  ext x
  simp only [mem_orthantFace, piece, Finset.mem_filter, facePiece, Set.mem_setOf_eq,
    Site.signedPerm_apply, Equiv.symm_swap, Equiv.swap_apply_left]
  refine and_congr_right fun hx => and_congr_right fun _ => ?_
  rw [mem_box] at hx
  constructor
  · intro h j hj
    have hj' : Equiv.swap 0 a j ≠ a := by
      intro h'
      have := Equiv.swap_apply_self 0 a j
      rw [h', Equiv.swap_apply_right] at this
      exact hj this.symm
    refine ⟨h _ hj', ?_⟩
    have := BGN.abs_units_mul (τ (Equiv.swap 0 a j)) (x (Equiv.swap 0 a j))
    have hb := hx (Equiv.swap 0 a j)
    have : |x (Equiv.swap 0 a j)| ≤ n := abs_le.2 ⟨hb.1, hb.2⟩
    calc (τ (Equiv.swap 0 a j) : ℤ) * x (Equiv.swap 0 a j) ≤ |(τ (Equiv.swap 0 a j) : ℤ) * x (Equiv.swap 0 a j)| :=
          le_abs_self _
      _ ≤ n := by rwa [BGN.abs_units_mul]
  · intro h j hj
    have hj0 : Equiv.swap 0 a j ≠ 0 := by
      intro h'
      have := Equiv.swap_apply_self 0 a j
      rw [h', Equiv.swap_apply_left] at this
      exact hj this.symm
    have := (h (Equiv.swap 0 a j) hj0).1
    rwa [Equiv.swap_apply_self] at this

/-! ## `Λ_k ↔ orthantFace in Λ_n` with high probability (Grimmett (7.14)–(7.16), `ℓ' = 1`) -/

/-- The event `{S ↔ T in Λ_n}`: some vertex of `S` is joined inside `Λ_n` to some vertex of `T`.
[cite: GrimmettPercolation1999, §7.2 (7.10) p. 150] -/
def linkEvent (S T : Finset (Site d)) (n : ℕ) : Set (BondConfig (Site d)) :=
  {ω | ∃ y ∈ S, ∃ x ∈ T, ω ∈ openConnIn (↑(box d n) : Set (Site d)) y x}

/-- `{1 ≤ |linked T k n|} ⊆ {Λ_k ↔ T in Λ_n}`. [folklore] -/
theorem linkEvent_box_of_linked {T : Finset (Site d)} {k n : ℕ} {ω : BondConfig (Site d)}
    (h : 1 ≤ (linked T k n ω).card) : ω ∈ linkEvent (box d k) T n := by
  obtain ⟨x, hx⟩ := Finset.card_pos.1 h
  rw [mem_linked] at hx
  obtain ⟨hxT, y, hy, hc⟩ := hx
  exact ⟨y, hy, x, hxT, hc⟩

/-- **`P_p(Λ_k ↔ orthantFace in Λ_n) > 1 - η` for `k` large (as large as desired) and all large
`n`**, every face orthant (Grimmett 1999, (7.14)–(7.16) with `ℓ' = 1`: choose `k` with
`P_p(B(k) ↮ ∞) < η^K/2`, `K = 2^d d!`, then `n` large so that `P_p(1 ≤ |U(n)| < K) < η^K/2`
(finite energy and the disjointness of the events `{U(n) ≠ ∅ = U(n+1)}`); the square-root trick
and symmetry give each orthant). Requires `θ(p) > 0` and `p < 1`.
[cite: GrimmettPercolation1999, §7.2 (7.14)–(7.16) p. 151] -/
theorem exists_forall_lt_real_linked_orthantFace [NeZero d] (p : unitInterval)
    (hθ : 0 < theta (zdGraph d) (0 : Site d) p) (hp1 : (p : ℝ) < 1) {η : ℝ} (hη : 0 < η) (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ ∃ n₁ : ℕ, k < n₁ ∧ ∀ n, n₁ ≤ n → ∀ (a : Fin d) (τ : Fin d → ℤˣ),
      1 - η < (bondPercolation (zdGraph d) p).real (linkEvent (box d k) (orthantFace a τ n) n) := by
  set μ := bondPercolation (zdGraph d) p with hμ
  -- trivial when `η > 1`
  by_cases hη1 : 1 < η
  · exact ⟨k₀, le_rfl, k₀ + 1, Nat.lt_succ_self _, fun n _ a τ => lt_of_lt_of_le (by linarith) measureReal_nonneg⟩
  push Not at hη1
  set K : ℕ := Fintype.card (HOct d) with hK
  have hKpos : 0 < K := Fintype.card_pos
  set δ : ℝ := η ^ K with hδ
  have hδpos : 0 < δ := pow_pos hη K
  -- choose `k`
  have hev := (tendsto_prob_not_boxPerc (d := d) p hθ).eventually (gt_mem_nhds (half_pos hδpos))
  obtain ⟨k, hk, hkk₀⟩ := (hev.and (eventually_ge_atTop k₀)).exists
  refine ⟨k, hkk₀, ?_⟩
  -- choose `n`
  have hq : 0 < (1 - (p : ℝ)) ^ (2 * d * K) := pow_pos (by linarith) _
  have hev2 := (tendsto_prob_lastLevel (d := d) p k).eventually
    (gt_mem_nhds (show 0 < (1 - (p : ℝ)) ^ (2 * d * K) * (δ / 2) from mul_pos hq (half_pos hδpos)))
  obtain ⟨j₁, hj₁⟩ := hev2.exists_forall_of_atTop
  refine ⟨k + j₁ + 1, by omega, fun n hn a τ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  have hj : j₁ ≤ j := by omega
  have hkn : k ≤ k + j := Nat.le_add_right k j
  -- `P(|U(n)| < K) < δ`
  have hfew : μ.real (fewLinked d k (k + j) K) < δ / 2 := by
    have h1 := prob_fewLinked_le (d := d) hkn K p
    have h2 := hj₁ j hj
    by_contra hcon
    push Not at hcon
    have : (1 - (p : ℝ)) ^ (2 * d * K) * (δ / 2) ≤ (1 - (p : ℝ)) ^ (2 * d * K) * μ.real (fewLinked d k (k + j) K) :=
      mul_le_mul_of_nonneg_left hcon hq.le
    linarith
  have hU : μ.real {ω | (bdLinked k (k + j) ω).card < K} < δ := by
    have := prob_bdLinked_lt_le (d := d) hkn K p
    linarith
  -- square-root trick and symmetry, `ℓ' = 1`
  set g : HOct d := (Equiv.swap 0 a, fun j => τ (Equiv.swap 0 a j)) with hg
  have hpiece : orthantFace a τ (k + j) = piece g (k + j) := orthantFace_eq_piece a τ (k + j)
  have hsqrt := prob_le_card_linked_faceFin_ge (d := d) k (k + j) 1 p
  rw [mul_one, ← hK] at hsqrt
  have hsymm := prob_le_card_linked_piece_eq (d := d) g k (k + j) 1 p
  -- `1 - δ^{1/K} = 1 - η`
  have hroot : (μ.real {ω | (bdLinked k (k + j) ω).card < K}) ^ ((K : ℝ)⁻¹) < η := by
    have h0 : 0 ≤ μ.real {ω | (bdLinked k (k + j) ω).card < K} := measureReal_nonneg
    calc (μ.real {ω | (bdLinked k (k + j) ω).card < K}) ^ ((K : ℝ)⁻¹)
        < δ ^ ((K : ℝ)⁻¹) := Real.rpow_lt_rpow h0 hU (by positivity)
      _ = η := by
          rw [hδ, ← Real.rpow_natCast, ← Real.rpow_mul hη.le, mul_inv_cancel₀ (by positivity), Real.rpow_one]
  have hmono : μ.real {ω | 1 ≤ (linked (piece g (k + j)) k (k + j) ω).card} ≤
      μ.real (linkEvent (box d k) (orthantFace a τ (k + j)) (k + j)) := by
    rw [hpiece]
    exact measureReal_mono (fun ω hω => linkEvent_box_of_linked hω)
  linarith

end Percolation.Literature
