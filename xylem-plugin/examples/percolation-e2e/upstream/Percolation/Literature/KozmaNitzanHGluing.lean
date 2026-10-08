import Percolation.Literature.KozmaNitzanHittable
import Percolation.Util.Linter

/-!
# Kozma–Nitzan, Theorem 6 under H-reliability: the gluing hypothesis the printed proof uses

Proofs-and-definitions companion of
`KozmaNitzanReduction.lean` / `KozmaNitzanTargetLemma.lean` (G. Kozma, S. Nitzan, *A reduction of
the `θ(p_c) = 0` problem to a conjectured inequality*, arXiv:2401.12397, §4).

Conjecture 3 (p. 15) asks, for a source `0`, relays `A` and a target `b`, that `P(0 ↔ A) > 1 - δ`
and `P(a ↔ b) > 1 - δ` for all `a ∈ A` force `P(0 ↔ b) > 1 - ε`. The printed proof of Theorem 6
(Conjecture 3 ⇒ `θ(p_c) = 0`, pp. 15–31) invokes Conjecture 3 at exactly one place, Step V of the
proof of Lemma 10 (p. 22), in the auxiliary graph `K_ξ`, with the source `o` lying OUTSIDE the
lattice subbox `D` (Lemma 10, p. 17: "for every vertex `o ∈ G \ D`") that contains the relay set
`A_ξ ⊆ S`, the target `T` and — by the definitions of a target (p. 16: `v + l(v)Q(v) ⊆ D`) and of
the scale `m` in (16) (p. 17) — every open path certifying in (22)–(24) that the relays are reliable
to the target.

## References

* G. Kozma, S. Nitzan, arXiv:2401.12397 (2024): Conjecture 3 and Theorem 6 (p. 15), Lemma 10 and
  its proof (pp. 17–22, esp. (16), (22)–(26) and Step V), Question 9 (p. 36, the graph `H`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Percolation.Literature

open LatticeModels SimpleGraph

namespace KozmaNitzan

variable {V W : Type*}

/-! ## The target property: the conclusion of Lemma 10 as the interface to the rest of §4 -/

variable {d : ℕ}

/-- **The target property at parameter `p`** — the conclusion of Kozma–Nitzan's Lemma 10 (p. 17) for
 the lattice weighting of `ℤ^d` at `p`: for every `ε > 0` there is `δ > 0` such that for every
 finite of hittable geometries there is `R` with: for every finitely supported weighting
 `W` with a lattice subbox `D ⊇ B⟨R⟩` at parameter `p`, every nonempty target `T ⊆ D` w.r.t. `(B, D,
 R, H)` and every source `o ∉ D`, `P_W(o ↔ B) > 1 - δ ⟹ P_W(o ↔ T) > 1 - ε`. [cite: KozmaNitzan2024,
 §4 Lemma 10 (p. 17)]
-/
def TargetProperty (d : ℕ) (p : unitInterval) : Prop :=
  ∀ ⦃ε : ℝ⦄, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ H : List (Geom d), (∀ g ∈ H, IsHittable p g) → ∃ R : ℕ,
      ∀ (W : Sym2 (Site d) → unitInterval) (Sfin D : Finset (Site d)) (lo hi : Site d)
        (T : Finset (Site d)) (o : Site d),
        FinSupp W Sfin → IsSubbox W p D → D ⊆ Sfin → o ∈ Sfin → o ∉ D →
        Finset.Icc (lo - (R : Site d)) (hi + (R : Site d)) ⊆ D →
        IsTarget T lo hi D R H → T ⊆ D → T.Nonempty →
        1 - δ < (prodBernoulli W).real (⋃ b ∈ Finset.Icc lo hi, openConn o b) →
          1 - ε < (prodBernoulli W).real (⋃ t ∈ T, openConn o t)

/-- **Lemma 10 from Conjecture 3**, as the target property. [cite: KozmaNitzan2024, §4 Lemma 10 (pp. 17–22)] -/
theorem targetProperty_of_conjecture3 [NeZero d] (hC : KozmaNitzan2024_conjecture3) (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hθ : 0 < theta (zdGraph d) 0 p) : TargetProperty d p :=
  fun _ hε => targetLemma hC p hp0 hp1 hθ hε

end KozmaNitzan

end Percolation.Literature

end
