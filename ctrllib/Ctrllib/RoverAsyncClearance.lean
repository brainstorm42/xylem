/-
Asynchronous two-rover clearance certificates.

The two delivered samples may be acquired at different timestamps.  Their
errors are transported independently to a common query time in one declared
Euclidean frame.  These theorems are generic metric-space bookkeeping; they
do not establish estimator, controller, plant, or hardware correspondence.
-/
import Ctrllib.RoverSampledClearance

/-! # Asynchronous two-rover clearance

Independent sample timestamps are transported to one common query time before
the existing all-pairs and body-cover clearance interfaces are applied. -/

namespace Ctrllib

/-! The point and family interfaces retain all-pair semantics.  The body
interface adds explicit target-time covers, so a finite sample family is not
silently treated as a whole-body certificate. -/

/--
Independent delivery times and ages give a two-point target-time clearance
bound. `pDelivered` estimates `p tauP`, and `qDelivered` estimates `q tauQ`, while
`t` is the common query time.  All three times are required to lie in the
admissible set `S`. Nonnegative budgets are retained for interpretation;
physical units and actual delivery availability remain application premises.
-/
theorem rover_async_clearance_lower_bound
    {S : Set ℝ}
    {p q : ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered qDelivered : EuclideanSpace ℝ (Fin 3)}
    {Lp Lq : NNReal} {epsP epsQ delta hP hQ t tauP tauQ : ℝ}
    (hp : LipschitzOnWith Lp p S)
    (hq : LipschitzOnWith Lq q S)
    (htauP : tauP ∈ S) (htauQ : tauQ ∈ S) (htarget : t ∈ S)
    (hpDelivered : dist pDelivered (p tauP) ≤ epsP)
    (hqDelivered : dist qDelivered (q tauQ) ≤ epsQ)
    (_hP_nonneg : 0 ≤ hP) (_hQ_nonneg : 0 ≤ hQ)
    (_hEpsP : 0 ≤ epsP) (_hEpsQ : 0 ≤ epsQ)
    (htP : |t - tauP| ≤ hP) (htQ : |t - tauQ| ≤ hQ)
    (hsep : delta ≤ dist pDelivered qDelivered) :
    delta - epsP - epsQ - (Lp : ℝ) * hP - (Lq : ℝ) * hQ ≤
      dist (p t) (q t) := by
  have hpTarget' : dist pDelivered (p t) ≤ epsP + (Lp : ℝ) * hP :=
    dist_delivered_to_target_on_le hp htauP htarget hpDelivered htP
  have hqTarget' : dist qDelivered (q t) ≤ epsQ + (Lq : ℝ) * hQ :=
    dist_delivered_to_target_on_le hq htauQ htarget hqDelivered htQ
  have hpTarget : dist (p t) pDelivered ≤ epsP + (Lp : ℝ) * hP := by
    simpa [dist_comm] using hpTarget'
  have hqTarget : dist (q t) qDelivered ≤ epsQ + (Lq : ℝ) * hQ := by
    simpa [dist_comm] using hqTarget'
  have heroded := dist_actual_ge_dist_nominal_sub
    pDelivered (p t) qDelivered (q t) hpTarget hqTarget
  linarith

/-- Uniform all-pairs asynchronous clearance for two indexed point families. -/
theorem rover_family_async_clearance_lower_bound
    {I J : Type*} {S : Set ℝ}
    {p : I → ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : J → ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered : I → EuclideanSpace ℝ (Fin 3)}
    {qDelivered : J → EuclideanSpace ℝ (Fin 3)}
    {Lp Lq : NNReal} {epsP epsQ delta hP hQ t tauP tauQ : ℝ}
    (hp : ∀ i, LipschitzOnWith Lp (p i) S)
    (hq : ∀ j, LipschitzOnWith Lq (q j) S)
    (htauP : tauP ∈ S) (htauQ : tauQ ∈ S) (htarget : t ∈ S)
    (hpDelivered : ∀ i, dist (pDelivered i) (p i tauP) ≤ epsP)
    (hqDelivered : ∀ j, dist (qDelivered j) (q j tauQ) ≤ epsQ)
    (hP_nonneg : 0 ≤ hP) (hQ_nonneg : 0 ≤ hQ)
    (hEpsP : 0 ≤ epsP) (hEpsQ : 0 ≤ epsQ)
    (htP : |t - tauP| ≤ hP) (htQ : |t - tauQ| ≤ hQ)
    (hsep : ∀ i j, delta ≤ dist (pDelivered i) (qDelivered j)) :
    ∀ i j, delta - epsP - epsQ - (Lp : ℝ) * hP - (Lq : ℝ) * hQ ≤
      dist (p i t) (q j t) := by
  intro i j
  exact rover_async_clearance_lower_bound
    (hp i) (hq j) htauP htauQ htarget (hpDelivered i) (hqDelivered j)
    hP_nonneg hQ_nonneg hEpsP hEpsQ htP htQ (hsep i j)

/--
Asynchronous delivered point separation transfers to whole-body clearance.
The cover hypotheses are at the common target time `t`, with independent
cover radii `rhoP` and `rhoQ`; `Bp` and `Bq` are arbitrary subsets of the
same Euclidean frame.
-/
theorem rover_body_async_clearance
    {I J : Type*} {S : Set ℝ}
    {p : I → ℝ → EuclideanSpace ℝ (Fin 3)}
    {q : J → ℝ → EuclideanSpace ℝ (Fin 3)}
    {pDelivered : I → EuclideanSpace ℝ (Fin 3)}
    {qDelivered : J → EuclideanSpace ℝ (Fin 3)}
    {Bp Bq : Set (EuclideanSpace ℝ (Fin 3))}
    {Lp Lq : NNReal} {epsP epsQ delta hP hQ t tauP tauQ rhoP rhoQ : ℝ}
    (hp : ∀ i, LipschitzOnWith Lp (p i) S)
    (hq : ∀ j, LipschitzOnWith Lq (q j) S)
    (htauP : tauP ∈ S) (htauQ : tauQ ∈ S) (htarget : t ∈ S)
    (hpDelivered : ∀ i, dist (pDelivered i) (p i tauP) ≤ epsP)
    (hqDelivered : ∀ j, dist (qDelivered j) (q j tauQ) ≤ epsQ)
    (hP_nonneg : 0 ≤ hP) (hQ_nonneg : 0 ≤ hQ)
    (hEpsP : 0 ≤ epsP) (hEpsQ : 0 ≤ epsQ)
    (_hRhoP : 0 ≤ rhoP) (_hRhoQ : 0 ≤ rhoQ)
    (htP : |t - tauP| ≤ hP) (htQ : |t - tauQ| ≤ hQ)
    (hsep : ∀ i j, delta ≤ dist (pDelivered i) (qDelivered j))
    (hpCover : ∀ x ∈ Bp, ∃ i, dist x (p i t) ≤ rhoP)
    (hqCover : ∀ y ∈ Bq, ∃ j, dist y (q j t) ≤ rhoQ) :
    ∀ x ∈ Bp, ∀ y ∈ Bq,
      delta - epsP - epsQ - (Lp : ℝ) * hP - (Lq : ℝ) * hQ - rhoP - rhoQ ≤
        dist x y := by
  apply rover_body_clearance_of_sample_cover hpCover hqCover
  exact rover_family_async_clearance_lower_bound
    hp hq htauP htauQ htarget hpDelivered hqDelivered
    hP_nonneg hQ_nonneg hEpsP hEpsQ htP htQ hsep

end Ctrllib

#print axioms Ctrllib.rover_async_clearance_lower_bound
#print axioms Ctrllib.rover_family_async_clearance_lower_bound
#print axioms Ctrllib.rover_body_async_clearance
