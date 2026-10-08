---
type: lean-module
module: Ctrllib.PointMassComFlow
title: Damped point-mass convergence and its inverse-mass dependency
status: e2e-source-explanation
sources: []
---

# Why the convergence proof uses an inverse-mass lemma

The [source](../../../../ctrllib/Ctrllib/PointMassComFlow.lean) studies an ideal damped point mass in three-dimensional Euclidean space. Position is `x`, velocity is `v`, and the state is ordered `z = (v, x)`. With `m > 0`, `d > 0`, and `k > 0`, the equations are

```text
m v' + d v + k x = 0,    x' = v.
```

Thus the linear field is `f(v,x) = (-(d/m) v - (k/m) x, v)`. The source constructs the global flow directly from the operator exponential: `Φ(t,z₀) = exp(t A) z₀`, where `A` is that block linear operator. It proves the flow identities and the ODE derivative identity; it does not assume a general nonlinear ODE-to-flow bridge.

## Exact captured convergence goal

`Ctrllib.pointMass_tendsto_zero` retains all seven binders:

```lean
(m d k : ℝ) (hm : 0 < m) (hd : 0 < d) (hk : 0 < k)
(z₀ : PointMassState) :
Tendsto (fun t : ℝ => pointMassFlow m d k hm t z₀) atTop (𝓝 0)
```

For every initial state, the entire state `(v,x)` tends to zero as time tends to positive infinity. This statement is in source lines 344–368 and the [compact capture](../graph/declarations.json). It is a result for this ideal mathematical model, not validation of a physical robot or a controller design.

## Energy and proof strategy

The mechanical energy is

```text
V(v,x) = (m/2) ‖v‖² + (k/2) ‖x‖².
```

Positive mass and stiffness make this energy coercive. Energy decrease bounds the forward trajectory and supplies forward precompactness in the finite dimensional state space. The convergence proof then applies the existing general theorem `Ctrllib.com_attractive` from [ComLaSalle](../../../../ctrllib/Ctrllib/ComLaSalle.lean), with scalar operators `M = m I`, `D = d I`, `K = k I`, and `Minv = m⁻¹ I`. The source discharges self-adjointness, the inverse identity, and the relevant nonnegative/positive operator conditions. It reuses that convergence theorem; this page does not introduce a new LaSalle proof or decompose the whole theorem.

## The useful dependency path

The recorded proof-use path is

```text
Ctrllib.pointMass_tendsto_zero → Ctrllib.pmM_inv
```

`pmM_inv`, source lines 269–271, establishes

```lean
(hm : 0 < m) (w : PointMassCoord) : pmM m (pmMinv m w) = w
```

Here `pmM m = m I` and `pmMinv m = m⁻¹ I`. The proof uses `hm.ne'` to cancel `m · m⁻¹`. The convergence proof explicitly passes this identity to the general operator result. That explains why the dependency matters: it discharges the inverse-mass obligation, rather than merely naming another theorem in the same module.

Start with the exact statement, a [bounded proof context and this path](../README.md), then inspect the source. The full depth-one dependency list remains available for audit.

## Evidence boundary

The fixture contains only five selected local declaration records. Its dependency state is `partial`; the expected 14-module omission warning is not proof that its inputs changed. Rebuilding an unchanged compact capture cannot add its omitted records. Full coverage requires the [full regeneration procedure](../REGENERATE-FULL.md).

The `PAIRED_WITH` edge from this page is a source-to-explanation navigation relationship. The edge supports authored navigation; formal correspondence requires separate evidence.

