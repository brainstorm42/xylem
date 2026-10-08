import Percolation.Continuity.HullPort.TADefs
import Percolation.Util.Linter

/-!
# The conditioned slack hierarchy: slack forms, decoy lists, the conditioned covariance margin `cshMargin`, and the statement `CSHHolds`

Definitions (and their elementary linear algebra) for the family of covariance inequalities — the *conditioned slack
hierarchy*, CSH — from which the gluing inequalities of Kozma and Nitzan are derived in this development.  The hierarchy itself is
the theorem `CSH.cshHolds`; this file only sets up its statement `CSH.CSHHolds` and the companion statement (S5D) `CSH.surplusMargin`.
All objects below are introduced in this work; none is taken from the literature.

SETTING.  `V` is a finite vertex type; `w : Sym2 V → [0,1]` puts a weight on every unordered pair (a pair of weight `0` is an absent
edge; the diagonal pairs play no role); `prodBernoulli w` is the product Bernoulli measure on bond configurations `ω : Set (Sym2 V)`;
`openConn u v` is the event "`u` and `v` are joined by an open path", `openCluster ω u` the vertex set `C_u` of the open cluster of
`u`, `openEdgeCluster ω x` its set `𝒞_x` of open pairs; `{u ↮ A}` is written `{ω | ∀ a ∈ A, ¬ Reachable u a}`.  We write `P` for
`(prodBernoulli w).real` and `E[X; B]` for `∫_B X`.

THE LEVEL FORMS (`slStep`, `slForm`, `cshMarg`).  A list `L = [(d_1,c_1),…,(d_k,c_k)]` of *decoys* `d_j : V` with *decoy constants*
`c_j : V → ℝ` acts on a real function `f` on `V` by successive discounting: `sl^0[f] = f`,
`sl^j[f](u) = sl^{j-1}[f](u) − c_j(u) · sl^{j-1}[f](d_j)` — the `j`-th step removes from the value at every vertex the part
"explained by the decoy `d_j`" at the rate `c_j`.  With an *observer constant* `p` and two *observers* `o, v` the **margin** is
`Marg[f] = sl^k[f](o) − p · sl^k[f](v)` (`cshMarg L p o v f`).  The forms are linear in `f` (`slForm_add`, `slForm_smul`, `cshMarg_add`,
`cshMarg_smul`), and the form of a list is expressed through the form of the list without its first decoy (`slForm_cons`,
`cshMarg_cons`: `Marg_{(d_0,c_0)::L}[f] = Marg_L[f] − f(d_0) · Marg_L[c_0]`), which is what drives every induction on the decoys.

THE PERCOLATION CONSTANTS (`avoidConst`, `decoyList`, `obsConst`).  `avoidConst w d A u = P(d ↮ A, d ↔ u)/P(d ↮ A)` is the
probability that `u` lies in the cluster of the decoy `d` given that `d` avoids `A`; `decoyList w A [d_1,…,d_k]` is the list
`[(d_j, c_j)]` in which the `j`-th decoy is conditioned to avoid `A ∪ {d_1,…,d_{j-1}}`; `obsConst w o v A = P(o ↔ v, v ↮ A)/P(v ↮ A)`
is the probability that the first observer is joined to the second given that the second avoids `A`.  The constants are computed under
the unconditioned measure `P` (not under `P(· | x ↮ Y)`); this is what makes the induction on the number of decoys close up.

THE CSH MARGIN (`covD`, `cshMargin`, `CSHHolds`).  For an *owner* `x`, an *avoided set* `Y` and a real function `f` of sets of pairs,
`covD w x Y f u = P(D) · E[f(𝒞_x); D ∩ {x ↔ u}] − E[f(𝒞_x); D] · P(D ∩ {x ↔ u})` with `D = {x ↮ Y}` is the conditioned covariance
`Cov(f(𝒞_x), 1{u ∈ C_x} | x ↮ Y)` multiplied by `P(D)²`, i.e. written without denominators.  `cshMargin w x Y D o v f` is the margin
of `u ↦ covD w x Y f u` for the decoy list `decoyList w ({x} ∪ Y) D` and the observer constant `obsConst w o v ({x} ∪ Y ∪ D)`, and
`CSHHolds w x Y D o v` — the inequality CSH(Y; x; D; o, v) — says that `0 ≤ cshMargin w x Y D o v f` for every monotone `f`.  At level
`k = 0` it reads `Cov(f(𝒞_x), 1_o | x ↮ Y) ≥ p · Cov(f(𝒞_x), 1_v | x ↮ Y)`, `p = P(o ∈ C_v | v ↮ {x} ∪ Y)` (the correlation of `f`
with "the owner reaches `o`" is at least the part of its correlation with "the owner reaches `v`" that is transported from `v` to
`o`); at level `1`, `Cov(f,1_o) − c(o)Cov(f,1_d) ≥ p · [Cov(f,1_v) − c(v)Cov(f,1_d)]`; for `Y = ∅`, `k = 0`, `f = 1{v ∈ ·}` it is the
Harris inequality `P(o ↔ {x,v}, x ↔ v) ≥ P(o ↔ {x,v}) · P(x ↔ v)`.

THE SURPLUS WITH DECOYS (`surplus`, `surplusMargin`).  For a *relay set* `T : Finset V`, an injective *rank* `r` on `T` and an increasing
function `F` of vertex sets with means `m_a = E F(C_a)`, the *first-relay events* `P^u_a = {u ↔ a} ∩ ⋂_{a' ∈ T, r a' < r a} {u ↮ a'}`
partition `{u ↔ T}`, and `surplus w T r F u = E[F(C_u); u ↔ T] − Σ_{a ∈ T} P(P^u_a) · m_a` is the surplus of the observer `u` over its
first relay.  `surplusMargin w T r D o v F` is the margin of `u ↦ surplus w T r F u` for decoys `D` conditioned to avoid `T` (and the earlier
decoys) and the observer constant `obsConst w o v (T ∪ D)`; the statement (S5D)[T; D; o, v] is `0 ≤ surplusMargin w T r D o v F`.  With no
decoys (`surplusMargin_nil`, `surplusTransfer_of_surplusMargin_nil`) this is the **surplus transfer inequality**
(S5) `P(v ↮ T) · Sur_o(T) ≥ P(o ↔ v, v ↮ T) · Sur_v(T)`: the surplus seen from `o` is at least the surplus seen from `v`, discounted by
the probability that `o` is glued to `v` while `v` misses the relays.  Downstream, (S5D) follows from CSH by induction on `|T|`
(`CSH.surplusMargin_nonneg_of_csh`), and (S5) gives the first-relay bound (GEN) `E[F(C_o); o ↔ A] ≥ Σ_a P(P^o_a) m_a` and with it the
additive and multiplicative gluing inequalities (`AGloc.gen_firstRank_of_surplusTransfer`).  The labels (S5), (S5D), (GEN) are the ones
used for these statements throughout the development.

Inputs: none beyond the definitions `prodBernoulli`, `openConn`, `openCluster`, `openEdgeCluster`.  For orientation: functionals of the
cluster as in [cite: KozmaNitzan2024, Conj. 4 (p. 32)]; conditioned one-cluster covariances as in
[cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)].
-/

noncomputable section

namespace Percolation.Continuity

open MeasureTheory Set Percolation.Literature.LatticeModels Percolation.Literature
open scoped Classical

namespace CSH

variable {V : Type*}

/-! ### The level forms `sl^k[f]` and their linearity -/

/-- **One step of the level forms.** For a decoy `d` with decoy constant `c : V → ℝ` (packed as `dc = (d, c)`) and a real function
`f` on the vertices, `slStep dc f = (u ↦ f u − c u · f d)`: the value at every vertex is reduced by the part explained by the decoy,
at the rate `c`.  Introduced in this development (the building block of `slForm`). -/
def slStep (dc : V × (V → ℝ)) (f : V → ℝ) : V → ℝ := fun u => f u - dc.2 u * f dc.1

/-- **The level form `sl^k[f]`** of a decoy/constant list `L = [(d_1,c_1),…,(d_k,c_k)]`: `sl^0[f] = f` and
`sl^j[f](u) = sl^{j-1}[f](u) − c_j(u) · sl^{j-1}[f](d_j)` for `1 ≤ j ≤ k`, i.e. the left fold of `slStep` over `L` (`d_1` acts first).
Only the values of `f` at the decoys and at the point of evaluation matter.  Linear in `f` (`slForm_add`, `slForm_smul`); the key
identity is `slForm_cons`.  Introduced in this development. -/
def slForm (L : List (V × (V → ℝ))) (f : V → ℝ) : V → ℝ := L.foldl (fun g dc => slStep dc g) f

/-- **The margin of a decoy/constant list** `L`, an observer constant `p` and observers `o, v`:
`cshMarg L p o v f = sl^k[f](o) − p · sl^k[f](v)` — "value of the level form at `o` minus `p` times its value at `v`".  The CSH
statement and (S5D) both say that a margin of this shape is nonnegative (`cshMargin`, `surplusMargin`).  Linear in `f` (`cshMarg_add`,
`cshMarg_smul`); `cshMarg_cons` peels off the first decoy.  Introduced in this development. -/
def cshMarg (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f : V → ℝ) : ℝ := slForm L f o - p * slForm L f v

/-- With no decoys the level form is `f` itself: `slForm [] f = f`. -/
@[simp] theorem slForm_nil (f : V → ℝ) : slForm ([] : List (V × (V → ℝ))) f = f := rfl

/-- Unfolding the fold at the head: `slForm (dc :: L) f = slForm L (slStep dc f)` (the first decoy acts first). -/
@[simp] theorem slForm_cons_eq (dc : V × (V → ℝ)) (L : List (V × (V → ℝ))) (f : V → ℝ) :
    slForm (dc :: L) f = slForm L (slStep dc f) := rfl

/-- `slStep dc` is additive in `f`. -/
theorem slStep_add (dc : V × (V → ℝ)) (f g : V → ℝ) : slStep dc (f + g) = slStep dc f + slStep dc g := by
  funext u; simp only [slStep, Pi.add_apply]; ring

/-- `slStep dc` commutes with scalar multiplication. -/
theorem slStep_smul (dc : V × (V → ℝ)) (a : ℝ) (f : V → ℝ) : slStep dc (a • f) = a • slStep dc f := by
  funext u; simp only [slStep, Pi.smul_apply, smul_eq_mul]; ring

/-- The level form `sl^k` is additive in `f`. -/
theorem slForm_add (L : List (V × (V → ℝ))) (f g : V → ℝ) : slForm L (f + g) = slForm L f + slForm L g := by
  induction L generalizing f g with
  | nil => rfl
  | cons dc L ih => simp only [slForm_cons_eq, slStep_add, ih]

/-- The level form `sl^k` commutes with scalar multiplication. -/
theorem slForm_smul (L : List (V × (V → ℝ))) (a : ℝ) (f : V → ℝ) : slForm L (a • f) = a • slForm L f := by
  induction L generalizing f with
  | nil => rfl
  | cons dc L ih => simp only [slForm_cons_eq, slStep_smul, ih]

/-- The level form `sl^k` is compatible with subtraction. -/
theorem slForm_sub (L : List (V × (V → ℝ))) (f g : V → ℝ) : slForm L (f - g) = slForm L f - slForm L g := by
  rw [sub_eq_add_neg, slForm_add, ← neg_one_smul ℝ g, slForm_smul, neg_one_smul, ← sub_eq_add_neg]

/-- The level form of the zero function vanishes: `sl^k[0] = 0`. -/
theorem slForm_zero (L : List (V × (V → ℝ))) : slForm L (0 : V → ℝ) = 0 := by
  have h := slForm_smul L 0 (0 : V → ℝ)
  rwa [zero_smul, zero_smul] at h

/-- **Prepending a decoy.** The level form of the list `(d_0,c_0) :: L` is expressed through the forms of `L`:
`sl_{(d_0,c_0)::L}[f] = sl_L[f] − f(d_0) · sl_L[c_0]` — apply `sl_L` (linear) to `slStep (d_0,c_0) f = f − f(d_0) · c_0`.  This is the
only algebraic fact about the forms used in the inductions on the number of decoys. -/
theorem slForm_cons (d₀ : V) (c₀ : V → ℝ) (L : List (V × (V → ℝ))) (f : V → ℝ) :
    slForm ((d₀, c₀) :: L) f = slForm L f - f d₀ • slForm L c₀ := by
  have hstep : slStep (d₀, c₀) f = f - f d₀ • c₀ := by
    funext u; simp only [slStep, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [slForm_cons_eq, hstep, slForm_sub, slForm_smul]

/-- The margin `cshMarg L p o v` is additive in `f`. -/
theorem cshMarg_add (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f g : V → ℝ) :
    cshMarg L p o v (f + g) = cshMarg L p o v f + cshMarg L p o v g := by
  simp only [cshMarg, slForm_add, Pi.add_apply]; ring

/-- The margin `cshMarg L p o v` commutes with scalar multiplication. -/
theorem cshMarg_smul (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (a : ℝ) (f : V → ℝ) :
    cshMarg L p o v (a • f) = a * cshMarg L p o v f := by
  simp only [cshMarg, slForm_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- **Prepending a decoy, for margins**: `Marg_{(d_0,c_0)::L}[f] = Marg_L[f] − f(d_0) · Marg_L[c_0]`.  Read from right to left this
is the step of the peeling induction: a margin for the decoys `L` minus `f(d_0)` times the margin of the new constant `c_0` is the
margin for one decoy more. -/
theorem cshMarg_cons (d₀ : V) (c₀ : V → ℝ) (L : List (V × (V → ℝ))) (p : ℝ) (o v : V) (f : V → ℝ) :
    cshMarg ((d₀, c₀) :: L) p o v f = cshMarg L p o v f - f d₀ * cshMarg L p o v c₀ := by
  simp only [cshMarg, slForm_cons, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- With no decoys the margin is `f o − p · f v`. -/
@[simp] theorem cshMarg_nil (p : ℝ) (o v : V) (f : V → ℝ) :
    cshMarg ([] : List (V × (V → ℝ))) p o v f = f o - p * f v := rfl

/-! ### The percolation data -/

/-- **The decoy constant** `avoidConst w d A : V → ℝ`, `u ↦ P(d ↮ A, d ↔ u) / P(d ↮ A)`: the probability, under `prodBernoulli w`,
that `u` lies in the open cluster of the decoy `d` given that `d` is joined to no vertex of `A` (in the hierarchy `A` is the owner, the
avoided set and the earlier decoys; in (S5D) it is the relay set and the earlier decoys).  Real division: the value is `0` if
`P(d ↮ A) = 0`, which does not happen for weights `< 1` and `d ∉ A`.  Introduced in this development. -/
def avoidConst (w : Sym2 V → unitInterval) (d : V) (A : Set V) : V → ℝ := fun u =>
  (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ A, ¬ (openGraph ω).Reachable d a} ∩ openConn d u) /
    (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ A, ¬ (openGraph ω).Reachable d a}

/-- **The decoy/constant list** `decoyList w A [d_1,…,d_k] = [(d_1,c_1),…,(d_k,c_k)]` with
`c_j = avoidConst w d_j (A ∪ {d_1,…,d_{j-1}})`: the decoys in order, the `j`-th constant being the probability of lying in the
cluster of `d_j` given that `d_j` avoids `A` and the earlier decoys (the avoided set grows along the list).  This is the list fed to
`slForm`/`cshMarg` in `cshMargin` (with `A = {x} ∪ Y`) and in `surplusMargin` (with `A = T`).  Introduced in this development. -/
def decoyList (w : Sym2 V → unitInterval) : Set V → List V → List (V × (V → ℝ))
  | _, [] => []
  | A, d :: ds => (d, avoidConst w d A) :: decoyList w (insert d A) ds

/-- **The observer constant** `obsConst w o v A = P(o ↔ v, v ↮ A) / P(v ↮ A)`: the probability that the first observer `o` lies in
the open cluster of the second observer `v` given that `v` is joined to no vertex of `A` (in the hierarchy `A` = owner ∪ avoided set ∪
all decoys; in (S5D) `A` = relay set ∪ all decoys).  It is the price `p` at which the margin transports the value at `v` to `o`; it is
computed under the unconditioned measure.  Real division (`0` if `P(v ↮ A) = 0`).  Introduced in this development. -/
def obsConst (w : Sym2 V → unitInterval) (o v : V) (A : Set V) : ℝ :=
  (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ A, ¬ (openGraph ω).Reachable v a} ∩ openConn o v) /
    (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ A, ¬ (openGraph ω).Reachable v a}

/-- **The conditioned covariance function, denominator-free.** For an owner `x`, an avoided set `Y`, a real function `f` of sets
of pairs and a vertex `u`, with `D = {x ↮ Y}`:
`covD w x Y f u = P(D) · E[f(𝒞_x); D ∩ {x ↔ u}] − E[f(𝒞_x); D] · P(D ∩ {x ↔ u})`, where `𝒞_x = openEdgeCluster ω x` is the open
edge cluster of the owner.  When `P(D) > 0` this equals `P(D)² · Cov(f(𝒞_x), 1{u ∈ C_x} | x ↮ Y)`, the covariance, given that the
owner avoids `Y`, between the functional and the event that the owner's cluster reaches `u`; the polynomial form avoids all
divisions and has the same sign.  This is the function `u ↦ κ_f(u)` to which the level forms are applied in `cshMargin`; the same
bracket appears in the level-zero transfer inequality `CovTau.markerDominanceAvoid`.  Introduced in this development; the
conditioning on a one-cluster avoidance event follows [cite: VandenbergHaggstromKahn2005, Thm. 1.3 (p. 6)]. -/
def covD (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (f : Set (Sym2 V) → ℝ) (u : V) : ℝ :=
  (prodBernoulli w).real {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} *
      (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} ∩ openConn x u,
        f (openEdgeCluster ω x) ∂(prodBernoulli w)) -
    (∫ ω in {ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y}, f (openEdgeCluster ω x) ∂(prodBernoulli w)) *
      (prodBernoulli w).real ({ω : BondConfig V | ∀ y ∈ Y, ¬ (openGraph ω).Reachable x y} ∩ openConn x u)

/-- **The CSH margin** of the datum (owner `x`, avoided set `Y`, decoys `D = [d_1,…,d_k]`, observers `o, v`) at the functional `f`:
the margin `sl^k[κ](o) − p · sl^k[κ](v)` of the conditioned covariance function `κ = covD w x Y f` (so `κ(u) ∝ Cov(f(𝒞_x), 1{u ∈ C_x} | x ↮ Y)`),
for the decoy list `decoyList w ({x} ∪ Y) D` — the `j`-th decoy discounted at the rate `c_j(u) = P(u ∈ C_{d_j} | d_j ↮ {x} ∪ Y ∪ {d_1,…,d_{j-1}})` —
and the observer constant `p = obsConst w o v ({x} ∪ Y ∪ D) = P(o ∈ C_v | v ↮ {x} ∪ Y ∪ D)`.  With no decoys it is
`κ(o) − p · κ(v)`; with one decoy `d`, `κ(o) − c(o)κ(d) − p · [κ(v) − c(v)κ(d)]`.  Introduced in this development. -/
def cshMargin (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (D : List V) (o v : V) (f : Set (Sym2 V) → ℝ) : ℝ :=
  cshMarg (decoyList w (insert x Y) D) (obsConst w o v (insert x Y ∪ {d | d ∈ D})) o v (covD w x Y f)

/-- **The conditioned slack hierarchy statement CSH(Y; x; D; o, v).**  `CSHHolds w x Y D o v` says: for every monotone real
function `f` of sets of pairs (applied to the open edge cluster `𝒞_x` of the owner `x`), the CSH margin is nonnegative,
`0 ≤ cshMargin w x Y D o v f`.  Unfolded at level `k = 0` (no decoys): `Cov(f(𝒞_x), 1{o ∈ C_x} | x ↮ Y) ≥ P(o ∈ C_v | v ↮ {x} ∪ Y) ·
Cov(f(𝒞_x), 1{v ∈ C_x} | x ↮ Y)` — given that the owner avoids `Y`, the correlation of `f` with "the owner's cluster reaches `o`" is
at least the part of its correlation with "the owner's cluster reaches `v`" that is transported from `v` to `o`, priced by the
unconditioned constant `p`; for `Y = ∅` and `f = 1{v ∈ ·}` this is the Harris inequality
`P(o ↔ {x,v}, x ↔ v) ≥ P(o ↔ {x,v}) · P(x ↔ v)`.  At level `k ≥ 1` the decoys are discounted successively from both sides, each
through the previous ones.  For fixed data the margin is a linear functional of `f` vanishing on constants, so the statement is a finite
family of polynomial inequalities in the weights (one per up-set).  THE NEW OBJECT of this development: `CSH.cshHolds` proves it for
all weights in `(0,1)` and all data with pairwise distinct named vertices outside `Y`, and the gluing inequalities of Kozma and Nitzan
are derived from it.  No published source; the inputs enter only in the proof (`CSH.cshHolds`). -/
def CSHHolds (w : Sym2 V → unitInterval) (x : V) (Y : Set V) (D : List V) (o v : V) : Prop :=
  ∀ f : Set (Sym2 V) → ℝ, Monotone f → 0 ≤ cshMargin w x Y D o v f

/-- **The surplus of an observer over its first relay.** For a relay set `T`, a rank `r : V → ℕ` (meant to be injective on `T`
and compatible with `F`: smaller rank, smaller mean `m_a = E F(C_a)`), an increasing function `F` of vertex sets and a vertex `u`:
`surplus w T r F u = E[F(C_u); u ↔ T] − Σ_{a ∈ T} P(P^u_a) · m_a`, where `P^u_a = {u ↔ a} ∩ ⋂_{a' ∈ T, r a' < r a} {u ↮ a'}` is the
event that `a` is the *first relay* of `u` (the relay of least rank in `C_u`); these events partition `{u ↔ T}`, so
`Sur_u(T) = E[(F(C_u) − m_{ι(u)}) ; u ↔ T]` with `ι(u)` the first relay.  For a single relay, `Sur_u({x}) = Cov(F(C_x), 1{u ∈ C_x})`.
The first-relay bound (GEN) is the statement `Sur_o(A) ≥ 0`; this expression is, term for term, the one in the hypothesis of
`AGloc.gen_firstRank_of_surplusTransfer`.  Introduced in this development; increasing functions of the cluster as the class of
functionals follow [cite: KozmaNitzan2024, Conj. 4 (p. 32)]. -/
def surplus (w : Sym2 V → unitInterval) (T : Finset V) (r : V → ℕ) (F : Set V → ℝ) (u : V) : ℝ :=
  (∫ ω in (⋃ a ∈ T, openConn u a), F (openCluster ω u) ∂(prodBernoulli w)) -
    ∑ a ∈ T, (prodBernoulli w).real
        (openConn u a ∩ ⋂ a' ∈ T.filter (fun a' => r a' < r a), (openConn u a')ᶜ : Set (BondConfig V)) *
      ∫ ω, F (openCluster ω a) ∂(prodBernoulli w)

/-- **The surplus-transfer margin with decoys, (S5D)[T; D; o, v].**  `surplusMargin w T r D o v F` is the margin
`sl^k[Sur](o) − p · sl^k[Sur](v)` of the surplus function `u ↦ surplus w T r F u`, for the decoy list `decoyList w T D` (the `j`-th
decoy conditioned to avoid `T ∪ {d_1,…,d_{j-1}}`) and the observer constant `p = obsConst w o v (T ∪ D) = P(o ∈ C_v | v ↮ T ∪ D)`.
The statement (S5D) is `0 ≤ surplusMargin w T r D o v F`; for `D = []` it is the surplus transfer inequality (S5)
`P(v ↮ T) · Sur_o(T) ≥ P(o ↔ v, v ↮ T) · Sur_v(T)` (`surplusMargin_nil`, `surplusTransfer_of_surplusMargin_nil`), and for a single relay `T = {x}` it is
the CSH statement with owner `x`, empty avoided set and the functional `F(V(·) ∪ {x})`.  The version with decoys is what the induction
on `|T|` needs: peeling the relay of largest rank turns it into a new first decoy (`CSH.surplusMargin_nonneg_of_csh`).  Introduced in
this development (the name records the label (S5) of the surplus transfer inequality, with D for decoys). -/
def surplusMargin (w : Sym2 V → unitInterval) (T : Finset V) (r : V → ℕ) (D : List V) (o v : V) (F : Set V → ℝ) : ℝ :=
  cshMarg (decoyList w ↑T D) (obsConst w o v (↑T ∪ {d | d ∈ D})) o v (surplus w T r F)

/-- **(S5D) with no decoys is (S5) divided by `P(v ↮ T)`**: `surplusMargin w T r [] o v F = Sur_o(T) − p · Sur_v(T)` with
`p = P(o ↔ v, v ↮ T) / P(v ↮ T)`. -/
theorem surplusMargin_nil (w : Sym2 V → unitInterval) (T : Finset V) (r : V → ℕ) (o v : V) (F : Set V → ℝ) :
    surplusMargin w T r [] o v F =
      surplus w T r F o -
        (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) /
            (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a} *
          surplus w T r F v := by
  simp only [surplusMargin, decoyList, cshMarg_nil, obsConst, List.not_mem_nil, setOf_false, union_empty]

/-- **The surplus transfer inequality (S5) from the decoy-free margin.** If `P(v ↮ T) > 0` and `0 ≤ surplusMargin w T r [] o v F`,
then `P(v ↮ T, o ↔ v) · Sur_v(T) ≤ P(v ↮ T) · Sur_o(T)` — the surplus seen from `o` is at least the surplus seen from `v` discounted by
the probability that `o` is glued to `v` while `v` misses the relays.  This product form (no division) is the hypothesis shape of
`AGloc.gen_firstRank_of_surplusTransfer`, which derives the first-relay bound (GEN) from (S5) by induction on the number of relays. -/
theorem surplusTransfer_of_surplusMargin_nil (w : Sym2 V → unitInterval) (T : Finset V) (r : V → ℕ) (o v : V) (F : Set V → ℝ)
    (hpos : 0 < (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a})
    (h : 0 ≤ surplusMargin w T r [] o v F) :
    (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v) *
        surplus w T r F v ≤
      (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a} * surplus w T r F o := by
  rw [surplusMargin_nil] at h
  set M := (prodBernoulli w).real {ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a} with hM
  set E := (prodBernoulli w).real ({ω : BondConfig V | ∀ a ∈ (↑T : Set V), ¬ (openGraph ω).Reachable v a} ∩ openConn o v)
    with hE
  have h2 : 0 ≤ M * (surplus w T r F o - E / M * surplus w T r F v) := mul_nonneg hpos.le h
  have h3 : M * (surplus w T r F o - E / M * surplus w T r F v) = M * surplus w T r F o - E * surplus w T r F v := by
    field_simp
  linarith [h2, h3]

end CSH

end Percolation.Continuity
