import Mathlib.Probability.Independence.InfinitePi
import Percolation.Literature.Basic
import Percolation.Literature.PercolationProofs

/-!
# Monotonicity of `θ` and `p_c` under passage to (induced) subgraphs

Statements from the literature (defs of type `Prop`, proved below)
recording the elementary coupling monotonicity of bond percolation in the underlying graph, as
printed in Grimmett, *Percolation*, 2nd ed. (1999):

* p. 13, before (1.9): "the origin of `𝕃^{d+1}` belongs to an infinite open cluster for a particular
  value of `p` whenever it belongs to an infinite open cluster of the sublattice `𝕃^d`. Thus
  `θ(p) = θ_d(p)` is non-decreasing in `d`, which implies (1.9) `p_c(d+1) ≤ p_c(d)`."
* §7.1, p. 146, after (7.1): "For any connected graph `G`, we write `p_c(G)` for the critical
  probability of bond percolation on `G` … Since `S_k ⊆ S_{k+1} ⊆ ℤ^d` for all `k`, we have that
  `p_c(S_k) ≥ p_c(S_{k+1}) ≥ p_c`."
* §7.2, p. 148: "`p_c(A)` denotes the critical value of bond percolation on the subgraph of `ℤ^d`
  induced by the vertex set `A`. In this notation, `p_c = p_c(ℤ^d)`."

In this library's vocabulary (`Percolation.Literature.theta`,
`Percolation.Literature.criticalProb`, Mathlib's `SimpleGraph.induce`): for `S ⊆ T ⊆ V`
and `x ∈ S`, `θ_{G[S]}(x, p) ≤ θ_{G[T]}(x, p) ≤ θ_G(x, p)` and hence `p_c(G) ≤ p_c(G[T]) ≤
p_c(G[S])`. The `θ`-inequalities are vendored as facts (`theta_induce_le`, `theta_induce_mono`; the
proof is the obvious coupling: restrict the configuration to the edges of the subgraph); the
`p_c`-inequalities are *derived* here from them.

Use: these are the "`p_c(ℤ³) ≤ p_c(S_k)`" / "`p_c(ℍ) ≥ p_c`" steps needed to specialise slab and
half-space facts stated at the subgraph's own critical point (Duminil-Copin–Sidoravicius–Tassion
2016, Thm 1; Barsky–Grimmett–Newman 1991) to the critical point of the ambient lattice.

Proofs: `theta_induce_le_holds`, `theta_induce_mono_holds`, via the general
coupling `theta_comap_le` — for an injective `f : W → V`, restricting a configuration `ω` on `V` to
the configuration `{e | e.map f ∈ ω}` on `W` pushes `P_p^G` forward to `P_p^{G.comap f}`
(`bondPercolation_map_comap`, from Mathlib's marginalisation lemma
`Measure.map_infinitePi_infinitePi_of_inj`) and maps infinite open clusters of `x` injectively into
the open cluster of `f x`; measurability of `{|C(x)| = ∞}` is `measurableSet_percolatesAt_holds`
(`PercolationProofs.lean`).

## References

* G. Grimmett, *Percolation*, 2nd ed., Grundlehren 321, Springer 1999: §1.4 p. 13 (1.9);
  §7.1 p. 146 (7.1); §7.2 p. 148.
-/

namespace Percolation.Literature

open MeasureTheory

variable {V : Type*}

/-- (Grimmett 1999, §1.4 p. 13 before (1.9), and §7.1 p. 146: "Since `S_k ⊆ S_{k+1} ⊆ ℤ^d` … we have
`p_c(S_k) ≥ p_c(S_{k+1}) ≥ p_c`", via "belongs to an infinite open cluster … whenever it belongs to
an infinite open cluster of the sublattice".) Percolation on an induced subgraph is dominated by
percolation on the whole graph: for `x ∈ S`, `θ_{G[S]}(x, p) ≤ θ_G(x, p)`.
[cite: GrimmettPercolation1999, §1.4 (1.9) p. 13; §7.1 (7.1) p. 146] -/
def theta_induce_le : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) (S : Set V) (x : V) (hx : x ∈ S)
    (p : unitInterval), theta (G.induce S) ⟨x, hx⟩ p ≤ theta G x p

/-- (Grimmett 1999, §7.1 p. 146: "Since `S_k ⊆ S_{k+1} ⊆ ℤ^d` for all `k`, we have that
`p_c(S_k) ≥ p_c(S_{k+1}) ≥ p_c`"; §1.4 p. 13: "`θ_d(p)` is non-decreasing in `d`".) `θ` is monotone
in the vertex set of an induced subgraph: for `x ∈ S ⊆ T`, `θ_{G[S]}(x, p) ≤ θ_{G[T]}(x, p)`.
[cite: GrimmettPercolation1999, §7.1 (7.1) p. 146; §1.4 p. 13] -/
def theta_induce_mono : Prop :=
  ∀ [Countable V] (G : SimpleGraph V) {S T : Set V} (hST : S ⊆ T) (x : V) (hx : x ∈ S)
    (p : unitInterval), theta (G.induce S) ⟨x, hx⟩ p ≤ theta (G.induce T) ⟨x, hST hx⟩ p

/-! ### Proofs: the restriction coupling (Grimmett 1999, §1.4 p. 13) -/

section Coupling

open ProbabilityTheory unitInterval

/-- The restriction of a configuration along `f : W → V`: the edge `e` of `W` is open iff its
image `e.map f` is open. For `f = Subtype.val` this restricts `ω` to the edges inside a vertex
subset (Grimmett 1999, §1.4 p. 13: the sublattice coupling). [cite: GrimmettPercolation1999, §1.4 p. 13] -/
def restrictConfig {W : Type*} (f : W → V) (ω : BondConfig V) : BondConfig W :=
  {e | e.map f ∈ ω}

/-- Membership in the restricted configuration. [folklore] -/
@[simp] theorem mem_restrictConfig {W : Type*} (f : W → V) (ω : BondConfig V) (e : Sym2 W) :
    e ∈ restrictConfig f ω ↔ e.map f ∈ ω := Iff.rfl

/-- `restrictConfig f` is measurable for the product σ-algebras. [folklore] -/
theorem measurable_restrictConfig {W : Type*} (f : W → V) :
    Measurable (restrictConfig (V := V) f) :=
  measurable_set_iff.2 fun e => measurable_set_mem (e.map f)

/-- **The restriction coupling has the right law**: for injective `f`, the image of `P_p^G` under
`restrictConfig f` is `P_p^{G.comap f}` — the states of the edges `s(f a, f b)`,
`G.Adj (f a) (f b)`, are i.i.d. Bernoulli(`p`) and the other pairs are a.s. closed. (Grimmett 1999, §1.4 p. 13, "the
origin of `𝕃^{d+1}` belongs to an infinite open cluster for a particular value of `p` whenever it
belongs to an infinite open cluster of the sublattice `𝕃^d`" — the coupling behind (1.9).)
[cite: GrimmettPercolation1999, §1.4 p. 13 (1.9)] -/
theorem bondPercolation_map_comap {W : Type*} (G : SimpleGraph V) {f : W → V}
    (hf : Function.Injective f) (p : unitInterval) :
    (bondPercolation G p).map (restrictConfig f) = bondPercolation (G.comap f) p := by
  have hSV : Measurable fun q : Sym2 V → Prop => {i | q i} := measurable_setOf
  have hSW : Measurable fun q : Sym2 W → Prop => {i | q i} := measurable_setOf
  rw [bondPercolation, bondPercolation, setBernoulli_eq_map, setBernoulli_eq_map,
    Measure.map_map (measurable_restrictConfig f) hSV]
  have hcomp : (restrictConfig f ∘ fun q : Sym2 V → Prop => {i | q i}) =
      (fun q : Sym2 W → Prop => {i | q i}) ∘
        fun (q : Sym2 V → Prop) (i : Sym2 W) => q (Sym2.map f i) := rfl
  rw [hcomp, ← Measure.map_map hSW (by fun_prop),
    Measure.map_infinitePi_infinitePi_of_inj (Sym2.map.injective hf)]
  congr 2 with e
  induction e using Sym2.ind with
  | h a b =>
    have : (Sym2.map f s(a, b) ∈ G.edgeSet) = (s(a, b) ∈ (G.comap f).edgeSet) := by
      simp [Sym2.map_mk]
    rw [this]

/-- Open paths of the restricted configuration map to open paths: `restrictConfig f ω`-reachability
of `x, y` gives `ω`-reachability of `f x, f y` (for injective `f`). [folklore] -/
theorem reachable_map_of_restrictConfig {W : Type*} {f : W → V} (hf : Function.Injective f)
    (ω : BondConfig V) {x y : W} (h : (openGraph (restrictConfig f ω)).Reachable x y) :
    (openGraph ω).Reachable (f x) (f y) := by
  let φ : openGraph (restrictConfig f ω) →g openGraph ω :=
    { toFun := f
      map_rel' := fun {a b} hab => by
        rw [openGraph_adj] at hab ⊢
        exact ⟨by simpa [Sym2.map_mk] using hab.1, hf.ne hab.2⟩ }
  exact h.map φ

/-- **`θ` of a subgraph, computed on the ambient space**: for injective `f : W → V`,
`θ_{G.comap f}(x, p) = P_p^G(|C(x)| = ∞ in the restricted configuration)` — e.g. for `f` the
inclusion of a vertex set `S`, `θ_{G[S]}(x, p) = P_p(x ↔ ∞ in S)` in Grimmett's notation
(`θ_ℍ(p) = P_p(0 ↔ ∞ in ℍ)`, §7.3 p. 162). This identifies this library's induced-graph convention with
the printed one. [cite: GrimmettPercolation1999, §7.3 p. 162 (θ_ℍ)] -/
theorem theta_comap_eq {W : Type*} [Countable W] (G : SimpleGraph V) {f : W → V}
    (hf : Function.Injective f) (x : W) (p : unitInterval) :
    theta (G.comap f) x p = (bondPercolation G p).real (restrictConfig f ⁻¹' percolatesAt x) := by
  rw [theta, ← bondPercolation_map_comap G hf p,
    map_measureReal_apply (measurable_restrictConfig f) (measurableSet_percolatesAt_holds x)]

/-- **Coupling inequality**: for injective `f : W → V`, `θ_{G.comap f}(x, p) ≤ θ_G(f x, p)` — under
the restriction coupling an infinite open cluster at `x` maps injectively into the open cluster of
`f x` (Grimmett 1999, §1.4 p. 13). Requires `W` countable (measurability of `{|C(x)| = ∞}`,
`measurableSet_percolatesAt_holds`). [cite: GrimmettPercolation1999, §1.4 p. 13 (1.9)] -/
theorem theta_comap_le {W : Type*} [Countable W] (G : SimpleGraph V) {f : W → V}
    (hf : Function.Injective f) (x : W) (p : unitInterval) :
    theta (G.comap f) x p ≤ theta G (f x) p := by
  rw [theta_comap_eq G hf, theta]
  refine measureReal_mono ?_
  intro ω hω
  simp only [Set.mem_preimage, percolatesAt, Set.mem_setOf_eq, openCluster] at hω ⊢
  refine ((hω.image hf.injOn).mono ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact reachable_map_of_restrictConfig hf ω hy

/-- **Proof of `theta_induce_le`** (Grimmett 1999, §1.4 p. 13 before (1.9); §7.1 p. 146):
`θ_{G[S]}(x, p) ≤ θ_G(x, p)`, the case `f = Subtype.val` of `theta_comap_le`
(`G.induce S = G.comap Subtype.val`). [cite: GrimmettPercolation1999, §1.4 (1.9) p. 13; §7.1 (7.1) p. 146] -/
theorem theta_induce_le_holds : theta_induce_le (V := V) := by
  intro _ G S x hx p
  exact theta_comap_le G Subtype.val_injective ⟨x, hx⟩ p

/-- **Proof of `theta_induce_mono`** (Grimmett 1999, §7.1 p. 146, "`p_c(S_k) ≥ p_c(S_{k+1})`"):
for `x ∈ S ⊆ T`, `θ_{G[S]}(x, p) ≤ θ_{G[T]}(x, p)`, the case `f = Set.inclusion hST` of
`theta_comap_le` (`G.induce S = (G.induce T).comap (Set.inclusion hST)`).
[cite: GrimmettPercolation1999, §7.1 (7.1) p. 146; §1.4 p. 13] -/
theorem theta_induce_mono_holds : theta_induce_mono (V := V) := by
  intro _ G S T hST x hx p
  have hG : G.induce S = (G.induce T).comap (Set.inclusion hST) := by
    ext a b; rfl
  rw [hG]
  exact theta_comap_le (G.induce T) (Set.inclusion_injective hST) ⟨x, hx⟩ p

end Coupling

end Percolation.Literature
