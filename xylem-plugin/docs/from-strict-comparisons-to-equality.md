# From strict comparisons to equality

*A small checked proof decomposition and an open question about mathematical motivation*

## The mathematical problem

Let $q:\mathbb R\to\mathbb R$ be continuous. Suppose that for all positive $u,v,x,y$,

$$uv<xy \implies q(u)q(v)<q(x)q(y).$$

We want to establish, for every $a,b>0$,

$$q(1)q(ab)=q(a)q(b).$$

The hypotheses require positive **inputs**, not positive values of $q$. Ordinary multiplicativity, $q(ab)=q(a)q(b)$, requires the additional normalization $q(1)=1$.

## Why choose two one-sided bounds?

The two factor pairs $(1,ab)$ and $(a,b)$ have equal products. Our hypothesis applies only to *strictly unequal* products, so we cannot use it directly.

A useful move is to perturb the inputs, obtain strict comparisons, and use continuity to recover the boundary case.

**First bound.** For $\varepsilon>0$,

$$ab<a(b+\varepsilon),$$

so

$$q(1)q(ab)<q(a)q(b+\varepsilon).$$

Taking $\varepsilon\to0^+$ gives

$$q(1)q(ab)\leq q(a)q(b).$$

**Second bound.** Similarly,

$$ab<ab+\varepsilon$$

gives

$$q(a)q(b)<q(1)q(ab+\varepsilon),$$

hence

$$q(a)q(b)\leq q(1)q(ab).$$

The two inequalities establish equality by antisymmetry.

Each bound resolves one necessary part of the equality. Together, they suggest a candidate reusable move: **when a strict comparison cannot establish an equality directly, derive both bounds by perturbation and pass to the boundary using continuity.** Both input perturbations here are upward; they produce opposite bounds on the output expressions.

## What was actually checked?

The first extraction produced two separately named Lean helpers, `boundary_lower` and `boundary_upper`, preserving the original assumptions and endpoint type.

A second, agent-chosen layer grouped these inequalities into `boundary_sandwich` and used `le_antisymm` to recover equality. A downstream client established normalized multiplicativity under the additional premise $q(1)=1$. The retained checking record reports that the resulting Lean file compiled and passed the matching kernel replay.

This demonstrates faithful extraction and checked typed composition within one curated example. It does **not** demonstrate that an agent independently discovered the technique, recognized it in another proof, or established its broader mathematical usefulness.

## The open question

Could an agent recognize the reason for this move when given a different problem and its hypotheses, but not the solution?

Could it explain why the move applies, or identify when the required continuity, domain or comparison assumptions have not been established?

**What evidence would distinguish recognition of a useful mathematical move from successful refactoring of an existing proof?**
