# Navier–Stokes: an assurance case for one inverse estimate

**Reader goal:** locate the exact interface behind a derivative estimate, inspect its evidence, and decide what connects the formal result to the written claim.

**Status: authored, source-inspected assurance case.** This bounded map follows Lemma 8.6, equation (8.19), of *Finite time blowup for Navier–Stokes* and four Lean files at commit [`f9e8bc5b38b6e212696e8a30e3e91517af887bbd`][commit]. It responds to Example 3.1 of [Bastounis, Circelli and Hansen][critique], whose authors explicitly reserve judgment on the natural-language proof’s correctness. All mathematical connections below carry an evidence type.

## Six boxes

### A. Intended claim: four additional torus derivatives

Fix $v_t=(\sqrt2-1,1)$, $N=v_t\cdot\partial_y$, and a smooth, zero-Haar-mean function $F$ on $\mathbb T^2$. The paper claims a unique smooth zero-mean solution and, for every integer $m\ge0$,

$$
\|N^{-1}F\|_{C_y^m}\le C_m\|F\|_{C_y^{m+4}}.
$$

For comparison, use the maximum of coordinate-derivative suprema through the indicated order; other parameters remain fixed. $C_m$ may depend on $m$ and the fixed direction, independently of $F$. The paper’s Fourier argument combines one divisor loss with a summable cubic tail. **Evidence:** [equation (6.2), p. 63; (6.7), p. 64; Lemma 8.6, pp. 95–96][paper].

### B. Representation and normalization: identify the inverse

Lean represents a torus function by a unit-periodic function on $\mathbb R^2$. Choose `Direction.temporal`, whose vector agrees with $v_t$. `derivativeWord` means successive coordinate derivatives. **Evidence:** [`TorusInverse`, direction, lines 190–213][torus]; [derivative words, lines 444–456][word].

For the family interface, $f:P\times\mathbb R^2\to\mathbb C$, with $P$ a real normed space. Fix a parameter $p$. Smoothness, periodicity and `ZeroMean f` support `inverse_solves`; that family theorem also uses finite-dimensional $P$. `inverse_zeroMean` records output normalization. **Evidence:** [`SmoothFamilyTorusInverse`, lines 20–37, 348, 572–616][family]. These declarations make the operator-identification obligation inspectable.

### C. Fourier coefficient interface: four derivatives beyond a moment

Set $W(k)=1+|k_1|+|k_2|$. `coefficient_seminorm_bound` controls the weighted absolute Fourier sum of order $q$ using bounds on the function and its two pure-coordinate derivatives of order $q+4$. Its summability constant uses $\sum_{k\in\mathbb Z^2}W(k)^{-4}$. **Evidence:** [`SmoothFourierData`, lines 325–387][fourier]. The definitions of `xJet` and `swapFunction` identify those two derivatives (lines 65–68, 182).

### D. Inverse derivative interface: one additional Fourier moment

`inverse_derivativeWord_bound` controls a derivative word of length $r$ by a constant times the coefficient seminorm of order $r+1$. Its input is a rapidly decaying coefficient family. **Evidence:** [`TorusInverse`, lines 503–525][inverse-bound] (with `Rapid` defined at lines 30–32). This box exposes where inversion spends one order.

### E. Formal result: the composed five-derivative budget

`norm_derivativeWord_inverse_le` composes C and D with $q=r+1$. It assumes joint smoothness and periodicity, and one real bound $C$ for the function and both pure derivatives of order $r+5$ on the unit square. It bounds each output word by `mixedLossConstant r * C`, at every $Y\in\mathbb R^2$. **Evidence:** [`SmoothFamilyTorusInverse`, lines 1058–1080][estimate]; [constant definition, lines 643–649][constant].

This estimate has no zero-mean premise. Its hypothesis named `hzero` bounds the function value. Box B separately supplies zero-mean input for solvability and zero-mean output for normalization of the solution of $N\varphi=F$.

### F. Correspondence obligation: recover the promised budget

At the same fixed $p$, take $C=\|f(p,\cdot)\|_{C_y^{m+5}}$ and $\widehat K_m=\max_{0\le r\le m}\mathrm{mixedLossConstant}(r)$. Suprema and the finite maximum over words of lengths $0,\ldots,m$ would then bound the $C_y^m$ output norm in terms of the $C_y^{m+5}$ input norm, still for smooth inputs. This is an **authored mathematical inference**, not an inspected Lean wrapper. To justify A from this route, a reviewer still needs an estimate with the $m+4$ input budget.

Both sides assume smooth inputs. The local difference concerns quantitative dependence on input seminorms. Smoothness supplies higher derivatives individually; it supplies no uniform control of their size by the lower-order budget. This distinction keeps existence, quantitative strength, and correspondence separately reviewable.

## Claim and evidence map

Authored/source-inspected diagram. Solid arrows identify inspected proof calls; dashed arrows identify interpretation or comparison obligations.

```mermaid
flowchart LR
  A["A · Written estimate: m+4"]
  B["B · Periodicity, direction, zero mean"]
  C["C · Coefficient control: q+4"]
  D["D · Inverse control: moment r+1"]
  E["E · Formal estimate: r+5"]
  F["F · Correspondence review"]
  C --&gt;|"proof dependency: supplies coefficient bound"| E
  D --&gt;|"proof dependency: supplies inverse bound"| E
  B -.-&gt;|"interpretation: identifies normalized operator"| F
  A -.-&gt;|"specification: supplies intended budget"| F
  E -.-&gt;|"comparison: supplies formal budget"| F
```

## Review decision and next check

**Assurance claim:** the cited sources expose a concrete budget difference at this interface. The evidence supports that local comparison; acceptance of semantic correspondence remains open.

**Human question:** must this interface certify the stated $m+4$ quantitative estimate, or does the intended use need only some fixed finite derivative loss?

A bounded next check is to formulate C with $q+3$, using cubic lattice summability, then check whether the same D composition recovers $r+4$. Alternatively, document a particular consumer’s larger budget explicitly. Either route produces a precise review target.

## Limitations

Potential defeaters include a stronger existing lemma, a different intended norm, or a consumer-specific assumption that closes the budget gap. This review reads selected source statements and proof bodies; it performs no build, kernel replay, repository-wide search, or automatic extraction. It establishes no checked semantic equivalence and gives no verdict on the original theorem or its full proof.

[commit]: https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd
[critique]: https://arxiv.org/html/2610.08144v1#S3.SS1
[paper]: https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf#page=95
[torus]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/TorusInverse.lean#L190-L213
[family]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/SmoothFamilyTorusInverse.lean#L572-L616
[fourier]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/SmoothFourierData.lean#L325-L387
[estimate]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/SmoothFamilyTorusInverse.lean#L1058-L1080
[constant]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/ParametricTorusInverse.lean#L643-L649

[word]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/TorusInverse.lean#L444-L456
[inverse-bound]: https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/TorusInverse.lean#L503-L525
