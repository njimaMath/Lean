# Generalized Latała bound for the SK model

This directory contains a Lean 4 formalization of a generalized Latała
interpolation argument for the finite-volume Sherrington--Kirkpatrick spin-glass
model. The main result proves overlap concentration and an $O(1/N)$ error bound
for the replica-symmetric pressure in the improved high-temperature region

$$
\rho(\beta,q)=\beta^2\kappa(q)<1,
\qquad
\kappa(q)=
\begin{cases}
q/\operatorname{artanh}(q),&q\ne0,\\
1,&q=0.
\end{cases}
$$

The public entry point is [`mainresult_latala.lean`](mainresult_latala.lean), and
the main theorem is
`SpinGlass.GeneralizedLatala.model_result`.

## Mathematical statement

For $N\ge 1$, a spin configuration is a function
$\sigma:\operatorname{Fin}(N)\to\operatorname{Bool}$, interpreted as a vector of
signs in $\{-1,1\}^N$. Its normalized overlap with $\tau$ is

$$
R(\sigma,\tau)=\frac1N\sum_{i=1}^N \sigma_i\tau_i.
$$

The disorder is represented abstractly by a centered Gaussian random field
$U(\sigma)$ with covariance

$$
\operatorname{Cov}(U(\sigma),U(\tau))
=\frac{N\beta^2}{2}R(\sigma,\tau)^2.
$$

With the sign convention used in the Lean definitions, the energy and Gibbs
weight are

$$
E_N(\sigma)=U(\sigma)+h\sum_{i=1}^N\sigma_i,
\qquad
G_N(\sigma)=\frac{\exp(-E_N(\sigma))}{Z_N}.
$$

Let $Z$ be a standard real Gaussian and suppose that $q$ satisfies

$$
0\le q<1,
\qquad
q=\mathbb E\!\left[
\tanh\!\left(h+\beta\sqrt q\,Z\right)^2
\right].
$$

If $\rho(\beta,q)<1$, then there is a finite common constant $C\ge0$ such
that

$$
\mathbb E\left\langle(R_{12}-q)^2\right\rangle
\le \frac{C}{N}
$$

and

$$
0\le
\phi^{\mathrm{RS}}(\beta,h,q)-\phi_N
\le\frac{C}{N},
$$

where

$$
\phi_N=\frac1N\mathbb E[\log Z_N]
$$

and

$$
\phi^{\mathrm{RS}}(\beta,h,q)
=\log 2
+\mathbb E\!\left[
\log\cosh\!\left(h+\beta\sqrt q\,Z\right)
\right]
+\frac{\beta^2}{4}(1-q)^2.
$$

In Lean, the two conclusions are bundled as `ModelClaims`. The proof actually
constructs a common constant from

$$
\lambda_*=\frac{\kappa(q)^{-1}-\beta^2}{4}
$$

and

$$
K(\beta,q)=
\frac12
\exp\!\left(\frac{2\rho}{1-\rho}\right)
\log\!\left(\frac{2}{1-\rho}\right).
$$

One may take

$$
C=\frac{K(\beta,q)}{\lambda_*}
+\frac{\beta^2K(\beta,q)}{4\lambda_*}.
$$

The formal theorem permits $\beta\in\mathbb R$; the usual convention
$\beta\ge0$ is unnecessary because the relevant covariance and bounds depend on
$\beta^2$.

## Lean interface

The theorem takes the following data:

- a probability space `Ω`;
- a positive system size `N`;
- real parameters `β`, `h`, and `q`;
- `sk : ModelSKDisorder N β h`, carrying the Gaussian SK field and its
  covariance identity;
- `sim : SimpleDisorder N β q`, the Gaussian one-site reference field used by
  the smart-path interpolation;
- the fixed-point and improved-region hypotheses above;
- `IndepFun sk.U sim.V ℙ`, expressing independence of the SK and reference
  disorders.

The reference disorder is a technical input to the interpolation proof. It
does not occur in `ModelClaims`.

The definitions intended for users are all in
`SpinGlass.GeneralizedLatala`:

- `ModelConfig`, `modelSpin`, and `modelOverlap`;
- `ModelSKDisorder`;
- `modelEnergy`, `modelPartitionFunction`, and `modelGibbsProbability`;
- `modelPressure` and `modelOverlapSecondMoment`;
- `ModelFixedPoint`, `modelKappa`, `modelRho`, and `modelRSPressure`;
- `ModelClaims` and `model_result`.

## Proof outline

The formal proof follows [`blueprint_latala.txt`](blueprint_latala.txt).

- At the independent endpoint, the Kearns--Saul inequality gives the sharp
  Bernoulli sub-Gaussian coefficient $\kappa(q)$.
- The Hubbard--Stratonovich identity turns that estimate into a bound for a
  quadratic exponential moment of the centered overlap.
- A coupled two-replica free energy is transported along Guerra's smart path.
  Gaussian integration by parts and a differential inequality control its
  growth.
- A Gronwall argument yields a uniform quadratic-coupling estimate whenever
  $\rho<1$.
- Convexity converts the exponential-moment estimate into the $O(1/N)$ overlap
  bound.
- Guerra's replica-symmetric sum rule then gives the pressure error bound.

The proof uses interpolation and replica calculus, not the cavity method.

## Directory guide

- [`mainresult_latala.lean`](mainresult_latala.lean): concise model definitions
  and the public theorem.
- [`blueprint_latala.txt`](blueprint_latala.txt): informal mathematical
  blueprint mirrored by the formal proof.
- [`Proof_of_generalized_latala/proof.lean`](Proof_of_generalized_latala/proof.lean):
  the main argument, including the endpoint estimate, coupled free energy,
  Gronwall bound, overlap concentration, and final theorem.
- [`Proof_of_generalized_latala/IndependentEndpoint.lean`](Proof_of_generalized_latala/IndependentEndpoint.lean):
  laws and independence facts for the one-site Gaussian endpoint.
- [`Proof_of_generalized_latala/IndependentGaussianAffineIBP.lean`](Proof_of_generalized_latala/IndependentGaussianAffineIBP.lean):
  Gaussian integration by parts for independent affine disorders.
- [`SpinGlass/`](SpinGlass/): finite-volume SK definitions, Guerra
  interpolation, replica calculus, analytic estimates, and local additions to
  the probability library.
- [`GibbsMeasure/`](GibbsMeasure/): a broader Gibbs-measure development included
  in this directory; it is not imported by the public generalized Latała
  theorem.

## Checking the formalization

The repository pins Lean `v4.28.0` and mathlib `v4.28.0`. From the repository
root, run

```powershell
lake env lean GeneralizedLatala/mainresult_latala.lean
```

This command checks the public entry point and all of its transitive imports.
The `lakefile.lean` and `lean-toolchain` files live at the repository root, so
this directory is not intended to be built as a standalone Lean project.
