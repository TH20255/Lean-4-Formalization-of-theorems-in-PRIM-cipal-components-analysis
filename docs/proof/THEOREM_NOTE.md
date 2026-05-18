# Accepted-Assumptions Theorem Note

Version: v0.1.0.

This note states the mathematical content of the v0.1.0 theorem boundary. It is
written for a first reader: the source assumptions are formulas, the conclusion
is a trace sandwich, and the Lean names are listed only after the mathematics.

The proof skeleton and release imports are summarized in
[PROOF_GUIDE.md](PROOF_GUIDE.md).

## Mathematical Setting

The theorem works in principal coordinates. Fix a dimension $d$ and use the
coordinate index set $\mathrm{Idx}(d)$.

The stochastic representation is

```math
Y_j(\omega)=R(\omega)\sqrt{\lambda_j}\,O_j(\omega)
\qquad (j\in \mathrm{Idx}(d)).
```

The ordered principal scale parameters satisfy

```math
\lambda_0\ge \lambda_1\ge\cdots\ge \lambda_{d-1}\ge 0.
```

For a nonnegative scalar radius $q\ge 0$, define the principal half-width
coordinatewise by

```math
w_j(q)=\sqrt{\lambda_j}\,q.
```

For a finite coordinate set $I\subseteq \mathrm{Idx}(d)$, the principal
central box is

```math
B_q(I)=\{\omega\mid
  \forall i\in I,\ |Y_i(\omega)|\le w_i(q)\}.
```

For an orthogonal matrix $U\in O(d)$, write the rotated coordinate vector as

```math
(UY)_i(\omega)=\sum_{\ell}U_{i\ell}Y_\ell(\omega).
```

The rotated central box is

```math
B_q^U(I)=\{\omega\mid
  \forall i\in I,\ |(UY)_i(\omega)|\le w_i(q)\}.
```

The covariance below is always taken after conditioning on a box, but its
entries are still measured in the original principal coordinates. For the
rotated box, define

```math
m_{U,I}(j)=\mathbb{E}[Y_j\mid B_q^U(I)],
```

and

```math
C_{U,I}(j,\ell)=
  \mathbb{E}[
    (Y_j-m_{U,I}(j))(Y_\ell-m_{U,I}(\ell))
    \mid B_q^U(I)].
```

When the rotation is the identity matrix, this is the principal-box covariance.

## Accepted Source Assumptions

The v0.1.0 theorem does not derive the following inputs. They are explicit
source assumptions supplied to Lean as structure fields.

### 1. Quantile and Radius Source

There is a tail level $\alpha\in\mathbb{R}$ and a nonnegative radius $q\ge 0$
such that every coordinate has at least the displayed tail mass on both sides of
the principal half-width:

```math
\alpha\le
\mu\{\omega:Y_i(\omega)\le -w_i(q)\},
```

```math
\alpha\le
\mu\{\omega:w_i(q)\le Y_i(\omega)\}.
```

The source also identifies the quantile interval event with the principal box:

```math
\{\omega\mid
  \forall i\in I,\ -w_i(q)\le Y_i(\omega)\le w_i(q)\}
  =B_q(I).
```

Lean uses this as the packaged quantile/radius boundary. It does not prove the
one-dimensional tail inequalities in this release.

### 2. Principal-Box Covariance Formula

There are real constants $a,b\in\mathbb{R}$ with nonpositive difference
$b-a\le 0$.

For every coordinate set $J$, conditioning on the principal box gives a
diagonal covariance matrix. Its diagonal entries are

```math
C_{\mathrm{id},J}(j,j)=b\lambda_j
\qquad (j\in J),
```

and

```math
C_{\mathrm{id},J}(j,j)=a\lambda_j
\qquad (j\notin J).
```

The off-diagonal entries vanish:

```math
C_{\mathrm{id},J}(j,\ell)=0
\qquad (j\ne \ell).
```

This assumption is the principal-box moment/formula source. The theorem uses
these two constants in every later trace formula.

### 3. Rotated Diagonal Formula

Fix a cardinality $k$. For every orthogonal matrix $U$ and every coordinate set
$I$ with $|I|=k$, the rotated conditioned covariance has prescribed diagonal
entries

```math
C_{U,I}(j,j)=D_{U,I}(j),
```

where

```math
D_{U,I}(j)
=
a\lambda_j+
\mathbf{1}_{j\in I}(b-a)
  \sum_{\ell}U_{j\ell}^{2}\lambda_\ell.
```

Equivalently, the stochastic-representation source supplies the weighted
angular second-moment formula

```math
\lambda_j\,\mathbb{E}[R^2 O_j^2\mid B_q^U(I)]
=
a\lambda_j+
\mathbf{1}_{j\in I}(b-a)
  \sum_{\ell}U_{j\ell}^{2}\lambda_\ell,
```

together with the sign-symmetry information needed to read this as the centered
second moment $C_{U,I}(j,j)$.

### 4. Rotated Off-Diagonal Cancellation

The upper-triangular v0 source assumes

```math
C_{U,I}(j,\ell)=0
\qquad (j<\ell).
```

Symmetry of covariance supplies the lower-triangular cases. The stronger
off-diagonal v0 source assumes directly

```math
C_{U,I}(j,\ell)=0
\qquad (j\ne \ell).
```

Thus the rotated covariance target is the diagonal matrix with the displayed
diagonal entries $D_{U,I}(j)$.

## Trace Objective

The trace objective is the sum of the diagonal entries:

```math
\mathrm{Obj}(U,I)
=
\sum_j D_{U,I}(j).
```

Expanding the formula for $D_{U,I}(j)$ gives

```math
\mathrm{Obj}(U,I)
=
a\sum_j\lambda_j
+
(b-a)\sum_{j\in I}\sum_{\ell}U_{j\ell}^{2}\lambda_\ell.
```

Let $L_k$ be the coordinate set indexing the $k$ largest principal scale
parameters, and let $T_k$ be the coordinate set indexing the $k$ smallest
principal scale parameters. Define

```math
\mathrm{LowerEndpoint}(k)
=
a\sum_j\lambda_j
+
(b-a)\sum_{j\in L_k}\lambda_j,
```

and

```math
\mathrm{UpperEndpoint}(k)
=
a\sum_j\lambda_j
+
(b-a)\sum_{j\in T_k}\lambda_j.
```

The coefficient $b-a$ is nonpositive, so selecting the largest eigenvalues gives
the lower endpoint and selecting the smallest eigenvalues gives the upper
endpoint.

## Theorem

For every orthogonal matrix $U$ and every coordinate set $I$ with $|I|=k$, the
checked theorem proves

```math
\mathrm{LowerEndpoint}(k)
\le
\mathrm{Obj}(U,I)
\le
\mathrm{UpperEndpoint}(k).
```

The same sandwich is proved for both theorem branches:

- the moment branch, written with centered products;
- the integral branch, written as explicit conditional integrals.

The upper-triangular and full off-diagonal source packages have the same final
rotation-optimality conclusion.

Under the expansion above, the Lean endpoint names mean:

- `momentLeadingQuantileTrace` and `integralLeadingQuantileTrace` are the lower
  endpoint.
- `momentTrailingQuantileTrace` and `integralTrailingQuantileTrace` are the
  upper endpoint.

## Lean Shape

The shortest public import for theorem-map aliases is:

```lean
import Prim.Release.TheoremMap.Core
```

The upper-triangular accepted-assumptions source is:

```lean
S : Prim.Release.AcceptedAssumptionsV0.Source d
```

Given:

```lean
U : OrthogonalMatrixRotation d
I : Finset (Prim.Idx d)
hI : I.card = S.k
```

The corresponding same-set theorem is:

```lean
Prim.Release.AcceptedAssumptionsV0.rotationOptimalityConst
```

It returns the moment and integral trace sandwiches:

```lean
(S.toRotationOptimalitySource.momentLeadingQuantileTrace <=
    S.toRotationOptimalitySource.momentObjective U I /\
  S.toRotationOptimalitySource.momentObjective U I <=
    S.toRotationOptimalitySource.momentTrailingQuantileTrace) /\
  S.toRotationOptimalitySource.integralLeadingQuantileTrace <=
    S.toRotationOptimalitySource.integralObjective U I /\
  S.toRotationOptimalitySource.integralObjective U I <=
    S.toRotationOptimalitySource.integralTrailingQuantileTrace
```

The full off-diagonal sibling uses:

```lean
S : Prim.Release.AcceptedAssumptionsV0.OffDiagSource d
```

and:

```lean
Prim.Release.AcceptedAssumptionsV0.offDiagRotationOptimalityConst
```

The compact stochastic citation aliases are also exported by:

```lean
import Prim.Release.StochasticRepresentation.Core
```

with names:

- `Prim.Release.StochasticRepresentation.AcceptedAssumptionSource`
- `Prim.Release.StochasticRepresentation.acceptedAssumptionRotationOptimalityConst`
- `Prim.Release.StochasticRepresentation.AcceptedAssumptionOffDiagSource`
- `Prim.Release.StochasticRepresentation.acceptedAssumptionOffDiagRotationOptimalityConst`

The theorem-map aliases are:

- `Prim.Release.TheoremMap.stochasticAcceptedAssumptionSource`
- `Prim.Release.TheoremMap.stochasticAcceptedAssumptionRotationOptimalityConst`
- `Prim.Release.TheoremMap.stochasticAcceptedAssumptionOffDiagSource`
- `Prim.Release.TheoremMap.stochasticAcceptedAssumptionOffDiagRotationOptimalityConst`

## What This Does Not Claim

The v0.1.0 theorem does not prove the quantile/radius source, the angular
second-moment formula, the sign-symmetry input, or the principal-box covariance
formula from lower-level probability and measure theory.

It also does not prove a characteristic-function-to-stochastic-representation
bridge.

The correct release description is:

> rotation optimality from an elliptical stochastic representation plus
> accepted quantile and principal-box moment/formula source assumptions.

It is not:

> rotation optimality from characteristic functions or from bare measure theory
> alone.
