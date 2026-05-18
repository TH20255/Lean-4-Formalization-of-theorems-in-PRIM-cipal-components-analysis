# Proof Guide

This guide describes the proof boundary for the v0.1.0 theorem-note package.
The paper-facing mathematical statement is in
[`THEOREM_NOTE.md`](THEOREM_NOTE.md).

## Main Claim

The project proves a stochastic-representation route to rotation optimality for
elliptical distributions.

The accepted-assumptions theorem takes the following as explicit source inputs:

1. a clean quantile/radius source for the principal box;
2. angular symmetry and moment data for the stochastic representation;
3. principal-box conditional moment/formula sources.

These inputs are structure fields and theorem hypotheses, not hidden local
axioms.

## Lean Entrances

| Purpose | Lean module |
| --- | --- |
| Default slim root | `Prim` |
| Accepted-assumptions release spine | `Prim.Release.AcceptedAssumptionsV0` |
| Publication stochastic release core | `Prim.Release.StochasticRepresentation.Core` |
| Public theorem aliases | `Prim.Release.TheoremMap.Core` |

The shortest checked publication-facing import is:

```lean
import Prim.Release.TheoremMap.Core
```

## Dependency Skeleton

```text
N0  Elliptical stochastic core
  -> N1  Quantile and principal-box event boundary
  -> N2  Moment/formula accepted source packages
  -> N3  Diagonal covariance and trace formula packages
  -> N4  Deterministic k-dimensional rotation inequalities
  -> N5  Stochastic source wrapper
  -> N6  Public theorem wrappers
  -> N7  Release aliases
```

## Public Theorem Surfaces

| Alias module | Important aliases |
| --- | --- |
| `Prim.Release.StochasticRepresentation.Core` | `acceptedAssumptionRotationOptimalityConst`, `acceptedAssumptionOffDiagRotationOptimalityConst` |
| `Prim.Release.AcceptedAssumptionsV0` | `rotationOptimalityConst`, `offDiagRotationOptimalityConst` |
| `Prim.Release.TheoremMap.Core` | public aliases for the stochastic and accepted-assumptions theorem surfaces |

Core theorem names behind the aliases:

- `Prim.Elliptical.stochasticPrincipalBoxAmbientFormulaSource_publicRotationOptimality`
- `Prim.Elliptical.stochasticPrincipalBoxAmbientOffDiagFormulaSource_publicRotationOptimality`

## What Is Outside v0.1.0

This package does not include lower-level derivations of the accepted source
inputs from probability/measure theory, and it does not include a
characteristic-function-to-representation bridge.
