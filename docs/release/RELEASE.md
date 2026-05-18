# Release Guide

Version: v0.1.0.

## Current Claim

The accepted-assumptions v0 theorem is checked from explicit stochastic
representation, quantile/source, and principal-box moment/formula inputs.

The release does not claim that the quantile/source theorem, angular moment
sources, or principal-box conditional moment formulas have been derived from
lower-level probability/measure theory.

## Public Citation Modules

| Purpose | Module |
| --- | --- |
| Default slim root | `Prim` |
| Accepted-assumptions release spine | `Prim.Release.AcceptedAssumptionsV0` |
| Publication stochastic release core | `Prim.Release.StochasticRepresentation.Core` |
| Public theorem aliases | `Prim.Release.TheoremMap.Core` |

## Minimum Release Commands

```bash
lake exe cache get
lake build Prim Prim.Release.AcceptedAssumptionsV0 Prim.Release.StochasticRepresentation.Core Prim.Release.TheoremMap.Core
rg -n "\b(sorry|admit|axiom)\b" Prim -g "*.lean"
rg -n "\x{00C3}|\x{00E2}|\x{00CF}|\x{00CE}" Prim docs -g "*.lean" -g "*.md"
```

## Boundary

This is a theorem-note package, not the full development workspace.
