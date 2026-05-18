# Lean 4 Formalization of `PRIM-cipal components analysis` v0.1.0

This is the slim v0.1.0 Lean 4 / mathlib upload package for the
accepted-assumptions stochastic-representation theorem described in
[`docs/proof/THEOREM_NOTE.md`](docs/proof/THEOREM_NOTE.md).

The package proves rotation optimality from an elliptical stochastic
representation plus explicit quantile/source and principal-box moment/formula
inputs. It does not claim a derivation from characteristic functions or from
bare measure theory.

## Build

```bash
lake exe cache get
lake build Prim
```

Direct citation surfaces:

```bash
lake build Prim.Release.TheoremMap.Core
lake build Prim.Release.StochasticRepresentation.Core
lake build Prim.Release.AcceptedAssumptionsV0
```

## Lean Entrances

| Purpose | Module |
| --- | --- |
| Default slim root | `Prim` |
| Public theorem aliases | `Prim.Release.TheoremMap.Core` |
| Stochastic theorem aliases | `Prim.Release.StochasticRepresentation.Core` |
| Accepted-assumptions aliases | `Prim.Release.AcceptedAssumptionsV0` |

## Reading Path

1. [`docs/proof/THEOREM_NOTE.md`](docs/proof/THEOREM_NOTE.md)
2. [`docs/proof/PROOF_GUIDE.md`](docs/proof/PROOF_GUIDE.md)
3. [`docs/release/RELEASE.md`](docs/release/RELEASE.md)

The upload package omits nonessential development material to keep the first
reading path short.

## License

This project is released under the MIT license. See [`LICENSE`](LICENSE).
