import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace Prim

/--
Shared lightweight definitions for the formalization project.

This file provides the common entry point for the project now that the
formalization is mathlib-backed.
-/
abbrev Idx (d : Nat) := Fin d

/--
Coordinate model for the ambient space.

We intentionally start with the concrete representation `Fin d → ℝ`, which
keeps the probabilistic and matrix-valued definitions lightweight. If needed, we
can later switch to an explicitly bundled Euclidean space once the core
measure-theoretic layer is stable.
-/
abbrev Vec (d : Nat) := Idx d → ℝ

/-- Convenient alias for real square matrices indexed by `Fin d`. -/
abbrev Mat (d : Nat) := Matrix (Idx d) (Idx d) ℝ

/-- Project version string for quick smoke tests. -/
def skeletonVersion : String := "0.1.0"

end Prim
