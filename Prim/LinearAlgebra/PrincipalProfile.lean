import Prim.Basic

/-!
Ordered eigenvalue profiles.

This lightweight linear-algebra layer owns the ordered nonnegative spectrum
data shared by geometry and elliptical modules.  `Prim.Elliptical` keeps a
compatibility alias so existing theorem statements do not need to change.
-/

namespace Prim.LinearAlgebra

/--
Ordered eigenvalue profile for principal-coordinate arguments.

The paper indexes eigenvalues as `lambda 0 >= lambda 1 >= ...`, so we record
this with `Antitone`.
-/
structure PrincipalProfile (d : Nat) where
  eigenvalue : Prim.Idx d -> Real
  lambda_nonneg : forall i, 0 <= eigenvalue i
  lambda_antitone : Antitone eigenvalue

end Prim.LinearAlgebra

namespace Prim.Elliptical

/--
Compatibility alias for older public theorem statements that refer to
`Prim.Elliptical.PrincipalProfile`.
-/
abbrev PrincipalProfile := Prim.LinearAlgebra.PrincipalProfile

end Prim.Elliptical
