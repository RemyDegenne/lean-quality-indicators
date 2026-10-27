set_option autoImplicit false

set_option linter.unusedSectionVars false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section FppfSite

open AlgebraicGeometry

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]

noncomputable abbrev FppfH (F : Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) (n : ℕ) :
    Type (u + 1) :=
  F.H n

end WithLocalInstances
end FppfSite
end FppfCohomologyLES
