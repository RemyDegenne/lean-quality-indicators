@[expose] public section

set_option warningAsError true

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

namespace RationalMap

/-- Compose existing quotient rational maps using an explicit first-map condition. -/
noncomputable def compOfPullsDenseOpens (f : X ⤏ Y) (hf : f.PullsDenseOpens)
    (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g
    (fun h => (f.representative.compOfPullsDenseOpens
      (f.pullsDenseOpens_representative_iff.mpr hf) h).toRationalMap)
    (fun _ _ h => PartialMap.toRationalMap_eq_iff.mpr
      (PartialMap.compOfPullsDenseOpens_equiv_of_equiv_right _ _ h))

end RationalMap
end AlgebraicGeometry.Scheme
end
