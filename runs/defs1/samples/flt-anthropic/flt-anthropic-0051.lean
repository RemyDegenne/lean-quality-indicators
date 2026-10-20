namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace B26

abbrev rO {Y : Scheme.{u}} {A B : Y.Opens} (h : B ≤ A) : Γ(Y, A) →+* Γ(Y, B) :=
  (Y.presheaf.map (homOfLE h).op).hom

end B26
end
end P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_inf_cocycle_of_face_cocycle
