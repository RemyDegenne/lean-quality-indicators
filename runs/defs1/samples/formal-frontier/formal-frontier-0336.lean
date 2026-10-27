public section

noncomputable section

universe u uC uA uB

variable {C : Type uC} {A : Type uA} {B : Type uB}
  [CommRing C] [CommRing A] [CommRing B]
  [Algebra C A] [Algebra C B]

/-- The scalar action on a target copy induced by a ring homomorphism. -/
@[expose]
def targetCopyMap (t : A →+* B) : A →+* TargetCopy B :=
  TargetCopy.map t

end
end
