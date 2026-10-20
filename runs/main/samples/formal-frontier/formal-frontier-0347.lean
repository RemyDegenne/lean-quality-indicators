@[expose] public section

universe vE vB uE uB

namespace CategoryTheory.Functor

variable {E : Type uE} {B : Type uB}

section Category

variable [Category.{vE} E] [Category.{vB} B] (F : E ⥤ B)
  (hF : F.toPrefunctor.IsCovering)

@[simp] theorem coveringLift_map {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    F.toPrefunctor.star x.val (F.coveringLift hF f x) =
      ⟨b', eqToHom x.property ≫ f⟩ :=
  Equiv.ofBijective_apply_symm_apply _ _ _

end Category
end CategoryTheory.Functor
end
