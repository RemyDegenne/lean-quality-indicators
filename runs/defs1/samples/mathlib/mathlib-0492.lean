@[expose] public section

namespace CategoryTheory

open Category

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*}

namespace CommShift

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  [Full G] [Faithful G]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [G.CommShift A] [H.CommShift A]

namespace OfComp

variable {A}

/-- Auxiliary definition for `Functor.CommShift.ofComp`. -/
noncomputable def iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  ((whiskeringRight C D E).obj G).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

end OfComp
end CommShift
end Functor
end CategoryTheory
end
