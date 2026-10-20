@[expose] public section

noncomputable section

open CategoryTheory.Category CategoryTheory.Preadditive CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type*) [Category* C]

namespace Idempotents

namespace Karoubi

variable {C}

theorem comp_proof {P Q R : Karoubi C} (g : Hom Q R) (f : Hom P Q) :
    P.p ≫ (f.f ≫ g.f) ≫ R.p = f.f ≫ g.f := by simp

end Karoubi
end Idempotents
end CategoryTheory
end
end
