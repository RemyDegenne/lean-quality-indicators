@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {J : Type w}

namespace SuccStruct

variable (Φ : SuccStruct C)

variable {Φ}

@[reassoc]
lemma prop.fac {X Y : C} {f : X ⟶ Y} (hf : Φ.prop f) :
    f = Φ.toSucc X ≫ eqToHom hf.succ_eq := by
  cases hf
  simp

end SuccStruct
end SmallObject
end CategoryTheory
end
