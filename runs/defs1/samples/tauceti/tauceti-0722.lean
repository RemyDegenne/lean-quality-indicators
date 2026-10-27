public section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace SplitEpi

variable {X S : C} {f : X ⟶ S}

/-- Pull a chosen section of `f : X ⟶ S` back along `g : T ⟶ S`.

The resulting section of `pullback.snd f g` has first projection `g ≫ h.section_`
and second projection the identity of `T`. -/
noncomputable def pullback (h : SplitEpi f) {T : C} (g : T ⟶ S) [HasPullback f g] :
    SplitEpi (Limits.pullback.snd f g) where
  section_ := Limits.pullback.lift (g ≫ h.section_) (𝟙 T) (by simp)
  id := Limits.pullback.lift_snd _ _ _

end SplitEpi
end CategoryTheory
end
