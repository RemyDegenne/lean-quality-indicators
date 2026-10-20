@[expose] public section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory

theorem pullback_eq_inf_of_isPullback {A : Type u} [SemilatticeInf A] [OrderTop A]
    {x y z : A} (f : x ⟶ z) (g : y ⟶ z) : pullback f g = x ⊓ y := by
  exact ((pullback.isLimit f g).conePointUniqueUpToIso (isPullback_inf f g).isLimit).to_eq

end CategoryTheory
end
