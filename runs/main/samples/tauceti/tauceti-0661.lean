public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {p : ℕ} [Fact p.Prime]

@[reassoc]
theorem qPowerFrobenius_naturality (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    (fY : Y ⟶ Spec (CommRingCat.of k)) (g : X ⟶ Y) (a : ℕ)
    (ha : Nat.card k = p ^ a) :
    qPowerFrobenius k fX a ha ≫ g = g ≫ qPowerFrobenius k fY a ha := by
  exact iterateFrobenius_naturality
    (natCast_eq_zero_of_hom fX (natCast_spec_eq_zero (CommRingCat.of k)))
    (natCast_eq_zero_of_hom fY (natCast_spec_eq_zero (CommRingCat.of k))) g a

end AlgebraicGeometry.Scheme
end
