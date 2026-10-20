public section

open Matrix

open scoped commutatorElement

namespace TauCeti

universe u v

variable {n : Type*} [DecidableEq n] {A : Type u} {i j k l : n}

variable [CommRing A]

section Map

variable [Fintype n] {B : Type v} [CommRing B]

@[simp]
theorem map_transvectionUnit (f : A →+* B) (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.map f (transvectionUnit hij c) = transvectionUnit hij (f c) := by
  ext a b
  exact congrArg (fun s : Matrix.SpecialLinearGroup n B => (s : Matrix n n B) a b)
    (SpecialLinearGroup.map_transvection f hij c)

end Map
end TauCeti
end
