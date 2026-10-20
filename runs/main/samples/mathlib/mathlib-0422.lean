@[expose] public section

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (b : B)

namespace Algebra

open Polynomial

theorem RingHom.adjoinAlgebraMap_surjective :
    Function.Surjective (RingHom.adjoinAlgebraMap (A := A) b (C := C)) := by
  intro c
  obtain ⟨p, hp⟩ := adjoin_eq_exists_aeval A (algebraMap B C b) c
  aesop (add safe ((aeval_algebraMap_apply C b p).symm))

end Algebra
end
