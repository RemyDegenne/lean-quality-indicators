@[expose] public section

universe uR uS vR vS

open CategoryTheory

namespace ModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

theorem isFiniteLength_iff_of_equivalence
    (e : ModuleCat.{vR} R ≌ ModuleCat.{vS} S) (X : ModuleCat.{vR} R) :
    IsFiniteLength S (e.functor.obj X) ↔ IsFiniteLength R X := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    length_eq_of_equivalence e X]

end ModuleCat
end
