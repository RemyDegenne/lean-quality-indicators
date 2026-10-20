@[expose] public section

universe u u' v w w'

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable {R}

theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩

end Algebra
end
