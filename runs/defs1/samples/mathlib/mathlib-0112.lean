@[expose] public section

universe u u' v w

variable {l m n o : Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

open Matrix

namespace Matrix

/-- The bottom-right `d × r` part of a `(u+d) × (l+r)` matrix. -/
abbrev subDownRight {d u l r : Nat} (A : Matrix (Fin (u + d)) (Fin (l + r)) α) :
    Matrix (Fin d) (Fin r) α :=
  subDown (subRight A)

end Matrix
end
