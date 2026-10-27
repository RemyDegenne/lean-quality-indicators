public section

open Matrix

namespace TauCeti

universe u

variable {A : Type u}

variable [CommRing A]

/-- **The pinned graph automorphism of the type-`A_r` matrix group.** It is signed reverse
inverse transpose, `g ↦ Q (g⁻¹)ᵀ Q⁻¹`. -/
def typeAGraphAutomorphism (r : ℕ) (A : Type u) [CommRing A] :
    GL (Fin (r + 1)) A ≃* GL (Fin (r + 1)) A :=
  Matrix.GeneralLinearGroup.inverseTranspose.trans (MulAut.conj (typeAGraphConjugator r A))

end TauCeti
end
