public section

open scoped Quaternion

namespace TauCeti

variable {R : Type*} [CommRing R]

section Rescale

@[simp]
theorem QuaternionAlgebra.rescaleIEquiv_apply_k (a b : R) (c : Rˣ) :
    rescaleIEquiv a b c ⟨0, 0, 0, 1⟩ =
      (c : R) • (QuaternionAlgebra.Basis.self R).k := by
  rw [← QuaternionAlgebra.Basis.k_self]
  rw [← QuaternionAlgebra.Basis.i_mul_j, map_mul]
  simp only [QuaternionAlgebra.Basis.i_self,
    QuaternionAlgebra.Basis.j_self, rescaleIEquiv_apply_i, rescaleIEquiv_apply_j]
  simp

end Rescale
end TauCeti
end
