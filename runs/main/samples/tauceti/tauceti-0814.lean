public section

namespace TauCeti

open scoped Matrix

universe u v

section Row

variable {ι : Type*} {k : Type u} {G : Type v} [Field k] [Group G]
  {M : Matrix ι (ConjClasses G) k} {i : ι}

@[simp]
theorem centralCharacterRow_submatrix {ι' : Type*} (M : Matrix ι (ConjClasses G) k) (e : ι' → ι)
    (i : ι') :
    centralCharacterRow (M.submatrix e id) i = centralCharacterRow M (e i) := by
  funext C
  rw [centralCharacterRow_apply, centralCharacterRow_apply, Matrix.submatrix_apply,
    Matrix.submatrix_apply, id_eq, id_eq]

end Row
end TauCeti
end
