public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

open CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {Γ : Type u} [Group Γ]

section Embedding

variable [Finite Γ] {E Y : Subgroup Γ}

omit [Finite Γ] in
theorem map_conj_one (X : Subgroup Γ) : X.map (MulAut.conj (1 : Γ)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map]

end Embedding
end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
end
