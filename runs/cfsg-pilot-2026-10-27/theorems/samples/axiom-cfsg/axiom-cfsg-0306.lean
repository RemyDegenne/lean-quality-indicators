public section

namespace CFSG.RankThree.PartOne.LIT

section Complement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eq_zero_of_mem_of_isCompl {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂) {x : V}
    (h₁ : x ∈ V₁) (h₂ : x ∈ V₂) : x = 0 :=
  Submodule.disjoint_def.mp hc.disjoint x h₁ h₂

end Complement
end CFSG.RankThree.PartOne.LIT
end
