public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Mono

variable {K : Type} [Field K] [CharP K 2] {s : ℕ}

theorem monoC_one_false :
    (monoC 1 (fun _ => false) : (Fin s → K × K) ≃ₗ[K] (Fin s → K × K)) = 1 :=
  LinearEquiv.ext fun _ => funext fun _ => rfl

end Mono
end ChoiceTwoOm
end CFSG.StandardType
end
