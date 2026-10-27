@[expose] public section

open FirstOrder

open FirstOrder.Language

open FirstOrder.Language.BoundedFormula

open ReplaceFV

open ZFC

open FixedSnoc

universe u v

namespace FirstOrder.ZFC

variable {V : Type u}

@[inherit_doc] infixl : 120 " ⊆' " => intIsSubset'

@[inherit_doc] infixl : 120 " ⊈' " => intNotIsSubset'

@[inherit_doc ExtNotIsSubset] infixl : 50 " ⊈ " => ExtNotIsSubset

/-- t = {x∈(bv n) : ϕ}. -/
def intIsSeparation {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
    LZFC.BoundedFormula ℕ n := (∀'((bv'' n ∈' fv' 1) ⇔
    (bv'' n ∈' fv' 0 ∧' ϕ.liftAndReplaceFV 1 n ![bv'' n])))

end FirstOrder.ZFC
end
