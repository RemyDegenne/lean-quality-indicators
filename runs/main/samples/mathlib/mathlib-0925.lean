@[expose] public section

noncomputable section

@[inherit_doc] infix:50 " ≤ᵥ " => ValuativeRel.vle

macro_rules | `($a ≤ᵥ $b) => `(binrel% ValuativeRel.vle $a $b)

namespace ValuativeRel

variable {R : Type*} [Semiring R] [ValuativeRel R] {x x' y y' z : R}

@[inherit_doc] infix:50 " <ᵥ " => ValuativeRel.vlt

macro_rules | `($a <ᵥ $b) => `(binrel% ValuativeRel.vlt $a $b)

@[inherit_doc] infix:50 " =ᵥ " => ValuativeRel.veq

macro_rules | `($a =ᵥ $b) => `(binrel% ValuativeRel.veq $a $b)

@[simp]
theorem ValueGroupWithZero.mk_le_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t ≤ ValueGroupWithZero.mk y s ↔ x * s ≤ᵥ y * t := Iff.rfl

end ValuativeRel
end
end
