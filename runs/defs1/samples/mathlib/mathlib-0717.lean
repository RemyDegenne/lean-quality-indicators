@[expose] public section

universe u v w w'

open Cardinal CategoryTheory

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}

variable (L)

variable {L}

namespace Theory

variable (T)

/-- A theory models a (bounded) formula when any of its nonempty models realizes that formula on all
  inputs. -/
def ModelsBoundedFormula (φ : L.BoundedFormula α n) : Prop :=
  ∀ (M : ModelType.{u, v, max u v w} T) (v : α → M) (xs : Fin n → M), φ.Realize v xs

end Theory
end Language
end FirstOrder
end
