public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {k : Type u} [Field k] {A : Type v}

variable {a₀ a₁ : A} {c d : k}

theorem not_isZero_kroneckerLineRep :
    ¬ IsZero (kroneckerLineRep k a₁ c) := by
  intro hz
  have : Subsingleton k :=
    ModuleCat.subsingleton_of_isZero (hz.obj (Quiver.Kronecker.src : Paths (Quiver.Kronecker A)))
  exact false_of_nontrivial_of_subsingleton k

end TauCeti
end
