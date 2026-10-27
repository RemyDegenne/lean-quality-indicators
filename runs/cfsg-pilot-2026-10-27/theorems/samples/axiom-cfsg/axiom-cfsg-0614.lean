public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

open scoped commutatorElement MatrixGroups

section Toral

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

namespace SecToral

variable {A : Subgroup G} {S : Set G} (T : SecToral Φ a A S)

include T

omit [Finite G] in
theorem comm {x y : G} (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (T.elem.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)

end SecToral
end Toral
end CFSG.ClassicalInvolution.Balance.Bootstrap
end
