public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable {R : Type u} {C : Type v}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

theorem coe_iSup_of_directed {ι : Type*} [Nonempty ι] {D : ι → Subcoalgebra R C}
    (hD : Directed (· ≤ ·) D) : ((⨆ i, D i : Subcoalgebra R C) : Set C) = ⋃ i, (D i : Set C) := by
  ext c
  simp only [SetLike.mem_coe, Set.mem_iUnion, mem_iSup_of_directed hD]

end Subcoalgebra
end TauCeti
end
