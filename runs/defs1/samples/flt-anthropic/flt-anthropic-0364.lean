namespace P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem

set_option autoImplicit false

open scoped TensorProduct

namespace DescentK

open HopfAlgebra PDivisibleGroup

section Frame

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

variable {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h)

variable (M : Submodule ℤ_[p] (TateModule p (G.Points (PadicAlgCl p))))

variable (K' : Type) [Field K'] [Algebra (PadicAlgCl.ringOfIntegers p K) K']
  [IsFractionRing (PadicAlgCl.ringOfIntegers p K) K']
  [Algebra K' (PadicAlgCl p)] [IsScalarTower (PadicAlgCl.ringOfIntegers p K) K' (PadicAlgCl p)]

local notation "𝒪" => PadicAlgCl.ringOfIntegers p K

local notation "ℚ̄" => PadicAlgCl p

abbrev Agen (v : ℕ) : Type := K' ⊗[𝒪] G.level v

end Frame
end DescentK
end P2MW.S_PDivisibleGroup_exists_baseChange_hopf_quotient_system_points_iff_mem_of_forall_smul_mem
