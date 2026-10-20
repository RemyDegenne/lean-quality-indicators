public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {L : Type*} [Field L] [CharZero L] {F : IntermediateField ℚ L} {ζ : L} {N : ℕ}

section Cyclotomic

open IsCyclotomicExtension

variable {d : ℤ} (hd : Squarefree d) (K : IntermediateField ℚ ℂ)
  [IsCyclotomicExtension {(∏ P ∈ genusPrimeDiscriminants hd, P).natAbs} ℚ K]

include K in
/-- A square root of the prime discriminant `P` itself, inside the cyclotomic field `K`. -/
noncomputable def genusFieldRootOfPrimeDiscriminant
    (P : {P // P ∈ genusPrimeDiscriminants hd}) : K :=
  ⟨algebraMap ℚ ℂ (genusFieldRootScale hd P) * genusFieldRoot hd P,
    K.mul_mem (K.algebraMap_mem _) (genusFieldRoot_mem_of_isCyclotomicExtension hd K P)⟩

end Cyclotomic
end TauCeti.Multiquadratic
end
