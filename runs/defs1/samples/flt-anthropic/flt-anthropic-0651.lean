namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped TensorProduct Quaternion

open IsDedekindDomain NumberField

namespace S4Local

local notation "Kv" v => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v

local notation "Ov" v => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v

section B

variable (w : HeightOneSpectrum (𝓞 ℚ))

def IsInt (A : Matrix (Fin 2) (Fin 2) ((Kv w))) : Prop := ∀ i j, A i j ∈ (Ov w)

end B
end S4Local
end
end P2MW.S_QuaternionAlgebra_IsOrder_exists_localBox_iff_and_localBox_iff_conj_diagonal_of_linearMap_matrix_zmod
