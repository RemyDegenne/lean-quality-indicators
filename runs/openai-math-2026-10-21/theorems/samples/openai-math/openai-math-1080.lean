namespace OAI

noncomputable section

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

 theorem exists_family : Nonempty Family := by
  classical
  obtain ⟨Γ,Q,hΓ,hQ,dΓ,A,M,hd,hr⟩ := UniversalMachine.exists_parameter_machine partrec_raw
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  let : DecidableEq Γ := dΓ
  let : Primcodable Γ := Effect.finitePrimcodable Γ
  let : Primcodable Q := Effect.finitePrimcodable Q
  exact ⟨⟨Γ,Q,A,M,UniversalMachine.restrict_decode (ParameterMachine.alphabet A) (ParameterMachine.output_decode A hd),hr⟩⟩

namespace FiniteAlgebraicEnvelopes.ZeroProduct

open scoped TensorProduct

open Contracted

variable (k K P : Type*) [CommRing k] [MonoidWithZero K] [Monoid P]

@[simp] theorem tensorMap_basis (a : K) (p : P) (r t : k) :
    tensorMap k K P (basis k K a r ⊗ₜ[k] MonoidAlgebra.single p t)=
      basis k (Mon K P) (pair K P (a,p)) (r*t) := by
  rw [tensorMap,Algebra.TensorProduct.lift_tmul,leftAlgebra_basis,rightAlgebra_single,basis_mul,←map_mul]
  simp

end FiniteAlgebraicEnvelopes.ZeroProduct
end
end OAI
