public section

open CliffordAlgebra QuadraticMap

namespace TauCeti.SpinPolarizationData

universe u v

section CommRing

variable {K : Type u} [CommRing K]

variable {V : Type v} [AddCommGroup V] [Module K V]

variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

variable {n : ℕ} (b : Module.Basis (Fin n) K P.W)

theorem typeDGraphOperator_basis_of_notMem (hn : 2 ≤ n) {s : Finset (Fin n)}
    (hs : (⟨n - 1, by omega⟩ : Fin n) ∉ s) :
    P.typeDGraphOperator b hn (b.ExteriorAlgebra s) =
      (TauCeti.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n)
          (insert (⟨n - 1, by omega⟩ : Fin n) s) : ℤ) •
        b.ExteriorAlgebra (insert (⟨n - 1, by omega⟩ : Fin n) s) := by
  rw [typeDGraphOperator_eq_wedge_sub_contract, P.wedge_apply, P.contract_apply,
    pairingEquiv_dualVector, TauCeti.ExteriorAlgebra.ι_mul_basis,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis, ite_eq_right hs, ite_eq_right hs, sub_zero,
    Units.smul_def]

end CommRing
end TauCeti.SpinPolarizationData
end
