namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

noncomputable section

namespace R4F4aEd2

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

section GLclause

open LT.LatticeTree

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]

variable [Algebra ℤ_[r] (WittVector r k)]

variable (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k)

variable (ι : Zp2 r →+* WittVector r k) (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))

variable (M : ModuliPackage.{0, 0} r (WittVector r k))

variable
  (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
    M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)

variable
  (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
    Rigidified r Φ B → M.obj B ψ hB)

variable (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])

def gzero (kk : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] :=
  scalarGL (Units.mk0 ((r : ℚ_[r]) ^ kk) (rpow_ne_zero kk)) * g⁻¹

end GLclause
end R4F4aEd2
end
end P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
