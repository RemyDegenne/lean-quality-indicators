namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme

attribute [-instance] MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra

set_option autoImplicit false

set_option linter.unusedSectionVars false

p2m_open

open scoped MatrixGroups

noncomputable section

p2m_reactivate

namespace TR

namespace LawEq

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

abbrev ιQ : Spec (CommRingCat.of ℚ) ⟶ base p := Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))

end LawEq
end TR
end
end P2MW.S_ModularCurve_JHNeronObjectAtP_exists_equiv_forall_toricLift_comp_eq_of_iso_of_representsRelSubPic_of_abelianScheme
