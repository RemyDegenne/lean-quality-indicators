public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Module Submodule Subgroup Matrix

open LinearMap (BilinForm)

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatFactsSp4

open SymplecticHigher SymplecticFlag

open CFSG.ClassicalGroups.Alternating

section Model

variable {F : Type} [Field F]

theorem mulVecLin_injective' : Function.Injective (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => Matrix.mulVecLin M) := by
  intro M N h
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
  exact h

end Model
end CFSG.GH74.GLS.Stage2.Local.P34
end
