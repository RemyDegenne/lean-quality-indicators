public section

namespace TauCeti

open CategoryTheory

open scoped ModuleCat

universe u

variable {k : Type*} [Field k] {A : Type u} [Ring A] [Algebra k A]

variable (k) in
theorem isEulerAdmissibleOn_isFG [FiniteDimensional k A]
    (h : ModuleCat.isFG A ≤
      (ExactStructure.abelian (ModuleCat.{u} A)).admitsFiniteResolution
        (finiteProjectiveModules A)) :
    IsEulerAdmissibleOn.{u} k (ModuleCat.isFG A) (ModuleCat.isFG A) where
  isEulerAdmissible X Y hX hY := by
    obtain ⟨r⟩ := (ExactStructure.admitsFiniteResolution_iff _ _).mp (h X hX)
    refine r.isEulerAdmissible (finiteProjectiveModules_le_isProjective A) fun Z hZ => ?_
    have : Module.Finite A Z := (finiteProjectiveModules_iff.mp hZ).1
    have : Module.Finite A Y := (ModuleCat.isFG_iff Y).mp hY
    have : FiniteDimensional k Z := Module.Finite.trans A Z
    have : FiniteDimensional k Y := Module.Finite.trans A Y
    exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := k)).symm

end TauCeti
end
