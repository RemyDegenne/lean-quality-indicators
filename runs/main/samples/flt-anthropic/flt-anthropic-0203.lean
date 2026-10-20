namespace P2MW.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed

open Polynomial

namespace AlgebraicCurve

namespace LinDisjSol

p2m_open

section Main

open IntermediateField

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem transcendental_algebraMap {x : F} [FiniteDimensional K⟮x⟯ F]
    (hfg' : ∃ x' : F', Transcendental K' x' ∧ FiniteDimensional K'⟮x'⟯ F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    Transcendental K' (algebraMap F F' x) := by
  intro hx₁
  obtain ⟨x', hx', -⟩ := hfg'
  apply hx'
  haveI : FiniteDimensional K' K'⟮algebraMap F F' x⟯ := adjoin.finiteDimensional hx₁.isIntegral
  have hS : ∀ z ∈ Set.range (algebraMap F F'), IsIntegral K' z := by
    rintro _ ⟨f, rfl⟩
    exact isIntegral_trans (R := K') _ (isIntegral_algebraMap (K := K) (K' := K') x f)
  haveI := IntermediateField.isAlgebraic_adjoin hS
  have hmem : x' ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; exact mem_top
  exact IntermediateField.isAlgebraic_iff.mp
    (Algebra.IsAlgebraic.isAlgebraic
      (⟨x', hmem⟩ : IntermediateField.adjoin K' (Set.range (algebraMap F F'))))

end Main
end LinDisjSol
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_linearIndependent_of_constantFieldExtension_of_isAlgClosed
