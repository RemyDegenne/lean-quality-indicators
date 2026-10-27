public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

open scoped commutatorElement

variable {K : Type} [Field K] [IsF2 K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} [FiniteDimensional K V]

theorem isSimpleGroup_elementaryGroup_of_six_le_finrank (hQ : (polarBilin Q).Nondegenerate)
    (hd : 6 ≤ finrank K V) : IsSimpleGroup (elementaryGroup Q) :=
  isSimpleGroup_elementaryGroup_of_perfect hQ (by omega) (Or.inl (by omega))
    (commutator_elementaryGroup_eq_top_f2 hQ hd)

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
end
