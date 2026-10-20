@[expose] public section

noncomputable section

namespace QuantumParallelRepetition

noncomputable local instance matrixComplexContinuousENormPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

noncomputable local instance matrixComplexESeminormedAddCommMonoidPartOne
    {m n : Type*} [Fintype m] [Fintype n] :
    ESeminormedAddCommMonoid (Matrix m n ℂ) :=
  let base := @NormedAddCommGroup.toENormedAddCommMonoid (Matrix m n ℂ)
    Matrix.normedAddCommGroup
  { toContinuousENorm := inferInstance
    toAddCommMonoid := base.toAddCommMonoid
    enorm_zero := base.enorm_zero
    enorm_add_le := base.enorm_add_le }

attribute [instance] Strategy.aliceFintype Strategy.bobFintype
  Strategy.aliceDecidableEq Strategy.bobDecidableEq

section

open Matrix

open scoped BigOperators ComplexOrder MatrixOrder

theorem purifiedRefinedPOVM_compression
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
      (purifiedRefinedPOVM F hF Γ hΓ effect hpositive hsum a₀).effect a *
        Γ = effect a :=
  purifiedRefinedEffect_compression F hF Γ hΓ effect
    hpositive hsum a₀ a

end
end QuantumParallelRepetition
end
end
