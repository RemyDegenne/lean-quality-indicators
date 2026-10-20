@[expose] public section

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable
section

section RatFuncCompatibility

variable (C M N S : Type*) [Field C] [Field M] [Field N] [Field S]
  [Algebra (RatFunc C) M] [Algebra (RatFunc C) N]
  [Algebra M N] [IsScalarTower (RatFunc C) M N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

/-- The constant algebra obtained by restricting a rational-function-field
algebra along `C → C(X)`.  Naming this definition makes the canonical
constant structures in the source and target definitionally transparent. -/
@[reducible] noncomputable def
    exactConstantExtensionTowerCanonicalConstantAlgebra
    (C T : Type*) [Field C] [Field T] [Algebra (RatFunc C) T] :
    Algebra C T :=
  RingHom.toAlgebra
    ((algebraMap (RatFunc C) T).comp (algebraMap C (RatFunc C)))

end RatFuncCompatibility
end
end BGS.HasseWeil
end
