public section

namespace TauCeti

universe uR uA uB uC uD

variable {R : Type uR} {A : Type uA} {B : Type uB} {C : Type uC}
  [CommRing R]
  [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalRing C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B} {𝒞 : ℤ → Submodule R C}
  [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
  [SetLike.GradedMul ℬ] [DirectSum.Decomposition ℬ]
  [SetLike.GradedMul 𝒞] [DirectSum.Decomposition 𝒞]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {dC : C →ₗ[R] C}

namespace NonUnitalDGAlgHom

variable {hA : IsNonUnitalDGAlgebra 𝒜 dA} {hB : IsNonUnitalDGAlgebra ℬ dB}
  {hC : IsNonUnitalDGAlgebra 𝒞 dC}

/-- Composition of morphisms of nonunital differential graded algebras. -/
def comp (g : NonUnitalDGAlgHom hB hC) (f : NonUnitalDGAlgHom hA hB) :
    NonUnitalDGAlgHom hA hC where
  toNonUnitalAlgHom := g.toNonUnitalAlgHom.comp f.toNonUnitalAlgHom
  map_mem' ha := Graded.map_mem g (Graded.map_mem f ha)
  map_d' a :=
    (g.map_d' (f.toNonUnitalAlgHom a)).trans
      (congrArg g.toNonUnitalAlgHom (f.map_d' a))

end NonUnitalDGAlgHom
end TauCeti
end
