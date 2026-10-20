open scoped TensorProduct

section FlatClosureHopf

universe u v w

variable {R : Type u} [CommRing R]

variable {F : Type v} [Field F] [Algebra R F]

variable {G : Type w} [CommRing G]

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass

set_option synthInstance.maxHeartbeats 400000

section ModuleLevel

variable [Algebra R G]

def closureTensorSpan (B : Subalgebra F (F ⊗[R] G)) : Submodule R (G ⊗[R] G) :=
  Submodule.span R (Set.image2 (· ⊗ₜ[R] ·) (flatClosure B : Set G) (flatClosure B : Set G))

end ModuleLevel
end FlatClosureHopf
