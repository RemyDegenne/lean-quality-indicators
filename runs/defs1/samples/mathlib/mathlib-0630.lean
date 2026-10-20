@[expose] public section

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) (ι : Type w) [CommRing R] [CommRing S] [Algebra R S]

namespace Algebra.Generators

variable {R S ι}

variable (P : Generators R S ι)

section Construction

variable {ι' : Type*} {T} [CommRing T] [Algebra R T]

variable (S) in
/-- If `R → S → T` is a tower of algebras, a family of generators `R[X] → T`
gives a family of generators `S[X] → T`. -/
@[simps val]
noncomputable
def extendScalars [Algebra S T] [IsScalarTower R S T] (P : Generators R T ι) :
    Generators S T ι where
  val := P.val
  σ' x := map (algebraMap R S) (P.σ x)
  aeval_val_σ' s := by simp [@aeval_def S, ← IsScalarTower.algebraMap_eq, ← @aeval_def R]

end Construction
end Algebra.Generators
end
