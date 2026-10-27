@[expose] public section

noncomputable section

universe u v s t

namespace SplitQuadric

variable (A : Type u) [CommRing A]

section UniversalMorphism

variable {S : Type v} [CommRing S] [Algebra A S]

/-- An assignment satisfying the determinant equation induces a quotient morphism. -/
def lift (values : Fin 4 → S) (h : values 0 * values 3 - values 1 * values 2 = 0) :
    CoordinateRing A →ₐ[A] S :=
  Ideal.Quotient.liftₐ (relationIdeal A) (MvPolynomial.aeval values)
    (fun _ hp => relationIdeal_le_ker_aeval A values h hp)

end UniversalMorphism
end SplitQuadric
end
end
