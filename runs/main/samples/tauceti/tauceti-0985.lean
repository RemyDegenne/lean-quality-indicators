public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (P : TopPair.{w}) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

variable {P R k M}

variable (P R k M)

variable {P R k M}

variable (R k M)

section LongExactSequence

variable (P)

@[simp]
lemma singularCochainComplexShortComplex_f_eq :
    (P.singularCochainComplexShortComplex R k M).f =
      (TauCeti.ChainComplex.linearYonedaFunctor k M).map (P.singularChainComplexπ R).op := rfl

end LongExactSequence
end TopPair
end
end
