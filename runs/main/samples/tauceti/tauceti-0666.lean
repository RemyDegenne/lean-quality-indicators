@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

variable {C} (P P' : TopPair.{w}) (f : P ⟶ P') (R : C)

section LongExactSequence

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  (P : TopPair.{w}) (R : A)

lemma singularHomology_exact_space (n : ℕ) :
    (ShortComplex.mk _ _ (P.homologyMap_comp_singularHomologyπ R n)).Exact :=
  (toSSetPair.obj P).homology_exact₂ R n

end LongExactSequence
end TopPair
end
end
