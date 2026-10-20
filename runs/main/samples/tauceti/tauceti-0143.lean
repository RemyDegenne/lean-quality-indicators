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

lemma isIso_singularHomologyMap_of_isIso {P P' : TopPair.{w}} (f : P ⟶ P') (n : ℕ)
    (hfst : IsIso (SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R n))
    (hsnd : IsIso (SSet.homologyMap (TopCat.toSSet.map (Hom.snd f)) R n))
    (hfst' : ∀ m, m + 1 = n → IsIso (SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R m))
    (hsnd' : ∀ m, m + 1 = n → IsIso (SSet.homologyMap (TopCat.toSSet.map (Hom.snd f)) R m)) :
    IsIso (TopPair.singularHomologyMap f R n) := by
  have := HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (SSetPair.chainComplexShortComplexMap (toSSetPair.map f) R)
    ((toSSetPair.obj P).shortExact_chainComplexShortComplex R)
    ((toSSetPair.obj P').shortExact_chainComplexShortComplex R) n
  simp only [SSetPair.chainComplexShortComplexMap_τ₁, SSetPair.chainComplexShortComplexMap_τ₂,
    SSetPair.chainComplexShortComplexMap_τ₃, ComplexShape.down_Rel] at this
  -- The homology maps of these chain maps are `SSet.homologyMap` and
  -- `TopPair.singularHomologyMap` by definition.
  have h₁ : IsIso (HomologicalComplex.homologyMap
      (SSet.chainComplexMap (toSSetPair.map f).left R) n) := hsnd
  exact this inferInstance hfst hsnd' fun m hm ↦
    have : IsIso (HomologicalComplex.homologyMap
        (SSet.chainComplexMap (toSSetPair.map f).right R) m) := hfst' m hm
    inferInstance

end LongExactSequence
end TopPair
end
end
