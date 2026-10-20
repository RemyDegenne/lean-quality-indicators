public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.GradedObject

variable {I : Type*} {C : Type*} [Category* C] [MonoidalCategory C]

section AddMonoid

variable [AddMonoid I]

section MonObj

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

variable (X : GradedObject I C) (one : 𝟙_ C ⟶ X 0) (mul : ∀ i j, X i ⊗ X j ⟶ X (i + j))
  (one_mul : ∀ n, (one ▷ X n) ≫ mul 0 n = (λ_ (X n)).hom ≫ eqToHom (congrArg X (zero_add n).symm))
  (mul_one : ∀ n, (X n ◁ one) ≫ mul n 0 = (ρ_ (X n)).hom ≫ eqToHom (congrArg X (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ X k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (X i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg X (add_assoc i j k).symm))

/-- The monoid object structure on a graded object `X` given by a unit `one : 𝟙_ C ⟶ X 0` and
homogeneous multiplications `mul i j : X i ⊗ X j ⟶ X (i + j)` satisfying the graded unit and
associativity laws, in which the degrees are identified along `0 + n = n`, `n + 0 = n` and
`i + (j + k) = i + j + k`. -/
abbrev monObjOfHomogeneous :
    MonObj X where
  one := Monoidal.oneOfDegreeZero X one
  mul := Monoidal.mulOfHomogeneous X mul
  one_mul := by
    rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id]
    ext n
    -- The inverse left unitor of graded objects includes `𝟙_ C ⊗ X n` as the summand `(0, n)`,
    -- and right whiskering of graded objects is `Monoidal.tensorHom`.
    change ((Monoidal.leftUnitor X).inv ≫
      Monoidal.tensorHom (Monoidal.oneOfDegreeZero X one) (𝟙 X) ≫
        Monoidal.mulOfHomogeneous X mul) n = 𝟙 _
    simp [Monoidal.leftUnitor_inv_apply, reassoc_of% one_mul n]
  mul_one := by
    rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id]
    ext n
    -- The inverse right unitor of graded objects includes `X n ⊗ 𝟙_ C` as the summand `(n, 0)`,
    -- and left whiskering of graded objects is `Monoidal.tensorHom`.
    change ((Monoidal.rightUnitor X).inv ≫
      Monoidal.tensorHom (𝟙 X) (Monoidal.oneOfDegreeZero X one) ≫
        Monoidal.mulOfHomogeneous X mul) n = 𝟙 _
    simp [Monoidal.rightUnitor_inv_apply, reassoc_of% mul_one n]
  mul_assoc := by
    ext n
    refine Monoidal.tensorObj₃'_ext _ _ fun i j k h ↦ ?_
    -- The associator of graded objects is `Monoidal.associator`, which sends the summand
    -- `(X i ⊗ X j) ⊗ X k` to `X i ⊗ (X j ⊗ X k)` by the associator of `C`; whiskering of
    -- graded objects is `Monoidal.tensorHom`.
    change Monoidal.ιTensorObj₃' X X X i j k n h ≫ (Monoidal.tensorHom
        (Monoidal.mulOfHomogeneous X mul) (𝟙 X) ≫ Monoidal.mulOfHomogeneous X mul) n =
      Monoidal.ιTensorObj₃' X X X i j k n h ≫ (Monoidal.associator X X X).hom n ≫
        (Monoidal.tensorHom (𝟙 X) (Monoidal.mulOfHomogeneous X mul) ≫
          Monoidal.mulOfHomogeneous X mul) n
    rw [Monoidal.ιTensorObj₃'_associator_hom_assoc,
      Monoidal.ιTensorObj₃'_eq X X X i j k n h (i + j) rfl,
      Monoidal.ιTensorObj₃_eq X X X i j k n h (j + k) rfl]
    simp [← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc, reassoc_of% mul_assoc i j k]

end MonObj
end AddMonoid
end CategoryTheory.GradedObject
end
end
