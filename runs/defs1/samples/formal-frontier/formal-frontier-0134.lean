@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite

universe v u w

namespace CategoryTheory.IsMonHom

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {H G : C} [GrpObj H] [GrpObj G] (i : H ⟶ G) [IsMonHom i]

variable {Q : C} (q : G ⟶ Q)

/-- A morphism `q : G ⟶ Q` whose self-pullback is the right action of `H`
induces a map from the pointwise left-coset presheaf to the functor represented
by `Q`. The target need not carry a group structure. -/
noncomputable def yonedaCosetMap
    (h : IsPullback (fst G H) ((𝟙 G ⊗ₘ i) ≫ μ[G]) q q) :
    yonedaCoset i ⟶ yoneda.obj Q :=
  NatTrans.cosetLift _ (yoneda.map q) (yonedaCosetMap_rel i q h)

end CategoryTheory.IsMonHom
end
end
