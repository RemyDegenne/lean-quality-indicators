@[expose] public section

universe u w

open CategoryTheory Limits LocallyConstant TopologicalSpace.Fiber Opposite Function Fiber

variable {P : TopCat.{u} → Prop}

namespace CompHausLike.LocallyConstant

section Adjunction

variable [∀ (S : CompHausLike.{u} P) (p : S → Prop), HasProp P (Subtype p)]

variable {S : CompHausLike.{u} P} {Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type (max u w)}
  [HasProp P PUnit.{u + 1}] (f : LocallyConstant S (Y.obj (op ↧PUnit.{u + 1})))

variable {T : CompHausLike.{u} P} (g : T ⟶ S)

variable (P) (X : TopCat.{max u w})
    [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/--
`CompHausLike.LocallyConstant.functor` is naturally isomorphic to the restriction of
`topCatToSheafCompHausLike` to discrete topological spaces.
-/
noncomputable def functorIso :
    functor.{u, w} P hs ≅ TopCat.discrete.{max w u} ⋙ topCatToSheafCompHausLike P hs :=
  NatIso.ofComponents (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIso P hs X))

end Adjunction
end CompHausLike.LocallyConstant
end
