@[expose] public section

open scoped MonoidAlgebra

universe t w w' u u' v v'

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (A : Rep.{w} k G)

section

variable {G H : Type u} [Group G] [Group H] (φ : G →* H) (A : Rep k G) (B : Rep k H)

open Representation

set_option backward.defeqAttrib.useBackward true in
/-- Given a group hom `φ : G →* H` and `A : Rep k G`, the functor `Rep k H ⥤ ModuleCat k` sending
`B ↦ (Ind(φ)(A) ⊗ B)_H` is naturally isomorphic to the one sending `B ↦ (A ⊗ Res(φ)(B))_G`. -/
@[simps! hom_app inv_app]
noncomputable def coinvariantsTensorIndNatIso :
    (coinvariantsTensor k H).obj (ind φ A) ≅ resFunctor φ ⋙ (coinvariantsTensor k G).obj A :=
  NatIso.ofComponents (fun B => coinvariantsTensorIndIso φ A B) fun {X Y} f => by
    ext
    simp [coinvariantsTensorIndHom, coinvariantsTensorMk, hom_comm_apply]

end
end Rep
end
