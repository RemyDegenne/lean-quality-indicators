@[expose] public section

open scoped MonoidAlgebra

universe t w w' u u' v v'

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H] (φ : G →* H)
  (A : Rep.{w} k G)

section Ind

variable (k) in
/-- Given a group homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the induced `H`-representation `ind φ A`, with action on maps induced by left tensoring. -/
@[implicit_reducible, simps obj map]
noncomputable def indFunctor : Rep.{w} k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

end Ind
end Rep
end
