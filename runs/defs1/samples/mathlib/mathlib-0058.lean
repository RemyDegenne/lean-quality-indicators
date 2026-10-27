@[expose] public section

universe u

open CategoryTheory Limits

namespace CompHausLike

variable {P : TopCat.{u} → Prop} (X Y : CompHausLike.{u} P)

section Coproduct

variable [HasProp P (X ⊕ Y)]

/--
Explicit binary cofan in `CompHausLike P`, given that the predicate `P` is preserved under taking
type-theoretic sums.
-/
def coproductCocone : BinaryCofan X Y := BinaryCofan.mk (P := ↧(X ⊕ Y))
  (ofHom _ { toFun := Sum.inl }) (ofHom _ { toFun := Sum.inr })

end Coproduct
end CompHausLike
end
