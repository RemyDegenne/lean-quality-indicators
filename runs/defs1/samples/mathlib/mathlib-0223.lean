@[expose] public section

open CategoryTheory

open scoped Simplicial

namespace SemiSimplexCategory

scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

/-- Constructor for morphisms in `SemiSimplexCategory` which takes as an input
a monomorphism in `SimplexCategory`. -/
def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

end SemiSimplexCategory
end
