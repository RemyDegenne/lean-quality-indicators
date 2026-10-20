@[expose] public section

universe u

variable {α : Type u} {r : α → α → Prop}

namespace WellFounded

variable {α : Type u} (r : α → α → Prop) [WellFounded r]

/-- An arbitrary well order on `α` that extends `r`.

The construction maps `r` into two well-orders: the first map is `WellFounded.rank`, which is not
necessarily injective but respects the order `r`; the other map is the identity (with an arbitrarily
chosen well-order on `α`), which is injective but doesn't respect `r`.

By taking the lexicographic product of the two, we get both properties, so we can pull it back and
get a well-order that extend our original order `r`. Another way to view this is that we choose an
arbitrary well-order to serve as a tiebreak between two elements of same rank.
-/
@[instance_reducible]
noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective congr($(h).snd)

end WellFounded
end
