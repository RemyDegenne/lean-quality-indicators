@[expose] public section

universe u w v v'

/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[pp_with_univ, no_expose]
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.choose (@Small.equiv_small α _)

end
