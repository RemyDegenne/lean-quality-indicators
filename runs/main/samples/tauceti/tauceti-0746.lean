public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

theorem monoidalPreadditive_of_monoidalClosed (D : Type*) [Category* D] [Preadditive D]
    [HasBinaryCoproducts D] [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D] :
    MonoidalPreadditive D := by
  let _ : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryCoproducts
  have (X : D) : (tensorLeft X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
    Functor.additive_of_preservesBinaryBiproducts _
  have (X : D) : (tensorRight X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
    Functor.additive_of_preservesBinaryBiproducts _
  exact
    { whiskerLeft_zero := (tensorLeft _).map_zero _ _
      zero_whiskerRight := (tensorRight _).map_zero _ _
      whiskerLeft_add _ _ := (tensorLeft _).map_add
      add_whiskerRight _ _ := (tensorRight _).map_add }

end TauCeti
end
