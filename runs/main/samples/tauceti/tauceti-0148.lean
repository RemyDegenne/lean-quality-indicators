public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u

variable (k : Type u) [Field k] (n : ℕ)

theorem hom_eq_unit_comp_counit {C : _root_.CommHopfAlgCat.{u} k}
    [Coalgebra.IsCocomm k C] (f : C ⟶ coordinateHopfAlgebra k n) :
    f = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom k (coordinateHopfAlgebra k n)).comp
        (Bialgebra.counitBialgHom k C)) := by
  let _ : Algebra.IsGeometricallyReduced k (coordinateHopfAlgebra k n) :=
    isGeometricallyReduced_of_smooth k _
  exact (_root_.CommHopfAlgCat.derivedDefiningIdeal_eq_bot_iff_forall_hom_eq_unit_comp_counit
    (coordinateHopfAlgebra k n)).mp (derivedDefiningIdeal_eq_bot k n) C f

end TauCeti.SpecialLinear
end
