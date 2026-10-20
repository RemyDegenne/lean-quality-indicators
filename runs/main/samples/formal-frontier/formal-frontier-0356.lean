@[expose] public section

universe v u

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] {X Y : C}

theorem conj_apply_eq_iff_commute (α β : X ≅ Y) (f : End X) :
    α.conj f = β.conj f ↔ Commute f (End.of (α.hom ≫ β.inv)) := by
  rw [commute_iff_eq, End.mul_def, End.mul_def]
  constructor
  · intro h
    have h' := congrArg (fun k : End Y => α.hom ≫ k ≫ β.inv) h
    simpa only [conj_apply, Category.assoc, hom_inv_id_assoc, hom_inv_id,
      Category.comp_id] using h'.symm
  · intro h
    have h' := congrArg (fun k : End X => α.inv ≫ k ≫ β.hom) h
    simpa only [conj_apply, Category.assoc, inv_hom_id_assoc, inv_hom_id,
      Category.comp_id] using h'.symm

end CategoryTheory.Iso
end
