public section

namespace CategoryTheory.Functor

open Limits

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w'} D] [Preadditive C]
  [Preadditive D] (F : C ⥤ D) [F.Additive]

section Op

open Opposite

variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{w'} D] [HasZeroMorphisms C]
  [HasZeroMorphisms D] (F : Cᵒᵖ ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]
  [F.PreservesZeroMorphisms] [PreservesBinaryBiproduct (op X) (op Y) F]

theorem mapIso_biprod_opIso_trans_mapBiprod_inv :
    (F.mapIso (biprod.opIso X Y) ≪≫ F.mapBiprod (op X) (op Y)).inv =
      biprod.desc (F.map (biprod.fst : X ⊞ Y ⟶ X).op) (F.map (biprod.snd : X ⊞ Y ⟶ Y).op) := by
  rw [Iso.trans_inv, Functor.mapIso_inv, Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, ← F.map_comp, biprod.inl_opIso_inv, biprod.inl_desc]
  · rw [biprod.inr_desc_assoc, ← F.map_comp, biprod.inr_opIso_inv, biprod.inr_desc]

end Op
end CategoryTheory.Functor
end
