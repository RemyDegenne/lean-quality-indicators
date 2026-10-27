@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe uC' uC uD' uD

variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]

variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

namespace BinaryBicones

variable (P Q : C) (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]

/-- A functor `F : C ⥤ D` sends binary bicones for `P` and `Q`
to binary bicones for `G.obj P` and `G.obj Q` functorially. -/
@[simps]
def functoriality : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  obj A :=
    { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

end BinaryBicones
end CategoryTheory.Limits
end
end
