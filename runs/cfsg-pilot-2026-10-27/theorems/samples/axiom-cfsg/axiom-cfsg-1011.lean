public section

namespace CFSG.AGLEmbedding

variable {A V : Type*} [CommGroup A] [CommGroup V] [MulDistribMulAction A V]

theorem fixedPiece_le_actCommutator {F F' : Subgroup A} (h : F ⊔ F' = ⊤) :
    (fixedPiece F : Subgroup V) ≤ actCommutator (⊤ : Subgroup V) F' :=
  actCommutator_le fun u hu a _ => by
    have ha : a ∈ F ⊔ F' := h ▸ Subgroup.mem_top a
    obtain ⟨b, hb, b', hb', rfl⟩ := Subgroup.mem_sup.mp ha
    rw [mul_comm b b', mul_smul, hu b hb]
    exact mem_actCommutator (Subgroup.mem_top u) hb'

end CFSG.AGLEmbedding
end
