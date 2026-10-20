public section

namespace IntermediateField

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower K L M]

-- Not `@[simp]`: it and `extendRight_adjoin_simple_le_iff` below cannot both be, since this
-- rewrites that one's left-hand side and `simpNF` rejects the pair. The simple-extension form
-- is the one worth reaching automatically, so it keeps the attribute and this is used by name.
theorem extendRight_le_iff {F : IntermediateField K L} {E : IntermediateField K M} :
    F.extendRight M ≤ E ↔ ∀ x ∈ F, algebraMap L M x ∈ E := by
  rw [extendRight_eq_map]
  simp only [IsConcreteLE.le_iff, mem_map, forall_exists_index, and_imp]
  exact ⟨fun h x hx => h x hx (congrFun (IsScalarTower.coe_toAlgHom' K L M) x),
    fun h _ x hx hxz => hxz ▸ h x hx⟩

end IntermediateField
end
