public section

open scoped Matrix

namespace TauCeti

namespace AffineDynkinType

@[simp] theorem starIndexEquivE8_symm_apply (v : Fin 9) :
    (@Equiv.symm (StarIndex ![1, 2, 5]) (Fin 9) starIndexEquivE8) v =
      ![none, some ⟨0, ⟨0, by decide⟩⟩, some ⟨1, ⟨0, by decide⟩⟩,
        some ⟨1, ⟨1, by decide⟩⟩, some ⟨2, ⟨0, by decide⟩⟩,
        some ⟨2, ⟨1, by decide⟩⟩, some ⟨2, ⟨2, by decide⟩⟩,
        some ⟨2, ⟨3, by decide⟩⟩, some ⟨2, ⟨4, by decide⟩⟩] v := by
  fin_cases v <;> apply starIndexEquivE8.symm_apply_eq.mpr <;> rfl

end AffineDynkinType
end TauCeti
end
