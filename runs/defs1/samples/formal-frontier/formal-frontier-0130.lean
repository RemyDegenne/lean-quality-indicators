set_option warningAsError true

@[expose] public section

universe uN uE uG vN vE vG

namespace GroupExtension

variable {N : Type uN} {E : Type uE} {G : Type uG}
  [Group N] [Group E] [Group G]

/-- Raise all three groups in a group extension through independently chosen
universes. -/
def ulift (S : GroupExtension N E G) :
    GroupExtension (ULift.{vN} N) (ULift.{vE} E) (ULift.{vG} G) where
  inl := MulEquiv.ulift.symm.toMonoidHom.comp (S.inl.comp MulEquiv.ulift.toMonoidHom)
  rightHom := MulEquiv.ulift.symm.toMonoidHom.comp
    (S.rightHom.comp MulEquiv.ulift.toMonoidHom)
  inl_injective := MulEquiv.ulift.symm.injective.comp
    (S.inl_injective.comp MulEquiv.ulift.injective)
  range_inl_eq_ker_rightHom := by
    ext e
    constructor
    · rintro ⟨n, rfl⟩
      simp [MonoidHom.mem_ker]
    · intro he
      rw [MonoidHom.mem_ker] at he
      have he' : S.rightHom e.down = 1 := by
        exact ULift.up_injective he
      rw [← MonoidHom.mem_ker, ← S.range_inl_eq_ker_rightHom,
        MonoidHom.mem_range] at he'
      obtain ⟨n, hn⟩ := he'
      exact ⟨ULift.up n, ULift.down_injective hn⟩
  rightHom_surjective g := by
    obtain ⟨e, he⟩ := S.rightHom_surjective g.down
    exact ⟨ULift.up e, ULift.down_injective he⟩

end GroupExtension
end
