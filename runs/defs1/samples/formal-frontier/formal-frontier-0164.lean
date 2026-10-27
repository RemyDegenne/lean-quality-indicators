@[expose] public section

universe u v w

namespace CharacterModule

variable {A : Type u} [AddCommGroup A]

variable [TopologicalSpace A] [IsTopologicalAddGroup A]

section Restriction

variable {B : Type v} [AddCommGroup B]

variable {C : Type w} [AddCommGroup C]

variable [TopologicalSpace B] [IsTopologicalAddGroup B]

variable [TopologicalSpace C] [IsTopologicalAddGroup C]

/-- Continuous precomposition of open-kernel characters. -/
def openKernelRestrict (f : A →ₜ+ B) : openKernel B →+ openKernel A where
  toFun c := ⟨dual f.toAddMonoidHom.toIntLinearMap c, by
    change IsOpen ((dual f.toAddMonoidHom.toIntLinearMap
      (c : CharacterModule B)).ker : Set A)
    have hker : ((dual f.toAddMonoidHom.toIntLinearMap
        (c : CharacterModule B)).ker : Set A) =
        (f : A → B) ⁻¹' ((c : CharacterModule B).ker : Set B) := by
      ext a
      simp only [Set.mem_preimage, dual_apply]
      rfl
    rw [hker]
    exact c.property.preimage f.continuous⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (dual f.toAddMonoidHom.toIntLinearMap)
  map_add' c d := by
    apply Subtype.ext
    exact map_add (dual f.toAddMonoidHom.toIntLinearMap)
      (c : CharacterModule B) (d : CharacterModule B)

end Restriction
end CharacterModule
end
