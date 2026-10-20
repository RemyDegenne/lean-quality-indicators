public section

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-- The pinned simply connected root datum of type `E₇`.

Both lattices are `Fin 7 → ℤ`: the character lattice in the fundamental-weight basis and the
cocharacter lattice in the simple-coroot basis. Root indices `0` through `6` are the Bourbaki
simple roots; see `TauCeti.DynkinType.root_e7SimpleIndex`. -/
noncomputable def e7SimplyConnectedRootDatum : RootDatum (Fin 126) (Fin 7 → ℤ) (Fin 7 → ℤ) :=
  RootPairing.mk' (dotProductEquiv ℤ (Fin 7)).toLinearMap e7Root e7Coroot
    e7Root_dotProduct_coroot
    (by
      rintro i _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_e7Coroot_reflection i j
      refine ⟨k, ?_⟩
      have hroot : e7Root k =
          e7Root j - (e7Root i ⬝ᵥ e7Coroot j) • e7Root i := by
        simpa only [sub_vecMul, smul_vecMul, ← e7Root_apply] using
          congrArg (fun x : Fin 7 → ℤ ↦ x ᵥ* CartanMatrix.E 7) hk
      rw [e7Root_dotProduct_e7Coroot_comm] at hroot
      simpa [Module.preReflection_apply, dotProductEquiv_apply_apply] using hroot)
    (by
      rintro i _ ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := exists_e7Coroot_reflection i j
      refine ⟨k, ?_⟩
      simpa [Module.preReflection_apply, dotProductEquiv_apply_apply] using hk)

end DynkinType
end TauCeti
end
