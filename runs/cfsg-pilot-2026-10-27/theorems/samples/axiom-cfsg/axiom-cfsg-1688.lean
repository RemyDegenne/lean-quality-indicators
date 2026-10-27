public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

section Action

variable (B : Subgroup (OGroup Q)) [Fintype ↥B] [DecidableEq ↥B] (f : OGroup Q)
  (hf : ∀ g, g ∈ B ↔ f * g * f⁻¹ ∈ B)

theorem fgWt_map_f (χ : ↥B → ZMod 3) :
    (fgWt (fgT B) χ).map (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) =
      fgWt (fgT B) (fgPerm B (ZMod 3) (fgCj B f hf) χ) := by
  apply le_antisymm
  · exact fgWt_map_le (fgT B) ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) (fgCj B f hf).toEquiv
      (fun g v => fgT_conj B f hf g v) χ
  · intro v hv
    set e : V ≃ₗ[ZMod 3] V := ((f⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) with he
    have hfe : ∀ w : V, ((f : OGroup Q) : V ≃ₗ[ZMod 3] V) (e w) = w := fun w => by
      show ((f * f⁻¹ : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w
      simp
    have hef : ∀ w : V, e (((f : OGroup Q) : V ≃ₗ[ZMod 3] V) w) = w := fun w => by
      show ((f⁻¹ * f : OGroup Q) : V ≃ₗ[ZMod 3] V) w = w
      simp
    have hint : ∀ (g : ↥B) (w : V),
        fgT B ((fgCj B f hf).toEquiv.symm g) (e w) = e (fgT B g w) := by
      intro g w
      have h1 := fgT_conj B f hf ((fgCj B f hf).toEquiv.symm g) (e w)
      rw [hfe] at h1
      have h2 : fgCj B f hf ((fgCj B f hf).toEquiv.symm g) = g := (fgCj B f hf).apply_symm_apply g
      rw [h2] at h1
      rw [h1, hef]
    have h1 := fgWt_map_le (fgT B) e (fgCj B f hf).toEquiv.symm hint
      (fgPerm B (ZMod 3) (fgCj B f hf) χ) ⟨v, hv, rfl⟩
    have h3 : (fun i => (fgPerm B (ZMod 3) (fgCj B f hf) χ)
        ((fgCj B f hf).toEquiv.symm.symm i)) = χ := by
      funext i
      simp [fgPerm_apply]
    rw [h3] at h1
    exact ⟨e v, h1, hfe v⟩

end Action
end CFSG.OddStandard.SmallF3.Omega
end
