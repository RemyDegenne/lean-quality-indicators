@[expose] public section

open IsLocalRing

namespace ValuationSubring

universe u

variable {K : Type u} [Field K]

/-- The composite of a valuation subring `A` of a field with a valuation
subring `W` of the residue field of `A`. Its elements are exactly the elements
of `A` whose residue belongs to `W`. -/
noncomputable def composite (A : ValuationSubring K)
    (W : ValuationSubring (ResidueField A)) : ValuationSubring K where
  carrier := {x | ∃ hx : x ∈ A, residue A ⟨x, hx⟩ ∈ W}
  zero_mem' := ⟨A.zero_mem, by
    change residue A (0 : A) ∈ W
    simp⟩
  one_mem' := ⟨A.one_mem, by
    change residue A (1 : A) ∈ W
    simp⟩
  add_mem' := by
    rintro x y ⟨hxA, hxW⟩ ⟨hyA, hyW⟩
    refine ⟨A.add_mem x y hxA hyA, ?_⟩
    change residue A (⟨x, hxA⟩ + ⟨y, hyA⟩) ∈ W
    simpa only [map_add] using W.add_mem _ _ hxW hyW
  neg_mem' := by
    rintro x ⟨hxA, hxW⟩
    refine ⟨A.neg_mem x hxA, ?_⟩
    change residue A (-⟨x, hxA⟩) ∈ W
    simpa only [map_neg] using W.neg_mem _ hxW
  mul_mem' := by
    rintro x y ⟨hxA, hxW⟩ ⟨hyA, hyW⟩
    refine ⟨A.mul_mem x y hxA hyA, ?_⟩
    change residue A (⟨x, hxA⟩ * ⟨y, hyA⟩) ∈ W
    simpa only [map_mul] using W.mul_mem _ _ hxW hyW
  mem_or_inv_mem' := by
    intro x
    by_cases hxA : x ∈ A
    · let xA : A := ⟨x, hxA⟩
      by_cases hxW : residue A xA ∈ W
      · exact Or.inl ⟨hxA, hxW⟩
      · right
        have hx0 : residue A xA ≠ 0 := fun h ↦ hxW (h ▸ W.zero_mem)
        have hxUnit : IsUnit xA := (residue_ne_zero_iff_isUnit xA).mp hx0
        obtain ⟨ux, hux⟩ := hxUnit
        have hInvW : (residue A xA)⁻¹ ∈ W :=
          (W.mem_or_inv_mem (residue A xA)).resolve_left hxW
        have huxK : ((ux : A) : K) = x := by
          simpa only [xA] using congrArg Subtype.val hux
        have huxInvK : ((↑(ux⁻¹) : A) : K) = x⁻¹ := by
          calc
            ((↑(ux⁻¹) : A) : K) =
                ↑(Units.map A.subtype.toMonoidHom (ux⁻¹)) :=
              (Units.coe_map A.subtype.toMonoidHom (ux⁻¹)).symm
            _ = ↑((Units.map A.subtype.toMonoidHom ux)⁻¹) := by rw [map_inv]
            _ = (↑(Units.map A.subtype.toMonoidHom ux) : K)⁻¹ :=
              Units.val_inv_eq_inv_val _
            _ = ((ux : A) : K)⁻¹ := by rfl
            _ = x⁻¹ := by rw [huxK]
        have hxInvA : x⁻¹ ∈ A := by
          rw [← huxInvK]
          exact (↑(ux⁻¹) : A).property
        refine ⟨hxInvA, ?_⟩
        have hxInvEq : (⟨x⁻¹, hxInvA⟩ : A) = ↑(ux⁻¹) := by
          ext
          exact huxInvK.symm
        rw [hxInvEq]
        have hResidueInv : residue A (↑(ux⁻¹) : A) = (residue A xA)⁻¹ := by
          calc
            residue A (↑(ux⁻¹) : A) =
                ↑(Units.map (residue A).toMonoidHom (ux⁻¹)) :=
              (Units.coe_map (residue A).toMonoidHom (ux⁻¹)).symm
            _ = ↑((Units.map (residue A).toMonoidHom ux)⁻¹) := by rw [map_inv]
            _ = (↑(Units.map (residue A).toMonoidHom ux) : ResidueField A)⁻¹ :=
              Units.val_inv_eq_inv_val _
            _ = (residue A (↑ux : A))⁻¹ := by rfl
            _ = (residue A xA)⁻¹ := by rw [hux]
        rw [hResidueInv]
        exact hInvW
    · right
      have hxInvNonunit : x⁻¹ ∈ A.nonunits :=
        A.inv_mem_nonunits_iff.mpr (Or.inr hxA)
      have hxInvA : x⁻¹ ∈ A := A.nonunits_subset hxInvNonunit
      refine ⟨hxInvA, ?_⟩
      rw [(residue_eq_zero_iff _).mpr (A.coe_mem_nonunits_iff.mp hxInvNonunit)]
      exact W.zero_mem

end ValuationSubring
end
