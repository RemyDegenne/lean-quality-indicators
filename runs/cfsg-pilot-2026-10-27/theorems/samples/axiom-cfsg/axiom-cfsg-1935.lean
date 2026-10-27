public section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.GroupActions.Exchange

namespace ChamberSystem

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}

variable {C : Type*} {X : ChamberSystem ι C}

variable (hres : ∀ s t : ι, s ≠ t → ∀ y : C, X.IsResidueBuilding cs {s, t} y)

include hres

theorem nfStep_spec {a : C} {ρ : List (ι × C)} (hρ : X.IsReducedOrdinary cs a ρ) {i : ι} {y : C}
    (hy : X.adj i (galleryEnd a ρ) y) :
    X.IsReducedOrdinary cs a (X.nfStep cs a ρ i y) ∧ galleryEnd a (X.nfStep cs a ρ i y) = y := by
  by_cases h1 : y = galleryEnd a ρ
  · rw [nfStep_of_eq h1]
    exact ⟨hρ, h1.symm⟩
  rcases cs.length_mul_simple (cs.wordProd (galleryType ρ)) i with h2 | h2
  · rw [nfStep_of_lt h1 h2]
    refine ⟨⟨(isOrdinary_concat a ρ (i, y)).mpr ⟨hρ.1, hy, Ne.symm h1⟩, ?_⟩, by simp⟩
    rw [CoxeterSystem.IsReduced, galleryType_append, cs.wordProd_append]
    simp [h2, hρ.2.eq]
  · obtain ⟨ρ₁, z, h3, h4⟩ := nfStep_of_gt hres hρ h1 h2
    have h5 := h3.isReducedOrdinary_iff.mp hρ
    have hend : galleryEnd a ρ = z := by rw [h3.galleryEnd_eq, galleryEnd_concat]
    obtain ⟨-, h6, -⟩ := (isOrdinary_concat a ρ₁ (i, z)).mp h5.1
    rcases h4 with ⟨h7, h8⟩ | ⟨h7, h8⟩
    · rw [h8]
      exact ⟨h5.of_append_left, h7.symm⟩
    · rw [h8]
      refine ⟨⟨(isOrdinary_concat a ρ₁ (i, y)).mpr ⟨h5.1.isGallery.of_append_left |>
        fun _ => ((isOrdinary_append a ρ₁ _).mp h5.1).1, adj_trans h6 (hend ▸ hy), Ne.symm h7⟩,
        ?_⟩, by simp⟩
      have := h5.2
      simpa [galleryType_append] using this

end ChamberSystem
end CFSG.Monster.B.Geometry
end
