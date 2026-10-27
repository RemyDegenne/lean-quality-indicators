public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan.TitsChamber

variable {I I' C D : Type*} {X : ChamberSystem I C} {Y : ChamberSystem I' D}

theorem connected_of_isTypeMorphism {τ : I → I'} {f : C → D} (hf : IsTypeMorphism X Y τ f)
    (hfs : Function.Surjective f) (hX : X.Connected) : Y.Connected := by
  intro a b
  obtain ⟨x, rfl⟩ := hfs a
  obtain ⟨y, rfl⟩ := hfs b
  obtain ⟨γ, hγ, hend⟩ := hX x y
  exact ⟨galleryMapT τ f γ, hf.isGallery hγ, by rw [galleryEnd_galleryMapT, hend]⟩

end CFSG.ClassicalInvolution.PhanG
end
