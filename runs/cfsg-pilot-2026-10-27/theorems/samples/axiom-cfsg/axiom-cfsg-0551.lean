public section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding

section Cover

variable {I C : Type*} {X : ChamberSystem I C} {c₀ : C}

theorem adj_iff_of_pi2_eq_bot (hK : X.pi2 c₀ = ⊥) (i : I) (A B : X.Cover c₀) :
    (X.universalCover c₀).adj i A B ↔ X.adj i (X.coverProj c₀ A) (X.coverProj c₀ B) := by
  refine ⟨ChamberSystem.isMorphism_coverProj i A B, fun h => ?_⟩
  have hB : X.coverProj c₀ B ∈ X.residue {i} (X.coverProj c₀ A) :=
    ChamberSystem.mem_residue_singleton.2 h
  obtain ⟨B', hB', hBB'⟩ := (ChamberSystem.bijOn_coverProj_panel i A).surjOn hB
  have hBeq : B' = B := coverProj_injective_of_pi2_eq_bot hK hBB'
  rw [← hBeq]
  exact ChamberSystem.mem_residue_singleton.1 hB'

end Cover
end CFSG.Monster.B.TwoA.Amalgam
end
