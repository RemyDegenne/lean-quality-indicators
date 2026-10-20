public section

set_option autoImplicit false

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}

variable (A : Rep.{u} R G) (L : LevelCompact A)

local instance : Nonempty (OpenNormalSubgroup G) := ⟨fullOpenNormalSubgroup G⟩

local instance : IsConnected (OpenNormalSubgroup G) :=
  IsCofiltered.isConnected (OpenNormalSubgroup G)

noncomputable local instance :
    HasLimitsOfShape (OpenNormalSubgroup G) CompHausAddCommGrp.{u} :=
  ⟨fun _ => inferInstance⟩

theorem compactTateLimit_exact_right :
    Function.Exact (compactTateLimitNorm A L)
      (compactTateLimitProjection A L) := by
  have he := CompHausAddCommGrp.limit_map_exact.{u,u}
    (compactFiniteCoinvariantsDiagram A L)
    (compactTotalInvariantsDiagram A L)
    (compactFiniteTateNorm A L)
    (compactFiniteZeroDeflationDiagram A L)
    (compactFiniteTateZeroProjection A L)
    (fun S => finiteTateNorm_exact_right A L S)
  intro x
  constructor
  · intro hx
    have hy : lim.map (compactFiniteTateZeroProjection A L)
        ((compactTotalInvariantsLimitIso A L).inv x) = 0 := hx
    obtain ⟨y, hy⟩ := (he _).mp hy
    exact ⟨y, by
      change (compactTotalInvariantsLimitIso A L).hom
        (lim.map (compactFiniteTateNorm A L) y) = x
      rw [hy]
      exact Iso.inv_hom_id_apply _ _⟩
  · rintro ⟨y, rfl⟩
    exact (he _).mpr ⟨y, by
      change lim.map (compactFiniteTateNorm A L) y =
        (compactTotalInvariantsLimitIso A L).inv
          ((compactTotalInvariantsLimitIso A L).hom
            (lim.map (compactFiniteTateNorm A L) y))
      exact (Iso.hom_inv_id_apply (compactTotalInvariantsLimitIso A L) _).symm⟩

end ContinuousGroupCohomology.LevelCompact
end
end
