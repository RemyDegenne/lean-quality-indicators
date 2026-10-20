@[expose] public section

noncomputable section

universe v u

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open CategoryTheory.GlueData

namespace AlgebraicGeometry

namespace Scheme

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

local notation "D_" => TopCat.GlueData.toGlueData
  D.toLocallyRingedSpaceGlueData.toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

/-- The open cover of the glued space given by the glue data. -/
@[simps -isSimp]
def openCover (D : Scheme.GlueData) : OpenCover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨D.ι_jointly_surjective, inferInstance⟩

end GlueData
end Scheme
end AlgebraicGeometry
end
end
