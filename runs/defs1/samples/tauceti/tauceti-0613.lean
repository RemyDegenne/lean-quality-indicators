public section

namespace TauCeti.QuiverRep

open CategoryTheory

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

variable (M N : QuiverRep.{u, v, w, t} k Q)

/-- The arrowwise commutativity defect of a family of vertex maps. -/
noncomputable def homDifferential : HomVertex M N →ₗ[k] HomArrow M N where
  toFun f i j a := (mapₗ k Q N a.toPath).comp (f i) -
    (f j).comp (mapₗ k Q M a.toPath)
  map_add' f g := by
    ext i j a x
    simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add,
      LinearMap.sub_apply]
    abel
  map_smul' c f := by
    ext i j a x
    simp [smul_sub]

end TauCeti.QuiverRep
end
