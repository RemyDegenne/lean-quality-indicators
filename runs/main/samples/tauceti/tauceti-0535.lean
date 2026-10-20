public noncomputable section

open CategoryTheory Representation

namespace TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [TotallyDisconnectedSpace G']

namespace NormalLayer

variable (L : NormalLayer G) (f : G →* G')

variable {F : Formation G} {F' : Formation G'}

theorem mapCoeffEquiv_rep_mk (hf : IsOpenMap f) (hfi : Function.Injective f)
    (e : TopRep.res f F'.module ≅ F.module) (u : L.ground) (x : F.level L.top) :
    L.mapCoeffEquiv f hf e ((L.rep F).ρ (QuotientGroup.mk u) x) =
      ((L.map f hf).rep F').ρ
        (QuotientGroup.mk (L.mapGroundEquiv f hf hfi u)) (L.mapCoeffEquiv f hf e x) := by
  apply Subtype.ext
  rw [mapCoeffEquiv_apply_coe, NormalLayer.rep_ρ_mk_apply_coe,
    NormalLayer.rep_ρ_mk_apply_coe, mapCoeffEquiv_apply_coe, mapGroundEquiv_apply_coe]
  exact TopRep.hom_comm_apply e.inv u x.1

end NormalLayer
end TauCeti.ClassFieldTheory
end
