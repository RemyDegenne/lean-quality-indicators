@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff

open NavierStokes.ProfileHistories

open NavierStokes.OutgoingProfile

open NavierStokes.NominalProfile (AxisStage Controls SmallDebt)

open NavierStokes.StressActivation

namespace NavierStokes.NominalConeAssembly

namespace Witness

variable {F : Profile} (W : NominalProfile.Witness F)

theorem prefix_coordinates {p : Point} (hp : p ∈ W.domain.carrier)
    (hX : 0 < p.1) (hR : p.1 ≤ W.controls.heatJoin)
    (hf : W.controls.f p ≠ 0) :
    ActivationContinuation.shearA W.profiles p =
        ActivationContinuation.shearA (W.controls.profiles W.separated) p ∧
      ActivationContinuation.shearB W.profiles p =
        ActivationContinuation.shearB (W.controls.profiles W.separated) p ∧
      ReferenceBounds.p1 W.profiles F.data.h p =
        ReferenceBounds.p1 (W.controls.profiles W.separated) F.data.h p ∧
      ReferenceBounds.p2 W.profiles F.data.h p =
        ReferenceBounds.p2 (W.controls.profiles W.separated) F.data.h p :=
  coordinates_of_prefix W.profiles (W.controls.profiles W.separated) F.data.h isOpen_univ rfl
    (fun _ _ hq => prefix_f W hq) (fun _ _ _ => rfl) hp hp.1 hX hR (mem_univ _) hf

end Witness
end NavierStokes.NominalConeAssembly
end
end
