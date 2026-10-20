@[expose] public section

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff

open NavierStokes.ProfileHistories

namespace NavierStokes.ModulatedProfileAssembly

namespace Witness

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
    {d : LoopData W} (v : Witness d)

theorem positive_f {p : Point} (hX : 0 < p.1) (heta : p.2 ∈ Icc (-1 : ℝ) 1) :
    0 < v.profiles.f p := by
  by_cases hp : p.1 ∈ Icc d.modulation.left (repairPatch W).right
  · exact (v.true_cone p ⟨hp, d.parameters_contains heta⟩).1
  · have hn : p.1 ∉ Ioo d.modulation.left (repairPatch W).right :=
      fun hx => hp ⟨hx.1.le, hx.2.le⟩
    rw [(v.fields_outside hn).1]
    exact NominalConeAssembly.Witness.f_positive W hX heta

end Witness
end NavierStokes.ModulatedProfileAssembly
end
end
