@[expose] public section

noncomputable section

open Set Filter MeasureTheory

open scoped Topology ContDiff

open NavierStokes.ProfileHistories

namespace NavierStokes.ModulatedProfileAssembly

theorem regularDomain_open {D : RadialDomain} (P : Profiles D) (h : ℝ) :
    IsOpen (regularDomain P h) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hf := (P.f_smooth.contDiffAt (D.isOpen.mem_nhds hp.1)).continuousAt
  have ha := (NominalConeAssembly.shears_smoothAt P hp.1 hp.2.1 hp.2.2.1.ne').1.continuousAt
  have hL : Continuous (fun q : Point => NaturalAxisData.L h q.2) := by
    exact continuous_const.sub ((continuous_const.mul continuous_const).mul (continuous_snd.pow 2))
  filter_upwards [D.isOpen.mem_nhds hp.1,
    continuous_fst.continuousAt.eventually (lt_mem_nhds hp.2.1),
    hf.eventually (lt_mem_nhds hp.2.2.1), ha.eventually (lt_mem_nhds hp.2.2.2.1),
    (isOpen_ne.preimage hL).mem_nhds hp.2.2.2.2] with q hq hx hqf hqa hqL
  exact ⟨hq, hx, hqf, hqa, hqL⟩

end NavierStokes.ModulatedProfileAssembly
end
end
