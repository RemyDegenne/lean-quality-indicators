@[expose] public section

universe u v

theorem DenseRange.units_map
    {M : Type u} {N : Type v} [Monoid M] [Monoid N] [TopologicalSpace N]
    {f : M →* N} [IsLocalHom f] (hf : DenseRange f)
    (hval : Topology.IsOpenEmbedding (Units.val : Nˣ → N)) :
    DenseRange (Units.map f) := by
  have hd : Dense ((Units.val : Nˣ → N) ⁻¹' Set.range f) :=
    Dense.preimage hf hval.isOpenMap
  refine hd.mono ?_
  rintro u ⟨m, hm⟩
  have hfm : IsUnit (f m) := ⟨u, hm.symm⟩
  obtain ⟨v, hv⟩ := (isUnit_map_iff f m).mp hfm
  refine ⟨v, Units.ext ?_⟩
  exact (Units.coe_map f v).trans ((congrArg f hv).trans hm)

end
