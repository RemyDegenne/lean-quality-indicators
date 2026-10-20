@[expose] public section

universe uR

theorem Units.isEmbedding_val_seminormedRing
    {R : Type uR} [SeminormedRing R] :
    Topology.IsEmbedding (Units.val : Rˣ → R) := by
  let c : R →+* UniformSpace.Completion R := UniformSpace.Completion.coeRingHom
  have hc : Topology.IsInducing c :=
    (UniformSpace.Completion.isUniformInducing_coe R).isInducing
  have hcomp : Topology.IsInducing (c ∘ (Units.val : Rˣ → R)) :=
    (Units.isOpenEmbedding_val (R := UniformSpace.Completion R)).isInducing.comp
      (Topology.IsInducing.units_map (f := c.toMonoidHom) hc)
  exact ⟨Topology.IsInducing.of_comp Units.continuous_val
    UniformSpace.Completion.continuous_coeRingHom hcomp, Units.val_injective⟩

end
