namespace WeierstrassCurve

universe u v

variable {F : Type u} [Field F] (k : Type v) [Field k] [Algebra F k] [DecidableEq k]

theorem zero_mem_kernelIdealSet (W₀ W : WeierstrassCurve F)
    (χ : (W₀.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    (0 : rationalEndSubring k W₀) ∈ kernelIdealSet k W₀ W χ :=
  ⟨0, zero_mem_rationalHomSet k W W₀, by rw [AddMonoidHom.zero_comp]; rfl⟩

end WeierstrassCurve
