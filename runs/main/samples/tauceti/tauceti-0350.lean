public section

namespace PowerSeries

section LinearFactor

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [T2Space A] [CompleteSpace A] [IsLinearTopology A A] {c : A}

theorem X_sub_C_mul_divXSubC (hc : HasEval c) {f : A⟦X⟧} (hf : aeval hc f = 0) :
    (X - C c) * divXSubC hc f = f := by
  simpa [hf] using X_sub_C_mul_divXSubC_add_C_aeval hc f

end LinearFactor
end PowerSeries
end
