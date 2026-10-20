public section

set_option warningAsError true

namespace Matrix

variable (ι : Type*) [LinearOrder ι]

@[simp]
theorem upperTriangularIndicesEquiv_strict (p : {p : ι × ι // p.1 < p.2}) :
    upperTriangularIndicesEquiv ι ⟨p.1, p.2.le⟩ = Sum.inr p := by
  simp [upperTriangularIndicesEquiv, ne_of_lt p.2]

end Matrix
end
