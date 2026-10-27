@[expose] public section

open Filter Function MeasureTheory Set

open scoped ENNReal Topology

namespace QuadraticCarleson

namespace HilbertMaximalWeakOneOne

open HilbertFiniteTruncationWeakOneOne

open HilbertL2Fourier

open CalderonZygmundDyadicStopping

noncomputable
section

/-- The canonical pointwise representative of the Fourier-side Hilbert
transform of the stopping good part. -/
noncomputable def stoppingGoodHilbertL2Representative
    (f : ℝ → ℂ) (hf : Integrable f) : ℝ → ℂ :=
  ⇑(ordinaryHilbertTransformL2 (stoppingGoodPartL2 f hf))

end
end HilbertMaximalWeakOneOne
end QuadraticCarleson
end
