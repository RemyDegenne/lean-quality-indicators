public section

open MeasureTheory FourierTransform

open scoped ENNReal FourierTransform

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The tensor-valued physical Bessel symbol obtained by scaling a tensor by the inverse weight. -/
@[expose]
def physicalTensorBesselSymbol
    (s : ℝ) (p : L2Vec3 × ComplexTensor3) : ComplexTensor3 :=
  physicalBesselInverseWeight s p.1 • p.2

end CKN.Leray
end
end
