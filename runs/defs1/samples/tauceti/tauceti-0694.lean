public section

namespace TauCeti

universe u

/-- The one-vertex plumbing with framing `w`: a single sphere of self-intersection `w`. For
`w < 0` its boundary three-manifold is the lens space `L(-w, 1)`. -/
def oneVertexPlumbing (w : ℤ) : PlumbingGraph (Fin 1) where
  toSimpleGraph := ⊥
  decidableAdj := inferInstance
  weight := fun _ => w

end TauCeti
end
