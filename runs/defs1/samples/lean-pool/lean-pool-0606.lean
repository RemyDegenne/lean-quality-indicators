@[expose] public section

namespace BGS.Markoff

universe u

/-- The five standard generators of the Markoff group on the surface. -/
def gammaGenerators (R : Type u) [CommRing R] : Set (Equiv.Perm (MarkoffSurface R)) :=
  {vieta1SurfacePerm R, vieta2SurfacePerm R, vieta3SurfacePerm R, swap12SurfacePerm R,
    swap23SurfacePerm R}

end BGS.Markoff
end
