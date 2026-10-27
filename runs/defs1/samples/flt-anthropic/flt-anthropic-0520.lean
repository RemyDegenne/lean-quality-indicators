set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry.OModulePresheaf.Leray

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits

section FiberAffine

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

def restrictToPreimage
    (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
    (K' : Scheme.OrderedAffineCover V') {U : Z.Opens} (hU : IsAffineOpen U) :
    Scheme.OrderedAffineCoverOf ((Opens.map p.base).obj U) where
  ι := K'.ι
  U := fun i => K'.U i ⊓ (Opens.map p.base).obj U
  isAffineOpen := fun i => Scheme.OrderedAffineCover.fiberAffineOpen p πZ (K'.isAffineOpen i) hU
  le := fun _ => inf_le_right
  iSup_eq := by rw [← iSup_inf_eq, K'.iSup_eq_top, top_inf_eq]

end FiberAffine
end AlgebraicGeometry.OModulePresheaf.Leray
end
