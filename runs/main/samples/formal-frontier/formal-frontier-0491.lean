@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

theorem backward_forward (S : Y.Sheaf CommRingCat.{v})
    {M : SheafOfModules.{v} (sourceRing S)}
    {N : SheafOfModules.{v} (targetRing f S)}
    (g : (RingedSpaces.Modules.SheafInverseImage.moduleFunctor f S).obj M ⟶ N) :
    backward f S (forward f S g) = g :=
  Equiv.symm_apply_apply (homEquiv f S M N) g

end RingedSpaces.Modules.SheafInverseImage
end
