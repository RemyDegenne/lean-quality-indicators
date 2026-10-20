public section

open CategoryTheory Limits Opposite AlgebraicGeometry

open Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X : Scheme.{u}} {A B : CommMon X.Modules}

variable (f g : A ⟶ B)

/-- The structure morphism from the structure presheaf of `X`: regular functions act on `A`
through the algebra map, and `f` and `g` agree on their images. -/
def _root_.CategoryTheory.CommMon.toEqualizerSectionsPresheaf :
    X.presheaf ⟶ CommMon.equalizerSectionsPresheaf f g where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop) (CommMon.equalizerSections f g U.unop))
  naturality {U V} i := by
    have h := A.toSectionsPresheaf.naturality i
    rw [CommMon.toSectionsPresheaf_app, CommMon.toSectionsPresheaf_app] at h
    ext r
    apply Subtype.ext
    exact congr($h r)

end
end TauCeti
end
