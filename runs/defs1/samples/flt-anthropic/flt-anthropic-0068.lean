set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k]

section transport

variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    {Csym : Scheme.{u}} {csym : Csym ⟶ Spec (CommRingCat.of k)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}

noncomputable def comapSubschemeMap (I : (pullback c csym).IdealSheafData) (φ : T ⟶ Csym)
    (hφ : φ ≫ csym = t) : (I.comap (mapOnProd c φ hφ)).subscheme ⟶ I.subscheme :=
  (I.comapIso (mapOnProd c φ hφ)).hom ≫ pullback.snd _ _

end transport
end AlgebraicCurve
