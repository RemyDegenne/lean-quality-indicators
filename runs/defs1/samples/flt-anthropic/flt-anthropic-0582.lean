namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

noncomputable section

namespace G2eAsm

section Descent

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  {N : Scheme.{u}} (i : N ⟶ G) (LN : RelativeGroupLaw k (i ≫ f))
  (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
  {S : Scheme.{u}} (j : S ⟶ G) (V : S.Opens)

def cover [UniversallyOpen (amap L i j)] : (NV (f := f) i j V).toScheme ⟶ (Uimg L i j V).toScheme :=
  (amap L i j).resLE (Uimg L i j V) (NV (f := f) i j V) (le_preimage_Uimg L i j V)

end Descent
end G2eAsm
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_opens_saturated_fppf_quotient_of_sliceQuotient
