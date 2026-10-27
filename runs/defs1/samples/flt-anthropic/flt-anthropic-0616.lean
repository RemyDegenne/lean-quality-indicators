namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit

set_option autoImplicit false

universe u

p2m_open

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace GoodReductionJacobian

namespace RelativeGroupLaw

namespace LawDescends

p2m_open

section Mul

variable {R : Type u} [CommRing R] {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  {E : Scheme.{u}} (ι : E ⟶ J) [IsClosedImmersion ι]
  {P : Scheme.{u}} (p : J ⟶ P) (w : pullback.snd (ι ≫ f) f ≫ p = L.action ι ≫ p)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
  (hR : IsPullback (pullback.snd (ι ≫ f) f) (L.action ι) p p)
  (hcoeq : IsColimit (Cofork.ofπ p w))
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x)

noncomputable def mP : pullback (g L ι p w hcoeq) (g L ι p w hcoeq) ⟶ P :=
  Cofork.IsColimit.desc (quotient_twoP L ι p w hR hcoeq).choose_spec.2.2.2.2.2.some (mOne L ι p w hR hcoeq hcomm)
    (cond_two L ι p w hR hcoeq hcomm)

end Mul
end LawDescends
end RelativeGroupLaw
end GoodReductionJacobian
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_quotient_of_isColimit
