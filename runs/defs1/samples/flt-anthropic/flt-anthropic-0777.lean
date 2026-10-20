namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint

attribute [-instance] kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType

set_option autoImplicit false

set_option maxHeartbeats 12800000

set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TweakGlue

section Ext

variable {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Algebra R A]
  {Ω : Type u} [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra R Ω] [IsScalarTower R A Ω]
  {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) [IsSeparated f]
  (ext : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f)
  (hext : ∀ x, Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ (ext x).1 = x.1)

noncomputable def extHom :
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) f →*
      SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R A))) f :=
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  MonoidHom.mk' ext (fun x y => ext_mul L ext hext x y)

end Ext
end TweakGlue
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isTorsionPoint_pow_and_reduction_eq_of_mem_closure_endomorphisms_of_forall_isTorsionPoint
