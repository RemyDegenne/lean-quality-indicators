import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import P2M.Util
namespace P2MW.S_IsLocalHom_algebraMap_quotient_of_ne_top

open IsLocalRing

theorem solution
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (algebraMap 𝒪 (A ⧸ I)) := by
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.mk_comp_algebraMap]
  exact RingHom.isLocalHom_comp _ _
