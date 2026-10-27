namespace P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt

set_option Elab.async false

open scoped Pointwise

set_option autoImplicit false

open GaloisRep

open TrivSqZeroExt

local notation "tsze" => TrivSqZeroExt

p2m_reactivate

open IsLocalRing TrivSqZeroExt

p2m_reactivate

open TrivSqZeroExt

p2m_reactivate

open GaloisRep

open scoped TensorProduct

p2m_reactivate

namespace WCOTTameD

open GaloisRep IsLocalRing TrivSqZeroExt

section xOfCotangentHom

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  (x : B →ₐ[𝒪] 𝒪) {S : Type} [CommRing S] [Algebra 𝒪 S]

noncomputable def xOfCotangentHom (φ : (RingHom.ker (x : B →+* 𝒪)).Cotangent →ₗ[𝒪] S) :
    B →ₐ[𝒪] tsze S S where
  toFun r := ⟨algebraMap 𝒪 S (x r), φ (cotOfEntry x r)⟩
  map_one' := by ext <;> simp [cotOfEntry_apply, δ_one]
  map_mul' r s := by
    ext
    · simp only [fst_mk, fst_mul, map_mul]
    · simp only [snd_mk, snd_mul, fst_mk, cotOfEntry_apply, toCotangent_δ_mul, map_add, map_smul,
        Algebra.smul_def, op_smul_eq_smul, Algebra.algebraMap_self, RingHom.id_apply]
  map_zero' := by ext <;> simp
  map_add' r s := by ext <;> simp [cotOfEntry_apply, δ_add]
  commutes' c := by
    ext
    · show algebraMap 𝒪 S (x (algebraMap 𝒪 B c)) = (algebraMap 𝒪 (tsze S S) c).fst
      rw [x.commutes]; rfl
    · show φ (cotOfEntry x (algebraMap 𝒪 B c)) = (algebraMap 𝒪 (tsze S S) c).snd
      rw [cotOfEntry_apply, δ_algebraMap, map_zero, map_zero]; rfl

end xOfCotangentHom
end WCOTTameD
end P2MW.S_GaloisRep_DeformationRingData_length_level_quotient_le_of_isUnramifiedAt
