public section

namespace TauCeti

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K]

variable (p K) in
theorem proPKernel_le_ker_localCyclotomicCharacter (hmu : ∃ ζ : K, IsPrimitiveRoot ζ p) :
    proPKernel p (Field.absoluteGaloisGroup K) ≤ (localCyclotomicCharacter p K).ker := by
  have hmem := localCyclotomicCharacter_mem_unitsPrincipal (n := 1) (by simpa using hmu)
  -- Corestrict the character to the profinite pro-`p` group `1 + pℤ_p`.
  let χ₁ := (localCyclotomicCharacter p K).codRestrict (unitsPrincipal p 1) hmem
  have hχ₁ : Continuous χ₁ := (localCyclotomicCharacter_continuous p K).subtype_mk hmem
  rw [← MonoidHom.ker_codRestrict _ _ hmem]
  exact proPKernel_le_ker (isProP_unitsPrincipal p one_pos) χ₁ hχ₁

end TauCeti
end
