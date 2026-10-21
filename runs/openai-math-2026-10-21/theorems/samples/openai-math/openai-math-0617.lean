namespace OAI

namespace PermanentBorder.ConductorLocalization

section

variable {S U B C E : Type*} [CommRing S] [CommRing U] [CommRing B]
  [CommRing C] [CommRing E] [Algebra S U] [Algebra S B] [Algebra S C]
  [Algebra U C] [IsScalarTower S U C] [Algebra S E] [Algebra U E]
  [IsScalarTower S U E]

variable (M : Submonoid S) [IsLocalization M U]

include M in

theorem integral_conductor_localizes (j : B →ₐ[S] C) (g : B →ₐ[S] E)
    (q : C →ₐ[U] E) (hcomp : (q.restrictScalars S).comp j = g)
    (b : B) (hb : ∀ x : E, IsIntegral S x → ∃ a : B, g a = g b * x) :
    ∀ x : E, IsIntegral U x → ∃ a : C, q a = q (j b) * x := by
  intro x hx
  obtain ⟨s, hs⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (M := M) x hx
  obtain ⟨a, ha⟩ := hb ((s : S) • x) hs
  obtain ⟨u, hu⟩ := IsLocalization.map_units U s
  have hu' : (u : U) = algebraMap S U (s : S) := hu
  refine ⟨(↑u⁻¹ : U) • j a, ?_⟩
  have hj (a : B) : q (j a) = g a := AlgHom.congr_fun hcomp a
  rw [map_smul, hj, ha, mul_smul_comm, ← hj b]
  rw [← algebraMap_smul U (s : S), ← hu', smul_smul]
  simp

end
end PermanentBorder.ConductorLocalization
end OAI
