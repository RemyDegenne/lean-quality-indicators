namespace P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup

set_option autoImplicit false

noncomputable section

p2m_open

namespace CerednikDrinfeld

namespace Mumford

namespace I4a

namespace OrbitCount

p2m_open

variable {H : Type} [Group H] (K : Subgroup H) {Y : Type} [MulAction H Y]

def psi (y₀ : Y) : H ⧸ K → orbitRel.Quotient K Y :=
  Quotient.lift (s := QuotientGroup.leftRel K)
    (fun h : H => (Quotient.mk (orbitRel K Y) (h⁻¹ • y₀) : orbitRel.Quotient K Y))
    (fun a b hab => by
      have hab' : a⁻¹ * b ∈ K := QuotientGroup.leftRel_apply.mp hab
      apply Quotient.sound
      refine ⟨⟨a⁻¹ * b, hab'⟩, ?_⟩
      show (a⁻¹ * b) • (b⁻¹ • y₀) = a⁻¹ • y₀
      rw [smul_smul, mul_assoc, mul_inv_cancel, mul_one])

end OrbitCount
end I4a
end Mumford
end CerednikDrinfeld
end
end P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup
