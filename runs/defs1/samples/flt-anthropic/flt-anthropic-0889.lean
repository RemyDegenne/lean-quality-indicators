namespace P2MW.S_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom

noncomputable section

namespace ModularCurve

namespace PoincareDualIntegrality

p2m_open

open UpperHalfPlane Filter Complex MeasureTheory Asymptotics

open scoped MatrixGroups Topology ModularForm Real Pointwise

section Cocycle

variable {N : ℕ}

local notation "Γ" => CongruenceSubgroup.Gamma0 N

local notation "Q" => SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N

def gam (M : SL(2, ℤ)) (q : Q) : Γ := ⟨_, gam_mem M q⟩

end Cocycle
end PoincareDualIntegrality
end ModularCurve
end
end P2MW.S_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
