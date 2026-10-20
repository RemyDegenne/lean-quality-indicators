set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup Function

open scoped MatrixGroups

noncomputable section

namespace ModularCurve.Period

variable {Γ Δ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

theorem transferElt_spec (γ : ↥Γ) (q : ↥Γ ⧸ Δ.subgroupOf Γ) :
    ((traceRep q : ↥Γ) : SL(2, ℤ)) * (γ : SL(2, ℤ))
      = (transferElt (Δ := Δ) γ q : SL(2, ℤ))
        * ((traceRep (γ⁻¹ • q) : ↥Γ) : SL(2, ℤ)) := by
  have h : traceRep q * γ
      = (HeckeEis.transferAux (Δ.subgroupOf Γ) γ (γ⁻¹ • q) : ↥Γ) * traceRep (γ⁻¹ • q) := by
    rw [HeckeEis.coe_transferAux, smul_inv_smul]
    unfold traceRep
    group
  exact congrArg (fun x : ↥Γ => (x : SL(2, ℤ))) h

end ModularCurve.Period
end
