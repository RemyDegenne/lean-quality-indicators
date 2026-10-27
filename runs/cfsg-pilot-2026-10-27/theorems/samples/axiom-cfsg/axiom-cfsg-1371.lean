public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.RootAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

variable {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}

theorem liftCoeff_sub_smul (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) (c : ℤ) (i : Fin n) :
    liftCoeff e (x - c • Pi.single i 1) = liftCoeff e x - c • liftCoeff e (Pi.single i 1) := by
  funext β
  by_cases h : β ∈ simpleRoots Ψ <;> simp [liftCoeff, h]

end CFSG.HardMathSupport.Timmesfeld.RootAut
end
