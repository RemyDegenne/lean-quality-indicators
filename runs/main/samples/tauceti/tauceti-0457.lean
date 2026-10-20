public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups DirectSum

noncomputable section

variable {N : ℕ} {k : ℤ}

theorem iSup_inf_cuspFormCharSpace_of_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k χ) = p := by
  have h : (⨆ χ₀ : (ZMod N)ˣ →* ℂˣ,
      p ⊓ ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace ((χ₀ d : ℂ))) = p :=
    TauCeti.iSup_inf_iInf_eigenspace_unitHom_of_invariant_of_commGroup
      isUnit_card_unitsZMod p hp
  simpa only [cuspFormCharSpace_def] using h

end
end
