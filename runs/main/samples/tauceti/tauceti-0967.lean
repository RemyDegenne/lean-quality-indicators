public noncomputable section

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped ModularForm MatrixGroups Pointwise

variable {𝒢 𝒢' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

open TauCeti TauCeti.UpperHalfPlane

namespace CuspForm

section Nebentypus

variable {N : ℕ} {χ : (ZMod N)ˣ →* ℂˣ}

@[simp]
lemma coe_conjCharSpace_apply (f : cuspFormCharSpace k χ) :
    (CuspForm.conjCharSpace k χ f : _root_.CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      CuspForm.conj (Gamma1_map_le_conjAct_inv_J N) (f : _root_.CuspForm _ k) :=
  (rfl)

end Nebentypus
end CuspForm
end
