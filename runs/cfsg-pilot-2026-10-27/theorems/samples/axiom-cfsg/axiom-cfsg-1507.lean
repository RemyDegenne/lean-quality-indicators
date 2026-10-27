public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.ClassicalInvolution.Q3.TC.Graph

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

open CFSG.ClassicalInvolution.Q3.TL4

section Model

variable {n : ℕ}

theorem conj_zBar_ofPerm (σ : Equiv.Perm (Fin n)) (α : Finset (Fin n)) (h : α.card = 4)
    (h' : (α.map σ.toEmbedding).card = 4) :
    mkQ n (ofPerm σ) * zBar α h * (mkQ n (ofPerm σ))⁻¹ = zBar (α.map σ.toEmbedding) h' := by
  rw [zBar_eq_vbar_indv, zBar_eq_vbar_indv, conj_vbar (permBar_mkQ (ofPerm σ))]
  exact congrArg (vbar n) (actV_indv σ α)

end Model
end CFSG.ClassicalInvolution.Q3.TC.Thin
end
