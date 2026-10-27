public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n : ℕ}

theorem mkQ_ofPerm_evalG (gs : List (Equiv.Perm (Fin n))) (w : List ℕ) :
    mkQ n (ofPerm (evalG gs w)) = evalG (gs.map fun g => mkQ n (ofPerm g)) w :=
  evalG_map ((mkQ n).comp (ofPermHom n)) gs w

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
end
