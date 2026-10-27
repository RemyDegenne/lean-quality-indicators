public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Near

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem permHom_apply (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    (x : centralizer ({z} : Set G)) : permHom h d e x = permOf h d e x.2 := rfl

end Near
end CFSG.OddStandard.AltStdSec
end
