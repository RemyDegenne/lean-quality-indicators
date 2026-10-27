public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup Equiv

variable {L : Type} [Group L]

theorem a7Emb_apply (e : L ≃* alternatingGroup (Fin 7)) (k : L) :
    a7Emb e k = ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl

end CFSG.LocalAnalysis.RankThreeTheoremC
end
