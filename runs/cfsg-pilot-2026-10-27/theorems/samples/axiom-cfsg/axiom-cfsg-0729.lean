public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup

section Lift

variable {N : ℕ} (h8 : 2 * 4 ≤ N)

variable {h8}

theorem pi0_pairEmb (kc : Fin 4 × Fin 2) : pi0 h8 (pairEmb h8 kc) = pairEmb h8 (zPair 4 kc) :=
  viaEmbeddingHom_apply_image _ _ _

end Lift
end CFSG.ComponentClassification.RankTwoAlt
end
