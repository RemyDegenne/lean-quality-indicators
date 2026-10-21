namespace OAI

section

open Encodable

open scoped BigOperators

namespace RapidForcing.EffectiveProfile.Formula

open EffectiveArithmetic

attribute [local irreducible] diff Expr.diff bound Expr.bound

variable {d : ℕ}

@[fun_prop] lemma computable_sumVector : Computable sumVector := by
  apply computable_fin_lambda
  intro i
  exact computable_listSum.comp (computable_list_map Computable.id
    (Computable.fin_app.comp Computable.snd (Computable.const i)).to₂)

end RapidForcing.EffectiveProfile.Formula
end
end OAI
