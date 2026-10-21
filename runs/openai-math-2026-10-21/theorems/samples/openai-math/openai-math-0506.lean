namespace OAI

universe uH

noncomputable section

open scoped BigOperators Pointwise

namespace LampProjectionDraft

open LampDraft AverageDraft SupportDraft GroupRingDeterminant

variable (H : Type uH) [Group H]

local instance : DecidableEq H := Classical.decEq H

lemma baseProjection_idempotent (S : Finset H) : IsIdempotentElem (baseProjection H S) :=
  (baseAverage_idempotent H 1).mul (complement_prod_idempotent H S)

end LampProjectionDraft
end
end OAI
