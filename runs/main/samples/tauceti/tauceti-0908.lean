public section

open Real

namespace TauCeti

variable {ι : Type*}

theorem hilbertProjectiveDist_def (x y : ι → ℝ) :
    hilbertProjectiveDist x y = ⨆ i, ⨆ j, log (x i * y j / (y i * x j)) :=
  -- `(rfl)` rather than `rfl`: this lemma is the supported unfolding interface, so the body of
  -- `hilbertProjectiveDist` need not be exposed.
  (rfl)

end TauCeti
end
