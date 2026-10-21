namespace OAI

section

namespace KLInvariance.AdaptedDyer

open TitsSpace SchedulePaths

open scoped BigOperators

universe u v

variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {cs}

variable (cs)

variable {cs}

variable (cs)

variable {cs}

variable (cs)

theorem path_rotate {x y : W} {p : List (Edge cs)} (i : I)
    (hp : IsPath (source cs) (target cs) x y p)
    (hn : ∀ e ∈ p, rootLabel cs e ≠ simplePositive i) :
    IsPath (source cs) (target cs) (cs.simple i*x) (cs.simple i*y) (p.map (rotateEdge cs i)) := by
  apply path_map_of_mem (source cs) (target cs) (source cs) (target cs)
    hp (fun z => cs.simple i*z) (rotateEdge cs i)
  · intro e he
    exact congrArg Prod.fst (rotateEdge_val cs i e (hn e he))
  · intro e he
    exact congrArg Prod.snd (rotateEdge_val cs i e (hn e he))

end
end KLInvariance.AdaptedDyer
end
end OAI
