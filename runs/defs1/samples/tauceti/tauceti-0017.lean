public section

noncomputable section

open CategoryTheory Limits Metric Topology Set

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) (n : ℕ)

/-- The step of `attachStageFunctor f n` from stage `n` to stage `n + 1` is `f`. -/
def attachStageArrowIso :
    Arrow.mk f ≅ Arrow.mk ((attachStageFunctor f n).map (homOfLE (Order.le_succ n))) :=
  mk₁ArrowIso f (monotone_attachStageIndex n (Order.le_succ n)) (attachStageIndex_of_le le_rfl)
    (attachStageIndex_of_lt (Nat.lt_succ_self n))

end TauCeti
end
end
