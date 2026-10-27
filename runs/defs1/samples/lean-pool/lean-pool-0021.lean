universe u

open Set Pointwise

public noncomputable section

namespace IGame

export Player (left right)

scoped notation:max x:max "ᴸ" => moves left x

scoped notation:max x:max "ᴿ" => moves right x

/-- **Conway recursion**: build data for a game by recursively building it on its
left and right sets. You rarely need to use this explicitly, as the termination checker will handle
things for you.

See `ofSetsRecOn` for an alternate form. -/
@[elab_as_elim]
def moveRecOn {motive : IGame → Sort*} (x)
    (ind : Π x, (Π p, Π y ∈ x.moves p, motive y) → motive x) :
    motive x :=
  subposition_wf.recursion x fun x IH ↦ ind x (fun _ _ h ↦ IH _ (.of_mem_moves h))

end IGame
end
