namespace OAI

namespace PureTypeSystem

namespace SignedPath

variable {V : Type*} {E : V → V → Bool → Prop}

theorem restrict {C : Set V} {v w : V} {p : Bool}
    (h : SignedPath E v w p) (hv : v ∈ C)
    (hi : ∀ z, Reach E v z → Reach E z w → z ∈ C) :
    SignedPath (fun x y p => E x y p ∧ x ∈ C ∧ y ∈ C) v w p := by
  induction h with
  | nil v => exact .nil _
  | @cons u v w p q he ht ih =>
      have hv' := hi v (Reach.single he) ⟨q, ht⟩
      exact .cons ⟨he, hv, hv'⟩ (ih hv' (fun z hz hzw =>
        hi z ((Reach.single he).trans hz) hzw))

end SignedPath
end PureTypeSystem
end OAI
