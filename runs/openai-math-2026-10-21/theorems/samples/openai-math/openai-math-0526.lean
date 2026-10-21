namespace OAI

namespace CommonBasesFPRAS

section

open scoped BigOperators Classical

open scoped BigOperators Classical

namespace DrawTree

variable {A B : Type*}

lemma all_bind (t : DrawTree A) (f : A → DrawTree B) (p : B → Prop)
    (hf : ∀ a,All p (f a)) : All p (t.bind f) := by
  induction t with
  | leaf a => exact hf a
  | draw v k ih => exact ih

end DrawTree
end
end CommonBasesFPRAS
end OAI
