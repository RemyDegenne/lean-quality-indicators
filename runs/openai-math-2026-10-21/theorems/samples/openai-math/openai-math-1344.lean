namespace OAI

section

namespace PerfectCompleteness.ReducedPartition

variable {X W R Y : Type*}

theorem label_surjective (r : X → R) (f : X → Y) :
    Function.Surjective (label r f) := by
  intro P
  exact ⟨representative r f P, label_representative r f P⟩

end PerfectCompleteness.ReducedPartition
end
end OAI
