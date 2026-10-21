namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology

open Set Metric Topology

namespace GroupRingTopology.Attachment

universe u v w

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {n : ℕ}

variable (a : ι → C(Sphere n,X))

@[simp] lemma cell_interior (i : ι) (x : OpenDisk n) :
    cell a i (interior n x) = Sum.inr ⟨i,x⟩ := quotient_interior a i x

end GroupRingTopology.Attachment
end
end OAI
