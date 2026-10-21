namespace OAI

noncomputable section

open Set Metric Topology BigOperators

open Set Metric Topology

namespace GroupRingTopology.PathExtension

section

open Path.Homotopic

universe u v

variable {X : Type u} [TopologicalSpace X]

namespace Q

variable {x y z : X}

lemma cast_equal {x' y' : X} (p : Path.Homotopic.Quotient x y) (hx : x' = x) (hy : y' = y) :
    Equal (p.cast hx hy) p := ⟨hx,hy,Path.Homotopic.Quotient.cast_heq hx hy⟩

end Q
end
end GroupRingTopology.PathExtension
end
end OAI
