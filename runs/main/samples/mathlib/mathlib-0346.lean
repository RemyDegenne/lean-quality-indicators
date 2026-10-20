@[expose] public section

variable {α β : Type*}

namespace Set

section Infsep

open ENNReal

open Set Function

section MetricSpace

variable [MetricSpace α] {s : Set α}

theorem Finite.infsep_pos_iff_nontrivial (hs : s.Finite) : 0 < s.infsep ↔ s.Nontrivial :=
  letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite

end MetricSpace
end Infsep
end Set
end
