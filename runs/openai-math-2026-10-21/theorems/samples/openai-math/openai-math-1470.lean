namespace OAI

namespace PartitionConsistency.DiagramOrder

universe u v w

namespace Conservative

variable {M : Type u} {N : Type v} {R : Type w} [Monoid M] [Monoid N] [Monoid R]
  {f : M →* N} (hf : Conservative f)

include hf

theorem dvd_iff (x y : M) : f x ∣ f y ↔ x ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨t, _, ht⟩ := hf.factor_eq hz.symm
    exact ⟨t, ht.symm⟩
  · exact f.map_dvd

end Conservative
end PartitionConsistency.DiagramOrder
end OAI
