public section

noncomputable section

namespace TauCeti

open Set Topology unitInterval

universe u v w

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

namespace MappingCylinder

variable {f : C(X, Y)}

theorem isClosed_of_preimages {S : Set (MappingCylinder f)}
    (hcyl : IsClosed (mkCyl f ⁻¹' S)) (hbase : IsClosed (mkBase f ⁻¹' S)) : IsClosed S := by
  rw [← isQuotientMap_sumElim_mkCyl_mkBase.isClosed_preimage, isClosed_sum_iff]
  exact ⟨hcyl, hbase⟩

end MappingCylinder
end TauCeti
end
end
