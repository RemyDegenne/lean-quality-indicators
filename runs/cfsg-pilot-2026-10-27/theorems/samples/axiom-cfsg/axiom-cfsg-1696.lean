public section

namespace CFSG.StandardType.U63TB

open CFSG CFSG.Assembly CFSG.StandardType TableB NbrInnerRest

theorem mulAut_mem_center {L : Type*} [Group L] (f : MulAut L) {z : L}
    (hz : z ∈ Subgroup.center L) : f z ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro l
  have h := congrArg f (Subgroup.mem_center_iff.mp hz (f.symm l))
  simpa [map_mul] using h

end CFSG.StandardType.U63TB
end
