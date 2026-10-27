public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates

theorem subgroupOf_inf' {G : Type*} [Group G] (A B H : Subgroup G) :
    A.subgroupOf H ⊓ B.subgroupOf H = (A ⊓ B).subgroupOf H := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]

end CFSG.ONSchreier
end
