public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoThree

open CFSG.Quasithin CFSG.SL2MinimalFaithful Matrix

namespace NatData

variable {K : Type*} [Field K] {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}
  (D : NatData K G)

theorem dg_mem_commV {v : V} (hv : v ∈ commV G) (l : Kˣ) : D.dg l v ∈ commV G :=
  D.ρ_mem_commV _ hv

end NatData
end CFSG.CGT.PushingUpLit.CGT6.TwoThree
end
