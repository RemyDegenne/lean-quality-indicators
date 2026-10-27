public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup

open scoped commutatorElement

namespace S3Sec29C

variable {G : Type} [Group G] [Finite G]

section PartC

variable {x y : G} {K A B Q D J R : Subgroup G}

theorem Zstar_conj_mem (X : Subgroup G) {g z : G} (hg : g ∈ normalizer (X : Set G))
    (hz : z ∈ Zstar X) : g * z * g⁻¹ ∈ Zstar X :=
  Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 (Subgroup.mem_inf.1 hz).1,
    Stage1.Thm2.Recip.cSec_conj X hg (Subgroup.mem_inf.1 hz).2⟩

end PartC
end S3Sec29C
end CFSG.GH74.Generic.BProg.B3
end
