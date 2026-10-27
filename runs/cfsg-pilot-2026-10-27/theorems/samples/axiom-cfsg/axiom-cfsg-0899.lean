public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG.GH74.GLS.IVK

namespace CtW

variable {G G' : Type} [Group G] [Group G']

section Model

open DihedralGroup

variable {k : ℕ}

section Std3

variable [NeZero k]

variable {T₁ : Subgroup ↥(Wsub k)} {z t : ↥(Wsub k)} {a : ZMod (2 * k)}

omit [NeZero k] in
theorem StdCfg.hpc (S : StdCfg k T₁ z t a) : par k (cc k) = 0 := par_cc S.hke

end Std3
end Model
end CtW
end CFSG.GH74.GLS.SP.Local
end
