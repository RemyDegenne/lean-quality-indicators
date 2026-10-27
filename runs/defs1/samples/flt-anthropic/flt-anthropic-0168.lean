namespace P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq

open scoped Pointwise

set_option autoImplicit false

namespace CTap

universe u v

section Conj

variable {M : Type u} {L : Type v} [Field M] [Field L] [Algebra M L]

def LiesOverVal (V : ValuationSubring L) (A₀ : ValuationSubring M) : Prop :=
  V.comap (algebraMap M L) = A₀

end Conj
end CTap
end P2MW.S_ValuationSubring_exists_mem_decompositionSubgroup_restrictNormal_eq
