public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem F0c_one_conj_mem
    {a : K} (ha : a ∈ Ax25) {f : K} (hf : f ∈ F0c 1) :
    a * f * a⁻¹ ∈ F0c 1 :=
  conj_mem_F0c (k := 1) (by decide) (mem_Ax25.1 ha).1
    (by rw [xLongK_one]; exact (mem_Ax25.1 ha).2) hf

end CFSG.Sporadic.Co2Smith
end
