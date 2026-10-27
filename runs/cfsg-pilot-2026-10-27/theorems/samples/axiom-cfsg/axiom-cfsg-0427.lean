public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type*} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem δ1hK_conj_xRootK {r s : ℕ} (hr : r < 18) (hs : s < 4) :
    δ1hK * xRootK r s * δ1hK = xRootK (Native.glWAct 4 r s).1 (Native.glWAct 4 r s).2 :=
  conj_xRootK (g := 4) (by norm_num) hr hs

end CFSG.Sporadic.Co2Smith
end
