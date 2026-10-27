public section

namespace CFSG.CGT.Stroth77

open Matrix

open Stroth42Core

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ}
  (dD : StrothWeakTypeData D (.t100 m))

theorem iii_uv_mul_ofInt' (x : Fin 3 → ℤ) :
    dD.uv * dD.ofTorus (Torus.ofInt _ x) = dD.ofTorus (Torus.ofInt _ 
      ![-3 * x 0 + 2 * x 1 + 2 * x 2, -2 * x 0 + x 1 + 2 * x 2, -2 * x 0 + 2 * x 1 + x 2]) *
        dD.uv := by
  rw [dD.uv_mul_ofTorus, t100_φuv]

end StrothWeakTypeData
end CFSG.CGT.Stroth77
end
