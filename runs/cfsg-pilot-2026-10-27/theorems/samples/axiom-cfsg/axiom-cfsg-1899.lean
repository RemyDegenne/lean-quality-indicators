public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P hiding X

open Polynomial

section

variable {K : Type*} [Field K] [CharP K 3] {T : Tab} {r : K}

theorem valid_ptVarsF {c0 c1 c2 c3 t : F3P} (h0 : c0.Valid) (h1 : c1.Valid) (h2 : c2.Valid)
    (h3 : c3.Valid) (ht : t.Valid) : ∀ i, (ptVarsF c0 c1 c2 c3 t i).Valid := by
  intro i
  rcases i with _ | _ | _ | _ | _ | i <;> simp [ptVarsF, valid_zero, *]

end
end Spec
end CFSG.Walter.Ree.Bombieri
end
