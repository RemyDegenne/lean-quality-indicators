@[expose] public section

open List (Vector)

open Finset Function Sym

universe u

variable {α β γ : Type*}

notation3 "s(" x ", " y ")" => Sym2.mk x y

namespace Sym2

section Membership

variable {x : α}

theorem mk_fst_out_snd_out (z : Sym2 α) : s(z.out.fst, z.out.snd) = z :=
  z.out_eq

end Membership
end Sym2
end
