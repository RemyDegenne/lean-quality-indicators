public section

namespace CFSG.Quasithin.H13.I51K

open Equiv Equiv.Perm CFSG.Permutation.FinPack CFSG.Quasithin.H13.A6 CFSG.Quasithin.H13.A6K

variable {A : Perm (Fin 6) → Prop} {l : List (Perm (Fin 6))}

theorem ff_walk : walkK 6 (fun c => qFF false c && qFF true c) 6 0 0 0 = true := by
  decide +kernel

end CFSG.Quasithin.H13.I51K
end
