public section

namespace CFSG.Quasithin.J2Cz

open Equiv

open F2

open QM

theorem lineFun_spec (α : MulAut QM) (j : Fin 5) :
    α (x j) = x (lineFun α j) ∨ α (x j) = z * x (lineFun α j) :=
  (aut_x α j).choose_spec

end CFSG.Quasithin.J2Cz
end
