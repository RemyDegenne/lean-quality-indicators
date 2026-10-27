public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem sigY_facts : ∀ j : Fin 15, Perm.sign (sigY j) = 1 ∧
    (fun k => c45 (dPerm (sigY j)⁻¹ k)) = cY j := by
  decide +kernel

end CFSG.Quasithin.H13.A6
end
