public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction.EPilot CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.Universal.Spin (cartanD isFiniteType_cartanD toStdD rootsD_eq boolSign)

open CFSG.LieType.RootSystem (roots weylAction coxeterMatrix reflection reflection_apply
  weylAction_simple weylAction_mul_apply)

theorem d6Embed_add (v w : Fin 6 → ℤ) : d6Embed (v + w) = d6Embed v + d6Embed w :=
  ext_d6Node (fun i => by simp only [d6Embed_d6Node, Pi.add_apply])
    (by simp only [d6Embed_highNode, Pi.add_apply, add_zero])

end CFSG.SeitzReduction.E7Pilot
end
