@[expose] public section

open UpperHalfPlane hiding I

open Real Complex ContinuousMap Matrix CongruenceSubgroup ModularGroup Filter Asymptotics

open scoped Interval Real Topology Manifold ModularForm MatrixGroups

@[fun_prop]
theorem ResToImagAxis.Pos.one : ResToImagAxis.Pos (fun _ => 1) :=
  ResToImagAxis.Pos.const 1 one_pos

end
