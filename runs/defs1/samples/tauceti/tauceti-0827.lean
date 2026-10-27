public section

namespace TauCeti

open CategoryTheory

universe u v w

/-- The **profinite integers** `ℤ̂`: the profinite completion of a universe lift of the additive
group of `ℤ`, written multiplicatively. The lift only places the completion in universe `u`.
This is the profinite group; its ring structure is put on `Additive zHat` in
`TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring`. -/
noncomputable abbrev zHat : ProfiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (ULift.{u} (Multiplicative ℤ)))

end TauCeti
end
