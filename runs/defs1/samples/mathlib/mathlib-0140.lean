public section

/-- An additive group `G` is residually finite if the intersection of all finite index normal
additive subgroups is trivial. -/
class AddGroup.ResiduallyFinite (G : Type*) [AddGroup G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

end
