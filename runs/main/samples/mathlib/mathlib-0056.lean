@[expose] public section

open Set Filter TopologicalSpace Function Topology MulOpposite Pointwise

variable {G H α β : Type*}

section IsTopologicalGroup

section Conj

variable [TopologicalSpace G] [Inv G] [Mul G]

@[to_additive continuous_addConj_prod
  ]
theorem IsTopologicalGroup.continuous_conj_prod [ContinuousMul G] [ContinuousInv G] :
    Continuous fun g : G × G => g.fst * g.snd * g.fst⁻¹ :=
  continuous_mul.mul (continuous_inv.comp continuous_fst)

end Conj
end IsTopologicalGroup
end
