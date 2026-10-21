namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace ExactPentagon

open AssociativeElimination RowTwo RowKernel LeadingRows PolynomialOrdering

open SourceEnveloping SourceModel

attribute [local instance] LieRing.ofAssociativeRing

@[simp] theorem sourceHom_23 : sourceHom (GenericBraid.t 2 3)=U23 := by
  rw [sourceHom_t]
  change SourceEnveloping.chord (some two) none=rawFiber (CountTables.Y 1)
  rw [rawFiber_Y]
  exact SourceEnveloping.chord_comm _ _

end ExactPentagon
end DeligneDrinfeld
end
end OAI
