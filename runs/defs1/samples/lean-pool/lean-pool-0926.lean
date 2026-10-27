@[expose] public section

namespace HadwigerNelsonBounds

/-- Independently checked hard-case certificate `partsGadgetHardCertificate15`. -/
def partsGadgetHardCertificate15 : PartsGadgetCertificate := {
  roots := [
    ⟨5, 0⟩, ⟨31, 3⟩, ⟨18, 0⟩, ⟨25, 1⟩, ⟨19, 2⟩, ⟨12, 3⟩,
    ⟨7, 0⟩, ⟨17, 3⟩
  ]
  nodeCount := 1
  nodes := #[
    #[
      ⟨[
        ⟨13, 1⟩, ⟨24, 2⟩, ⟨11, 1⟩, ⟨6, 2⟩, ⟨10, 2⟩,
        ⟨26, 0⟩, ⟨20, 3⟩, ⟨8, 2⟩, ⟨14, 0⟩
      ], 30, ![0, 0, 0, 0]⟩,
    ],
  ]
}

end HadwigerNelsonBounds
end
