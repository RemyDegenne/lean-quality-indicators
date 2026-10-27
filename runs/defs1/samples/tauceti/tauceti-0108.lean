public section

namespace TauCeti

/-- A finite group presentation together with auditable source and transcription metadata.

The source must be a full presentation of the abstract group, not a semi-presentation for
recognizing generators in a group already constructed elsewhere. `generatorNames` alone determines
the relator arity; `expectedGeneratorCount` is retained only as metadata checked by
`matchesMetadata`.

There is deliberately no checksum field: without a pinned normalization and algorithm, a checksum
would not be a reproducible check on the transcribed expressions. -/
structure GroupPresentation where
  /-- Generator names, in the order used by the relator indices. -/
  generatorNames : List String
  /-- Bibliographic citation or database name for the full presentation. -/
  source : String
  /-- Page, theorem number, or stable database identifier locating the presentation. -/
  sourceLocator : String
  /-- The source's generator and commutator conventions. -/
  generatorConvention : String
  /-- Notes explaining any normalization or conversion made during transcription. -/
  transcriptionNotes : String
  /-- The number of generators stated by the source. -/
  expectedGeneratorCount : ℕ
  /-- The number of relators stated by the source. -/
  expectedRelatorCount : ℕ
  /-- Relators transcribed in the generator order recorded by `generatorNames`. -/
  transcribed : List (Relator (Fin generatorNames.length))

end TauCeti
end
