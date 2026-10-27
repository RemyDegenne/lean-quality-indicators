public section

noncomputable section

open StateTransition (EvalsToInTime)

open scoped BigOperators

namespace GapCVP

open GapCVP.TraceGolf (oneStep rebound)

namespace CNFFiveFamilyForbiddenWholeClauseExactSourceTM

open Computability Turing GapCVP.BinaryEncoding GapCVP.SourceUniformTuringTM

open GapCVP.CLStructuralPrefixWriter GapCVP.CNFFlatSourceGridDescriptorTM

open GapCVP.CNFFlatPhysicalBinaryAppendTM

open GapCVP.SourceFourFamilyInterpolationMembershipPredicateTM

open GapCVP.CNFFiveFamilyFlatCandidateGenerationTM

open GapCVP.CNFFiveFamilyForbiddenWholeClauseWorkerTM

open GapCVP.CNFFiveFamilyForbiddenWholeClauseSourceCert

/-- GapCVP reduction support. -/
def fiveForbiddenRawDistinctPayloadWord
    (first second third fourth payload : List Bool → List Bool)
    (input : List Bool) : List Bool :=
  payload (first input) ++
    fiveForbiddenRawStrictPayloadWord first second
      (fun source => payload (second source)) input ++
    fiveForbiddenRawStrictPayloadWord second third
      (fun source => payload (third source)) input ++
    fiveForbiddenRawStrictPayloadWord third fourth
      (fun source => payload (fourth source)) input

end CNFFiveFamilyForbiddenWholeClauseExactSourceTM
end GapCVP
end
end
