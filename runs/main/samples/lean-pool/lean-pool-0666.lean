@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

theorem coverageBranchLocallyValid_6_25 :
    branchClaims6Row25.LocallyValid := by
  intro identifier hidentifier
  change identifier < 211 at hidentifier
  by_cases hchunk0 : identifier < 64
  · exact nodeLocalValid_of_chunk coverageBranchNodes_6_25_00000 (by omega) hchunk0
  by_cases hchunk1 : identifier < 128
  · exact nodeLocalValid_of_chunk coverageBranchNodes_6_25_00064 (by omega) hchunk1
  by_cases hchunk2 : identifier < 192
  · exact nodeLocalValid_of_chunk coverageBranchNodes_6_25_00128 (by omega) hchunk2
  exact nodeLocalValid_of_chunk coverageBranchNodes_6_25_00192 (by omega) (by omega)

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
end
