@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

theorem coverageBranchLocallyValid_6_04 :
    branchClaims6Row4.LocallyValid := by
  intro identifier hidentifier
  change identifier < 51 at hidentifier
  exact nodeLocalValid_of_chunk coverageBranchNodes_6_04_00000 (by omega) (by omega)

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
end
