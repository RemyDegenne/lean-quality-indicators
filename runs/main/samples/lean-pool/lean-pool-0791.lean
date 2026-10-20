@[expose] public section

namespace AtanasovRanganathan.GenusFiveTwoPole

open Utilities Utilities.Certificate

open Utilities.Certificate.TwoPoleSubdivision

open Utilities.Subdivision.SubdivisionCoreSupport

open GenusFiveCoreAtlas GenusFiveTwoPoleData

theorem row04_rank_positive (s : SubdivisionGraph.Spec 8 12)
    (hCore : s.core = row04Core) :
    rank s.graph (coreDivisor s row04Weight) ≥ 1 := by
  cases s with
  | mk core length hn hl hp =>
    dsimp at hCore
    subst core
    apply rank_ge_one_of_twoPoleData _
      (SubdivisionGraph.Spec.graph_connected_of_coreConnected _ row04_connected)
      row04Weight row04_weight_nonneg row04
      row04_left_connected row04_right_connected
      row04_left_degree_ge_two row04_right_degree_ge_two
      row04_weight_left row04_weight_right row04_coverage

end AtanasovRanganathan.GenusFiveTwoPole
end
