@[expose] public section

open Complex Set Metric Filter Topology

namespace RectHomotopyProof

lemma fdPolygon_seg4_continuous :
    Continuous fdPolygonSeg4 := by unfold fdPolygonSeg4; continuity

end RectHomotopyProof
end
