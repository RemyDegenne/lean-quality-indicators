namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem reindexCheck2190 : List.Perm (Integer.Sparse.reindex keyMap MixedData.row2190)
    (Integer.Sparse.reindex Sum.inl PairSemantics.boundaryRow26) := by decide +kernel

end MUB6.Certificate.MixedSourceBridge
end OAI
