namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

theorem numericCheck430 (x : Master → ℝ) : Integer.Sparse.eval numericRow430 x =
    (1 : ℝ) * reducedSource430 x := by
  norm_num [numericRow430, reducedSource430, Integer.Sparse.eval, Sparse.eval, nodeValue1384, nodeValue1389, nodeValue1391, nodeValue1407, nodeValue3078, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge
end OAI
