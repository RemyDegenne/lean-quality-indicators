namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

open scoped BigOperators

variable (verifier : NPVerifier) (input : List Bool)

@[simp] theorem initial_input_stack (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).stk verifier.computation.tm.k₀ =
      (pairBits (input, decode bits)).map verifier.computation.inputAlphabet.invFun := by
  simp [initial, Turing.initList]

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding
end
end OAI
