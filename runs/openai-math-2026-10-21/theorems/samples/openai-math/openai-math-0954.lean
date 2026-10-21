namespace OAI

namespace TuringRigidity.ArithmeticPrefixForcing

open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements

open EncodedForcing (word word_primrec)

theorem decides_arith {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v => Decides (Q O v)) := hQ.or (avoids_arith hQ)

end TuringRigidity.ArithmeticPrefixForcing
end OAI
