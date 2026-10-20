@[expose] public section

namespace BeyondBethe

open Complexity

/-- Pure list-level fold mirrored by the bounded machine loop. -/
def binaryMulFold : List Bool → List Bool → List Bool →
    List Bool × List Bool
  | [], shift, acc => (shift, acc)
  | bit :: remaining, shift, acc =>
      binaryMulFold remaining
        (machineBinaryAddBits (pair shift shift))
        (if bit then machineBinaryAddBits (pair acc shift) else acc)

end BeyondBethe
end
