@[expose] public section

namespace Erdos97Octagon.RawIncidence

/-- Add one selected pair to a packed pair mask. -/
def addPairBit
    (rowMask : UInt64) (result : UInt64) (pair : Vertex × Vertex) : UInt64 :=
  if pairSelectedB rowMask pair then
    result ||| (1 <<< UInt64.ofNat (varIndex pair.1 pair.2))
  else result

end Erdos97Octagon.RawIncidence
end
