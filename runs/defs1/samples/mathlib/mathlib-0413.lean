@[expose] public section

namespace PosNum

/-- `divMod x y = (y / x, y % x)`. -/
def divMod (d : PosNum) : PosNum → Num × Num
  | bit0 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit0 r₁)
  | bit1 n =>
    let (q, r₁) := divMod d n
    divModAux d q (Num.bit1 r₁)
  | 1 => divModAux d 0 1

end PosNum
end
