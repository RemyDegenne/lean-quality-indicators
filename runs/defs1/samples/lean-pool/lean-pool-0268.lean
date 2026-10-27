namespace IsoGraph

namespace Canon

/-- Scatter the cell's vertices into `block` in count order, each bucket keeping the order it had
in the cell.  Phase (3c). -/
def scatterFrom (lab cnt : Array Nat) (ec : Nat) :
    Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, block, bc => (block, bc)
  | fuel + 1, k, block, bc =>
    if k ≥ ec then (block, bc)
    else
      let v := lab[k]!
      let t := cnt[v]!
      let o := bc[t]!
      scatterFrom lab cnt ec fuel (k + 1) (block.set! o v) (bc.set! t (o + 1))

end Canon
end IsoGraph
