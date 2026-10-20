@[expose] public section

namespace IsoGraph

namespace Canon

theorem splitCell_tr_general {cnt : Array Nat} {c : Nat} {st : SplitState} {bc0 ks0 : Array Nat}
    (hb : bucketFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c st.bc #[] = (bc0, ks0))
    (h1 : ¬(st.cen[c]! - c == 1) = true) (h2 : ¬(ks0.size == 1) = true)
    {sizes bc1 : Array Nat} (ho : offsetFrom (sortNats ks0) (sortNats ks0).size 0
      (Array.replicate (sortNats ks0).size 0) bc0 0 = (sizes, bc1))
    {block bc2 : Array Nat} (hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c
      (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))
    {lab pos : Array Nat} (hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))
    {cst cen starts : Array Nat} {tr : UInt64} (hbd : boundsFrom (sortNats ks0) sizes
      (sortNats ks0).size 0 st.cst st.cen #[] c (mixN st.tr c) = (cst, cen, starts, tr)) :
    (splitCell cnt c st).tr = tr := by
  rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]

end Canon
end IsoGraph
end
