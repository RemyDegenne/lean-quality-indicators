namespace IsoGraph

namespace Canon

/-- Perform one refinement step: use the cell starting at position `s` as a splitter, splitting
every cell that meets its neighbourhood.

Returns the new partition, the updated worklist (`inW`, indexed by cell start position), the
updated trace hash, and the scratch space, restored to its cleared state.  Cells created by a
split are pushed onto the worklist following Hopcroft's rule: all fragments if the parent was
queued, otherwise all but a largest fragment. -/
def refineStep (G : Graph) (p : Part) (inW : Array Bool) (s : Nat) (tr : UInt64) (sc : Scratch) :
    Part × Array Bool × UInt64 × Scratch :=
  let e := p.cen[s]!
  let tr := mixN tr s
  -- (1) count neighbours inside the splitter cell `lab[s:e]`.
  match countFrom G p.lab e (e - s) s sc.cnt #[] with
  | (cnt, touched) =>
    if touched.isEmpty then (p, inW, tr, sc)
    else
      -- (2) collect the cells met by the splitter and process them left to right, so that the
      -- order in which they are processed depends only on positions.  Only *met* cells are
      -- visited, which is what keeps a refinement step proportional to the splitter's degree sum
      -- rather than to the number of cells.
      match collectFrom p.pos p.cst touched touched.size 0 sc.hit #[] with
      | (hit, collected) =>
        let cells := sortNats collected
        match splitCellsFrom cnt cells cells.size 0
            { lab := p.lab, pos := p.pos, cst := p.cst, cen := p.cen, inW, tr, bc := sc.bc } with
        | st =>
          -- (6) restore the scratch space, touching only the entries that were dirtied.  `bc` is
          -- already back to all-zero: every bucket counter is reset as soon as its cell is done.
          ({ lab := st.lab, pos := st.pos, cst := st.cst, cen := st.cen }, st.inW, st.tr,
            { cnt := clearCntFrom touched touched.size 0 cnt,
              hit := clearHitFrom cells cells.size 0 hit,
              bc := st.bc })

end Canon
end IsoGraph
