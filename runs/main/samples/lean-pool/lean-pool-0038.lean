@[expose] public section

namespace IsoGraph

namespace Canon

theorem individualize_refines {n : Nat} {p : Part} {v : Nat} (hp : Part.WF n p) (hv : v < n) :
    Refines n (individualize p v).1 p := by
  have hd : IndivData n p v p.pos[v]! p.cst[p.pos[v]!]! p.cen[p.pos[v]!]! p.lab[p.cst[p.pos[v]!]!]!
    := ⟨hv, rfl, rfl, rfl, rfl⟩
  intro i hi hstart
  rw [individualize_cst_getElemD hp hd]
  split
  · rename_i hmem
    have := hd.cst_eq hp (by omega) hmem.2
    omega
  · exact hstart

end Canon
end IsoGraph
end
