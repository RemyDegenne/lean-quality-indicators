@[expose] public section

namespace ACMax

variable {V : Type*} [Fintype V]

namespace MShapeP4

variable {G : SimpleGraph V} {a b c d : V}

open Classical in
theorem nadj_bd (hs : MShapeP4 G a b c d) : ¬G.Adj b d := fun h => by
  rcases hs.mnbr_b d h hs.deg_d with e | e
  · exact hs.ne_ad e.symm
  · exact G.ne_of_adj hs.adj_cd e.symm

end MShapeP4
end ACMax
end
