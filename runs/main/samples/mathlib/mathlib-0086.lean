@[expose] public section

open List (Vector)

namespace PosNum

@[simp] lemma land_eq_and (p q : PosNum) : p.land q = p &&& q := rfl

end PosNum
end
