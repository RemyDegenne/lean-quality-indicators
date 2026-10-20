namespace P2MW.S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units

set_option maxHeartbeats 25600000

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace NodeAddEquiv

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

variable (d : L)

variable (hd : d ≠ 0)

include hd

lemma phi_some {x y : L} (h : (Wd d).toAffine.Nonsingular x y) :
    ((phi d hd (.some x y h) : Lˣ) : L) = (y - d * x) / (y + d * x) := rfl

end NodeAddEquiv
end P2MW.S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units
