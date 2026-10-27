public section

namespace CFSG.LargeExtraspecial.AS62

open Sem

namespace Frame

variable {G : Type*} [Group G] (F : Frame G)

theorem rep_congr {h : G} {d d' : ℕ × ℕ} (hd : F.Rep h d) (e : d = d') : F.Rep h d' := e ▸ hd

end Frame
end CFSG.LargeExtraspecial.AS62
end
