public section

namespace CFSG.ComponentClassification.GMS78.RuSimCode

open CFSG.GMS78Ru CFSG.GMS78RuSim

local instance : Std.Associative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

local instance : Std.Commutative (α := Fin 8) (· ^^^ ·) := ⟨by decide⟩

section Data

variable (h0 : s0Check = true) {d : SData} (hd : d ∈ steinData)

include h0 hd

theorem xiApply_xor {m m' : Nat} (hm : m < 256) (hm' : m' < 256) :
    xiApply d.2.2 (m ^^^ m') = addV (xiApply d.2.2 m) (xiApply d.2.2 m') := by
  have hc := canon_d h0 hd
  have ha := xiApply_mem h0 hd hm
  have hb := xiApply_mem h0 hd hm'
  have h1 := xApply_addV d.2.1 hc (RuCode.mem_wList.mp ha) (RuCode.mem_wList.mp hb)
  rw [xApply_xiApply h0 hd hm, xApply_xiApply h0 hd hm'] at h1
  rw [← h1, xiApply_xApply h0 hd (addV_mem_wList hc ha hb)]

end Data
end CFSG.ComponentClassification.GMS78.RuSimCode
end
