public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

section Frame

section CData

variable {K K' J : Subgroup G} {z u t c : G}

theorem TwinFrameSettingCore.comm_t_c (hs : TwinFrameSettingCore p f Ω K K' J z u t)
    (hc : c = t ∨ c = t * z) : t * c = c * t := by
  have hzt : z * t = t * z := hs.frame.comm_zt hs.odd hs.hyp
  rcases hc with hc | hc
  · rw [hc]
  · rw [hc]
    calc t * (t * z) = t * (z * t) := by rw [hzt]
      _ = (t * z) * t := by group

end CData
end Frame
end CFSG.ClassicalInvolution.Asc77
end
