public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

open Matrix

theorem t121_φuv_ab_half {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t121 m hm).action.φuv
        ((2 ^ (m - 1) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
            Torus.b (k := (StrothTypeIndex.t121 m hm).k))) =
      -((2 ^ (m - 1) : ℕ) •
          (Torus.a (k := (StrothTypeIndex.t121 m hm).k) +
            Torus.b (k := (StrothTypeIndex.t121 m hm).k))) := by
  obtain ⟨v, hv⟩ := t121_uv_preimage (m := m) hm
  have hsq := (StrothTypeIndex.t121 m hm).action.rels.uv_sq
  have hvv : (StrothTypeIndex.t121 m hm).action.φuv
      ((StrothTypeIndex.t121 m hm).action.φuv v) = v := by
    have := DFunLike.congr_fun hsq v
    simpa using this
  have h2 : (StrothTypeIndex.t121 m hm).action.φuv
      ((StrothTypeIndex.t121 m hm).action.φuv v - v) =
      -((StrothTypeIndex.t121 m hm).action.φuv v - v) := by
    rw [map_sub, hvv]
    abel
  rwa [hv] at h2

end StrothFrame.IsD
end CFSG.CGT.Stroth77
end
