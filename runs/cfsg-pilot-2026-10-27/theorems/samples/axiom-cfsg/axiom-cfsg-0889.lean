public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

open CFSG.RankThree.Native

theorem le_apply_rS {w : Equiv.Perm (Fin 240)} (hc : ∀ e ∈ eSub, w * e = e * w) :
    112 ≤ (w rS : ℕ) := by
  by_contra h
  push Not at h
  obtain ⟨m, hm, he, h0, hfix⟩ := dFix_spec h
  have h1 : signPerm (frameDecode m) (w rS) = w rS :=
    Fin.ext (by rw [signPerm_decode_apply hm he]; exact hfix)
  have h2 : signPerm (frameDecode m) rS = rS := by
    have := apply_comm (hc _ (signPerm_decode_mem hm he)) rS
    rw [h1] at this
    exact w.injective this
  rcases d_facts.sFix 112 (by norm_num) with h' | h'
  · norm_num at h'
  · have h3 := signPerm_decode_apply hm he rS
    rw [h2] at h3
    exact h' m hm he h0 h3.symm

end CFSG.EvenSmallLie.OmegaEight.Weyl
end
