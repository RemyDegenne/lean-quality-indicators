public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

open Stroth42Core

namespace Type300

variable {n : ℕ}

theorem W_u (w : Torus (StrothTypeIndex.t300 n).k) (hw : InW w) :
    ((StrothTypeIndex.t300 n).action.φu w) 0 = 0 := by
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt w
  obtain ⟨h0, -, -⟩ := (inW_ofInt_iff x).mp hw
  rw [t300_φu, ofInt_apply_zero_eq_zero_iff]
  simpa only [Matrix.cons_val_zero] using h0

end Type300
end CFSG.CGT.Stroth77
end
