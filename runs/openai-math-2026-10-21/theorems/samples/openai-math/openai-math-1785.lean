namespace OAI

noncomputable section

namespace HarmonicCounterexample.Construction

open Module Angular LinearODE Certificate

open scoped BigOperators

lemma charge_distinct {l p q:ℕ} (hp:2*p<l+2) (hq:2*q<l+2)
    (h:(-((p:ℝ)-(l+2-p:ℕ))^2)=(-((q:ℝ)-(l+2-q:ℕ))^2)) : p=q := by
  have hpl : p≤l+2 := by omega
  have hql : q≤l+2 := by omega
  rw [Nat.cast_sub hpl,Nat.cast_sub hql] at h
  have hp' : 2*(p:ℝ)<(l+2:ℕ) := by exact_mod_cast hp
  have hq' : 2*(q:ℝ)<(l+2:ℕ) := by exact_mod_cast hq
  have he : (p:ℝ)=q := by nlinarith
  exact_mod_cast he

end HarmonicCounterexample.Construction
end
end OAI
