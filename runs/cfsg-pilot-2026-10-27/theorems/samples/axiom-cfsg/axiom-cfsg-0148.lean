public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

section Model

variable {Y : Subgroup (Perm (Fin 5))}

open Classical in
theorem selClosed_of_subgroup (Y : Subgroup (Perm (Fin 5))) :
    SelClosed (decide (sA ∈ Y)) (decide (sB ∈ Y)) (decide (sA * sB ∈ Y)) := by
  have hAA : sA * sA = 1 := by decide
  have hBB : sB * sB = 1 := by decide
  simp only [SelClosed, decide_eq_true_eq]
  refine ⟨fun ha hb => Y.mul_mem ha hb, fun ha hc => ?_, fun hb hc => ?_⟩
  · have h := Y.mul_mem ha hc
    rwa [← mul_assoc, hAA, one_mul] at h
  · have h := Y.mul_mem hc hb
    rwa [mul_assoc, hBB, mul_one] at h

end Model
end CFSG.Quasithin.Vol2.Ch10.SecE
end
