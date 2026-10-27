public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

theorem gA_stab (N : Matrix (Fin 3) (Fin 3) (ZMod 2)) : gA N ∈ stabM Sm := by
  intro v
  constructor
  · intro hv i
    rw [gA_apply, gfun_inr]
    exact hv i
  · intro hv i
    have h := hv i
    rw [gA_apply, gfun_inr] at h
    exact h

end CFSG.Quasithin.H13.C1294.Model
end
