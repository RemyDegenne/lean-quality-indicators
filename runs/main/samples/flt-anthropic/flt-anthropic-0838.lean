set_option autoImplicit false

noncomputable section

namespace ModularForm

variable {N : ℕ} {p : ℕ}

@[simp] theorem coe_heckeTLin_apply (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f := rfl

end ModularForm
end
