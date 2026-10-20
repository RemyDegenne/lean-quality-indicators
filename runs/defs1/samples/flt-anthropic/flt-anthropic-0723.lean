set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point

open ModularFormClass

namespace CuspForm

variable {N : ℕ}

variable (N) in

def NewformBadPrimeCoeff : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f.IsNewform →
    ∀ q : ℕ, q.Prime → q ∣ N →
      (¬ q ^ 2 ∣ N → qCoeff f q ^ 2 = 1) ∧ (q ^ 2 ∣ N → qCoeff f q = 0)

end CuspForm
end
