public section

namespace CFSG.Quasithin.H13.VzL34

open CFSG.Open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.L34Z
  CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Monster.Code CFSG.QuasithinUnique
  CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.H.ZTrans Equiv

theorem sigX_order : orderOf (⟨sigX, sigX_alt⟩ : Alt5) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · apply Subtype.ext; show sigX ^ 2 = 1; decide +kernel
  · intro h; have := congrArg Subtype.val h; revert this; show ¬ (sigX = 1); decide +kernel

end CFSG.Quasithin.H13.VzL34
end
