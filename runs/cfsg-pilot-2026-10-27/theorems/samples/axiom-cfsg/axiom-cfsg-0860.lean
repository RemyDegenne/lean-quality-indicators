public section

namespace CFSG.ClassicalInvolution.Asc77

namespace MuTab

theorem noIndep3_perm3 : ∀ a b c : Equiv.Perm (Fin 3), ¬ Indep3 a b c := fun a b c h => by
  have h0 : ∀ a b c : Equiv.Perm (Fin 3), indepB a b c = false := by decide +kernel
  have := indepB_of_indep3 h
  rw [h0] at this
  exact Bool.false_ne_true this

end MuTab
end CFSG.ClassicalInvolution.Asc77
end
