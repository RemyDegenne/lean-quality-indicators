@[expose] public section

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Ordinal

@[inherit_doc] scoped notation "ω_ " => omega

scoped notation "ω₁" => ω_ 1

theorem le_omega_self (o : Ordinal) : o ≤ omega o :=
  omega_strictMono.le_apply

end Ordinal
end
end
