@[expose] public section

namespace RS

open Equiv Equiv.Perm

theorem permCongr_eq_extendDomain {α β : Type}
    (e : α ≃ β) (π : Equiv.Perm α) :
    e.permCongr π =
      π.extendDomain
        (e.trans (Equiv.subtypeUnivEquiv
          (fun _ => trivial : ∀ x : β, (fun _ => True) x)).symm) := by
  ext x
  rw [Equiv.permCongr_apply,
    Equiv.Perm.extendDomain_apply_subtype _ _ (by trivial)]
  rfl

end RS
end
