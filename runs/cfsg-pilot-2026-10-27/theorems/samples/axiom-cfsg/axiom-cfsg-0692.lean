public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Act

variable {S M W : Type*} [Group S] (act : S → M → M) (h1 : ∀ m, act 1 m = m)
  (hmul : ∀ s t m, act (s * t) m = act s (act t m)) (κ : M ≃ W)

theorem actPerm_apply (s : S) (m : M) : actPerm act h1 hmul κ s (κ m) = κ (act s m) := by
  show κ (act s (κ.symm (κ m))) = _
  rw [Equiv.symm_apply_apply]

end Act
end CFSG.CGT.PushingUpLit.CGT6.TwoEight
end
