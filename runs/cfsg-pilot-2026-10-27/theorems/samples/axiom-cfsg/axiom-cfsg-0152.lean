public section

namespace CFSG.LargeExtraspecial.S13

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem fix_of_fix_sq {k : V ≃ₗ[ZMod 2] V} (hk3 : k ^ 3 = 1) {v : V} (hv : k (k v) = v) :
    k v = v := by
  have h3 : k (k (k v)) = v := by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hk3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  rw [hv] at h3
  exact h3

end CFSG.LargeExtraspecial.S13
end
