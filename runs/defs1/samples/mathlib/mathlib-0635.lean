@[expose] public section

variable {A M G α β γ : Type*}

namespace MulAut

variable (M) [Mul M]

/-- Isomorphic groups have isomorphic automorphism groups. -/
@[to_additive (attr := simps) /-- Isomorphic groups have isomorphic automorphism groups. -/]
def congr [Group G] {H : Type*} [Group H] (ϕ : G ≃* H) :
    MulAut G ≃* MulAut H where
  toFun f := ϕ.symm.trans (f.trans ϕ)
  invFun f := ϕ.trans (f.trans ϕ.symm)
  left_inv _ := by simp [DFunLike.ext_iff]
  right_inv _ := by simp [DFunLike.ext_iff]
  map_mul' := by simp [DFunLike.ext_iff]

end MulAut
end
