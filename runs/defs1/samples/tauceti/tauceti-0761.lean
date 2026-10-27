public section

namespace TauCeti.Hodge

universe u v

namespace HodgeStructureOn

variable {W : Type u} [AddCommGroup W] [Module ℂ W]

variable {ω : Conjugation W} {n : ℤ}

/-- Conjugation restricts to a **real**-linear isomorphism from the Hodge component `H^{p,n-p}`
onto its conjugate `H^{n-p,p}`. It is not complex-linear: it is conjugate-linear, so it is only an
isomorphism after restricting scalars to `ℝ`. -/
def pieceConjEquiv (hs : HodgeStructureOn W ω n) (p : ℤ) :
    hs.piece p ≃ₗ[ℝ] hs.piece (n - p) where
  toFun x := ⟨ω.toEquiv x, hs.conj_mem_piece x.2⟩
  invFun y := ⟨ω.toEquiv y, by simpa only [sub_sub_cancel] using hs.conj_mem_piece y.2⟩
  map_add' x y := by ext; exact map_add _ _ _
  map_smul' r x := by
    ext
    simp only [Submodule.coe_smul_of_tower, RingHom.id_apply, ← Complex.coe_smul,
      ω.toEquiv.map_smulₛₗ, Complex.conj_ofReal]
  left_inv x := by ext; exact ω.apply_apply _
  right_inv y := by ext; exact ω.apply_apply _

end HodgeStructureOn
end TauCeti.Hodge
end
