public section

namespace TauCeti.Toric

variable {N N' N'' V V' V'' : Type*}
  [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V'']
  [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'} {υ : PointedCone ℝ V''}

/-- A compatible map of lattices carrying a source cone into a target cone induces the
contravariant map on dual semigroups by precomposition of characters. -/
noncomputable def dualSemigroupMap (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) : dualSemigroup hi' τ →+ dualSemigroup hi σ :=
  (AddMonoidHom.compHom' f).restrict fun m hm ↦ by
    have hcomp : AddMonoidHom.compHom' f m = m.comp f := by
      ext n
      simp
    rw [SetLike.mem_coe, hcomp, mem_dualSemigroup, hi.realCharacter_comp hi' f g hfg]
    intro x hx
    exact (mem_dualSemigroup hi' m).1 hm (hστ hx)

end TauCeti.Toric
end
