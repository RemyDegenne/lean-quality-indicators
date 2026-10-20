@[expose] public section

universe u v w x

namespace Module

section Ring

variable (R : Type u) [Ring R]

variable (M : Type v) [AddCommGroup M] [Module R M]

variable {R M}

theorem IsCoherent.of_exact {N : Type w} {P : Type x}
    [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
    [Module.IsCoherent R M] [Module.IsCoherent R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.IsCoherent R N where
  finite := Module.Finite.of_exact h hg
  finitePresentation_submodule Q hQ := by
    let _ : Module.Finite R Q := Module.Finite.of_fg hQ
    let r : Q →ₗ[R] P := g ∘ₗ Q.subtype
    let I : Submodule R P := LinearMap.range r
    let q : Q →ₗ[R] I := r.rangeRestrict
    have hq : Function.Surjective q := LinearMap.surjective_rangeRestrict r
    have hI : I.FG := Submodule.fg_range r
    let _ : Module.IsCoherent R I := IsCoherent.submodule I hI
    have hker : (LinearMap.ker q).FG := Module.FinitePresentation.fg_ker q hq
    let _ : Module.Finite R (LinearMap.ker q) := Module.Finite.of_fg hker
    let j : LinearMap.ker q →ₗ[R] N := Q.subtype ∘ₗ (LinearMap.ker q).subtype
    have hj : ∀ z, j z ∈ LinearMap.range f := by
      intro z
      rw [← h.linearMap_ker_eq]
      have hz := congrArg Subtype.val z.2
      change r z.1 = 0 at hz
      simpa [j, r] using hz
    let k : LinearMap.ker q →ₗ[R] M :=
      (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
        j.codRestrict (LinearMap.range f) hj
    have hk : Function.Injective k := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa [k, j] using congrArg f hab
    let _ : Module.IsCoherent R (LinearMap.range k) := IsCoherent.range k
    let _ : Module.FinitePresentation R (LinearMap.ker q) :=
      Module.FinitePresentation.of_equiv (R := R) (M := LinearMap.range k)
        (N := LinearMap.ker q) (LinearEquiv.ofInjective k hk).symm
    exact Module.finitePresentation_of_ker q hq

end Ring
end Module
end
