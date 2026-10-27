@[expose] public section

namespace LinearMap

/-- The kernel-product equivalence of a linear map with a specified right
inverse. It sends `(k, b)` to `k + g b`, and its inverse has coordinates
`a - g (f a)` and `f a`. The splitting formula used for row kernels in
Weibel's *The K-book*, Chapter I, §1.2.1 and Theorem I.1.3, only requires a
semiring of scalars, an additive group source and an additive monoid target. -/
noncomputable def kerProdEquivOfRightInverse
    {R A B : Type*} [Semiring R]
    [AddCommGroup A] [Module R A] [AddCommMonoid B] [Module R B]
    (f : A →ₗ[R] B) (g : B →ₗ[R] A)
    (hfg : f.comp g = LinearMap.id) :
    (f.ker × B) ≃ₗ[R] A := by
  let φ : (f.ker × B) →ₗ[R] A := f.ker.subtype.coprod g
  have hfg' (b : B) : f (g b) = b := by
    simpa using LinearMap.congr_fun hfg b
  have hg : Function.Injective g := g.injective_of_comp_eq_id f hfg
  let kproj : A →ₗ[R] f.ker :=
    LinearMap.codRestrict f.ker (LinearMap.id - g.comp f) fun a ↦ by
      rw [mem_ker]
      apply hg
      change (g.comp f) (a - g (f a)) = g 0
      rw [map_sub]
      simp only [comp_apply, hfg', map_zero, sub_self]
  let ψ : A →ₗ[R] (f.ker × B) := kproj.prod f
  exact LinearEquiv.ofLinearMap φ ψ
    (by
      apply LinearMap.ext
      intro a
      change (a - g (f a)) + g (f a) = a
      exact sub_add_cancel a (g (f a)))
    (by
      apply LinearMap.ext
      intro p
      apply Prod.ext
      · apply Subtype.ext
        change (p.1.val + g p.2) - g (f (p.1.val + g p.2)) = p.1.val
        rw [map_add, mem_ker.mp p.1.2, zero_add, hfg']
        exact add_sub_cancel_right _ _
      · change f (p.1.val + g p.2) = p.2
        rw [map_add, mem_ker.mp p.1.2, zero_add, hfg'])

end LinearMap
end
