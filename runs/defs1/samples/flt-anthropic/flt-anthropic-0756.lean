namespace P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists

set_option autoImplicit false

set_option maxHeartbeats 3200000

namespace AlgebraicCurve

p2m_open

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

set_option autoImplicit false

set_option autoImplicit false

noncomputable section

p2m_open

namespace Submodule

p2m_open

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

def nestedComapMapMkQEquiv {A B C : Submodule K X} (_hAB : A ≤ B) (hBC : B ≤ C) :
    ((B.comap C.subtype).map (A.comap C.subtype).mkQ : Submodule K _)
      ≃ₗ[K] B ⧸ A.comap B.subtype := by
  set S := A.comap C.subtype with hS
  set T := B.comap C.subtype with hT

  let ψ : (T : Type _) →ₗ[K] (C ⧸ S) := S.mkQ ∘ₗ T.subtype
  have hker : LinearMap.ker ψ = S.comap T.subtype := by
    simp only [ψ, LinearMap.ker_comp, ker_mkQ]
  have hran : LinearMap.range ψ = T.map S.mkQ := by
    simp only [ψ, LinearMap.range_comp, range_subtype]
  let e1 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (T.map S.mkQ : Submodule K _) :=
    (Submodule.Quotient.equiv _ (LinearMap.ker ψ) (LinearEquiv.refl K T)
        (by rw [hker]; simp)).trans
      (ψ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hran))

  have hmap : (S.comap T.subtype).map
      (Submodule.comapSubtypeEquivOfLe hBC : (T : Type _) →ₗ[K] B) = A.comap B.subtype := by
    ext ⟨b, hb⟩
    simp only [mem_map, mem_comap, Submodule.coe_subtype, hS]
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxB⟩, hxA, hxeq⟩
      have hx : x = b := congrArg Subtype.val hxeq
      subst hx; exact hxA
    · intro hbA
      exact ⟨⟨⟨b, hBC hb⟩, hb⟩, hbA, rfl⟩
  let e2 : (T ⧸ S.comap T.subtype) ≃ₗ[K] (B ⧸ A.comap B.subtype) :=
    Submodule.Quotient.equiv _ _ (Submodule.comapSubtypeEquivOfLe hBC) hmap
  exact e1.symm.trans e2

end Submodule
end
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_exists_genus_riemannIndex_of_stichtenothGenusExists
