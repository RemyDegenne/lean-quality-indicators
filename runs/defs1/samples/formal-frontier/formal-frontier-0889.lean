@[expose] public section

universe uR uM

namespace LinearMap

/-- The simultaneous range-kernel equivalence for two commuting idempotents.
The four coordinates are the range-range, range-kernel, kernel-range and
kernel-kernel components, and the inverse is the sum of their inclusions. -/
noncomputable def commutingIdempotentsEquiv
    {R : Type uR} [Semiring R]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (p q : Module.End R M)
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : Commute p q) :
    M ≃ₗ[R] ((↥(p.range ⊓ q.range) × ↥(p.range ⊓ q.ker)) ×
      (↥(p.ker ⊓ q.range) × ↥(p.ker ⊓ q.ker))) := by
  refine (commutingIdempotentsPiEquiv ![p, q]
    (by exact pair_idempotent p q hp hq) (by exact pair_commute p q hpq)).trans
    (show ((ε : Fin 2 → Bool) → jointBlock ![p, q] ε) ≃ₗ[R]
      ((↥(p.range ⊓ q.range) × ↥(p.range ⊓ q.ker)) ×
        (↥(p.ker ⊓ q.range) × ↥(p.ker ⊓ q.ker))) from ?_)
  -- Only coordinate rearrangement and equality transport remain after the
  -- finite decomposition. No group structure on the block fibers is used.
  exact
    { toFun := fun b ↦
        (((LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![true, true]))
            (b ![true, true]),
          (LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![true, false]))
            (b ![true, false])),
          ((LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![false, true]))
            (b ![false, true]),
          (LinearEquiv.ofEq _ _ (by exact jointBlock_pair p q ![false, false]))
            (b ![false, false])))
      invFun := fun z ε ↦
        ⟨if ε 0 then (if ε 1 then (z.1.1 : M) else (z.1.2 : M))
          else (if ε 1 then (z.2.1 : M) else (z.2.2 : M)), by
          rw [jointBlock_pair]
          cases h₀ : ε 0 <;> cases h₁ : ε 1
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.2.2.property
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.2.1.property
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.1.2.property
          · simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte] using z.1.1.property⟩
      left_inv := by
        intro b
        funext ε
        apply Subtype.ext
        cases h₀ : ε 0 <;> cases h₁ : ε 1
        · have hε : ε = ![false, false] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
        · have hε : ε = ![false, true] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
        · have hε : ε = ![true, false] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
        · have hε : ε = ![true, true] :=
            funext (Fin.forall_fin_two.mpr ⟨h₀, h₁⟩)
          simpa only [h₀, h₁, Bool.false_eq_true, ↓reduceIte,
            LinearEquiv.coe_ofEq_apply] using
            congrArg (fun η : Fin 2 → Bool ↦ (b η : M)) hε.symm
      right_inv := by
        intro z
        apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> rfl
      map_add' := by
        intro b c
        apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> rfl
      map_smul' := by
        intro r b
        apply Prod.ext <;> apply Prod.ext <;> apply Subtype.ext <;> rfl }

end LinearMap
end
