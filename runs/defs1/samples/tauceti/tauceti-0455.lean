public section

namespace TauCeti.HomCokernel

open CategoryTheory

universe u v t

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
  [Linear R C] {S : ShortComplex C} {P Y : C}

/-- Replacing a relation object by its quotient identifies the resulting Hom cokernel
with the kernel of the cocycle restriction map. -/
noncomputable def equivKerRestrict (hS : S.Exact) [Epi S.g] (i : S.X₃ ⟶ P) :
    HomCokernel R i Y ≃ₗ[R]
      LinearMap.ker (restrict R (S.g ≫ i) S.f (Y := Y) (by simp)) :=
  LinearEquiv.ofBijective
    ((precomp R i S.g).codRestrict _ fun x ↦
      (exact_precomp_restrict R hS i).apply_apply_eq_zero x)
    ⟨fun _ _ h ↦ precomp_injective R i S.g (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨y, hy⟩ := (exact_precomp_restrict R hS i x.val).mp x.property
      exact ⟨y, Subtype.ext hy⟩⟩

end TauCeti.HomCokernel
end
