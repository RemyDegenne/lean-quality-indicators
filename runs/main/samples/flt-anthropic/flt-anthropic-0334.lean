namespace P2MW.S_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Quaternion NumberField

open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

namespace P2mKcNormUnits

section General

variable {S : Type*} [CommRing S] {c₁ c₃ : S}

open scoped IsMulCommutative in

theorem isIntegral_nrd_of_isIntegral {O : Type*} [CommRing O] [Algebra O S] {m : ℍ[S, c₁, c₃]}
    (hm : IsIntegral O m) : IsIntegral O (nrd m) := by
  let T : Subalgebra O ℍ[S, c₁, c₃] := Algebra.adjoin O {m, star m}
  haveI : IsMulCommutative T := by
    refine Algebra.isMulCommutative_adjoin O ?_
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · rw [mul_star_eq_coe_nrd, star_mul_eq_coe_nrd]
    · rw [mul_star_eq_coe_nrd, star_mul_eq_coe_nrd]
    · rfl
  have hmT : m ∈ T := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hsT : star m ∈ T := Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  have h1 : IsIntegral O (⟨m, hmT⟩ : T) :=
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp hm
  have h2 : IsIntegral O (⟨star m, hsT⟩ : T) :=
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (isIntegral_star hm)
  have h3 : IsIntegral O ((⟨m, hmT⟩ : T) * ⟨star m, hsT⟩) := h1.mul h2
  have h4 : IsIntegral O (m * star m) := (isIntegral_algHom_iff T.val Subtype.val_injective).mpr h3
  rw [mul_star_eq_coe_nrd, ← QuaternionAlgebra.coe_algebraMap] at h4
  have h5 : IsIntegral O (IsScalarTower.toAlgHom O S ℍ[S, c₁, c₃] (nrd m)) := by
    rwa [IsScalarTower.coe_toAlgHom']
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom O S ℍ[S, c₁, c₃]) ?_).mp h5
  intro x y h
  rw [IsScalarTower.coe_toAlgHom', QuaternionAlgebra.coe_algebraMap] at h
  exact QuaternionAlgebra.coe_injective h

end General
end P2mKcNormUnits
end
end P2MW.S_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits
