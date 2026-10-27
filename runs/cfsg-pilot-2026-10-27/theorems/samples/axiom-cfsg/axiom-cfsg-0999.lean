public noncomputable section

open scoped Classical Pointwise

namespace CFSG.Wreathed.LocalOddCorePerfectNormalizer

universe u

variable {G : Type u} [Group G]

universe v

variable {A : Type u} {B : Type v} [Group A] [Group B]

open scoped commutatorElement

theorem quotient_involution_central_of_factorization
    (O : Subgroup A) [O.Normal] (x : A)
    (hfactor : O ⊔ Subgroup.centralizer {x} = ⊤) :
    (QuotientGroup.mk' O) x ∈ Subgroup.center (A ⧸ O) := by
  let q := QuotientGroup.mk' O
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O y
  have hg : g ∈ O ⊔ Subgroup.centralizer {x} := hfactor ▸ Subgroup.mem_top g
  obtain ⟨o, ho, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  have hoq : q o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  change q (o * c) * q x = q x * q (o * c)
  rw [map_mul, hoq, one_mul, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp hc]

end CFSG.Wreathed.LocalOddCorePerfectNormalizer
end
