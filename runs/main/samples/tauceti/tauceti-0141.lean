public section

namespace TauCeti

open AlgebraicGeometry

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace Divisor

theorem finite_ker_degreeClass (hF : IsFunctionField k F) [Finite k] :
    Finite (Divisor.degreeClass hF).ker := by
  obtain ⟨P⟩ := Place.nonempty hF
  set B : Divisor k F := WeilDivisor.ofPoint P with hBdef
  have hBpos : 1 ≤ degree B := by
    rw [hBdef, degree_ofPoint]
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  set n : ℕ := genus k F
  have hgen : (genus k F : ℤ) ≤ n * degree B := by nlinarith [Int.natCast_nonneg (genus k F)]
  set m : ℕ := (n * degree B).toNat
  have hmcast : (m : ℤ) = n * degree B := Int.toNat_of_nonneg (by positivity)
  set T : Set (Divisor k F) := {D | WeilDivisor.IsEffective D ∧ degree D = (m : ℤ)}
  have : Finite T :=
    ((finite_setOf_isEffective_degree_le hF m).subset (t := T) fun _ hD ↦
      ⟨hD.1, hD.2.le⟩).to_subtype
  have hnB : degree (n • B) = n * degree B := by rw [map_nsmul, nsmul_eq_mul]
  have hker : ∀ A : T, (Place.orderSystem hF).divisorClass ((A : Divisor k F) - n • B) ∈
      (Divisor.degreeClass hF).ker := by
    intro A
    rw [AddMonoidHom.mem_ker, degreeClass_divisorClass, degree_sub, hnB, A.2.2, hmcast, sub_self]
  refine Finite.of_surjective (fun A : T ↦ (⟨_, hker A⟩ : (Divisor.degreeClass hF).ker)) ?_
  rintro ⟨c, hc⟩
  obtain ⟨D, rfl⟩ := (Place.orderSystem hF).divisorClass_surjective c
  rw [AddMonoidHom.mem_ker, degreeClass_divisorClass] at hc
  obtain ⟨A, hA0, hAdeg, hAeq⟩ := exists_isEffective_linearlyEquivalent_add_nsmul hF hgen hc
  refine ⟨⟨A, hA0, by rw [hAdeg, hmcast]⟩, Subtype.ext ?_⟩
  have hclass : (Place.orderSystem hF).divisorClass A =
      (Place.orderSystem hF).divisorClass (D + n • B) :=
    ((Place.orderSystem hF).divisorClass_eq_iff).mpr hAeq
  -- Unfold the value of the surjection at the chosen preimage before rewriting.
  dsimp only
  rw [map_sub, hclass, map_add, add_sub_cancel_right]

end Divisor
end TauCeti
end
