public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification

variable {X : Type} [Group X]

theorem exists_eq_conj_G2 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .G2 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .G2 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f hf hker hZ
    (MonoidHom.id ↥(adjointGroup Tag.G2 (GaloisField 3 1))) Function.surjective_id
    (ker_id_le_center _) center_adjointGroup_eq_bot
  exact exists_eq_conj_of_mulEquiv e
    (fun β hβ => mem_inner_of_odd_adjoint_G2 _ natCard_galoisField_three β hβ) α hodd

end CFSG.ClassicalInvolution.Q3.Q3T
end
