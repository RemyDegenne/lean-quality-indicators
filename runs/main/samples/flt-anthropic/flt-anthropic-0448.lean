namespace P2MW.S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

noncomputable section

p2m_open

open scoped Classical

namespace AutomorphicForm

namespace WeylIntegrable

p2m_open

section EntryBox

variable {A : Type*} [CommRing A]

theorem unitBox_eq_preimage (C : Set A) :
    unitBox C = Units.embedProduct (Matrix (Fin 2) (Fin 2) A) ⁻¹' (matBox C ×ˢ (MulOpposite.op '' matBox C)) := by
  ext k
  simp only [unitBox, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, M, hM, hMk⟩
    refine ⟨h1, ?_⟩
    have : M = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hMk
    rwa [← this]

end EntryBox
end WeylIntegrable
end AutomorphicForm
end
end P2MW.S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half
