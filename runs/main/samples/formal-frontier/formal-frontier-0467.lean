set_option warningAsError true

@[expose] public section

namespace Bass

universe u v

variable {R : Type u} [Ring R]

theorem IsVonNeumannRegular.exists_principalRightIdeals_isCompl
    (h : IsVonNeumannRegular R) (a : R) :
    ∃ x : R,
      IsCompl (principalRightIdeal a) (principalRightIdeal (1 - a * x)) := by
  obtain ⟨x, hx⟩ := h a
  exact ⟨x, principalRightIdeals_isCompl_of_innerInverse hx⟩

end Bass
end
