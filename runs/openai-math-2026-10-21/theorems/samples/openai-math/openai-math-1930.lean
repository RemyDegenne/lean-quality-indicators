namespace OAI

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {J : Type*} {c : J → ℝ}

theorem exists_simultaneous_modular_cluster [Nontrivial H]
    (hc : ∀ j, 0 ≤ c j) (F : WeakMapFamily M c) :
    ∃ G ∈ closure (familyRowOrbit hc F), ∀ j a b, (G j).map (a * b) = (G j).map a * b := by
  obtain ⟨C, hCF, hne, hcl, hi, hm⟩ := exists_minimal_familyRowFamily hc F
  obtain ⟨G, hG⟩ := hne
  refine ⟨G, hCF hG, ?_⟩
  intro j
  obtain ⟨hdcl, hdi, hdm⟩ := minimal_family_coordinate hc C hcl hi hm j
  apply minimal_row_family_right_module (hc j) (F j) ((fun A => A j) '' C) _ hdcl hdi hdm
    (G j) ⟨G, hG, rfl⟩
  rintro B ⟨A, hA, rfl⟩
  exact family_orbitClosure_coordinate hc F (hCF hA) j

end
end KadisonKastler
end OAI
