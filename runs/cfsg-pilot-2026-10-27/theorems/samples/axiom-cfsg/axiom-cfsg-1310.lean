public section

open CFSG.Open

open CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] {D : Subgroup G}

theorem bar_core (D : Subgroup G) : bar D (aschbacherThm5Core D) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, hO, rfl⟩ := (mem_bar_iff D _ x).mp hx
  exact (toBar_eq_one_iff D h).mpr hO

end SectionSix
end CFSG.ComponentClassification.AschbacherTheorem5
end
