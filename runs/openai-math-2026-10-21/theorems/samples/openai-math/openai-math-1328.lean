namespace OAI

namespace SnakyPrototype.Certificate21

theorem children_work_680_i0 : ∀ j, Template HasSnaky 5 (childrenC_680_i0 j) (childrenD_680_i0 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_56 2 (4, 0)).mono (by decide +kernel)
  · exact (placed21_template row_works_179 6 (5, 5)).mono (by decide +kernel)

end SnakyPrototype.Certificate21
end OAI
