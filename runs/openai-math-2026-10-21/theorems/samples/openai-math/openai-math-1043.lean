namespace OAI

namespace SnakyPrototype.Certificate21

theorem children_work_559_i4 : ∀ j, Template HasSnaky 3 (childrenC_559_i4 j) (childrenD_559_i4 j) := by
  intro j
  fin_cases j
  · exact (placed21_template row_works_5 1 (3, 1)).mono (by decide +kernel)
  · exact row_works_559_i5.mono (by decide +kernel)

end SnakyPrototype.Certificate21
end OAI
