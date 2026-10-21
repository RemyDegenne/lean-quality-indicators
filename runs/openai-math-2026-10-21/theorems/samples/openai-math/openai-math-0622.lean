namespace OAI

namespace SnakyConditional

theorem children_work_136 : ∀ j, Template HasSnaky 4 (childrenC_136 j) (childrenD_136 j) := by
  intro j
  fin_cases j
  · exact (placed_template_map row_works_6 3 (-1, 3)).mono (by decide)
  · exact (placed_template_map row_works_102 2 (-1, -1)).mono (by decide)

end SnakyConditional
end OAI
