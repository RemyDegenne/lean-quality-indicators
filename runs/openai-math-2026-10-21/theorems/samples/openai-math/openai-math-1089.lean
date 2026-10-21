namespace OAI

namespace SnakyConditional

theorem row_works_223 : Template HasSnaky 7 required_223 envelope_223 := by
  refine compose HasSnaky 6 childrenC_223 childrenD_223 children_work_223 (0, 0)
    required_223 envelope_223 pivot_mem_223 child_required_sub_223 child_envelope_sub_223 ?_
  intro b hb; exact common_sub_223 (mem_commonEnvelope childrenD_223 b hb)

end SnakyConditional
end OAI
