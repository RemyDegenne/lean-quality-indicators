namespace OAI

namespace SnakyPrototype.Certificate21

theorem row_works_22 : Template HasSnaky 2 required_22 envelope_22 := by
  refine compose HasSnaky 1 childrenC_22 childrenD_22 children_work_22 (0, 3)
    required_22 envelope_22 pivot_mem_22 child_required_sub_22 child_envelope_sub_22 ?_
  intro b hb
  exact common_sub_22 (mem_commonEnvelope childrenD_22 b hb)

end SnakyPrototype.Certificate21
end OAI
