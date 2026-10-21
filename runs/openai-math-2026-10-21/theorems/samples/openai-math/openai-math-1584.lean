namespace OAI

namespace SnakyPrototype.Certificate21

theorem envelope_exact_521_i1 : envelope_521_i1 =
    insert (2, 3) (Finset.univ.biUnion childrenD_521_i1) := by
  exact envelope_eq_combination childrenD_521_i1 (2, 3) envelope_521_i1
    pivot_mem_521_i1 child_envelope_sub_521_i1 envelope_origin_521_i1

end SnakyPrototype.Certificate21
end OAI
