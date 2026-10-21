namespace OAI

namespace SnakyPrototype.Certificate21

theorem envelope_exact_605 : envelope_605 =
    insert (4, 3) (Finset.univ.biUnion childrenD_605) := by
  exact envelope_eq_combination childrenD_605 (4, 3) envelope_605
    pivot_mem_605 child_envelope_sub_605 envelope_origin_605

end SnakyPrototype.Certificate21
end OAI
