namespace OAI

namespace SnakyPrototype.Certificate21

theorem envelope_exact_164 : envelope_164 =
    insert (3, 3) (Finset.univ.biUnion childrenD_164) := by
  exact envelope_eq_combination childrenD_164 (3, 3) envelope_164
    pivot_mem_164 child_envelope_sub_164 envelope_origin_164

end SnakyPrototype.Certificate21
end OAI
