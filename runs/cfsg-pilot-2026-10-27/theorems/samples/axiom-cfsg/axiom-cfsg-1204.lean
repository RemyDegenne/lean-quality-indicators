public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

open CFSG.Quasithin.H13.A5 (Hstar piQ piQ_surjective piQ_eq_one_iff piQ_eq_iff preQ mem_preQ
  preQ_le le_normalizer_preQ perm3_cube_of_odd)

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)

include S

theorem isPGroup_T : IsPGroup 2 T := S.hF.sylow.2.1

end A5Sit
end CFSG.Quasithin.H13
end
