public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution

section Layer

variable {G : Type*} [Group G]

theorem componentLayerOf_subgroupOf_normal (C : Subgroup G) :
    ((GorensteinWalter.componentLayerOf C).subgroupOf C).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (GorensteinWalter.componentLayerOf_isNormalIn C).1).mpr
    (GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.componentLayerOf_isNormalIn C))

end Layer
end CFSG.ClassicalInvolution.Q3
end
