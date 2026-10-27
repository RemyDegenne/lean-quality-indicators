public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

theorem mem_sup_zpowers_iff' {A : Subgroup (G6.PermMod 24)} {p : G6.PermMod 24} (hp : p * p = 1)
    (m : G6.PermMod 24) : m ∈ A ⊔ Subgroup.zpowers p ↔ m ∈ A ∨ m * p ∈ A :=
  mem_sup_zpowers_iff (G := G6.PermMod 24) hp m

end CFSG.Quasithin.H.Mathieu
end
