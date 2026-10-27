public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native B6

namespace E2P

variable {Γ : Type} [Group Γ] [Finite Γ] {H T M : Subgroup Γ}

namespace Setting

variable {L : Subgroup (E2.StarQuot M H)} {K : Subgroup Γ} (S : Setting H T M L K)

include S

theorem isSolvable_jbar : Group.IsSolvable (jbar M H) := by
  rw [← S.kerIn_bar]
  exact S.minPar_bar.isSolvable_kerIn

end Setting
end E2P
end CFSG.Quasithin
end
