public section

namespace CFSG.Quasithin.C116Three

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.R3c23 CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {M C : Subgroup V}

section Std

theorem mem_jwBg {D : L3Data G M C} {B : Subgroup (MulAut V)} {γ : L3.Γ} :
    γ ∈ jwBg D B ↔ L3F.Ustd γ ∧ D.rho γ ∈ B := by
  classical
  simp [jwBg]

end Std
end CFSG.Quasithin.C116Three
end
