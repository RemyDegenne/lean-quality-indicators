public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P55

variable (ℓ : Line Γ)

variable {ℓ}

section Transport

variable (F : FanTree Γ G) {g : G} {s : ℤ} (hg : IsShift ℓ g s)

include F hg

omit F in
theorem IsShift.cen_edgeStab_iff (z : G) (i : ℤ) :
    g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) (i + s) : Set G) ↔
      z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) :=
  P55.cen_conj_iff g (fun k => IsShift.edgeStab_iff hg i k) z

end Transport
end P55
end CFSG.Quasithin.Fan86
end
