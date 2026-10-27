public section

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.RootSystem

open CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld.RankTwo

open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.Pres

open scoped commutatorElement

section WeylConj

variable {F K : Type} [Field F] [Field K] [CharP K 2] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c)
  {ι : F →+* K} {ζ : K}

variable {hσ} (hι : ∀ x, σ (ι x) = ι x)

include hι

variable {b c : F} (hb : ι b = ζ + σ ζ)

include hb

theorem weyl₃_suS_nd23 (p : Fin 2 → F) :
    weyl₃ σ hσ * suS σ hσ ι ζ (-(sr nd2 + sr nd3)) p * (weyl₃ σ hσ)⁻¹ =
      suS σ hσ ι ζ (-(sr nd2 + sr nd3)) (planeRefl b c planeOne p) := by
  simp only [suS, shortIdx_nd23, kap_planeRefl hb hι]
  rw [← CharTwo.neg_eq (σ (kap ι ζ p)), ← suElt_swap hσ idx_nd23]
  exact conj_suElt_of_mat hσ hπ₃ (mat_weyl₃ hσ) idx_nd23 (by decide) (by decide) (by decide) _

end WeylConj
end CFSG.Timmesfeld.ARS.CaseOADeg
end
