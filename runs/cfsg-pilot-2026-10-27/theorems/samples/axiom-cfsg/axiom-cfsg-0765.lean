public noncomputable section

namespace CFSG.StandardType.TwE6ThreeLang

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc
  CFSG.StandardType.TBE6IndTwist CFSG.LocalAnalysis.StandardType.GGTBE6Cover
  CFSG.StandardType.TableBExc.E6Three

variable {K L : Type} [Field K] [Finite K] [CharP K 2] [Group L]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)
  (φ : fixedGroup K θ.toRingHom →* L)
  (δ : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* MulAut L)

theorem ofAdd_mem_range_of_mem_hyp {A : Subgroup (MulAut L)}
    (κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3))
    (hκr : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6)
    {v : Fin Tag.E6.rank → ZMod 3} (hv : v ∈ NoOffRest.hypE6) :
    Multiplicative.ofAdd v ∈ κ.range := by
  rcases hκr with h | h
  · rw [h]
    exact Subgroup.mem_top _
  · exact (h v).2 hv

end CFSG.StandardType.TwE6ThreeLang
end
