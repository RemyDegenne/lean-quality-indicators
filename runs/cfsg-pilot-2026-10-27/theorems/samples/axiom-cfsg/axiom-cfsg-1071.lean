public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {X N : Subgroup G} [X.Normal] [N.Normal]

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

variable {B : LinearMap.BilinForm (ZMod 2) W}

variable {π : ↥X →* Multiplicative W}

theorem toAdd_pi_commSelf_zpow (hπsurj : Function.Surjective π)
    (hπker : π.ker = Subgroup.center ↥X) (g : G) (k : ℤ) (x : ↥X) :
    Multiplicative.toAdd (π (commSelf (g ^ k) x)) =
      Multiplicative.toAdd (π x) -
        (conjEquiv hπsurj hπker g ^ k) (Multiplicative.toAdd (π x)) := by
  have h := conjEquiv_apply hπsurj hπker (g ^ k) x
  rw [conjEquiv_zpow] at h
  rw [commSelf, map_mul, map_inv, toAdd_mul, toAdd_inv, ← h]
  abel

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
end
