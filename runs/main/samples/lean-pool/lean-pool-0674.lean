@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)

theorem bmc_capPeel_split (m : ℕ) :
    bundleMapClass f (capPeelRotation m) =
      HomSpace.comp f ((m + 1) + (m + 1)) ((m + 1) + (m + 1))
        ((m + m) + 2)
        (bundleMapClass f ((capPeelPerm m) :
          Fin ((m + 1) + (m + 1)) ≃ Fin ((m + 1) + (m + 1))))
        (bundleMapClass f (finCongr
          (by omega : (m + 1) + (m + 1) = (m + m) + 2))) := by
  rw [bundleMapClass_comp]
  exact bundleMapClass_congr f (capPeelEquiv_split m)

end RS
end
