public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem layer_inf_centralizer_eq_KBar (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    (h : GSThmB.layerIn (fixedPoints (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (hs.setup.tBar i j))) = fixedPoints (conjOn (layer (MBar (w ^ (orderOf w / 2) * t ^ i *
        z ^ j))) (hs.setup.tBar i j))) :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hs.setup.tBar i j} =
      KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  rw [layerIn_fixedPoints_conjOn, fixedPoints_conjOn_eq, h412.layerIn_layer_centralizer,
    subgroupOf_inj, inf_of_le_left hs.KBar_le_layer] at h
  rw [h, inf_comm]

end Setting46e
end CFSG.ComponentClassification.HarrisLit
end
