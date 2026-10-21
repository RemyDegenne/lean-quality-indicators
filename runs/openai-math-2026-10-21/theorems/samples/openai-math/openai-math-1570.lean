namespace OAI

noncomputable section

namespace CKSADM

noncomputable section

open Set Filter Finset CKSSphericalHarmonics CKSInducedSphere CKSSphericalChart CKSBending

open scoped Topology ContDiff

theorem constructed_metric_word_decay (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ)
    {R : ℝ} (hR : 12 ≤ R) (i j : Ix) (w : List Ix) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in spatialInfinity,
      |cartWord w (fun y => metric (cartB f₀ m R) y i j-(if i=j then 1 else 0)) x| ≤
        C*‖x‖^(-(1+w.length:ℝ)) :=
  SymbolN.word (constructed_metric_decay f₀ hf₀ m hR i j) w

end
end CKSADM
end
end OAI
