public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial CFSG.Open

theorem ggBstarAbelianPreimageJUniS1On_of_deg {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarAbelianPreimageJUniS1OnDeg (fun p _ lab => S p lab)) :
    GGBstarAbelianPreimageJUniS1On S := by
  intro G _ _ p B Bs x L D J hcfg hID hN d m hshape hpm hdm E _ hE θ hlab
  exact h G p B Bs x L D J hcfg hID hN d m hshape hpm hdm E hE θ hlab

end CFSG.StandardType
end
