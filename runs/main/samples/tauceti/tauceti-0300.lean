public noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {k G Q : Type u} [CommRing k] [Group G] [Group Q] [Fintype G] [Fintype Q]
  (φ : G →* Q) {M : Rep k Q} {N : Rep k G}

@[reassoc]
theorem posMap_comp_map (f : Rep.res φ M ⟶ N) {N' : Rep k G} (g : N ⟶ N') (n : ℕ) [NeZero n] :
    posMap φ f n ≫ (tateCohomologyFunctor n).map g = posMap φ (f ≫ g) n := by
  refine (cancel_mono ((_root_.TateCohomology.isoGroupCohomology n).hom.app N')).1 ?_
  rw [Category.assoc, NatTrans.naturality, posMap_comp_isoGroupCohomology_hom_assoc,
    posMap_comp_isoGroupCohomology_hom]
  exact congrArg (_ ≫ ·) (groupCohomology.map_comp φ (MonoidHom.id G) f g n).symm

end TauCeti.TateCohomology
end
