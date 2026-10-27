public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.S2MathAs51642Interfaces

open CFSG.StandardType.TableBExc.E6Three (hatAut)

theorem q1E8_component_layer_of_equiv
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {C : Type} [Group C] (e : L ≃* C) :
    ∃ (y : Bs) (u : MulAut L),
      (y : G) ∈ D ∧ ggGamma L hN y = u ∧ orderOf u = p ∧
      (∀ b : Bs, Commute (ggGamma L hN b) u) ∧ J ≤ L ∧
      IsComponentOf ((J.subgroupOf L).map e.toMonoidHom)
        (ggAutFixedSubgroup (MulAut.congr e u)) ∧
      (J.subgroupOf L).map e.toMonoidHom =
        LargeEvenLayer (ggAutFixedSubgroup (MulAut.congr e u)) := by
  obtain ⟨y, u, hy, hyu, hu, hc, hJL, hJcomp, hJlayer⟩ :=
    q1_fixed_component_layer_data hcfg hN
  have hfixed : (ggAutFixedSubgroup u).map e.toMonoidHom =
      ggAutFixedSubgroup (MulAut.congr e u) := by
    ext c
    constructor
    · rintro ⟨l, hl, rfl⟩
      change (MulAut.congr e u) (e l) = e l
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
        using congrArg e hl
    · intro hc
      change (MulAut.congr e u) c = c at hc
      refine ⟨e.symm c, ?_, e.apply_symm_apply c⟩
      change u (e.symm c) = e.symm c
      apply e.injective
      simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using hc
  refine ⟨y, u, hy, hyu, hu, hc, hJL, ?_, ?_⟩
  · rw [← hfixed]
    exact isComponentOf_map_of_injective e.toMonoidHom e.injective
      (CFSG.Assembly.isComponentOf_iff_open.mpr hJcomp)
  · rw [hJlayer, ← largeEvenLayer_map_of_injective e.toMonoidHom e.injective, hfixed]

end CFSG.StandardType
end
