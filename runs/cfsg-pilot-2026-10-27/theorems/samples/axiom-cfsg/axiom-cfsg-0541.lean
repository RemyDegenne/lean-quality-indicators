public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem conjAct_mem_autOn_of_conj {V W : Subgroup G} {b w : G}
    (hb : b ∈ Subgroup.normalizer (V : Set G)) (hw : w ∈ Subgroup.normalizer (V : Set G))
    (hbw : b * w * b⁻¹ ∈ W) :
    conjAct V ⟨b, hb⟩ * conjAct V ⟨w, hw⟩ * (conjAct V ⟨b, hb⟩)⁻¹ ∈ autOn W V := by
  have hbwV : b * w * b⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    mul_mem (mul_mem hb hw) (inv_mem hb)
  rw [conjAct_conj hb hw hbwV]
  exact mem_autOn_iff.mpr ⟨_, hbwV, hbw, rfl⟩

end SBc17
end CFSG.Quasithin
end
