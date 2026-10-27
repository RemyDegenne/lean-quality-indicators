public section

namespace CFSG.Quasithin.G11

open CFSG.Quasithin.G11.P4GL

theorem outerGLInput : OuterGLInput := by
  intro U _ _ _ K hK h3 h4 α P hαP hαα hnot
  classical
  have : Finite (U ≃ₗ[ZMod 2] U) := Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank (ZMod 2) U = m + 3 :=
    ⟨Module.finrank (ZMod 2) U - 3, by omega⟩
  have hm1 : m ≠ 1 := by omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) U hm
  have hKtop : K = ⊤ := eq_top_iff.2 fun g _ => hK g
  let kE : ↥K ≃* (U ≃ₗ[ZMod 2] U) := (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
  let θ : ↥K ≃* Gm m := kE.trans (glvEquiv b)
  obtain ⟨θ', hθ'⟩ := exists_iso_sylow θ P
  have hprops := transport_props θ' α (P : Set ↥K) (UTm m : Set (Gm m)) hθ' hαP hαα
  refine concl_transport θ' α (P : Set ↥K) (UTm m : Set (Gm m)) hθ' ?_
  refine concl_gl hm1 _ hprops.1 hprops.2 ?_
  rintro ⟨A, hA⟩
  obtain ⟨c', hc'⟩ := inner_of_conj θ' α A hA
  exact hnot ⟨(c' : U ≃ₗ[ZMod 2] U), fun k => by rw [hc' k]; simp⟩

end CFSG.Quasithin.G11
end
