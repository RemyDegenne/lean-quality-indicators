@[expose] public section

open Function Set TopologicalSpace

open scoped Topology

universe u v

namespace Subgroup

theorem quotientMapOfLE_isLocallyInjective_of_isOpen
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {T S : Subgroup G} (hTS : T ≤ S) (hT : IsOpen (T.subgroupOf S : Set S)) :
    IsLocallyInjective (quotientMapOfLE hTS) := by
  rcases isOpen_induced_iff.mp hT with ⟨O, hOopen, hO⟩
  have hOneO : (1 : G) ∈ O := by
    have hOneT : (1 : S) ∈ (T.subgroupOf S : Set S) := (T.subgroupOf S).one_mem
    rw [← hO] at hOneT
    exact hOneT
  obtain ⟨V, hVopen, hOneV, hVV⟩ :=
    exists_open_nhds_one_mul_subset (hOopen.mem_nhds hOneO)
  let W : Set G := V ∩ V⁻¹
  have hWopen : IsOpen W := hVopen.inter hVopen.inv
  have hOneW : (1 : G) ∈ W := ⟨hOneV, by simpa using hOneV⟩
  intro q
  induction q using Quotient.inductionOn' with
  | _ g =>
      refine ⟨QuotientGroup.mk '' ((g * ·) '' W),
        QuotientGroup.isOpenMap_coe _ ((isOpenMap_mul_left g) W hWopen), ?_, ?_⟩
      · exact ⟨g * 1, ⟨1, hOneW, rfl⟩, by simp⟩
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ hab
        apply QuotientGroup.eq.mpr
        have habS : a⁻¹ * b ∈ S := by
          have : (g * a)⁻¹ * (g * b) ∈ S :=
            QuotientGroup.eq.mp (by simpa using hab)
          simpa [mul_assoc] using this
        have hainvV : a⁻¹ ∈ V := by simpa [W] using ha.2
        have habO : a⁻¹ * b ∈ O := hVV ⟨a⁻¹, hainvV, b, hb.1, rfl⟩
        have habTsub : (⟨a⁻¹ * b, habS⟩ : S) ∈ (T.subgroupOf S : Set S) := by
          rw [← hO]
          exact habO
        change a⁻¹ * b ∈ T at habTsub
        simpa [mul_assoc] using habTsub

end Subgroup
end
