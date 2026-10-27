public section

namespace CFSG

namespace FiveTransitive.KernelImageGeneration

theorem eq_closure_insert
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (S Q : Subgroup G) (hQ : S ⊓ f.ker = Q)
    (a : G) (hgen : Q = Subgroup.zpowers a)
    (s : Set G) (hs : s ⊆ S)
    (himage : S.map f = Subgroup.closure (f '' s)) :
    S = Subgroup.closure (insert a s) := by
  let K := Subgroup.closure (insert a s)
  have haQ : a ∈ Q := by rw [hgen]; exact Subgroup.mem_zpowers a
  have hKS : K ≤ S := (Subgroup.closure_le S).mpr (by
    intro x hx
    rcases hx with rfl | hx
    · exact (hQ.ge haQ).1
    · exact hs hx)
  have hker : S ⊓ f.ker ≤ K := by
    rw [hQ, hgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert a s))
  apply eq_of_kernel_image f S K hKS hker
  rw [himage]
  apply (Subgroup.closure_le (K.map f)).mpr
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, Subgroup.subset_closure (Set.mem_insert_of_mem a hg), rfl⟩

end FiveTransitive.KernelImageGeneration
end CFSG
end
