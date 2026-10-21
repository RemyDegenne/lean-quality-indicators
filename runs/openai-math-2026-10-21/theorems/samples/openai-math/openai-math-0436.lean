namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteSiteInnerFamily_image_mem {T X : Type*} [Fintype T] [DecidableEq T] [DecidableEq X]
    (e : T → X) (D : Finset (Finset X)) {A : Finset T}
    (hA : A ∈ finiteSiteInnerFamily e D) : A.image e ∈ D := by
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
  rw [image_finiteSitePreimage e B (Finset.mem_filter.mp hB).2]
  exact (Finset.mem_filter.mp hB).1

end Erdos3
end
end OAI
