namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

namespace Lech.Koszul

universe u

variable {R : Type u} [CommRing R]

lemma length_le_sum_of_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
    Module.length R S.X₂ ≤ Module.length R S.X₁ + Module.length R S.X₃ := by
  have he : Function.Exact S.f.hom S.g.hom := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · exact S.moduleCat_exact_iff.mp hS x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f : S.X₁ ⟶ S.X₃ => f y) S.zero
  have he' : Function.Exact S.f.hom S.g.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, LinearMap.exact_iff.mp he]
  exact (Lech.length_le_add_of_exact S.f.hom S.g.hom.rangeRestrict
    S.g.hom.surjective_rangeRestrict he').trans
    (add_le_add le_rfl (Module.length_le_of_injective S.g.hom.range.subtype
      S.g.hom.range.subtype_injective))

end Lech.Koszul
end
end OAI
