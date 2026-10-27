public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open CFSG

namespace FDRep

open CategoryTheory CategoryTheory.Limits

universe u v

section homSpace

lemma finrank_hom_eq_zero_of_not_iso_simple
    {k : Type u} [Field k]
    {G : Type v} [Monoid G]
    {S T : FDRep k G} [Simple S] [Simple T]
    (h : IsEmpty (S ≅ T)) :
    Module.finrank k (S ⟶ T) = 0 := by
  haveI : Subsingleton (S ⟶ T) :=
    hom_subsingleton_of_not_iso_simple h
  exact Module.finrank_zero_of_subsingleton

end homSpace
end FDRep
end
