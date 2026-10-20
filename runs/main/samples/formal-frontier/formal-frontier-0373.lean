@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

@[simp] theorem indDualRealization_map
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} (f : Q ⟶ R) :
    indDualRealization.map f = indDualRealizationMap f := rfl

end Profinite
end
