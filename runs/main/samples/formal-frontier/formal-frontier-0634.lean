@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

theorem indDualRealizationEssSurj : indDualRealization.{u}.EssSurj :=
  ⟨fun T => ⟨skeletalQuotientIndDual T, ⟨skeletalQuotientRealizationIso T⟩⟩⟩

end Profinite
end
