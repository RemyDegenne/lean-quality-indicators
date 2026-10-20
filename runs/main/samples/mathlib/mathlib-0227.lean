public section

universe u v

open Function Cardinal Set Order Ordinal

namespace Cardinal

variable {c : Cardinal}

theorem IsSingular.of_not_isRegular (h₀ : ℵ₀ ≤ c) (hc : ¬ IsRegular c) : IsSingular c :=
  (isRegular_or_isSingular h₀).resolve_left hc

end Cardinal
end
