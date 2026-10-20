namespace MisereGames

universe u

open Form

open Form.Misere.Outcome

public section

open AugmentedForm (Normal)

namespace Form

namespace MisereQuotient

namespace Augmented

/--
The class of a short augmented form in the short quotient.
-/
noncomputable def mkShort (g : AugmentedForm.{u}) (hg : IsShort g) : ShortQuotient.{u} :=
  mk ⟨g, hg⟩

end Augmented
end MisereQuotient
end Form
end
end MisereGames
