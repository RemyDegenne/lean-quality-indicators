namespace OAI

noncomputable section

namespace Tachikawa

namespace LeftCorner

variable {R : Type*} [Ring R] {p : R} (hp : p * p = p)

include hp in
lemma projective : Module.Projective R (LeftCorner p) :=
  Module.Projective.of_split (LeftCorner p).subtype (projection hp) (projection_comp_inclusion hp)

end LeftCorner
end Tachikawa
end
end OAI
