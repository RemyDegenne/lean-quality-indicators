@[expose] public section

namespace SyntheticEuclid4

variable [I : IncidenceGeometry] {a a1 a2 b b1 b2 c d e f g h i j k l x y :
  IncidenceGeometry.Point} {L M N O P Q R S T U W V X : IncidenceGeometry.Line}
  {α β : IncidenceGeometry.Circle} {r : ℝ}

open IncidenceGeometry

theorem not_B_of_sameside (abL : SameSide a b L) (cL : OnLine c L) : ¬B a c b :=
  fun Bacb => (diffside_of_B_offline' Bacb cL (not_online_of_sameside abL)).2.2 abL

end SyntheticEuclid4
end
