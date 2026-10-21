namespace OAI

noncomputable section

namespace CubicFirstMoment

lemma cubicThetaExceptionalProjection_idempotent (z : ℂ) :
    cubicThetaExceptionalProjection z*cubicThetaExceptionalProjection z=
      cubicThetaExceptionalProjection z :=
  (cubicThetaEnergyPencil z).ker.isIdempotentElem_starProjection

end CubicFirstMoment
end
end OAI
