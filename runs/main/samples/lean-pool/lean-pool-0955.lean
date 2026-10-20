@[expose] public section

namespace GaleStewartGame.BorelDet.One

open Stream'.Discrete Descriptive Tree Game PreStrategy

open CategoryTheory

variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}

noncomputable section «Section1»

namespace Lift'

variable (H : Lift' hyp)

variable (hp : IsPosition H.x.val Player.one)
  (R : ResStrategy (gameAsTrees hyp) Player.one H.x.val.length) (hR : R.res (by simp) = H.R)

@[simp] lemma extensionLift_liftShort : (H.extensionLift hp R).liftShort = H.liftShort := by
  rw [← extensionLift_take, Lift.liftShort_take]

end Lift'
end «Section1»
end GaleStewartGame.BorelDet.One
end
