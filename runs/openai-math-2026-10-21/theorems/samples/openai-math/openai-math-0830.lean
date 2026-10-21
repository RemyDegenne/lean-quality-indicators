namespace OAI

noncomputable section

open scoped BigOperators

namespace CubicFirstMoment

lemma principalLatticeTheta_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun a : Eisenstein => (Real.exp (-norm a*t/residueHeckeScale 1):ℂ)) := by
  have hA := residueHeckeScale_pos (q := 1) one_ne_zero
  have h := schwartz_summable_eisenstein
    (radialGaussianSchwartz (t/residueHeckeScale 1) (div_pos ht hA))
  convert h using 1
  funext a
  rw [radialGaussianSchwartz_apply]
  change (Real.exp (-Complex.normSq (a:ℂ)*t/residueHeckeScale 1):ℂ)=
    (Real.exp (-(t/residueHeckeScale 1)*‖(a:ℂ)‖^2):ℂ)
  rw [Complex.normSq_eq_norm_sq]
  congr 2
  ring

end CubicFirstMoment
end
end OAI
