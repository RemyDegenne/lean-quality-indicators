public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace TauCeti

namespace AbelianK0

variable [EssentiallySmall.{w} A]

section CochainComplex

variable (K : CochainComplex A ℤ)

section QuasiIso

variable {K} {L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]

include f in
theorem homologyEulerChar_eq_of_quasiIso (s : Finset ℤ) :
    homologyEulerChar K s = homologyEulerChar L s :=
  Finset.sum_congr rfl fun n _ => by
    have : IsIso (HomologicalComplex.homologyMap f n) :=
      (quasiIsoAt_iff_isIso_homologyMap f n).mp inferInstance
    rw [of_congr (asIso (HomologicalComplex.homologyMap f n))]

end QuasiIso
end CochainComplex
end AbelianK0
end TauCeti
end
