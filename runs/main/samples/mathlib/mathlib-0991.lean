@[expose] public section

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) {S : Type*} [CommSemiring S]

variable [Algebra R S] {P : Type*} [CommSemiring P]

namespace IsLocalization

section Away

variable (x : R)

namespace Away

variable [IsLocalization.Away x S]

variable {g : R →+* P}

variable (S) (Q : Type*) [CommSemiring Q] [Algebra P Q]

lemma mul (T : Type*) [CommSemiring T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away (algebraMap R S y) T] :
    IsLocalization.Away (y * x) T := by
  refine mk _ ?_ (fun z ↦ ?_) (fun a b h ↦ ?_)
  · simp only [map_mul, IsUnit.mul_iff, IsScalarTower.algebraMap_apply R S T]
    exact ⟨algebraMap_isUnit _, IsUnit.map _ (algebraMap_isUnit x)⟩
  · obtain ⟨m, p, hpq⟩ := surj (algebraMap R S y) z
    obtain ⟨n, a, hab⟩ := surj x p
    use m + n, a * x ^ m * y ^ n
    simp only [mul_pow, pow_add, map_pow, map_mul, ← mul_assoc, hpq,
      IsScalarTower.algebraMap_apply R S T, ← hab]
    ring
  · repeat rw [IsScalarTower.algebraMap_apply R S T] at h
    obtain ⟨n, hn⟩ := exists_of_eq (algebraMap R S y) h
    simp only [← map_pow, ← map_mul, ← map_mul] at hn
    obtain ⟨m, hm⟩ := exists_of_eq x hn
    use n + m
    convert_to y ^ m * x ^ n * (x ^ m * (y ^ n * a)) = y ^ m * x ^ n * (x ^ m * (y ^ n * b))
    · ring
    · ring
    · rw [hm]

end Away
end Away
end IsLocalization
end CommSemiring
end
