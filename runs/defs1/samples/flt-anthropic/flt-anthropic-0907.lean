namespace P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

universe u

namespace P2mSchlessingerUniversal

open IsLocalRing

variable {O : Type u} [CommRing O] [IsLocalRing O] {R : Type u} [CommRing R] [Algebra O R]
  (S : Hull O R)

namespace Hull

section pullback

variable {A : Type u} [CommRing A] [Algebra O A]

def τ [IsLocalRing A] [IsArtinianRing A] (resA : A →+* ResidueField O)
    (hcA : resA.comp (algebraMap O A) = residue O) (t : A) (ht0 : t ≠ 0) (htm : t ∈ RingHom.ker resA) :
    ↥(Bt (O := O) t) →ₐ[O] DualNumber (ResidueField O) where
  toFun b := ((resA (b : A × A).1, lam resA t b) : ResidueField O × ResidueField O)
  map_one' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    change lam resA t 1 = 0
    rw [lam_eq_of resA t ht0 1 0 (by simp), map_zero]
  map_mul' b b' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change resA ((b : A × A) * (b' : A × A)).1 = resA (b : A × A).1 * resA (b' : A × A).1
      rw [Prod.fst_mul, map_mul]
    · change lam resA t (b * b') = resA (b : A × A).1 • lam resA t b' +
        MulOpposite.op (resA (b' : A × A).1) • lam resA t b
      rw [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
        lam_eq_of resA t ht0 (b * b') ((b : A × A).1 * coef t b' + coef t b * (b' : A × A).2) ?_]
      · rw [map_add, map_mul, map_mul, res_snd_eq resA t htm b']
        rfl
      · change _ = ((b : A × A) * (b' : A × A)).2 - ((b : A × A) * (b' : A × A)).1
        rw [Prod.snd_mul, Prod.fst_mul, add_mul, mul_assoc, coef_spec, mul_assoc, mul_comm _ t,
          ← mul_assoc, coef_spec]
        ring
  map_zero' := by
    refine TrivSqZeroExt.ext (by simp) ?_
    change lam resA t 0 = 0
    rw [lam_eq_of resA t ht0 0 0 (by simp), map_zero]
  map_add' b b' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change resA ((b : A × A) + (b' : A × A)).1 = resA (b : A × A).1 + resA (b' : A × A).1
      rw [Prod.fst_add, map_add]
    · change lam resA t (b + b') = lam resA t b + lam resA t b'
      rw [lam_eq_of resA t ht0 (b + b') (coef t b + coef t b') ?_, map_add]
      · rfl
      · change _ = ((b : A × A) + (b' : A × A)).2 - ((b : A × A) + (b' : A × A)).1
        rw [Prod.snd_add, Prod.fst_add, add_mul, coef_spec, coef_spec]
        ring
  commutes' o := by
    refine TrivSqZeroExt.ext ?_ ?_
    · change resA (algebraMap O (A × A) o).1 = TrivSqZeroExt.fst (algebraMap O (DualNumber _) o)
      rw [Prod.algebraMap_apply, ← RingHom.comp_apply, hcA]
      rfl
    · change lam resA t (algebraMap O _ o) = TrivSqZeroExt.snd (algebraMap O (DualNumber _) o)
      rw [lam_eq_of resA t ht0 _ 0 ?_, map_zero]
      · rfl
      · change (0 : A) * t = (algebraMap O (A × A) o).2 - (algebraMap O (A × A) o).1
        simp

end pullback
end Hull
end P2mSchlessingerUniversal
end
end P2MW.S_IsLocalRing_exists_forall_algHom_bijective_of_forall_pullback_bijective_of_hull
