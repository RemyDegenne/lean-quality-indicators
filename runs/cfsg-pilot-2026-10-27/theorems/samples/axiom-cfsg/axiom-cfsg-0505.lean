public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Quasithin CFSG.Quasithin.MS93.S32 CFSG.Assembly.LowTwoRank

open scoped Matrix

section Normalizing

variable {V : Type} [CommGroup V] {F : Type} [Field F]

variable {K P : Subgroup (MulAut V)} {π : ↥(StatedSL 3 F) →* ↥K}

theorem Coord.trivial_of_rep_det_one (c : Coord K π) (hπ : Function.Surjective π)
    {x : MulAut V} (hxK : x ∈ K) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1)
    (hrep : ∃ a b d e : F, c.Rep x a b d e ∧ a * e - b * d = 1) :
    ∀ u ∈ commV K, x u = u := by
  intro u hu
  obtain ⟨a, b, d, e, hr, hdet⟩ := hrep
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hxK⟩
  have hγx : ∀ w, c.T (dg (γ : GL (Fin 3) F) w) = x (c.T w) := fun w => by
    rw [c.equiv, hγ]
  have key : ∀ w, blockSmul a b d e w = dg (γ : GL (Fin 3) F) w := fun w =>
    c.inj ((hr w).trans (hγx w).symm)
  have h1 := key (fun _ => 1, 0)
  have h2 := key (0, fun _ => 1)
  simp only [blockSmul, dg, smul_zero, add_zero, zero_add, Matrix.mulVec_zero, Prod.mk.injEq]
    at h1 h2
  have hd : d = 0 := by simpa using congrFun h1.2 0
  have hb : b = 0 := by simpa using congrFun h2.1 0
  have hae : a = e := by
    have p1 := congrFun h1.1 0
    have p2 := congrFun h2.2 0
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at p1 p2
    exact p1.trans p2.symm
  subst hd hb hae
  have haa : a * a = 1 := by simpa using hdet
  have hpow : ∀ k : ℕ, c.Rep (x ^ k) (a ^ k) 0 0 (a ^ k) := by
    intro k
    induction k with
    | zero => simpa using c.rep_one
    | succ k ih => simpa [pow_succ] using c.rep_mul ih hr
  have hm' : a ^ m = 1 := by
    have h := hpow m
    rw [hxm] at h
    exact (c.rep_unique c.rep_one h).1.symm
  obtain ⟨k, rfl⟩ := hm
  have ha : a = 1 := by
    rw [pow_succ, pow_mul, sq, haa, one_pow, one_mul] at hm'
    exact hm'
  subst ha
  obtain ⟨w, rfl⟩ := c.surj u hu
  rw [← hr w]
  congr 1
  simp [blockSmul]

end Normalizing
end CFSG.HardMathSupport.Curtis.Coordinator
end
