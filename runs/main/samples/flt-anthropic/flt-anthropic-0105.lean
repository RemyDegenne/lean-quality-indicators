namespace P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero

attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly

p2m_open

p2m_open

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace DivSepDescent

p2m_open

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k]

variable (W : WeierstrassCurve F)

scoped instance instIsEllipticBaseChange [W.IsElliptic] : (W.baseChange k).IsElliptic :=
  inferInstanceAs ((W.map (algebraMap F k)).IsElliptic)

theorem exists_hom_of_ker {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℤ}
    (hsurj : ∀ P : A, ∃ Q : A, n • Q = P) (α : A →+ B) (hker : ∀ P, n • P = 0 → α P = 0) :
    ∃ β : A →+ B, (∀ Q, β (n • Q) = α Q) ∧ ∀ P, α P = n • β P := by
  choose f hf using hsurj
  have key : ∀ P Q : A, n • P = n • Q → α P = α Q := fun P Q h => by
    rw [← sub_eq_zero, ← map_sub]
    exact hker _ (by rw [smul_sub, h, sub_self])
  refine ⟨{ toFun := fun P => α (f P), map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · simpa using key (f 0) 0 (by rw [hf, smul_zero])
  · intro P Q
    simp only [← map_add]
    exact key _ _ (by rw [hf, smul_add, hf, hf])
  · intro Q
    exact key _ _ (hf _)
  · intro P
    show α P = n • α (f P)
    rw [← map_zsmul, hf]

end DivSepDescent
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_mem_rationalHomSet_eq_smul_of_forall_smul_eq_zero
