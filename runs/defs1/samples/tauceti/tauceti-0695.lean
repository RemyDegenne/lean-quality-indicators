public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

variable [HasKernels C]

/-- **Reduced homology in degree zero is free on the path components other than that of a
basepoint.**  A point `x` identifies the reduced zeroth singular homology of `X` with the
coproduct of copies of `R` indexed by the path components of `X` different from that of `x`.  The
generator at the component of `y` corresponds to the class `[y] - [x]`
(`TauCeti.ι_reducedSingularHomology₀Iso_inv_ι`). -/
def reducedSingularHomology₀Iso {X : TopCat.{w}} (x : X) :
    (reducedSingularHomologyFunctor R 0).obj X ≅
      ∐ fun _ : {c : ZerothHomotopy X // c ≠ ZerothHomotopy.mk x} ↦ R :=
  haveI := hasCoproducts_shrink.{0, w} (C := C)
  haveI : HasZeroObject C := ⟨_, initialIsInitial.isZero⟩
  eqToIso (reducedSingularHomologyFunctor_zero_obj R X) ≪≫
    kernelIsoOfEq (X.singularHomology₀Iso_sigma_desc_id R).symm ≪≫
    kernelIsIsoComp (X.singularHomology₀Iso R).hom (Sigma.desc fun _ ↦ 𝟙 R) ≪≫
    kernelSigmaDescIdIso R (ZerothHomotopy.mk x)

end TauCeti
end
end
