@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe uC' uC uD' uD

variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]

variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

attribute [instance 100] HasBinaryBiproducts.has_binary_biproduct

variable {P Q : C}

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

section BiprodKernel

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

/-- The fork `biprod.fstKernelFork` is indeed a limit. -/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

end HasBinaryBiproduct
end BiprodKernel
end CategoryTheory.Limits
end
end
