@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable {A : Type u}

section WhiskerKernel

theorem kernelSubobject_tensorHom_le
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {Z₁ W₁ Z₂ W₂ : A}
    (p₁ : Z₁ ⟶ W₁) (p₂ : Z₂ ⟶ W₂) [Epi p₁] :
    kernelSubobject (p₁ ⊗ₘ p₂) ≤
      imageSubobject (kernel.ι p₁ ▷ Z₂) ⊔
        imageSubobject (Z₁ ◁ kernel.ι p₂) := by
  have hv : kernelSubobject (W₁ ◁ p₂) ≤
      imageSubobject ((Z₁ ◁ kernel.ι p₂) ≫ (p₁ ▷ Z₂)) := by
    have : Epi (p₁ ▷ kernel p₂) := epi_whiskerRight_of_epi p₁ _
    refine kernelSubobject_le_of_factors
      (factors_kernel_ι_whiskerLeft p₂
        (factors_of_epi_comp _ (p₁ ▷ kernel p₂) _ ?_))
    rw [← whisker_exchange p₁ (kernel.ι p₂)]
    exact factors_self_imageSubobject _
  calc kernelSubobject (p₁ ⊗ₘ p₂)
      = kernelSubobject ((p₁ ▷ Z₂) ≫ (W₁ ◁ p₂)) :=
        kernelSubobject_congr (MonoidalCategory.tensorHom_def p₁ p₂)
    _ ≤ kernelSubobject (p₁ ▷ Z₂) ⊔
          imageSubobject (Z₁ ◁ kernel.ι p₂) :=
        kernelSubobject_comp_le_of_cover (p₁ ▷ Z₂) (W₁ ◁ p₂)
          (Z₁ ◁ kernel.ι p₂) hv
    _ ≤ imageSubobject (kernel.ι p₁ ▷ Z₂) ⊔
          imageSubobject (Z₁ ◁ kernel.ι p₂) :=
        sup_le_sup_right (kernelSubobject_whiskerRight_le p₁ Z₂) _

end WhiskerKernel
end RS
end
