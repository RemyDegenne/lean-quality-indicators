@[expose] public section

namespace AspPerm

infixl:70 " ⋆ " => star

infixl:70 " ◃ " => lres

/-- Right residual on ASP permutations, characterized by
$s_{\alpha \triangleright \beta} = s_\alpha \triangleright s_\beta$.

In Lean this operation is written `α ▹ β`. -/
noncomputable def rres (α β : AspPerm) : AspPerm :=
  Classical.choose (show ∃! τ : AspPerm, τ.s = α.s ▹ β.s from by
    exact rres_exists α β)

end AspPerm
end
