@[expose] public section

namespace Matrix

variable (I J K L R R' : Type*)

section Basic

variable {R I J K L}

theorem transpose_comp (M : Matrix I J (Matrix K L R)) :
    (comp I J K L R M)ᵀ = comp J I L K R (Mᵀ.map (·ᵀ)) :=
  rfl

end Basic
end Matrix
end
