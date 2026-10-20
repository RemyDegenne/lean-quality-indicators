@[expose] public section

namespace RS

attribute [instance] Fragment.flagFintype Fragment.flagDecEq
  Fragment.vertexFintype

namespace Fragment

variable {α β : Type}

section GluePair

theorem glueAttach_spec (W : Fragment α) (i j : α)
    (f : SurvivingFlag W i j) :
    (glueAttach W i j f).map id Subtype.val = W.attach f.val :=
  glueAttachOn_spec W i j f _ rfl

end GluePair
end Fragment
end RS
end
