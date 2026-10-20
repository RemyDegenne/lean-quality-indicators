public section

namespace TauCeti.AdditiveCode

variable {A ι : Type*} [AddCommGroup A]

/-- Restriction of codewords to the retained coordinates, with codomain the punctured code. -/
def punctureHom (C : AdditiveCode A ι) (s : Set ι) : C →+ puncture C s :=
  ((AddMonoidHom.pi fun i : s ↦ Pi.evalAddMonoidHom (fun _ : ι ↦ A) i).domRestrict C)
    |>.codRestrict (puncture C s) fun x ↦ mem_puncture.mpr ⟨x.1, x.2, fun _ ↦ rfl⟩

end TauCeti.AdditiveCode
end
