@[expose] public section

namespace BGS.Markoff

universe u

@[simp]
theorem gammaVieta1_smul_punctured {R : Type u} [CommRing R]
    (x : PuncturedMarkoffSurface R) : gammaVieta1 R • x = vieta1PuncturedPerm R x := by
  apply Subtype.ext
  rfl

end BGS.Markoff
end
