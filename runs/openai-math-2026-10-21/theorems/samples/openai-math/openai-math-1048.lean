namespace OAI

namespace ArtinCAT0.TriangleMesh

variable {F V : Type*} (M : TriangleMesh F V)

namespace SimplicialLabeling

variable {M} (L : M.SimplicialLabeling)

lemma qvertex_zero (d : F × Fin 3) (hd : ¬ L.Active d) :
    L.qvertex (M.tail d) = L.qvertex (M.tail (rotate d)) :=
  Quot.sound ⟨d,hd,rfl,rfl⟩

end SimplicialLabeling
end ArtinCAT0.TriangleMesh
end OAI
