public section

open scoped Matrix

namespace exteriorPower

attribute [local instance 100] LieRing.ofAssociativeRing

section Action

variable {K : Type*} [CommRing K]

noncomputable scoped instance glLieRingModule (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    LieRingModule (Matrix n n K) (⋀[K]^d (n → K)) :=
  LieRingModule.compLieHom _ (glLieMap d)

noncomputable scoped instance glLieModule (d : ℕ) {n : Type*} [DecidableEq n] [Fintype n] :
    LieModule K (Matrix n n K) (⋀[K]^d (n → K)) :=
  LieModule.compLieHom _ (glLieMap d)

section BasisWedge

variable {n : Type*} [DecidableEq n] [Fintype n] [LinearOrder n] {N : ℕ}

variable (K) in
/-- The wedge of the standard basis vectors of `n → K` indexed by a finite set `S` of coordinates,
an element of the exterior power of degree the size of `S`. The factors are wedged together in the
order `S` inherits from `n`. -/
noncomputable def basisWedge (S : Finset n) (h : S.card = N) : ⋀[K]^N (n → K) :=
  ιMulti_family K N (Pi.basisFun K n) ⟨S, h⟩

end BasisWedge
end Action
end exteriorPower
end
