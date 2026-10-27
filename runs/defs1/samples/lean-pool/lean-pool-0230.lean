@[expose] public section

namespace RS

/-- **The symplectic matrix** `J = [[0, I], [-I, 0]]` in
coordinates: `J c d` is `1` when `d = c + ℓ`, `-1` when
`c = d + ℓ`, and `0` otherwise. -/
noncomputable def symplecticJ (ℓ : ℕ) (c d : Fin (2 * ℓ)) : ℂ :=
  if d.val = c.val + ℓ then 1
  else if c.val = d.val + ℓ then -1
  else 0

end RS
end
