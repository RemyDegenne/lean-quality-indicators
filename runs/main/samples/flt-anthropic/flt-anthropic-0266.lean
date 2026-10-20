namespace P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open CQAux in
theorem solution
    {C X : Scheme.{0}} [ConnectedSpace X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (horbit : ∀ x x' : C, π.base x = π.base x' ↔ ∃ g : G, (ρ g).hom.base x = x')
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (U : C.Opens) (hUcl : IsClosed (U : Set C)) (hUconn : _root_.IsConnected (U : Set C))
    (G₀ : Subgroup G) (hG₀ : ∀ g : G, g ∈ G₀ ↔ (ρ g).hom ⁻¹ᵁ U = U) :
    ∃ ρ₀ : G₀ →* Aut (U : Scheme.{0}),
      (∀ g : G₀, (ρ₀ g).hom ≫ U.ι = U.ι ≫ (ρ (g : G)).hom) ∧
      (∃ hπ₀ : ∀ g : G₀, (ρ₀ g).hom ≫ (U.ι ≫ π) = U.ι ≫ π,
        IsFinite (U.ι ≫ π) ∧
        Function.Surjective (U.ι ≫ π).base ∧
        (∀ u u' : (U : Scheme.{0}), (U.ι ≫ π).base u = (U.ι ≫ π).base u' ↔ ∃ g : G₀, (ρ₀ g).hom.base u = u') ∧
        (∀ V : X.Opens, Function.Injective ((U.ι ≫ π).app V)) ∧
        (∀ V : X.Opens, Set.range ((U.ι ≫ π).app V) =
          {s | ∀ g : G₀, (ρ₀ g).hom.appLE ((U.ι ≫ π) ⁻¹ᵁ V) ((U.ι ≫ π) ⁻¹ᵁ V)
            (by rw [← Scheme.Hom.comp_preimage, hπ₀ g]) s = s})) := by
  classical
  have hUne : (U : Set C).Nonempty := hUconn.nonempty
  refine ⟨rho0 ρ U G₀ hG₀, rho0_hom_ι ρ U G₀ hG₀, ?_⟩
  have hπ₀ : ∀ g : G₀, (rho0 ρ U G₀ hG₀ g).hom ≫ (U.ι ≫ π) = U.ι ≫ π := by
    intro g; rw [← Category.assoc, rho0_hom_ι, Category.assoc, hπ]
  refine ⟨hπ₀, ?_, ?_, ?_, ?_, ?_⟩
  · haveI := isClosedImmersion_ι_of_isClosed U hUcl
    infer_instance
  · exact Set.range_eq_univ.mp (range_ι_comp_eq_univ ρ π hπ hsurj horbit U hUcl hUne)
  · intro u u'
    constructor
    · intro h
      have h' : π.base (U.ι.base u) = π.base (U.ι.base u') := h
      obtain ⟨g, hg⟩ := (horbit _ _).mp h'
      have hgU : (ρ g).hom ⁻¹ᵁ U = U :=
        preimage_eq_of_mem ρ U hUcl hUconn g (U.ι.base u) (by simp [Scheme.Opens.ι_apply]) (by rw [hg]; simp [Scheme.Opens.ι_apply])
      refine ⟨⟨g, (hG₀ g).mpr hgU⟩, ?_⟩
      apply U.ι.isOpenEmbedding.injective
      show (((rho0 ρ U G₀ hG₀ ⟨g, _⟩).hom ≫ U.ι).base u) = U.ι.base u'
      rw [rho0_hom_ι]
      exact hg
    · rintro ⟨g, hg⟩
      rw [← hg]
      show (U.ι ≫ π).base u = ((rho0 ρ U G₀ hG₀ g).hom ≫ U.ι ≫ π).base u
      rw [hπ₀]
  ·
    intro V t₁ t₂ h
    apply hsec V
    let O : C.Opens := U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V)
    have hO : O ≤ π ⁻¹ᵁ V := U.ι.image_preimage_le _
    have hT : ∀ g : G, (ρ g).hom ⁻¹ᵁ O ≤ π ⁻¹ᵁ V := by
      intro g
      calc (ρ g).hom ⁻¹ᵁ O ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := ((ρ g).hom.preimage_mono hO)
        _ = π ⁻¹ᵁ V := by rw [← Scheme.Hom.comp_preimage, hπ g]
    apply C.sheaf.eq_of_locally_eq' (fun g : G => (ρ g).hom ⁻¹ᵁ O) (π ⁻¹ᵁ V) (fun g => homOfLE (hT g))
      (le_iSup_preimage_imagePreimage ρ π hπ hsurj horbit U hUcl hUne V)
    intro g
    have e : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := by rw [← Scheme.Hom.comp_preimage, hπ g]
    have key : ∀ t : Γ(X, V), C.sheaf.1.map (homOfLE (hT g)).op (π.app V t) =
        (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl ((U.ι ≫ π).app V t) := by
      intro t
      have m1 : (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e ≫ C.presheaf.map (homOfLE (hT g)).op =
          (ρ g).hom.appLE (π ⁻¹ᵁ V) ((ρ g).hom ⁻¹ᵁ O) ((ρ g).hom.preimage_mono hO) := Scheme.Hom.appLE_map _ _ _
      have m2 : C.presheaf.map (homOfLE hO).op ≫ (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl =
          (ρ g).hom.appLE (π ⁻¹ᵁ V) ((ρ g).hom ⁻¹ᵁ O) ((ρ g).hom.preimage_mono hO) := Scheme.Hom.map_appLE _ _ _
      have m3 : (U.ι ≫ π).app V t = C.presheaf.map (homOfLE hO).op (π.app V t) := rfl
      calc C.sheaf.1.map (homOfLE (hT g)).op (π.app V t)
          = C.presheaf.map (homOfLE (hT g)).op ((ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e (π.app V t)) := by
            rw [appLE_app_eq_of_comp_eq (ρ g).hom π (hπ g) V e t]; rfl
        _ = ((ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) e ≫ C.presheaf.map (homOfLE (hT g)).op) (π.app V t) := by
            rw [CommRingCat.comp_apply]
        _ = (C.presheaf.map (homOfLE hO).op ≫ (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl) (π.app V t) := by
            rw [m1, m2]
        _ = (ρ g).hom.appLE O ((ρ g).hom ⁻¹ᵁ O) le_rfl ((U.ι ≫ π).app V t) := by
            rw [CommRingCat.comp_apply, m3]
    rw [key, key, h]
  ·
    intro V
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩ g
      exact appLE_app_eq_of_comp_eq _ _ (hπ₀ g) V _ t
    · intro s hs

      let O : C.Opens := U.ι ''ᵁ U.ι ⁻¹ᵁ (π ⁻¹ᵁ V)
      have hO : O ≤ π ⁻¹ᵁ V := U.ι.image_preimage_le _
      have hOU : O ≤ U := U.ι_image_le _
      have hT : ∀ g : G, (ρ g).hom ⁻¹ᵁ O ≤ π ⁻¹ᵁ V := by
        intro g
        calc (ρ g).hom ⁻¹ᵁ O ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V) := ((ρ g).hom.preimage_mono hO)
          _ = π ⁻¹ᵁ V := by rw [← Scheme.Hom.comp_preimage, hπ g]
      have hcover := le_iSup_preimage_imagePreimage ρ π hπ hsurj horbit U hUcl hUne V

      have hs' : ∀ (k : G) (hk : (ρ k).hom ⁻¹ᵁ U = U) (e : O ≤ (ρ k).hom ⁻¹ᵁ O),
          (ρ k).hom.appLE O O e s = s := by
        intro k hk e
        have h1 := hs ⟨k, (hG₀ k).mpr hk⟩
        exact (Scheme.Hom.resLE_appLE (ρ k).hom (le_of_eq ((hG₀ k).mp ((hG₀ k).mpr hk)).symm) _ _ _ ▸ h1 :)

      let T : G → C.Opens := fun g => (ρ g).hom ⁻¹ᵁ O
      let sf : ∀ g : G, Γ(C, T g) := fun g => (ρ g).hom.appLE O (T g) le_rfl s

      have hmeet : ∀ (g h : G) (x : C), x ∈ (T g : Set C) → x ∈ (T h : Set C) →
          (ρ (g * h⁻¹)).hom ⁻¹ᵁ U = U := by
        intro g h x hxg hxh
        have hgx : (ρ g).hom.base x ∈ (U : Set C) := hOU hxg
        have hhx : (ρ h).hom.base x ∈ (U : Set C) := hOU hxh
        refine preimage_eq_of_mem ρ U hUcl hUconn (g * h⁻¹) ((ρ h).hom.base x) hhx ?_
        have e1 : (ρ (g * h⁻¹)).hom.base ((ρ h).hom.base x) = ((ρ h).hom ≫ (ρ (g * h⁻¹)).hom).base x := rfl
        rw [e1, ← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        exact hgx
      have hTeq : ∀ (g h : G), (ρ (g * h⁻¹)).hom ⁻¹ᵁ U = U → T g = T h := by
        intro g h hk
        show (ρ g).hom ⁻¹ᵁ O = (ρ h).hom ⁻¹ᵁ O
        conv_lhs => rw [← inv_mul_cancel_right g h, ← preimage_preimage_act ρ (g * h⁻¹) h O,
          preimage_O_eq ρ π hπ U V (g * h⁻¹) hk]
      have hsf : ∀ (g h : G) (hk : (ρ (g * h⁻¹)).hom ⁻¹ᵁ U = U) (e : T g ≤ (ρ h).hom ⁻¹ᵁ O),
          sf g = (ρ h).hom.appLE O (T g) e s := by
        intro g h hk e
        have eO : O ≤ (ρ (g * h⁻¹)).hom ⁻¹ᵁ O := by rw [preimage_O_eq ρ π hπ U V (g * h⁻¹) hk]
        have hcomp : (ρ h).hom ≫ (ρ (g * h⁻¹)).hom = (ρ g).hom := by
          rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        conv_rhs => rw [← hs' (g * h⁻¹) hk eO]
        rw [appLE_appLE_apply (ρ (g * h⁻¹)).hom (ρ h).hom O O (T g) eO e
          (by rw [hcomp]) s]
        exact (appLE_congr_hom hcomp O (T g) _ le_rfl s).symm
      have hcompat : TopCat.Presheaf.IsCompatible C.sheaf.1 T sf := by
        intro g h
        by_cases hne : ((T g ⊓ T h : C.Opens) : Set C).Nonempty
        · obtain ⟨x, hxg, hxh⟩ := hne
          have hk := hmeet g h x hxg hxh
          have hgh : T g = T h := hTeq g h hk
          have e : T g ≤ (ρ h).hom ⁻¹ᵁ O := hgh.le
          show C.presheaf.map (homOfLE inf_le_left).op (sf g) = C.presheaf.map (homOfLE inf_le_right).op (sf h)
          rw [hsf g h hk e, map_appLE_apply, map_appLE_apply]
        · have hbot : (T g ⊓ T h : C.Opens) = ⊥ := by
            ext x; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
            exact fun hx => hne ⟨x, hx⟩
          haveI := CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty hbot)
          exact Subsingleton.elim _ _

      obtain ⟨S, hS, -⟩ := C.sheaf.existsUnique_gluing' T (π ⁻¹ᵁ V) (fun g => homOfLE (hT g)) hcover sf hcompat

      have hSinv : ∀ k : G, (ρ k).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ k]) S = S := by
        intro k
        apply C.sheaf.eq_of_locally_eq' T (π ⁻¹ᵁ V) (fun g => homOfLE (hT g)) hcover
        intro g
        have eTk : T g ≤ (ρ k).hom ⁻¹ᵁ (T (g * k⁻¹)) := by
          show (ρ g).hom ⁻¹ᵁ O ≤ (ρ k).hom ⁻¹ᵁ ((ρ (g * k⁻¹)).hom ⁻¹ᵁ O)
          rw [preimage_preimage_act ρ (g * k⁻¹) k O, inv_mul_cancel_right]
        have hcomp : (ρ k).hom ≫ (ρ (g * k⁻¹)).hom = (ρ g).hom := by
          rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        show C.presheaf.map (homOfLE (hT g)).op ((ρ k).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) _ S) =
          C.presheaf.map (homOfLE (hT g)).op S
        rw [map_appLE_apply]
        have step : (ρ k).hom.appLE (π ⁻¹ᵁ V) (T g) ((hT g).trans (by rw [← Scheme.Hom.comp_preimage, hπ k])) S =
            (ρ k).hom.appLE (T (g * k⁻¹)) (T g) eTk (C.presheaf.map (homOfLE (hT (g * k⁻¹))).op S) := by
          rw [appLE_map_apply]
        rw [step]
        have hSg : C.presheaf.map (homOfLE (hT (g * k⁻¹))).op S = sf (g * k⁻¹) := hS (g * k⁻¹)
        rw [hSg]
        show (ρ k).hom.appLE (T (g * k⁻¹)) (T g) eTk ((ρ (g * k⁻¹)).hom.appLE O (T (g * k⁻¹)) le_rfl s) = _
        rw [appLE_appLE_apply (ρ (g * k⁻¹)).hom (ρ k).hom O (T (g * k⁻¹)) (T g) le_rfl eTk (by rw [hcomp]) s,
          appLE_congr_hom hcomp O (T g) _ le_rfl s]
        exact (hS g).symm

      have hSrange : S ∈ Set.range (π.app V) := by
        rw [hinv V]; exact hSinv
      obtain ⟨t, ht⟩ := hSrange
      refine ⟨t, ?_⟩

      have hT1 : O ≤ T 1 := by
        show O ≤ (ρ 1).hom ⁻¹ᵁ O
        rw [preimage_O_eq ρ π hπ U V 1 (by rw [map_one]; rfl)]
      have m3 : (U.ι ≫ π).app V t = C.presheaf.map (homOfLE hO).op (π.app V t) := rfl
      rw [m3, ht]
      have : C.presheaf.map (homOfLE hO).op S = C.presheaf.map (homOfLE hT1).op (C.presheaf.map (homOfLE (hT 1)).op S) := by
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
      rw [this]
      have hS1 : C.presheaf.map (homOfLE (hT 1)).op S = sf 1 := hS 1
      rw [hS1]
      show C.presheaf.map (homOfLE hT1).op ((ρ 1).hom.appLE O (T 1) le_rfl s) = s
      rw [map_appLE_apply]
      exact appLE_one_apply ρ O _ s

end P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected
