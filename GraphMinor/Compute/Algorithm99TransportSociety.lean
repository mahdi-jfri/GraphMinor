module

public import GraphMinor.Compute.Algorithm99TransportWall

/-!
# Transport of societies, wall societies and divisions along injective relabellings

Section 9 of Graph Minors XIII (pages 103–104) attaches to a wall `H` in `G` its society: the
compass of `H` with the cyclic order of its four corners. Step (5) of Algorithm (9.9) finds a
rural division of this society. Here we rename a cyclic permutation (`relabelCyclicPerm`) and a
society (`relabelSociety`) along embeddings `f : α ↪ α'` and `g : β ↪ β'`, and show:

* the corner order of a renamed wall is the renamed corner order (`wallCornerCyclicPerm_relabelWall`),
  so the society of a renamed wall is the renamed society (`isWallSociety_relabelGraph`);
* the boundary `∂A` of a renamed member is the renamed boundary (`divBoundary_relabelSociety`);
* a division renames to a division (`IsSocietyDivision.relabel`).

Ruralness, which needs drawings, is in `Algorithm99TransportRural.lean`.
-/

@[expose] public section

namespace GraphMinor.Transport

open Graph Function Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14 GraphMinor.GM13

universe u u' v v'

variable {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
variable (f : α ↪ α') (g : β ↪ β')

/-! ### Cyclic permutations -/

/-- Two cyclic permutations with the same set and the same map are equal. -/
theorem cyclicPerm_ext {γ : Type*} {Ω Ω' : CyclicPerm γ} (hbar : Ω.bar = Ω'.bar)
    (hfun : Ω.toFun = Ω'.toFun) : Ω = Ω' := by
  cases Ω
  cases Ω'
  cases hbar
  cases hfun
  rfl

/-- The map `f x ↦ f (Ω x)`, the identity outside the range of `f`. -/
noncomputable def relabelPermFun (Ω : CyclicPerm α) (x' : α') : α' :=
  open Classical in
  if h : x' ∈ Set.range f then f (Ω h.choose) else x'

@[simp]
theorem relabelPermFun_apply (Ω : CyclicPerm α) (x : α) :
    relabelPermFun f Ω (f x) = f (Ω x) := by
  have h : f x ∈ Set.range f := ⟨x, rfl⟩
  unfold relabelPermFun
  simp only [h, ↓reduceDIte]
  congr 2
  exact f.injective h.choose_spec

theorem relabelPermFun_iterate (Ω : CyclicPerm α) (k : ℕ) (x : α) :
    (relabelPermFun f Ω)^[k] (f x) = f ((Ω.toFun)^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, relabelPermFun_apply]
    exact ih (Ω x)

/-- The cyclic permutation `Ω` with its elements renamed along `f`. -/
noncomputable def relabelCyclicPerm (Ω : CyclicPerm α) : CyclicPerm α' where
  bar := f '' Ω.bar
  toFun := relabelPermFun f Ω
  finite_bar := Ω.finite_bar.image f
  bijOn := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [relabelPermFun_apply]
      exact ⟨Ω x, Ω.bijOn.mapsTo hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
      rw [relabelPermFun_apply, relabelPermFun_apply] at h
      rw [Ω.bijOn.injOn hx hy (f.injective h)]
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Ω.bijOn.surjOn hy
      exact ⟨f x, ⟨x, hx, rfl⟩, relabelPermFun_apply f Ω x⟩
  single_orbit := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := Ω.single_orbit x hx y hy
    exact ⟨k, by rw [relabelPermFun_iterate, hk]⟩

@[simp]
theorem relabelCyclicPerm_bar (Ω : CyclicPerm α) : (relabelCyclicPerm f Ω).bar = f '' Ω.bar := rfl

@[simp]
theorem relabelCyclicPerm_apply (Ω : CyclicPerm α) (x : α) :
    relabelCyclicPerm f Ω (f x) = f (Ω x) :=
  relabelPermFun_apply f Ω x

theorem relabelCyclicPerm_iterate (Ω : CyclicPerm α) (k : ℕ) (x : α) :
    ((relabelCyclicPerm f Ω).toFun)^[k] (f x) = f ((Ω.toFun)^[k] x) :=
  relabelPermFun_iterate f Ω k x

theorem firstHitIn_relabelCyclicPerm_iff (Ω : CyclicPerm α) (X : Set α) (x y : α) :
    (relabelCyclicPerm f Ω).FirstHitIn (f '' X) (f x) (f y) ↔ Ω.FirstHitIn X x y := by
  unfold CyclicPerm.FirstHitIn
  simp only [relabelCyclicPerm_iterate, f.injective.eq_iff, f.injective.mem_set_image]

theorem isClockwiseSeq_relabelCyclicPerm_iff (Ω : CyclicPerm α) (L : List α) :
    (relabelCyclicPerm f Ω).IsClockwiseSeq (L.map f) ↔ Ω.IsClockwiseSeq L := by
  unfold CyclicPerm.IsClockwiseSeq
  have hset : {v | v ∈ L.map f} = f '' {v | v ∈ L} := by
    ext v'
    simp [List.mem_map, eq_comm]
  rw [List.nodup_map_iff f.injective, hset]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · simp only [List.mem_map, relabelCyclicPerm_bar, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, f.injective.mem_set_image]
  · simp only [List.length_map, List.getElem_map]
    exact forall_congr' fun i => forall_congr' fun hi =>
      firstHitIn_relabelCyclicPerm_iff f Ω _ _ _

/-- A clockwise triple of a renamed cyclic permutation is a renamed clockwise triple. -/
theorem exists_of_isClockwise3_relabelCyclicPerm (Ω : CyclicPerm α) {v₁ v₂ v₃ : α'}
    (h : (relabelCyclicPerm f Ω).IsClockwise3 v₁ v₂ v₃) :
    ∃ w₁ w₂ w₃, f w₁ = v₁ ∧ f w₂ = v₂ ∧ f w₃ = v₃ ∧ Ω.IsClockwise3 w₁ w₂ w₃ := by
  have hbar := h.2.1
  obtain ⟨w₁, -, rfl⟩ := hbar v₁ (by simp)
  obtain ⟨w₂, -, rfl⟩ := hbar v₂ (by simp)
  obtain ⟨w₃, -, rfl⟩ := hbar v₃ (by simp)
  refine ⟨w₁, w₂, w₃, rfl, rfl, rfl, ?_⟩
  have := (isClockwiseSeq_relabelCyclicPerm_iff f Ω [w₁, w₂, w₃]).1 h
  exact this

theorem relabelCyclicPerm_injective : Injective (relabelCyclicPerm (α := α) f) := by
  intro Ω Ω' h
  have hbar : Ω.bar = Ω'.bar := by
    have := congrArg CyclicPerm.bar h
    exact (Set.image_injective.2 f.injective) this
  have hfun : Ω.toFun = Ω'.toFun := by
    funext x
    have := congrArg (fun Ψ : CyclicPerm α' => Ψ.toFun (f x)) h
    exact f.injective (by simpa using this)
  exact cyclicPerm_ext hbar hfun

open Classical in
/-- The corner order of a renamed wall is the renamed corner order. -/
theorem wallCornerCyclicPerm_relabelWall (W : Wall α β) :
    wallCornerCyclicPerm (relabelWall f g W) = relabelCyclicPerm f (wallCornerCyclicPerm W) := by
  have hbar : (wallCornerCyclicPerm (relabelWall f g W)).bar =
      (relabelCyclicPerm f (wallCornerCyclicPerm W)).bar := relabelWall_corners f g W
  have hfun : (wallCornerCyclicPerm (relabelWall f g W)).toFun =
      (relabelCyclicPerm f (wallCornerCyclicPerm W)).toFun := by
    funext x'
    change _ = relabelPermFun f _ x'
    by_cases hx : x' ∈ Set.range f
    · obtain ⟨x, rfl⟩ := hx
      rw [relabelPermFun_apply]
      change (if f x = f (W.corner 0) then f (W.corner 1)
        else if f x = f (W.corner 1) then f (W.corner 2)
        else if f x = f (W.corner 2) then f (W.corner 3)
        else if f x = f (W.corner 3) then f (W.corner 0)
        else f x) = f (if x = W.corner 0 then W.corner 1
        else if x = W.corner 1 then W.corner 2
        else if x = W.corner 2 then W.corner 3
        else if x = W.corner 3 then W.corner 0
        else x)
      simp only [f.injective.eq_iff]
      split_ifs <;> rfl
    · have hc : ∀ k, x' ≠ f (W.corner k) := fun k h => hx ⟨_, h.symm⟩
      unfold relabelPermFun
      rw [dite_eq_right_iff.2 (fun h => absurd h hx)]
      change (if x' = f (W.corner 0) then f (W.corner 1)
        else if x' = f (W.corner 1) then f (W.corner 2)
        else if x' = f (W.corner 2) then f (W.corner 3)
        else if x' = f (W.corner 3) then f (W.corner 0)
        else x') = x'
      simp only [hc, ↓reduceIte]
  exact cyclicPerm_ext hbar hfun

/-! ### Societies -/

/-- The society `S` with its vertices renamed along `f` and its edges along `g`. -/
noncomputable def relabelSociety (S : Society α β) : Society α' β' where
  G := relabelGraph f g S.G
  Ω := relabelCyclicPerm f S.Ω
  finite_V := S.finite_V.image f
  finite_E := S.finite_E.image g
  bar_subset := Set.image_mono S.bar_subset

@[simp] theorem relabelSociety_G (S : Society α β) :
    (relabelSociety f g S).G = relabelGraph f g S.G := rfl

@[simp] theorem relabelSociety_Ω (S : Society α β) :
    (relabelSociety f g S).Ω = relabelCyclicPerm f S.Ω := rfl

/-- The society of a renamed wall in a renamed graph is the renamed society. -/
theorem isWallSociety_relabelGraph {G : Graph α β} {W : Wall α β} {S : Society α β}
    (h : IsWallSociety G W S) :
    IsWallSociety (relabelGraph f g G) (relabelWall f g W) (relabelSociety f g S) :=
  ⟨by rw [relabelSociety_G, h.1, wallCompass_relabelGraph],
    by rw [relabelSociety_Ω, h.2, wallCornerCyclicPerm_relabelWall]⟩

/-! ### Divisions -/

/-- The boundary of a renamed member is the renamed boundary. -/
theorem divBoundary_relabelSociety (S : Society α β) (A : Graph α β) :
    divBoundary (relabelSociety f g S) (relabelGraph f g A) = f '' divBoundary S A := by
  unfold divBoundary
  ext v'
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hbar | ⟨_, ⟨⟨e, he, rfl⟩, heA⟩, hinc⟩⟩
    · exact ⟨v, ⟨hv, Or.inl (f.injective.mem_set_image.1 hbar)⟩, rfl⟩
    · refine ⟨v, ⟨hv, Or.inr ⟨e, ⟨he, fun h => heA ⟨e, h, rfl⟩⟩, ?_⟩⟩, rfl⟩
      exact (relabelGraph_inc_apply f g).1 hinc
  · rintro ⟨v, ⟨hv, hbar | ⟨e, ⟨he, heA⟩, hinc⟩⟩, rfl⟩
    · exact ⟨⟨v, hv, rfl⟩, Or.inl ⟨v, hbar, rfl⟩⟩
    · refine ⟨⟨v, hv, rfl⟩, Or.inr ⟨g e, ⟨⟨e, he, rfl⟩, fun h => heA ?_⟩, ?_⟩⟩
      · exact g.injective.mem_set_image.1 h
      · exact (relabelGraph_inc_apply f g).2 hinc

theorem divTotalBoundary_relabelSociety (S : Society α β) (𝒜 : Set (Graph α β)) :
    divTotalBoundary (relabelSociety f g S) (relabelGraph f g '' 𝒜) =
      f '' divTotalBoundary S 𝒜 := by
  unfold divTotalBoundary
  rw [Set.image_iUnion₂, Set.biUnion_image]
  simp only [divBoundary_relabelSociety]

/-- A division renames to a division. -/
theorem IsSocietyDivision.relabel {S : Society α β} {𝒜 : Set (Graph α β)}
    (hD : IsSocietyDivision S 𝒜) :
    IsSocietyDivision (relabelSociety f g S) (relabelGraph f g '' 𝒜) where
  sub_of_mem := by
    rintro _ ⟨A, hA, rfl⟩
    exact relabelGraph_mono f g (hD.sub_of_mem hA)
  sUnion_eq := by
    rw [relabelSociety_G, ← relabelGraph_subgraphSUnion, hD.sUnion_eq]
  edge_disjoint := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨A', hA', rfl⟩ hne
    rw [edgeSet_relabelGraph, edgeSet_relabelGraph, Set.disjoint_image_iff g.injective]
    exact hD.edge_disjoint hA hA' (fun h => hne (h ▸ rfl))
  vertex_inter_eq := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨A', hA', rfl⟩ hne
    rw [divBoundary_relabelSociety, divBoundary_relabelSociety, vertexSet_relabelGraph,
      vertexSet_relabelGraph, ← Set.image_inter f.injective, ← Set.image_inter f.injective,
      hD.vertex_inter_eq hA hA' (fun h => hne (h ▸ rfl))]
  boundary_ncard_le_three := by
    rintro _ ⟨A, hA, rfl⟩
    rw [divBoundary_relabelSociety, Set.ncard_image_of_injective _ f.injective]
    exact hD.boundary_ncard_le_three hA
  disjoint_paths_to_bar := by
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨P, hdisj, hP⟩ := hD.disjoint_paths_to_bar hA
    have hcard : (divBoundary (relabelSociety f g S) (relabelGraph f g A)).ncard =
        (divBoundary S A).ncard := by
      rw [divBoundary_relabelSociety, Set.ncard_image_of_injective _ f.injective]
    refine ⟨fun i => relabelGraph f g (P (Fin.cast hcard i)), ?_, ?_⟩
    · intro i j hij
      rw [vertexSet_relabelGraph, vertexSet_relabelGraph, Set.disjoint_image_iff f.injective]
      exact hdisj (fun h => hij (Fin.cast_injective hcard h))
    · intro i
      obtain ⟨s, hs, t, ht, hst⟩ := hP (Fin.cast hcard i)
      refine ⟨f s, ?_, f t, ⟨t, ht, rfl⟩, ?_⟩
      · rw [divBoundary_relabelSociety]
        exact ⟨s, hs, rfl⟩
      · exact isGraphPathWithEnds_relabelGraph f g hst
  internal_path := by
    rintro _ ⟨A, hA, rfl⟩ u' hu' v' hv'
    rw [divBoundary_relabelSociety] at hu' hv' ⊢
    obtain ⟨u, hu, rfl⟩ := hu'
    obtain ⟨v, hv, rfl⟩ := hv'
    obtain ⟨P, hP, hPint⟩ := hD.internal_path hA u hu v hv
    refine ⟨relabelGraph f g P, isGraphPathWithEnds_relabelGraph f g hP, ?_⟩
    rw [vertexSet_relabelGraph, ← Set.image_inter f.injective, ← Set.image_pair]
    exact Set.image_mono hPint
  boundary_injOn := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨A', hA', rfl⟩ h
    rw [divBoundary_relabelSociety, divBoundary_relabelSociety] at h
    rw [hD.boundary_injOn hA hA' ((Set.image_injective.2 f.injective) h)]
  has_private_element := by
    rintro _ ⟨A, hA, rfl⟩
    rcases hD.has_private_element hA with ⟨v, hv, hpriv⟩ | ⟨e, he, hpriv⟩
    · refine Or.inl ⟨f v, ⟨v, hv, rfl⟩, ?_⟩
      rintro _ ⟨B, hB, rfl⟩ hne hvB
      exact hpriv B hB (fun h => hne (h ▸ rfl)) ((mem_vertexSet_relabelGraph_apply f g).1 hvB)
    · refine Or.inr ⟨g e, ⟨e, he, rfl⟩, ?_⟩
      rintro _ ⟨B, hB, rfl⟩ hne heB
      exact hpriv B hB (fun h => hne (h ▸ rfl)) ((mem_edgeSet_relabelGraph_apply f g).1 heB)

/-! ### Interior members -/

@[simp]
theorem isInteriorMember_relabelWall_iff {W : Wall α β} {𝒜 : Set (Graph α β)} {A : Graph α β} :
    IsInteriorMember (relabelWall f g W) (relabelGraph f g '' 𝒜) (relabelGraph f g A) ↔
      IsInteriorMember W 𝒜 A := by
  unfold IsInteriorMember
  rw [(relabelGraph_injective f g).mem_set_image, relabelWall_perimeter, vertexSet_relabelGraph,
    vertexSet_relabelGraph, Set.disjoint_image_iff f.injective]

end GraphMinor.Transport
