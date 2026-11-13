module

public import GraphMinor.Compute.Algorithm99BitImage

/-!
# Output (iii) of (9.9) in the labels of `G`, for any target set `Y`

Output (a) of steps (5) to (7) of Algorithm (9.9) (Graph Minors XIII, page 104) is a block of
the renumbered graph `G' = (G_i \ X) ∪ H_i` on `Fin v`. Renamed along `orig`, it is a block of
`G \ Y` for every set `Y ⊆ V(G)` that meets the image of `orig` in exactly `orig(X)`.

Two sets `Y` are used. For the standalone form of (9.9), `Y = orig(X)`. For the form
`Alg99Spec` that Algorithm (10.5) calls on `G_i \ Z_i`, the loop runs on `D = G_i \ Z_i`, and
`Y = orig(X) ∪ Z_i`; the image of `orig` misses `Z_i` there.

* `wallCompass_relabel_eq_of_target`: the compass of the renamed wall in `G \ Y` is the renamed
  compass. This is `wallCompass_eq_of_closed_outside_Z` applied in `G \ (Y \ orig(X))`.
* `isAlg99OutputIII_of_target`: the five conditions of output (iii) for `G` and `Y`.
* `isAlg99Output_of_case3StepsOutputA`: for `Y = orig(X)`, the word list
  `2 :: bitSetList (orig(X)) ++ block` is an output (iii) of (9.9).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport

variable {n : ℕ} {G : MultiDigraph n}

/-- Deleting `A` and then `B` deletes `A ∪ B`. -/
theorem deleteVertices_deleteVertices_union {α β : Type*} (K : Graph α β) (A B : Set α) :
    GM09.deleteVertices (GM09.deleteVertices K A) B = GM09.deleteVertices K (A ∪ B) := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext x
    simp only [vertexSet_deleteVertices, Set.mem_sdiff, Set.mem_union]
    tauto
  · simp only [deleteVertices_isLink, Set.mem_union]
    tauto

/-- **(9.5) for the renamed wall, with target `Y`.** For a valid state of (9.9), let `H` be a
wall of `G_i \ X` whose compass there misses `Z_i`, and let `Y ⊆ V(G)` meet the image of `orig`
in `orig(X)`. Then the compass of the renamed wall in `G \ Y` is the renamed compass. The proof
applies `wallCompass_eq_of_closed_outside_Z` (Graph Minors XIII, (9.9) (ii): "no vertex of
$G_i \setminus Z_i$ is incident with an edge of $G$ not in $G_i$") to the renamed `G_i` inside
`G \ (Y \ orig(X))`, from which `orig(X)` is then deleted. -/
theorem wallCompass_relabel_eq_of_target {h' s : ℕ} {st : Alg99Iter h' G} (hst : st.IsValid s)
    {X : Finset (Fin st.v)} {Y : Finset (Fin n)} (hY : ∀ u, st.orig u ∈ Y ↔ u ∈ X)
    {H : Wall ℕ (ℕ × ℕ × ℕ)} (hH : H.graph ≤ delGraph st.Gi X)
    (hZ : Disjoint V(wallCompass (delGraph st.Gi X) H) st.Z.toNatSet) :
    wallCompass (delGraph G Y)
        (relabelWall (origVertexEmb st.orig hst.orig_injective)
          (origEdgeEmb st.orig hst.orig_injective) H) =
      relabelGraph (origVertexEmb st.orig hst.orig_injective)
        (origEdgeEmb st.orig hst.orig_injective) (wallCompass (delGraph st.Gi X) H) := by
  set f := origVertexEmb st.orig hst.orig_injective
  set g := origEdgeEmb st.orig hst.orig_injective
  set R := relabelGraph f g st.Gi.toGMDigraph.toGraph
  set Gd := GM09.deleteVertices G.toGMDigraph.toGraph (Y.toNatSet \ f '' X.toNatSet)
  have hfX : f '' X.toNatSet ⊆ Y.toNatSet := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rw [origVertexEmb_apply_val]
    exact (mem_toNatSet_iff Y _).mpr ((hY u).mpr hu)
  have hK : relabelGraph f g (delGraph st.Gi X) = GM09.deleteVertices R (f '' X.toNatSet) := by
    rw [delGraph_eq_deleteVertices, relabelGraph_deleteVertices]
  have hKG : delGraph G Y = GM09.deleteVertices Gd (f '' X.toNatSet) := by
    rw [delGraph_eq_deleteVertices, deleteVertices_deleteVertices_union, Set.sdiff_union_self,
      Set.union_eq_left.mpr hfX]
  have hRle : R ≤ Gd := by
    refine le_deleteVertices hst.relabelGraph_le ?_
    rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨hxY, hxX⟩
    have hxv : x < st.v := hx
    rw [origVertexEmb_apply_val st.orig hst.orig_injective ⟨x, hxv⟩] at hxY
    have hu : (⟨x, hxv⟩ : Fin st.v) ∈ X := (hY _).mp ((mem_toNatSet_iff Y _).mp hxY)
    exact hxX ⟨x, (mem_toNatSet_iff X _).mpr hu, rfl⟩
  have hW : (relabelWall f g H).graph ≤ GM09.deleteVertices R (f '' X.toNatSet) := by
    rw [relabelWall_graph, ← hK]
    exact relabelGraph_mono f g hH
  have hdisj : Disjoint V(wallCompass (GM09.deleteVertices R (f '' X.toNatSet))
      (relabelWall f g H)) (f '' st.Z.toNatSet) := by
    rw [← hK, wallCompass_relabelGraph, vertexSet_relabelGraph]
    exact (Set.disjoint_image_iff f.injective).2 hZ
  have hclosed : ∀ x ∈ V(R) \ f '' st.Z.toNatSet, ∀ e ∈ E(Gd), Gd.Inc e x → e ∈ E(R) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩ e he hinc
    have hxv : x < st.v := hx
    have hfx : f x = (st.orig ⟨x, hxv⟩).1 := origVertexEmb_apply_val st.orig _ ⟨x, hxv⟩
    have hu : (⟨x, hxv⟩ : Fin st.v) ∉ st.Z := fun hmem =>
      hxZ ⟨x, (mem_toNatSet_iff st.Z ⟨x, hxv⟩).mpr hmem, rfl⟩
    rw [hfx] at hinc
    exact hst.relabelGraph_closed ⟨x, hxv⟩ hu e
      ((deleteVertices_le _ _).edgeSet_mono he)
      (let ⟨y, hy⟩ := hinc; ⟨y, hy.1⟩)
  rw [hKG, ← wallCompass_eq_of_closed_outside_Z hRle hclosed hW hdisj, ← hK,
    wallCompass_relabelGraph]

/-- **Output (iii) of (9.9) for `G` and `Y`, from output (a).** For a valid state of (9.9) and
output (a) of steps (5) to (7) for a wall `W` whose compass misses `Z_i`, the block in `a_wall`
parses to some `p`, and the renamed block `p.movedBlock` has the five properties of output
(iii) for `G` and any `Y` that meets the image of `orig` in `orig(X)`. -/
theorem isAlg99OutputIII_of_target {h' s h ω : ℕ} {st : Alg99Iter h' G}
    (hst : st.IsValid s) {X : Finset (Fin st.v)} {Y : Finset (Fin n)}
    (hY : ∀ u, st.orig u ∈ Y ↔ u ∈ X)
    {W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)}
    {h2 : 2 ≤ h} {he : Even h} {hW : W.IsValid} (hZ : Disjoint W.compassFinset st.Z)
    (hK : W.compassFinset.toNatSet =
      V(wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
        (W.toGMWall h2 he hW)))
    {C_blk w a_out a_wall : ℕ} {s' : State}
    (hA : IsCase3StepsOutputA h ω (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he
      hW C_blk w a_out a_wall s') :
    ∃ p : ParsedCase3Block
        ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X,
      parseCase3Block _ X (s'.arrs a_wall) = some p ∧
      let blk' := p.movedBlock hst.orig_injective (hst.edgeMult_wallUnion X)
      let H := case3Decoder.wall n G Y blk'
      let S_H := case3Decoder.society n G Y blk'
      let 𝒜 := case3Decoder.division n G Y blk'
      H.height = h ∧
      IsFlatWallIn (GM09.deleteVertices G.toGMDigraph.toGraph Y.toNatSet) H ∧
      IsWallSociety (GM09.deleteVertices G.toGMDigraph.toGraph Y.toNatSet) H S_H ∧
      IsRuralDivision S_H 𝒜 ∧
      ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        IsInteriorMember H 𝒜 A →
          let bd := case3Decoder.branchDecomp n G Y blk' A
          E(A).ncard ≤ 1 ∨
            (IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω) := by
  obtain ⟨Kv, Ke, c, ms, -, hwall, -, -, hH, hheight, hflat, hsoc, hrd, hbd⟩ := hA
  rw [← hwall] at hH hheight hflat hsoc hrd hbd
  set blk := s'.arrs a_wall
  obtain ⟨p, hparse⟩ : ∃ p, parseCase3Block
      ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X blk = some p := by
    cases hp : parseCase3Block
        ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X blk with
    | some p => exact ⟨p, rfl⟩
    | none =>
      have hdiv : case3Decoder.division st.v (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H)
          X blk = ∅ := by
        simp [case3Decoder, case3DivisionOfDel, hp]
      rw [hdiv] at hrd
      exact absurd hrd (not_isRuralDivision_empty hsoc)
  refine ⟨p, hparse, ?_⟩
  obtain ⟨hw, -, -⟩ := case3Decoder_of_parse hparse
  have hpH : p.toGMWall = W.toGMWall h2 he hW := hw ▸ hH
  have hdel : delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X =
      delGraph st.Gi X := delGraph_wallUnionMultiDigraph _ _ _
  have hHle : p.toGMWall.graph ≤ delGraph st.Gi X := by
    rw [← hdel, delGraph_eq_deleteVertices, ← hw]
    exact hflat.1
  have hZ' : Disjoint V(wallCompass (delGraph st.Gi X) p.toGMWall) st.Z.toNatSet := by
    rw [← hdel, hpH, ← hK]
    exact disjoint_toNatSet hZ
  have hcomp := wallCompass_relabel_eq_of_target hst hY hHle hZ'
  rw [← hdel] at hcomp
  exact isCase3Output_movedBlock hst.orig_injective (hst.edgeMult_wallUnion X) hY p hparse hcomp
    hheight hflat hsoc hrd hbd

/-- **Output (iii) of (9.9), standalone form.** With `Y = orig(X)` and `|X| < C(p, 2)`, the word
list `2 :: (bitSetList (orig(X)) ++ p.movedBlock)` is an output (iii) of (9.9) for `G`
(`IsAlg99Output`). -/
theorem isAlg99Output_of_case3StepsOutputA {h' s pp h ω : ℕ} {st : Alg99Iter h' G}
    (hst : st.IsValid s) {X : Finset (Fin st.v)} (hXc : X.card < pp.choose 2)
    {W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)}
    {h2 : 2 ≤ h} {he : Even h} {hW : W.IsValid} (hZ : Disjoint W.compassFinset st.Z)
    (hK : W.compassFinset.toNatSet =
      V(wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
        (W.toGMWall h2 he hW)))
    {C_blk w a_out a_wall : ℕ} {s' : State}
    (hA : IsCase3StepsOutputA h ω (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he
      hW C_blk w a_out a_wall s') :
    ∃ p : ParsedCase3Block
        ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X,
      parseCase3Block _ X (s'.arrs a_wall) = some p ∧
      IsAlg99Output case3Decoder pp h ω ⟨n, G⟩
        (2 :: (bitSetList (X.image st.orig) ++
          p.movedBlock hst.orig_injective (hst.edgeMult_wallUnion X))) := by
  obtain ⟨p, hparse, hH, hflat, hsoc, hrd, hbd⟩ :=
    isAlg99OutputIII_of_target hst (fun _ => mem_image_orig_iff hst.orig_injective) hZ hK hA
  refine ⟨p, hparse, Or.inr (Or.inr ⟨X.image st.orig, _, rfl, ?_, hH, hflat, hsoc, hrd, hbd⟩)⟩
  rw [Finset.card_image_of_injective _ hst.orig_injective]
  exact hXc

/-- The words of a union of finsets. -/
theorem toNatSet_union' {m : ℕ} (A B : Finset (Fin m)) :
    (A ∪ B).toNatSet = A.toNatSet ∪ B.toNatSet := by
  simp only [Finset.toNatSet, Finset.coe_union, Set.image_union]

/-- `(G_i \ Z) \ X` is `G_i \ (X ∪ Z)`, for the graphs of `Alg99Spec`. -/
theorem deleteVertices_toGraph_deleteVertices_eq {m : ℕ} (Gi : MultiDigraph m)
    (Z X : Finset (Fin m)) :
    GM09.deleteVertices (Gi.toGMDigraph.deleteVertices Z.toNatSet).toGraph X.toNatSet =
      delGraph Gi (X ∪ Z) := by
  rw [GM13.Digraph.toGraph_deleteVertices, deleteVertices_deleteVertices_union,
    delGraph_eq_deleteVertices, toNatSet_union', Set.union_comm]

/-- **Output (iii) of (9.9) in the form `Alg99Spec`, from output (a).** Let the loop of (9.9)
run on `D = G_i \ Z_i` (on `Fin m`), with a valid state whose map `orig` misses `Z_i`. From
output (a) for a wall whose compass misses the `Z` of the state, the block parses to some `p`,
and with `X_G = orig(X)` and `X' = X_G ∪ Z_i`, the renamed block has the properties that
`Alg99Spec` asks for in case (iii). -/
theorem isAlg99SpecIII_of_case3StepsOutputA {m h' s pp h ω : ℕ} {Gi : MultiDigraph m}
    {Zs : Finset (Fin m)} {st : Alg99Iter h' (Gi.deleteVertices Zs)}
    (hst : st.IsValid s) (hR : ∀ u, st.orig u ∉ Zs) {X : Finset (Fin st.v)}
    (hXc : X.card < pp.choose 2)
    {W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)}
    {h2 : 2 ≤ h} {he : Even h} {hW : W.IsValid} (hZ : Disjoint W.compassFinset st.Z)
    (hK : W.compassFinset.toNatSet =
      V(wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X)
        (W.toGMWall h2 he hW)))
    {C_blk w a_out a_wall : ℕ} {s' : State}
    (hA : IsCase3StepsOutputA h ω (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he
      hW C_blk w a_out a_wall s') :
    ∃ p : ParsedCase3Block
        ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X,
      parseCase3Block _ X (s'.arrs a_wall) = some p ∧
      Disjoint (X.image st.orig) Zs ∧
      (X.image st.orig).card < pp.choose 2 ∧
      let block := p.movedBlock hst.orig_injective (hst.edgeMult_wallUnion X)
      let X' := X.image st.orig ∪ Zs
      let H := case3Decoder.wall m Gi X' block
      let S_H := case3Decoder.society m Gi X' block
      let 𝒜 := case3Decoder.division m Gi X' block
      H.height = h ∧
      IsFlatWallIn
        (GM09.deleteVertices (Gi.toGMDigraph.deleteVertices Zs.toNatSet).toGraph
          (X.image st.orig).toNatSet) H ∧
      IsWallSociety
        (GM09.deleteVertices (Gi.toGMDigraph.deleteVertices Zs.toNatSet).toGraph
          (X.image st.orig).toNatSet) H S_H ∧
      IsRuralDivision S_H 𝒜 ∧
      ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        IsInteriorMember H 𝒜 A →
          let bd := case3Decoder.branchDecomp m Gi X' block A
          E(A).ncard ≤ 1 ∨
            (IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω) := by
  have hY : ∀ u, st.orig u ∈ X.image st.orig ∪ Zs ↔ u ∈ X := by
    intro u
    rw [Finset.mem_union, mem_image_orig_iff hst.orig_injective]
    exact ⟨fun h => h.resolve_right (hR u), Or.inl⟩
  obtain ⟨p, hparse, hH, hflat, hsoc, hrd, hbd⟩ := isAlg99OutputIII_of_target hst hY hZ hK hA
  have hsub : Zs ⊆ X.image st.orig ∪ Zs := Finset.subset_union_right
  have hgraph : GM09.deleteVertices (Gi.deleteVertices Zs).toGMDigraph.toGraph
      (X.image st.orig ∪ Zs).toNatSet =
      GM09.deleteVertices (Gi.toGMDigraph.deleteVertices Zs.toNatSet).toGraph
        (X.image st.orig).toNatSet := by
    rw [deleteVertices_toGraph_deleteVertices_eq, ← delGraph_eq_deleteVertices,
      delGraph_deleteVertices_of_subset _ hsub]
  rw [hgraph, case3Decoder_wall_deleteVertices_of_subset Gi hsub] at hflat hsoc
  rw [case3Decoder_society_deleteVertices_of_subset Gi hsub] at hsoc
  rw [case3Decoder_wall_deleteVertices_of_subset Gi hsub] at hH
  rw [case3Decoder_society_deleteVertices_of_subset Gi hsub,
    case3Decoder_division_deleteVertices_of_subset Gi hsub] at hrd
  rw [case3Decoder_wall_deleteVertices_of_subset Gi hsub,
    case3Decoder_division_deleteVertices_of_subset Gi hsub] at hbd
  refine ⟨p, hparse, ?_, ?_, hH, hflat, hsoc, hrd, fun A hA => ?_⟩
  · rw [Finset.disjoint_left]
    rintro _ hx hxZ
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
    exact hR u hxZ
  · rw [Finset.card_image_of_injective _ hst.orig_injective]
    exact hXc
  · have hb := hbd hA
    simp only at hb ⊢
    rw [case3Decoder_branchDecomp_deleteVertices_of_subset Gi hsub] at hb
    exact hb

end GraphMinor.Compute
