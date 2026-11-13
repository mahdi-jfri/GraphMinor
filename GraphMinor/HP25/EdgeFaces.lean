module

public import GraphMinor.HP25.Rib
import GraphMinor.HP25.PlaneLens
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.SurfaceGraph

/-!
# The faces on the two sides of an edge

Used in the proof of Proposition 2.3 of Humeau and Pous (page 7): "Each consecutive pair of edges
bounds a common face", and in the proof of Lemma 3.3 (page 10): "In a plane embedding of a planar
graph, an edge may bound at most two faces".

Let `uv` be an edge of a plane embedding with line `L`. The thin disc around `L`
(`exists_plane_edge_lens_sides`) is cut by `L` into two sides, and each side lies in one face. We
show (`PlaneEmbedding.edge_faces`):
* each of these two faces has all of `L` on its frontier;
* every face whose closure has a point of `L` other than its ends is one of the two;
* the two faces are different when `L` lies on an `O`-arc `T` of the drawn set: the inner and the
  outer domain of `T` both come near every point of `L`, so a single face on both sides of `L` would
  meet both domains, and it cannot, being connected and away from `T`.

For a rib embedding the faces are the outer domain of the frame and the inner domains of the
triangles. So the edge `xy` lies in at most two triangles, in at most one when it is an edge of the
frame, and in exactly two otherwise (`PlaneEmbedding.IsRibEmbedding.common_neighbours`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

/-- The drawn set without the line of the edge `uv`: the points of the vertices and the lines of the
other edges. -/
@[expose] def rest (u v : V) : Set ℂ :=
  φ.pt '' R ∪ ⋃ a ∈ R, ⋃ b ∈ R, ⋃ (_ : G.Adj a b ∧ s(a, b) ≠ s(u, v)), φ.line a b

theorem isClosed_rest (u v : V) : IsClosed (φ.rest u v) := by
  refine ((φ.finite.image _).isCompact.union ?_).isClosed
  exact φ.finite.isCompact_biUnion fun a ha => φ.finite.isCompact_biUnion fun b hb =>
    isCompact_iUnion fun h => (φ.isLine a ha b hb h.1).isCompact

theorem U_eq_rest {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    φ.U = φ.rest u v ∪ φ.line u v := by
  refine Subset.antisymm (fun z hz => ?_) (union_subset (fun z hz => ?_) (φ.line_subset_U hu hv huv))
  · rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ha, b, hb, hab, hz⟩ := hz
      by_cases he : s(a, b) = s(u, v)
      · right
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hz
        · rwa [φ.line_comm]
      · left; right
        simp only [mem_iUnion]
        exact ⟨a, ha, b, hb, ⟨hab, he⟩, hz⟩
  · rcases hz with hz | hz
    · exact Or.inl hz
    · simp only [mem_iUnion] at hz
      obtain ⟨a, ha, b, hb, hab, hz⟩ := hz
      exact φ.line_subset_U ha hb hab.1 hz

theorem line_inter_rest {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    φ.line u v ∩ φ.rest u v ⊆ {φ.pt u, φ.pt v} := by
  rintro z ⟨hz1, hz2 | hz2⟩
  · obtain ⟨w, hw, rfl⟩ := hz2
    rcases φ.avoid u hu v hv huv w hw hz1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp only [mem_iUnion] at hz2
    obtain ⟨a, ha, b, hb, ⟨hab, hne⟩, hz2⟩ := hz2
    obtain ⟨w, ⟨hw, -⟩, rfl⟩ := φ.inter u hu v hv a ha b hb huv hab hne.symm ⟨hz1, hz2⟩
    rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The faces of the embedding with a common point are equal. -/
theorem eq_of_mem_faces {f f' : Set ℂ} (hf : f ∈ φ.faces) (hf' : f' ∈ φ.faces) {z : ℂ} (hz : z ∈ f)
    (hz' : z ∈ f') : f = f' := by
  obtain ⟨a, -, rfl⟩ := hf
  obtain ⟨b, -, rfl⟩ := hf'
  rw [connectedComponentIn_eq hz, connectedComponentIn_eq hz']

/-- A point of `U`'s complement lies in a face. -/
theorem mem_faces_of_notMem {z : ℂ} (hz : z ∉ φ.U) :
    connectedComponentIn (univ \ φ.U) z ∈ φ.faces ∧ z ∈ connectedComponentIn (univ \ φ.U) z :=
  ⟨mem_image_of_mem _ ⟨mem_univ _, hz⟩, mem_connectedComponentIn ⟨mem_univ _, hz⟩⟩

/-- A line has a point other than its ends. -/
theorem _root_.GraphMinor.HP25.exists_inner_point {L : Set ℂ} {a b : ℂ} (hL : IsLineWithEnds L a b) :
    ∃ p ∈ L, p ≠ a ∧ p ≠ b := by
  obtain ⟨c, hc, hrc, hc0, hc1⟩ := hL.exists_arc
  refine ⟨c ⟨1 / 2, by norm_num, by norm_num⟩, hrc ▸ mem_range_self _, ?_, ?_⟩
  · rw [← hc0]
    intro h
    have := congrArg Subtype.val (hc.2 h)
    norm_num at this
  · rw [← hc1]
    intro h
    have := congrArg Subtype.val (hc.2 h)
    norm_num at this

/-- **The two faces at an edge.** For an edge `uv` there are faces `f₁`, `f₂` with the line `L` of
`uv` on their frontiers, such that every face whose closure meets `L` away from its ends is `f₁` or
`f₂`, and `f₁ ≠ f₂` when `L` lies on an `O`-arc of the drawn set. -/
theorem edge_faces {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) :
    ∃ f₁ ∈ φ.faces, ∃ f₂ ∈ φ.faces, φ.line u v ⊆ frontier f₁ ∧ φ.line u v ⊆ frontier f₂ ∧
      (∀ f ∈ φ.faces, ∀ p ∈ φ.line u v, p ≠ φ.pt u → p ≠ φ.pt v → p ∈ closure f → f = f₁ ∨ f = f₂) ∧
      (∀ T : Set ℂ, IsJordanParts T → T ⊆ φ.U → φ.line u v ⊆ T → f₁ ≠ f₂) := by
  have hL := φ.isLine u hu v hv huv
  have hne : φ.pt u ≠ φ.pt v := fun h => huv.ne (φ.injOn hu hv h)
  obtain ⟨D, A, B, hD, hLD, hDZ, -, -, hbdL, hDeq, hA, hB, hAne, hBne, hAL, hBL, hLA, hLB, -, -, -, -,
    -⟩ := exists_plane_edge_lens_sides hL hne (φ.isClosed_rest u v) (φ.line_inter_rest hu hv huv)
  have hUeq := φ.U_eq_rest hu hv huv
  -- the two sides miss the drawn set
  have hAU : A ⊆ φ.Uᶜ := by
    intro z hz hzU
    rw [hUeq] at hzU
    rcases hzU with h | h
    · have : z ∈ ({φ.pt u, φ.pt v} : Set ℂ) := hDZ ⟨hDeq ▸ Or.inl (Or.inl hz), h⟩
      rcases this with rfl | rfl
      · exact disjoint_left.mp hAL hz hL.left_mem
      · exact disjoint_left.mp hAL hz hL.right_mem
    · exact disjoint_left.mp hAL hz h
  have hBU : B ⊆ φ.Uᶜ := by
    intro z hz hzU
    rw [hUeq] at hzU
    rcases hzU with h | h
    · have : z ∈ ({φ.pt u, φ.pt v} : Set ℂ) := hDZ ⟨hDeq ▸ Or.inl (Or.inr hz), h⟩
      rcases this with rfl | rfl
      · exact disjoint_left.mp hBL hz hL.left_mem
      · exact disjoint_left.mp hBL hz hL.right_mem
    · exact disjoint_left.mp hBL hz h
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨hf₁, ha₁⟩ := φ.mem_faces_of_notMem (hAU ha)
  obtain ⟨hf₂, hb₂⟩ := φ.mem_faces_of_notMem (hBU hb)
  set f₁ := connectedComponentIn (univ \ φ.U) a
  set f₂ := connectedComponentIn (univ \ φ.U) b
  have hAf : A ⊆ f₁ := φ.subset_face hf₁ hA hAU ha ha₁
  have hBf : B ⊆ f₂ := φ.subset_face hf₂ hB hBU hb hb₂
  have hint : ∀ p ∈ φ.line u v, p ≠ φ.pt u → p ≠ φ.pt v → p ∈ discInt D := fun p hp h1 h2 =>
    ⟨hLD hp, fun h => by rcases hbdL ⟨h, hp⟩ with h | h <;> contradiction⟩
  have hopen : IsOpen (discInt D) := hD.isOpen_discInt isManifoldPoint_complex
  -- a point of the disc off the line is on one of the two sides
  have hside : ∀ z ∈ D, z ∉ φ.line u v → z ∈ f₁ ∨ z ∈ f₂ := by
    intro z hz hzL
    rw [hDeq] at hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl (hAf hz)
    · exact Or.inr (hBf hz)
    · exact absurd hz hzL
  have hfront : ∀ {f : Set ℂ} (hf : f ∈ φ.faces) {S : Set ℂ}, S ⊆ f → φ.line u v ⊆ closure S →
      φ.line u v ⊆ frontier f := by
    intro f hf S hSf hLS p hp
    have hfo := (φ.isOpen_of_mem_faces hf)
    rw [frontier, hfo.1.interior_eq]
    exact ⟨closure_mono hSf (hLS hp), fun h => hfo.2.2 h (φ.line_subset_U hu hv huv hp)⟩
  refine ⟨f₁, hf₁, f₂, hf₂, hfront hf₁ hAf hLA, hfront hf₂ hBf hLB, ?_, ?_⟩
  · intro f hf p hp h1 h2 hpf
    obtain ⟨z, hzD, hzf⟩ := mem_closure_iff.mp hpf _ hopen (hint p hp h1 h2)
    have hzL : z ∉ φ.line u v := fun h =>
      (φ.isOpen_of_mem_faces hf).2.2 hzf (φ.line_subset_U hu hv huv h)
    rcases hside z hzD.1 hzL with h | h
    · exact Or.inl (φ.eq_of_mem_faces hf hf₁ hzf h)
    · exact Or.inr (φ.eq_of_mem_faces hf hf₂ hzf h)
  · intro T J hTU hLT he
    obtain ⟨p, hp, h1, h2⟩ := exists_inner_point hL
    have hpT : p ∈ T := hLT hp
    have hmeet : ∀ {W : Set ℂ}, IsOpen W → frontier W = T → (W ∩ f₁).Nonempty := by
      intro W hW hfr
      have hpW : p ∈ closure W := by
        have : p ∈ frontier W := hfr ▸ hpT
        exact this.1
      obtain ⟨z, hzD, hzW⟩ := mem_closure_iff.mp hpW _ hopen (hint p hp h1 h2)
      have hzT : z ∉ T := by
        intro hzT
        have : z ∈ frontier W := hfr ▸ hzT
        rw [frontier, hW.interior_eq] at this
        exact this.2 hzW
      rcases hside z hzD.1 (fun h => hzT (hLT h)) with h | h
      · exact ⟨z, hzW, h⟩
      · exact ⟨z, hzW, he ▸ h⟩
    have hf₁T : Disjoint f₁ T := disjoint_left.mpr fun z hz hzT =>
      (φ.isOpen_of_mem_faces hf₁).2.2 hz (hTU hzT)
    obtain ⟨z₁, hz₁i, hz₁f⟩ := hmeet J.isOpen_inner J.frontier_inner
    obtain ⟨z₂, hz₂o, hz₂f⟩ := hmeet J.isOpen_outer J.frontier_outer
    have hsub := J.subset_inner (φ.isOpen_of_mem_faces hf₁).2.1.isPreconnected hf₁T ⟨z₁, hz₁f, hz₁i⟩
    exact disjoint_left.mp J.disjoint (hsub hz₂f) hz₂o

end PlaneEmbedding

/-! ### Edges and faces of a rib -/

namespace PlaneEmbedding

variable {φ : PlaneEmbedding G R}

/-- `xy` is an edge of the cycle `C`: some pair of cyclically consecutive entries of `C` is `x, y` in
some order. -/
@[expose] def IsCycleEdge (C : List V) (x y : V) : Prop :=
  ∃ p ∈ C.zip (C.rotate 1), s(x, y) = s(p.1, p.2)

/-- The line of an edge `xy` lies on the image of a cycle `C` exactly when `xy` is an edge of `C`. -/
theorem line_subset_cycleImage_iff {C : List V} (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R)
    {x y : V} (hx : x ∈ R) (hy : y ∈ R) (hxy : G.Adj x y) :
    φ.line x y ⊆ φ.cycleImage C ↔ IsCycleEdge C x y := by
  constructor
  · intro hsub
    obtain ⟨p, hp, h1, h2⟩ := exists_inner_point (φ.isLine x hx y hy hxy)
    have hpC := hsub hp
    simp only [cycleImage, mem_iUnion] at hpC
    obtain ⟨q, hq, hpq⟩ := hpC
    refine ⟨q, hq, by_contra fun hne => ?_⟩
    have hq1 := hR _ (List.of_mem_zip hq).1
    have hq2 := hR _ (List.mem_rotate.mp (List.of_mem_zip hq).2)
    obtain ⟨w, ⟨hw, -⟩, rfl⟩ := φ.inter x hx y hy q.1 hq1 q.2 hq2 hxy (hC.2.2 q hq) hne ⟨hp, hpq⟩
    rcases hw with rfl | rfl
    · exact h1 rfl
    · exact h2 rfl
  · rintro ⟨q, hq, he⟩ z hz
    simp only [cycleImage, mem_iUnion]
    refine ⟨q, hq, ?_⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hz
    · rwa [φ.line_comm]

/-- A point lies on the image of a triangle `abc` exactly when it lies on the line of two distinct
vertices of `{a, b, c}`. -/
theorem mem_cycleImage_three_iff {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) {z : ℂ} :
    z ∈ φ.cycleImage [a, b, c] ↔
      ∃ u ∈ ({a, b, c} : Set V), ∃ v ∈ ({a, b, c} : Set V), u ≠ v ∧ z ∈ φ.line u v := by
  rw [φ.cycleImage_three]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨a, by simp, b, by simp, hab, h⟩
    · exact ⟨b, by simp, c, by simp, hbc, h⟩
    · exact ⟨c, by simp, a, by simp, hac.symm, h⟩
  · rintro ⟨u, hu, v, hv, huv, hz⟩
    simp only [mem_insert_iff, mem_singleton_iff] at hu hv
    have hl := φ.line_comm
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl huv
      | exact Or.inl (Or.inl hz) | exact Or.inl (Or.inr hz) | exact Or.inr hz
      | exact Or.inl (Or.inl (hl _ _ ▸ hz)) | exact Or.inl (Or.inr (hl _ _ ▸ hz))
      | exact Or.inr (hl _ _ ▸ hz)

/-- The image of a triangle depends only on its set of vertices. -/
theorem cycleImage_three_eq {a b c a' b' c' : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hab' : a' ≠ b') (hbc' : b' ≠ c') (hac' : a' ≠ c') (h : ({a, b, c} : Set V) = {a', b', c'}) :
    φ.cycleImage [a, b, c] = φ.cycleImage [a', b', c'] := by
  ext z
  rw [mem_cycleImage_three_iff hab hbc hac, mem_cycleImage_three_iff hab' hbc' hac', h]

end PlaneEmbedding

end GraphMinor.HP25
