module

public import GraphMinor.GM13.Section4
public import GraphMinor.GM16.SubcubicSubdivision
import GraphMinor.GM16.RectangularGridDrawing
import GraphMinor.GM16.EmbeddedLineGraphDrawing
import GraphMinor.GM16.RectangularGridLinePoints
import GraphMinor.GM16.RectangularGridLineIntersections

/-!
# Graph Minors XIII, Section 7 (Part A): Elementary Walls, Planarity, and (7.1)–(7.2)

This file formalizes the first part of Section 7 of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 88–90):

- Planarity and subcubic degree bound for `elementaryWall h` (`isPlanar_elementaryWall`,
  `isPlanarGraph_elementaryWall`, `exists_wall_of_isIsoMinor_elementaryWall`).
- `exists_wall_of_large_branchWidth`: for every even `h ≥ 2` there is a number `ω` such that
  every finite graph with branch-width `≥ ω` has a subgraph which is a wall of height `h`. This
  is (4.2) for the elementary wall, together with the remark on page 89 that turns a minor of the
  elementary wall into a wall. It is the hypothesis of (7.1) (page 89), not (7.1) itself.
- `exists_wall_or_branchDecomposition`: what the output of Algorithm (7.2) (page 89) satisfies,
  without the running time. Every finite graph has a wall of height `h` as a subgraph or has
  small branch-width, and (3.3) gives a subgraph with a branch-decomposition of small width.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}

/-! ## Basic properties of `elementaryWall h` -/

/-- `elementaryWallAdj h` is symmetric. -/
lemma elementaryWallAdj_symm {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q) :
    elementaryWallAdj h q p := by
  rcases hadj with ⟨hp, hq, ⟨hy, hx⟩ | ⟨hx, hy⟩⟩
  · exact ⟨hq, hp, Or.inl ⟨hy.symm, hx.symm⟩⟩
  · exact ⟨hq, hp, Or.inr ⟨hx.symm, hy.symm⟩⟩

/-- `elementaryWallAdj h` is irreflexive. -/
lemma elementaryWallAdj_irrefl {h : ℕ} (p : ℕ × ℕ) : ¬ elementaryWallAdj h p p := by
  rintro ⟨_, _, ⟨_, h1 | h1⟩ | ⟨_, ⟨h1, _⟩ | ⟨h1, _⟩⟩⟩ <;> omega

/-- The vertex set `V(elementaryWall h)` is finite. -/
lemma elementaryWall_finite_V (h : ℕ) : V(elementaryWall h).Finite := by
  have hsub : elementaryWallVerts h ⊆
      (Finset.Iic (2 * h + 1) ×ˢ Finset.Iic h : Finset (ℕ × ℕ)) := by
    intro p hp
    simp only [Finset.coe_product, Finset.coe_Iic, mem_prod, mem_Iic]
    exact ⟨hp.1, hp.2.1⟩
  exact (Finset.finite_toSet _).subset hsub

/-- The edge set `E(elementaryWall h)` is finite. -/
lemma elementaryWall_finite_E (h : ℕ) : E(elementaryWall h).Finite := by
  let Vfin := elementaryWall_finite_V h
  let P : Set ((ℕ × ℕ) × (ℕ × ℕ)) := V(elementaryWall h) ×ˢ V(elementaryWall h)
  have hP : P.Finite := Vfin.prod Vfin
  have hsub : E(elementaryWall h) ⊆ (fun pq : (ℕ × ℕ) × (ℕ × ℕ) => s(pq.1, pq.2)) '' P := by
    rintro e ⟨p, q, hadj, rfl⟩
    exact ⟨(p, q), ⟨hadj.1, hadj.2.1⟩, rfl⟩
  exact (hP.image _).subset hsub

/-- Coordinate embedding of `ℕ × ℕ` into `Fin (2 * h + 6) × Fin (2 * h + 6)` for `elementaryWall h`. -/
def elementaryWallGridEmbed (h : ℕ) (p : ℕ × ℕ) : Fin (2 * h + 6) × Fin (2 * h + 6) :=
  (⟨min p.1 (2 * h + 5), by omega⟩, ⟨min p.2 (2 * h + 5), by omega⟩)

lemma elementaryWallGridEmbed_fst {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    ((elementaryWallGridEmbed h p).1 : ℕ) = p.1 := by
  have hp1 : p.1 ≤ 2 * h + 1 := hp.1
  dsimp [elementaryWallGridEmbed]
  omega

lemma elementaryWallGridEmbed_snd {h : ℕ} {p : ℕ × ℕ} (hp : p ∈ elementaryWallVerts h) :
    ((elementaryWallGridEmbed h p).2 : ℕ) = p.2 := by
  have hp2 : p.2 ≤ h := hp.2.1
  dsimp [elementaryWallGridEmbed]
  omega

lemma elementaryWallGridEmbed_injOn (h : ℕ) :
    InjOn (elementaryWallGridEmbed h) (elementaryWallVerts h) := by
  intro p hp q hq heq
  have hx : p.1 = q.1 := by
    rw [← elementaryWallGridEmbed_fst hp, ← elementaryWallGridEmbed_fst hq]
    exact congrArg (fun z : Fin (2 * h + 6) × Fin (2 * h + 6) => (z.1 : ℕ)) heq
  have hy : p.2 = q.2 := by
    rw [← elementaryWallGridEmbed_snd hp, ← elementaryWallGridEmbed_snd hq]
    exact congrArg (fun z : Fin (2 * h + 6) × Fin (2 * h + 6) => (z.2 : ℕ)) heq
  exact Prod.ext hx hy

lemma elementaryWallAdj_imp_grid_adj {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q) :
    (pathGraph (2 * h + 6) □ pathGraph (2 * h + 6)).Adj
      (elementaryWallGridEmbed h p) (elementaryWallGridEmbed h q) := by
  have hp := hadj.1
  have hq := hadj.2.1
  rw [SimpleGraph.boxProd_adj]
  rcases hadj.2.2 with ⟨hy, hx⟩ | ⟨hx, ⟨hy, _⟩ | ⟨hy, _⟩⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.pathGraph_adj, elementaryWallGridEmbed_fst hp, elementaryWallGridEmbed_fst hq]
      exact hx
    · apply Fin.ext
      rw [elementaryWallGridEmbed_snd hp, elementaryWallGridEmbed_snd hq, hy]
  · right
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.pathGraph_adj, elementaryWallGridEmbed_snd hp, elementaryWallGridEmbed_snd hq]
      exact Or.inl hy
    · apply Fin.ext
      rw [elementaryWallGridEmbed_fst hp, elementaryWallGridEmbed_fst hq, hx]
  · right
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.pathGraph_adj, elementaryWallGridEmbed_snd hp, elementaryWallGridEmbed_snd hq]
      exact Or.inr hy
    · apply Fin.ext
      rw [elementaryWallGridEmbed_fst hp, elementaryWallGridEmbed_fst hq, hx]

lemma gridGraph_isLink_of_adj {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q) :
    (GM01.gridGraph (2 * h + 6)).IsLink
      (s(elementaryWallGridEmbed h p, elementaryWallGridEmbed h q))
      (elementaryWallGridEmbed h p) (elementaryWallGridEmbed h q) := by
  unfold GM01.gridGraph
  rw [Graph.ofSimpleGraph_isLink, SimpleGraph.mem_edgeSet]
  exact ⟨rfl, elementaryWallAdj_imp_grid_adj hadj⟩

/-- Every elementary wall `elementaryWall h` is isomorphic to a minor of the `(2h + 6)`-grid. -/
theorem isPlanarGraph_elementaryWall (h : ℕ) :
    ∃ θ : ℕ, 6 ≤ θ ∧ Even θ ∧ IsIsoMinor (elementaryWall h) (GM01.gridGraph θ) := by
  let θ := 2 * h + 6
  refine ⟨θ, by omega, ⟨h + 3, by omega⟩, ?_⟩
  let ηv (p : ℕ × ℕ) : Set (Fin θ × Fin θ) := {elementaryWallGridEmbed h p}
  let ηe (e : Sym2 (ℕ × ℕ)) : Sym2 (Fin θ × Fin θ) := Sym2.map (elementaryWallGridEmbed h) e
  have hm : IsMinorModel (elementaryWall h) (GM01.gridGraph θ) ηv ηe :=
    { vertex_nonempty := fun p _ => singleton_nonempty _
      vertex_subset := fun p _ _ _ => trivial
      edge_mem := fun e he => by
        rcases he with ⟨p, q, hadj, rfl⟩
        exact (gridGraph_isLink_of_adj hadj).edge_mem
      vertex_disjoint := fun p hp q hq hne => by
        rw [disjoint_singleton]
        exact fun heq => hne (elementaryWallGridEmbed_injOn h hp hq heq)
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        rcases he₁ with ⟨p₁, q₁, hadj₁, rfl⟩
        rcases he₂ with ⟨p₂, q₂, hadj₂, rfl⟩
        change s(elementaryWallGridEmbed h p₁, elementaryWallGridEmbed h q₁) =
          s(elementaryWallGridEmbed h p₂, elementaryWallGridEmbed h q₂) at heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [elementaryWallGridEmbed_injOn h hadj₁.1 hadj₂.1 h1,
              elementaryWallGridEmbed_injOn h hadj₁.2.1 hadj₂.2.1 h2]
        · rw [elementaryWallGridEmbed_injOn h hadj₁.1 hadj₂.2.1 h1,
              elementaryWallGridEmbed_injOn h hadj₁.2.1 hadj₂.1 h2, Sym2.eq_swap]
      inc_iff := fun u hu e he => by
        rcases he with ⟨p, q, hadj, rfl⟩
        simp only [ηv, mem_singleton_iff, exists_eq_left]
        constructor
        · rintro ⟨w, hlink⟩
          rcases Sym2.eq_iff.mp hlink.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← h1]
            exact ⟨elementaryWallGridEmbed h q, gridGraph_isLink_of_adj hadj⟩
          · rw [← h2]
            exact ⟨elementaryWallGridEmbed h p, (gridGraph_isLink_of_adj hadj).symm⟩
        · rintro ⟨z, hz⟩
          unfold GM01.gridGraph at hz
          rw [Graph.ofSimpleGraph_isLink] at hz
          rcases Sym2.eq_iff.mp hz.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hu_eq : u = p := (elementaryWallGridEmbed_injOn h hadj.1 hu h1).symm
            subst hu_eq
            exact ⟨q, hadj, rfl⟩
          · have hu_eq : u = q := (elementaryWallGridEmbed_injOn h hadj.2.1 hu h2).symm
            subst hu_eq
            exact ⟨p, elementaryWallAdj_symm hadj, Sym2.eq_swap⟩
      isLoopAt_iff := fun u hu e he => by
        rcases he with ⟨p, q, hadj, rfl⟩
        simp only [ηv, mem_singleton_iff]
        constructor
        · intro hloop
          exfalso
          exact elementaryWallAdj_irrefl u hloop.1
        · intro hall
          exfalso
          have hinc_p : (GM01.gridGraph θ).Inc
              (s(elementaryWallGridEmbed h p, elementaryWallGridEmbed h q))
              (elementaryWallGridEmbed h p) :=
            ⟨elementaryWallGridEmbed h q, gridGraph_isLink_of_adj hadj⟩
          have hinc_q : (GM01.gridGraph θ).Inc
              (s(elementaryWallGridEmbed h p, elementaryWallGridEmbed h q))
              (elementaryWallGridEmbed h q) :=
            ⟨elementaryWallGridEmbed h p, (gridGraph_isLink_of_adj hadj).symm⟩
          have hp_eq : elementaryWallGridEmbed h p = elementaryWallGridEmbed h u := hall _ hinc_p
          have hq_eq : elementaryWallGridEmbed h q = elementaryWallGridEmbed h u := hall _ hinc_q
          have hpq : p = q :=
            elementaryWallGridEmbed_injOn h hadj.1 hadj.2.1 (hp_eq.trans hq_eq.symm)
          subst hpq
          exact elementaryWallAdj_irrefl p hadj
      connected := fun u _ => by
        let G₀ := (GM01.gridGraph θ).deleteEdges (ηe '' E(elementaryWall h))
        refine ⟨G₀.induce {elementaryWallGridEmbed h u},
          Graph.induce_le (by simp [G₀, GM01.gridGraph]), ?_, ?_⟩
        · ext x
          simp [G₀, GM01.gridGraph, ηv]
        · refine ⟨⟨elementaryWallGridEmbed h u, by simp [G₀, GM01.gridGraph]⟩, ?_⟩
          intro x hx y hy
          have hx' : x = elementaryWallGridEmbed h u := by simpa [G₀, GM01.gridGraph] using hx
          have hy' : y = elementaryWallGridEmbed h u := by simpa [G₀, GM01.gridGraph] using hy
          subst hx' hy'
          exact Relation.ReflTransGen.refl }
  exact isIsoMinor_of_isMinorModel (elementaryWall h) (GM01.gridGraph θ)
    (elementaryWall_finite_V h) (elementaryWall_finite_E h)
    (Set.toFinite _) (Set.toFinite _) ηv ηe hm

/-- The vertex coordinate map placing `elementaryWall h` at lattice points in `ℝ × ℝ`. -/
private def elementaryWallPoint (h : ℕ) (p : ℕ × ℕ) : ℝ × ℝ :=
  rectangularGridPoint (elementaryWallGridEmbed h p)

/-- The unit lattice line assigned to each edge of `elementaryWall h`. -/
private def elementaryWallLine (h : ℕ) (e : Sym2 (ℕ × ℕ)) : Set (ℝ × ℝ) :=
  rectangularGridLine (Sym2.map (elementaryWallGridEmbed h) e)

private lemma elementaryWallPoint_injOn (h : ℕ) :
    InjOn (elementaryWallPoint h) V(elementaryWall h) :=
  (rectangularGridPoint_injective (2 * h + 6) (2 * h + 6)).comp_injOn
    (elementaryWallGridEmbed_injOn h)

/-- The elementary wall `elementaryWall h` of any height `h : ℕ` is planar (`IsPlanar`). -/
theorem isPlanar_elementaryWall (h : ℕ) : IsPlanar (elementaryWall h) := by
  apply IsPlanar.of_plane_openEmbedding
  intro S _ _ j hj
  obtain ⟨Γ, _, _, _⟩ := exists_graphDrawing_of_embedded_lines
    (elementaryWall h) (elementaryWall_finite_V h) (elementaryWall_finite_E h)
    (elementaryWallPoint h) (elementaryWallPoint_injOn h) (elementaryWallLine h)
    (fun e v hLoop => elementaryWallAdj_irrefl v hLoop.1)
    (fun e _ a b hLink => by
      rcases hLink with ⟨hadj, rfl⟩
      change IsLineWithEnds
        (rectangularGridLine s(elementaryWallGridEmbed h a, elementaryWallGridEmbed h b))
        (rectangularGridPoint (elementaryWallGridEmbed h a))
        (rectangularGridPoint (elementaryWallGridEmbed h b))
      exact rectangularGridLine_isLine (elementaryWallAdj_imp_grid_adj hadj))
    (fun e he v hv hpt => by
      rcases he with ⟨a, b, hadj, rfl⟩
      have hadj_grid :
          s(elementaryWallGridEmbed h a, elementaryWallGridEmbed h b) ∈
            (pathGraph (2 * h + 6) □ pathGraph (2 * h + 6)).edgeSet :=
        elementaryWallAdj_imp_grid_adj hadj
      have hv_end :
          elementaryWallGridEmbed h v ∈
            s(elementaryWallGridEmbed h a, elementaryWallGridEmbed h b) :=
        rectangularGridLine_vertex hadj_grid hpt
      rw [Sym2.mem_iff] at hv_end
      rcases hv_end with h1 | h1
      · have hva : v = a := elementaryWallGridEmbed_injOn h hv hadj.1 h1
        subst hva
        exact ⟨b, hadj, rfl⟩
      · have hvb : v = b := elementaryWallGridEmbed_injOn h hv hadj.2.1 h1
        subst hvb
        exact ⟨a, elementaryWallAdj_symm hadj, Sym2.eq_swap⟩)
    (fun e he d hd hne x hx => by
      rcases he with ⟨a, b, hadj₁, rfl⟩
      rcases hd with ⟨c, dst, hadj₂, rfl⟩
      have hadj_grid₁ :
          s(elementaryWallGridEmbed h a, elementaryWallGridEmbed h b) ∈
            (pathGraph (2 * h + 6) □ pathGraph (2 * h + 6)).edgeSet :=
        elementaryWallAdj_imp_grid_adj hadj₁
      have hadj_grid₂ :
          s(elementaryWallGridEmbed h c, elementaryWallGridEmbed h dst) ∈
            (pathGraph (2 * h + 6) □ pathGraph (2 * h + 6)).edgeSet :=
        elementaryWallAdj_imp_grid_adj hadj₂
      have hne_grid :
          s(elementaryWallGridEmbed h a, elementaryWallGridEmbed h b) ≠
            s(elementaryWallGridEmbed h c, elementaryWallGridEmbed h dst) := by
        intro heq
        apply hne
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [elementaryWallGridEmbed_injOn h hadj₁.1 hadj₂.1 h1,
              elementaryWallGridEmbed_injOn h hadj₁.2.1 hadj₂.2.1 h2]
        · rw [elementaryWallGridEmbed_injOn h hadj₁.1 hadj₂.2.1 h1,
              elementaryWallGridEmbed_injOn h hadj₁.2.1 hadj₂.1 h2, Sym2.eq_swap]
      obtain ⟨z, rfl⟩ := rectangularGridLine_intersection hadj_grid₁ hadj_grid₂ hne_grid hx
      have hz_end :
          z ∈ s(elementaryWallGridEmbed h a, elementaryWallGridEmbed h b) :=
        rectangularGridLine_vertex hadj_grid₁ hx.1
      rw [Sym2.mem_iff] at hz_end
      rcases hz_end with rfl | rfl
      · exact ⟨a, hadj₁.1, rfl⟩
      · exact ⟨b, hadj₁.2.1, rfl⟩)
    j hj.isEmbedding
  exact ⟨Γ⟩

/-! ## Subcubic subdivision of `elementaryWall h` -/

/-- The simple graph on the subtype `elementaryWallVerts h` induced by `elementaryWallAdj h`. -/
def elementaryWallSimpleGraph (h : ℕ) : SimpleGraph (elementaryWallVerts h) where
  Adj u v := elementaryWallAdj h u.1 v.1
  symm := ⟨fun _ _ => elementaryWallAdj_symm⟩
  loopless := ⟨fun u => elementaryWallAdj_irrefl u.1⟩

/-- The unique candidate vertical neighbor of `p : ℕ × ℕ` in `elementaryWall h`. -/
def elementaryWallVertNeighbor (p : ℕ × ℕ) : ℕ × ℕ :=
  if Odd (p.1 + p.2) then (p.1, p.2 + 1) else (p.1, p.2 - 1)

lemma elementaryWallAdj_mem_three {h : ℕ} {p q : ℕ × ℕ} (hadj : elementaryWallAdj h p q) :
    q ∈ ({(p.1 + 1, p.2), (p.1 - 1, p.2), elementaryWallVertNeighbor p} : Set (ℕ × ℕ)) := by
  simp only [mem_insert_iff, mem_singleton_iff, elementaryWallVertNeighbor]
  rcases hadj.2.2 with ⟨hy, h1 | h1⟩ | ⟨hx, ⟨hy, hodd⟩ | ⟨hy, hodd⟩⟩
  · left
    exact Prod.ext h1.symm hy.symm
  · right; left
    exact Prod.ext (by omega) hy.symm
  · right; right
    simp only [hodd, ↓reduceIte]
    exact Prod.ext hx.symm hy.symm
  · right; right
    have hnot_odd : ¬ Odd (p.1 + p.2) := by
      rcases hodd with ⟨k, hk⟩
      intro ⟨m, hm⟩
      omega
    simp only [hnot_odd, ↓reduceIte]
    exact Prod.ext hx.symm (by omega)

/-- Every vertex of `elementaryWallSimpleGraph h` has degree at most 3. -/
lemma elementaryWallSimpleGraph_neighborSet_ncard_le_three (h : ℕ)
    (u : elementaryWallVerts h) :
    ((elementaryWallSimpleGraph h).neighborSet u).ncard ≤ 3 := by
  let T : Set (ℕ × ℕ) :=
    {(u.1.1 + 1, u.1.2), (u.1.1 - 1, u.1.2), elementaryWallVertNeighbor u.1}
  have hT_fin : T.Finite := by
    dsimp [T]
    exact ((finite_singleton _).insert _).insert _
  have hT_le : T.ncard ≤ 3 := by
    dsimp [T]
    calc ({(u.1.1 + 1, u.1.2), (u.1.1 - 1, u.1.2), elementaryWallVertNeighbor u.1} : Set (ℕ × ℕ)).ncard
        ≤ ({(u.1.1 - 1, u.1.2), elementaryWallVertNeighbor u.1} : Set (ℕ × ℕ)).ncard + 1 :=
          ncard_insert_le _ _
      _ ≤ ({elementaryWallVertNeighbor u.1} : Set (ℕ × ℕ)).ncard + 1 + 1 :=
          Nat.add_le_add_right (ncard_insert_le _ _) 1
      _ = 3 := by rw [ncard_singleton]
  have hsub : Subtype.val '' ((elementaryWallSimpleGraph h).neighborSet u) ⊆ T := by
    rintro _ ⟨v, hv, rfl⟩
    exact elementaryWallAdj_mem_three hv
  have hinj : Function.Injective (Subtype.val : elementaryWallVerts h → ℕ × ℕ) := Subtype.val_injective
  rw [← ncard_image_of_injective _ hinj]
  exact (ncard_le_ncard hsub hT_fin).trans hT_le

/-- Map from `E(Graph.ofSimpleGraph (elementaryWallSimpleGraph h))` to `E(elementaryWall h)`. -/
def elementaryWallEdgeTo (h : ℕ)
    (e : E(Graph.ofSimpleGraph (elementaryWallSimpleGraph h))) : E(elementaryWall h) :=
  ⟨Sym2.map Subtype.val e.1, by
    rcases e with ⟨e₀, he₀⟩
    change e₀ ∈ (elementaryWallSimpleGraph h).edgeSet at he₀
    induction e₀ using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he₀
      exact ⟨u.1, v.1, he₀, rfl⟩⟩

lemma elementaryWallEdgeTo_bijective (h : ℕ) :
    Function.Bijective (elementaryWallEdgeTo h) := by
  refine ⟨?_, ?_⟩
  · intro e₁ e₂ heq
    apply Subtype.ext
    have hmap := congrArg Subtype.val heq
    exact Sym2.map.injective Subtype.val_injective hmap
  · rintro ⟨e₀, p, q, hadj, rfl⟩
    let u : elementaryWallVerts h := ⟨p, hadj.1⟩
    let v : elementaryWallVerts h := ⟨q, hadj.2.1⟩
    have he_mem : s(u, v) ∈ E(Graph.ofSimpleGraph (elementaryWallSimpleGraph h)) := by
      change s(u, v) ∈ (elementaryWallSimpleGraph h).edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact hadj
    refine ⟨⟨s(u, v), he_mem⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Canonical isomorphism between `Graph.ofSimpleGraph (elementaryWallSimpleGraph h)` and
`elementaryWall h`. -/
noncomputable def simpleGraphIsoElementaryWall (h : ℕ) :
    Iso (Graph.ofSimpleGraph (elementaryWallSimpleGraph h)) (elementaryWall h) where
  vertexEquiv := Equiv.Set.univ (elementaryWallVerts h)
  edgeEquiv := Equiv.ofBijective (elementaryWallEdgeTo h) (elementaryWallEdgeTo_bijective h)
  isLink_iff := fun e x y => by
    rw [Graph.ofSimpleGraph_isLink]
    change (e.1 = s(x.1, y.1) ∧ e.1 ∈ (elementaryWallSimpleGraph h).edgeSet) ↔
      elementaryWallAdj h x.1.1 y.1.1 ∧ Sym2.map Subtype.val e.1 = s(x.1.1, y.1.1)
    constructor
    · rintro ⟨he, hadj⟩
      rw [he, SimpleGraph.mem_edgeSet] at hadj
      exact ⟨hadj, by rw [he]; rfl⟩
    · rintro ⟨hadj, hmap⟩
      have he : e.1 = s(x.1, y.1) := by
        apply Sym2.map.injective Subtype.val_injective
        exact hmap
      refine ⟨he, ?_⟩
      rw [he, SimpleGraph.mem_edgeSet]
      exact hadj

/-- Precomposing `IsIsoMinor H G` with an isomorphism `Iso H' H`. -/
lemma isIsoMinor_of_iso_left {α₁ β₁ α₂ β₂ : Type*}
    {H' : Graph α₁ β₁} {H : Graph α₂ β₂} {G : Graph α β}
    (iso : Iso H' H) (hminor : IsIsoMinor H G) : IsIsoMinor H' G := by
  rcases hminor with ⟨G', hG', C, hC, ⟨iso₂⟩⟩
  refine ⟨G', hG', C, hC, ⟨{
    vertexEquiv := iso.vertexEquiv.trans iso₂.vertexEquiv
    edgeEquiv := iso.edgeEquiv.trans iso₂.edgeEquiv
    isLink_iff := fun e x y =>
      (iso.isLink_iff e x y).trans
        (iso₂.isLink_iff (iso.edgeEquiv e) (iso.vertexEquiv x) (iso.vertexEquiv y))
  }⟩⟩

/-- When `2 ≤ h`, `E(elementaryWall h)` is nonempty (`s((1, 0), (2, 0))` is an edge). -/
lemma elementaryWall_edgeSet_nonempty {h : ℕ} (h2 : 2 ≤ h) : E(elementaryWall h).Nonempty := by
  refine ⟨s((1, 0), (2, 0)), (1, 0), (2, 0), ?_, rfl⟩
  refine ⟨?_, ?_, Or.inl ⟨rfl, Or.inl rfl⟩⟩
  · refine ⟨by omega, by omega, ?_, ?_⟩ <;> intro h_eq <;>
      have := congrArg Prod.fst h_eq <;> dsimp at this <;> omega
  · refine ⟨by omega, by omega, ?_, ?_⟩ <;> intro h_eq <;>
      have := congrArg Prod.fst h_eq <;> dsimp at this <;> omega

/-- If `IsIsoMinor (elementaryWall h) G` and `2 ≤ h`, then `β` is nonempty. -/
lemma nonempty_edge_of_isIsoMinor_elementaryWall {G : Graph α β} {h : ℕ} (h2 : 2 ≤ h)
    (hminor : IsIsoMinor (elementaryWall h) G) : Nonempty β := by
  rcases elementaryWall_edgeSet_nonempty h2 with ⟨e₀, he₀⟩
  rcases hminor with ⟨G', _, C, _, ⟨iso⟩⟩
  exact ⟨(iso.edgeEquiv ⟨e₀, he₀⟩).1⟩

/-- If a finite graph `G` has a minor isomorphic to `elementaryWall h` (`h ≥ 2` even), then `G`
contains a subgraph which is a wall of height `h`. -/
theorem exists_wall_of_isIsoMinor_elementaryWall {G : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite)
    {h : ℕ} (h2 : 2 ≤ h) (heven : Even h)
    (hminor : IsIsoMinor (elementaryWall h) G) :
    ∃ W : Wall α β, IsWallIn G W ∧ W.height = h := by
  have : Finite (elementaryWallVerts h) := (elementaryWall_finite_V h).to_subtype
  have : Nonempty β := nonempty_edge_of_isIsoMinor_elementaryWall h2 hminor
  let S := elementaryWallSimpleGraph h
  have hminorS : IsIsoMinor (Graph.ofSimpleGraph S) G :=
    isIsoMinor_of_iso_left (simpleGraphIsoElementaryWall h) hminor
  obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hVG hEG hminorS
  obtain ⟨N, c, P, hNG, hcInj, hc, hVN, hEN, hPaths, hInter⟩ :=
    GM16.exists_subcubic_subdivision hm (elementaryWallSimpleGraph_neighborSet_ncard_le_three h)
  let eMapS (e : S.edgeSet) : β := ηe e.1
  have heMapS_inj : Function.Injective eMapS := by
    intro e₁ e₂ heq
    apply Subtype.ext
    exact hm.edge_injOn e₁.2 e₂.2 heq
  let baseG : Graph α β :=
    { vertexSet := range c
      edgeSet := range eMapS
      IsLink := fun b x y => ∃ (e : S.edgeSet) (u v : elementaryWallVerts h),
        e.1 = s(u, v) ∧ S.Adj u v ∧ b = eMapS e ∧ x = c u ∧ y = c v
      isLink_symm := fun b _ => ⟨fun x y ⟨e, u, v, he, hadj, hb, hx, hy⟩ =>
        ⟨e, v, u, he.trans Sym2.eq_swap, hadj.symm, hb, hy, hx⟩⟩
      eq_or_eq_of_isLink_of_isLink := fun b x y z w h1 h2 => by
        rcases h1 with ⟨e₁, u₁, v₁, he₁, _, hb₁, rfl, rfl⟩
        rcases h2 with ⟨e₂, u₂, v₂, he₂, _, hb₂, rfl, rfl⟩
        have he_eq : e₁ = e₂ := heMapS_inj (hb₁.symm.trans hb₂)
        subst he_eq
        rcases Sym2.eq_iff.mp (he₁.symm.trans he₂) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      edge_mem_iff_exists_isLink := fun b => by
        constructor
        · rintro ⟨e, rfl⟩
          rcases e with ⟨e₀, he₀⟩
          induction e₀ using Sym2.ind with
          | _ u v =>
            rw [SimpleGraph.mem_edgeSet] at he₀
            exact ⟨c u, c v, ⟨s(u, v), he₀⟩, u, v, rfl, he₀, rfl, rfl, rfl⟩
        · rintro ⟨x, y, e, _, _, _, _, rfl, _, _⟩
          exact ⟨e, rfl⟩
      left_mem_of_isLink := fun b x y ⟨_, u, _, _, _, _, hx, _⟩ => ⟨u, hx.symm⟩ }
  let vEquivS : V(Graph.ofSimpleGraph S) ≃ V(baseG) :=
    (Equiv.Set.univ (elementaryWallVerts h)).trans (Equiv.ofInjective c hcInj)
  let eEquivS : E(Graph.ofSimpleGraph S) ≃ E(baseG) :=
    Equiv.ofInjective eMapS heMapS_inj
  have hIsoS_base : Iso (Graph.ofSimpleGraph S) baseG :=
    { vertexEquiv := vEquivS
      edgeEquiv := eEquivS
      isLink_iff := fun e x y => by
        rw [Graph.ofSimpleGraph_isLink]
        change (e.1 = s(x.1, y.1) ∧ e.1 ∈ S.edgeSet) ↔
          ∃ (e' : S.edgeSet) (u v : elementaryWallVerts h),
            e'.1 = s(u, v) ∧ S.Adj u v ∧ eMapS e = eMapS e' ∧ c x.1 = c u ∧ c y.1 = c v
        constructor
        · rintro ⟨he, hadj⟩
          rw [he, SimpleGraph.mem_edgeSet] at hadj
          exact ⟨e, x.1, y.1, he, hadj, rfl, rfl, rfl⟩
        · rintro ⟨e', u, v, he', hadj', hb, hx, hy⟩
          have he_eq : e = e' := heMapS_inj hb
          subst he_eq
          have hx_eq : x.1 = u := hcInj hx
          have hy_eq : y.1 = v := hcInj hy
          subst hx_eq hy_eq
          refine ⟨he', ?_⟩
          rw [he', SimpleGraph.mem_edgeSet]
          exact hadj' }
  let isoElem : Iso (elementaryWall h) baseG :=
    { vertexEquiv := (simpleGraphIsoElementaryWall h).vertexEquiv.symm.trans hIsoS_base.vertexEquiv
      edgeEquiv := (simpleGraphIsoElementaryWall h).edgeEquiv.symm.trans hIsoS_base.edgeEquiv
      isLink_iff := fun e x y => by
        have h1 := (simpleGraphIsoElementaryWall h).isLink_iff
          ((simpleGraphIsoElementaryWall h).edgeEquiv.symm e)
          ((simpleGraphIsoElementaryWall h).vertexEquiv.symm x)
          ((simpleGraphIsoElementaryWall h).vertexEquiv.symm y)
        simp only [Equiv.apply_symm_apply] at h1
        exact h1.symm.trans
          (hIsoS_base.isLink_iff
            ((simpleGraphIsoElementaryWall h).edgeEquiv.symm e)
            ((simpleGraphIsoElementaryWall h).vertexEquiv.symm x)
            ((simpleGraphIsoElementaryWall h).vertexEquiv.symm y)) }
  let subPaths (b : β) : Graph α β :=
    if hb : b ∈ range eMapS then P hb.choose else ⊥
  have hsubPaths_eq (e : S.edgeSet) : subPaths (eMapS e) = P e := by
    have hb : eMapS e ∈ range eMapS := ⟨e, rfl⟩
    dsimp [subPaths]
    rw [dite_eq_left hb]
    congr 1
    exact heMapS_inj hb.choose_spec
  let W : Wall α β :=
    { graph := N
      height := h
      two_le_height := h2
      even_height := heven
      baseGraph := baseG
      baseIso := isoElem
      subdivisionPaths := subPaths
      base_verts_subset := by
        rw [hVN]
        exact subset_union_left
      path_of_edge := by
        rintro b ⟨e, rfl⟩
        rw [hsubPaths_eq e]
        obtain ⟨u, v, he_uv, hadj_uv, hP_path, hηe_mem, hP_inter⟩ := hPaths e
        refine ⟨c u, c v, ⟨e, u, v, he_uv, hadj_uv, rfl, rfl, rfl⟩,
          hP_path, ⟨eMapS e, hηe_mem⟩, hP_inter⟩
      paths_disjoint := by
        rintro b₁ ⟨e₁, rfl⟩ b₂ ⟨e₂, rfl⟩ hne
        rw [hsubPaths_eq e₁, hsubPaths_eq e₂]
        have he_ne : e₁ ≠ e₂ := fun h => hne (congrArg eMapS h)
        exact hInter e₁ e₂ he_ne
      vertexSet_eq := by
        rw [hVN]
        congr 1
        ext x
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨e, hx⟩
          exact ⟨eMapS e, ⟨e, rfl⟩, (hsubPaths_eq e).symm ▸ hx⟩
        · rintro ⟨b, ⟨e, rfl⟩, hx⟩
          exact ⟨e, (hsubPaths_eq e) ▸ hx⟩
      edgeSet_eq := by
        rw [hEN]
        ext f
        simp only [mem_iUnion, exists_prop]
        constructor
        · rintro ⟨e, hf⟩
          exact ⟨eMapS e, ⟨e, rfl⟩, (hsubPaths_eq e).symm ▸ hf⟩
        · rintro ⟨b, ⟨e, rfl⟩, hf⟩
          exact ⟨e, (hsubPaths_eq e) ▸ hf⟩ }
  exact ⟨W, hNG, rfl⟩

/-! ## The walls of (7.1) and (7.2) (page 89) -/

/-- **A wall of height `h` in every graph of large branch-width.** For every even `h ≥ 2` there is
a number `ω ≥ 2` such that every finite graph with branch-width `≥ ω` has a subgraph which is a
wall of height `h`.

This is not (7.1). Graph Minors XIII, page 89, states (7.1) as follows: "*For $h \ge 2$, even,
if every graph with branch-width $\ge \omega/3$ has a minor isomorphic to the elementary wall of
height $h$, then there is an algorithm as in (7.2), with running time $O(v^2 + \varepsilon)$.*"
That is a statement about an algorithm. The theorem here is the graph fact behind it. The
elementary wall is planar (`isPlanar_elementaryWall`), so (4.2) gives the number `ω`: "*For
every planar graph $H$ there is a number $\omega$ such that every graph with branch-width $\ge
\omega$ has a minor isomorphic to $H$.*" Then the remark just before (7.1) turns the minor into a
subgraph: "Now since every vertex of an elementary wall $H$ of height $h$ has valency $\le 3$, if
a graph has a minor isomorphic to $H$ then it has a wall of height $h$ as a subgraph"
(`exists_wall_of_isIsoMinor_elementaryWall`). -/
theorem exists_wall_of_large_branchWidth (h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    ∃ ω : ℕ, 2 ≤ ω ∧ ∀ (G : Graph α β), V(G).Finite → E(G).Finite →
      ¬ GraphBranchWidthLE G (ω - 1) →
      ∃ W : Wall α β, IsWallIn G W ∧ W.height = h := by
  have hPlanar : IsPlanar (elementaryWall h) := isPlanar_elementaryWall h
  obtain ⟨ω, hω2, h42⟩ := theorem_4_2_proof (α := α) (β := β) (elementaryWall h) hPlanar
  refine ⟨ω, hω2, fun G hVG hEG hnot_bw => ?_⟩
  have hminor : IsIsoMinor (elementaryWall h) G := h42 G hVG hEG hnot_bw
  exact exists_wall_of_isIsoMinor_elementaryWall hVG hEG h2 heven hminor

/-- **What the output of Algorithm (7.2) satisfies.** For every even `h ≥ 2` there is a number
`ω₁ ≥ 2` such that, with `ω = 3ω₁ + 1`, every finite graph `G` has a wall of height `h` as a
subgraph or has branch-width `≤ ω - 1`. Moreover, if `G` has at least two edges, Algorithm (3.3)
gives a subgraph `G'` of `G` and a branch-decomposition of `G'` of width `< ω`, such that `G' = G`
and `G` has branch-width `≤ ω - 1`, or `G'` has a wall of height `h` as a subgraph.

This is not (7.2), which is an algorithm. Graph Minors XIII, page 89, gives its output as
"Either a branch-decomposition of $G$ of width $\le \omega$, or a wall of height $h$ which is a
subgraph of $G$." The theorem here says that such an output exists, and it follows the
description of (7.2): "We apply (3.3) to $G$ and obtain a subgraph $G'$ of $G$ and a
branch-decomposition of $G'$ of width $\le \omega$, such that either $G' = G$ or $G'$ has
branch-width $\ge \omega/3$." It says nothing about the running time. The number `ω₁` comes from
`exists_wall_of_large_branchWidth`, and the decomposition from `algorithm_3_3_correct`. -/
theorem exists_wall_or_branchDecomposition (h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    ∃ ω₁ : ℕ, 2 ≤ ω₁ ∧
      let ω := 3 * ω₁ + 1
      (∀ G : Graph α β, V(G).Finite → E(G).Finite →
        (∃ W : Wall α β, IsWallIn G W ∧ W.height = h) ∨ GraphBranchWidthLE G (ω - 1)) ∧
      (∀ G : Graph α β, V(G).Finite → E(G).Finite → 2 ≤ E(G).ncard →
        ∃ (G' : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
          G' ≤ G ∧
          2 ≤ E(G').ncard ∧
          IsGraphBranchDecomposition G' T τ ∧
          graphBranchDecompWidth G' T τ < ω ∧
          ((G' = G ∧ GraphBranchWidthLE G (ω - 1)) ∨
            ∃ W : Wall α β, IsWallIn G' W ∧ IsWallIn G W ∧ W.height = h)) := by
  obtain ⟨ω₁, hω₁2, h71⟩ := exists_wall_of_large_branchWidth (α := α) (β := β) h h2 heven
  refine ⟨ω₁, hω₁2, ?_, ?_⟩
  · intro G hVG hEG
    by_cases hbw : GraphBranchWidthLE G (3 * ω₁)
    · exact Or.inr hbw
    · left
      have hnot_ω₁ : ¬ GraphBranchWidthLE G (ω₁ - 1) := by
        intro hle
        apply hbw
        rcases hle with hle1 | ⟨ι, hfin, T, τ, hbd, hw⟩
        · exact Or.inl hle1
        · exact Or.inr ⟨ι, hfin, T, τ, hbd, hw.trans (by omega)⟩
      exact h71 G hVG hEG hnot_ω₁
  · intro G hVG hEG hE2
    obtain ⟨G', ι, hfin, T, τ, hG'_le, hE2_G', hbd, hw, _, hcase⟩ :=
      algorithm_3_3_correct G hVG hEG hE2 ω₁ hω₁2
    refine ⟨G', ι, hfin, T, τ, hG'_le, hE2_G', hbd, by omega, ?_⟩
    rcases hcase with rfl | hnot_bw
    · exact Or.inl ⟨rfl, Or.inr ⟨ι, hfin, T, τ, hbd, hw⟩⟩
    · right
      have hVG' : V(G').Finite := hVG.subset hG'_le.vertexSet_mono
      have hEG' : E(G').Finite := hEG.subset hG'_le.edgeSet_mono
      obtain ⟨W, hWG', hWh⟩ := h71 G' hVG' hEG' hnot_bw
      exact ⟨W, hWG', hWG'.trans hG'_le, hWh⟩

end GraphMinor.GM13
