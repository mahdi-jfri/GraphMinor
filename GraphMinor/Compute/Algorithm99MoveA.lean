module

public import GraphMinor.Compute.Algorithm99TransportMove
public import GraphMinor.Compute.Algorithm99Step4
public import GraphMinor.GM13.Section9

/-!
# Moving output (a) of steps (5) to (7) of (9.9) to the labels of `G`

Steps (5) to (7) of Algorithm (9.9) (Graph Minors XIII, page 104) work in the renumbered graph
`G'` on `Fin v` and write their output (a) as a Case (iii) block of `G' \ X`
(`IsCase3StepsOutputA`). Output (iii) of (9.9) must be a block of `G \ X_G`, where `G` is the
input graph on `Fin n`, `orig : Fin v → Fin n` is the injective map from the labels of `G'` to
those of `G`, and `X_G = orig(X)`. So we rename the block along `orig`.

This file is the pure part of that renaming. A vertex word `x` becomes `origVertexEmb orig x`
(that is `orig x` for `x < v`) and an edge triple `(a, b, k)` becomes
`(orig a, orig b, k)` (`origEdgeEmb`). The wall is moved by `WallOfHeight.moveOrig`, and the
lengths and the trees of the member records are kept (`Case3MemberRecord.rename`).

* `ParsedCase3Block.moveOrig`: when the edges of `G'` from `u` to `w` are none or all of those
  of `G` from `orig u` to `orig w`, the renamed data is again a parsed block, now for `G \ X_G`.
  The reason is that renaming along `orig` sends `delGraph G' X` into `delGraph G X_G`
  (`relabelGraph_delGraph_le`), so every check of the parser still passes.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport

namespace Case3MemberRecord

/-- The record `r` with its vertices renamed by `f` and its edges by `g`; the tree is kept. -/
def rename (f : ℕ → ℕ) (g : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ) (r : Case3MemberRecord) :
    Case3MemberRecord :=
  ⟨r.vList.map f, r.eList.map g, r.t_len, r.parList, r.tauList⟩

end Case3MemberRecord

/-- Deleting the same vertices from a smaller graph gives a smaller graph. -/
theorem deleteVertices_le_deleteVertices {α β : Type*} {H K : Graph α β} (h : H ≤ K)
    (S : Set α) : GM09.deleteVertices H S ≤ GM09.deleteVertices K S where
  vertexSet_mono := fun _ hx => ⟨h.vertexSet_mono hx.1, hx.2⟩
  isLink_mono := by
    intro e x y hl
    rw [deleteVertices_isLink] at hl ⊢
    exact ⟨hl.1.mono h, hl.2⟩

/-- A list of distinct edges of `G` has at most `|E(G)|` entries. -/
theorem length_le_numEdges_of_nodup_mem {n : ℕ} (G : MultiDigraph n)
    {eList : List (ℕ × ℕ × ℕ)} (hnd : eList.Nodup)
    (he : ∀ e ∈ eList, e ∈ G.toGMDigraph.edgeSet) : eList.length ≤ G.numEdges := by
  have hsub : (eList.toFinset : Set (ℕ × ℕ × ℕ)) ⊆ G.toGMDigraph.edgeSet :=
    fun e he_mem => he e (List.mem_toFinset.mp he_mem)
  have hle := Set.ncard_le_ncard hsub G.isFinite_toGMDigraph.finite_E
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, G.ncard_edgeSet_toGMDigraph] at hle
  exact hle

variable {v n : ℕ} {G' : MultiDigraph v} {G : MultiDigraph n} {X : Finset (Fin v)}
  {orig : Fin v → Fin n} {Y : Finset (Fin n)}

set_option hygiene false in
/-- The renaming of vertex words along `orig`. -/
local notation "𝔣" => origVertexEmb orig hinj
set_option hygiene false in
/-- The renaming of edge triples along `orig`. -/
local notation "𝔤" => origEdgeEmb orig hinj

/-- The labels of `G'` are at most as many as those of `G`, since `orig` is injective. -/
theorem le_of_injective_orig (hinj : Injective orig) : v ≤ n := by
  simpa using Fintype.card_le_of_injective orig hinj

theorem mem_image_orig_iff (hinj : Injective orig) {u : Fin v} : orig u ∈ X.image orig ↔ u ∈ X := by
  rw [Finset.mem_image]
  exact ⟨fun ⟨x, hx, hxu⟩ => hinj hxu ▸ hx, fun hu => ⟨u, hu, rfl⟩⟩

/-- Deleting `X` from `G'` and `orig(X)` from `G` keeps the hypothesis on the multiplicities. -/
theorem edgeMult_deleteVertices_orig (_hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X) (u w : Fin v) :
    (G'.deleteVertices X).edgeMult u w = 0 ∨
      (G'.deleteVertices X).edgeMult u w =
        (G.deleteVertices Y).edgeMult (orig u) (orig w) := by
  simp only [MultiDigraph.deleteVertices_edgeMult, hY]
  by_cases h1 : u ∉ X ∧ w ∉ X
  · simp only [h1, not_false_eq_true, and_self, ↓reduceIte]
    exact hmult u w
  · simp only [h1, ↓reduceIte, true_or]

/-- Renaming along `orig` keeps adjacency from `G' \ X` to `G \ orig(X)`. -/
theorem adj_deleteVertices_orig (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X)
    (u w : Fin v) (hadj : (G'.deleteVertices X).toSimpleGraph.Adj u w) :
    (G.deleteVertices Y).toSimpleGraph.Adj (orig u) (orig w) := by
  rw [MultiDigraph.toSimpleGraph_adj] at hadj ⊢
  refine ⟨fun h => hadj.1 (hinj h), ?_⟩
  rcases hadj.2 with h | h
  · rcases edgeMult_deleteVertices_orig hinj hmult hY u w with h0 | heq
    · exact absurd (h0 ▸ h) (lt_irrefl 0)
    · exact Or.inl (heq ▸ h)
  · rcases edgeMult_deleteVertices_orig hinj hmult hY w u with h0 | heq
    · exact absurd (h0 ▸ h) (lt_irrefl 0)
    · exact Or.inr (heq ▸ h)

/-- Renaming `delGraph G' X` along `orig` gives a subgraph of `delGraph G Y`, for every `Y`
that meets the image of `orig` in `orig(X)`. -/
theorem relabelGraph_delGraph_le (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X) :
    relabelGraph 𝔣 𝔤 (delGraph G' X) ≤ delGraph G Y := by
  have h0 : relabelGraph 𝔣 𝔤 (delGraph G' X) ≤ G.toGMDigraph.toGraph := by
    rw [delGraph_eq_deleteVertices, relabelGraph_deleteVertices]
    exact (deleteVertices_le _ _).trans (relabelGraph_toGMGraph_le hinj hmult)
  rw [delGraph_eq_deleteVertices (G := G)]
  refine le_deleteVertices h0 ?_
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ hxY
  obtain ⟨hxv, hxX⟩ := (mem_vertexSet_delGraph_iff G' X x).mp hx
  rw [origVertexEmb_apply_val orig hinj ⟨x, hxv⟩] at hxY
  exact hxX ((hY _).mp ((mem_toNatSet_iff Y _).mp hxY))

/-- `G' \ X` has at most as many edges as `G \ orig(X)`. -/
theorem numEdges_deleteVertices_le_orig (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X) :
    (G'.deleteVertices X).numEdges ≤ (G.deleteVertices Y).numEdges := by
  rw [← MultiDigraph.ncard_edgeSet_toGMDigraph, ← MultiDigraph.ncard_edgeSet_toGMDigraph,
    ← edgeSet_delGraph, ← edgeSet_delGraph, ← ncard_edgeSet_relabelGraph 𝔣 𝔤]
  refine Set.ncard_le_ncard (relabelGraph_delGraph_le hinj hmult hY).edgeSet_mono ?_
  rw [edgeSet_delGraph]
  exact (MultiDigraph.isFinite_toGMDigraph _).finite_E

/-! ### The renamed block is a parsed block of `G \ orig(X)` -/

/-- A valid member record stays valid after renaming. -/
theorem isValidMemberRecord_rename (hinj : Injective orig) {m m' : ℕ} (hm : m ≤ m')
    {KV : List ℕ} {KE : List (ℕ × ℕ × ℕ)} {r : Case3MemberRecord}
    (h : isValidMemberRecord v m KV KE r = true) :
    isValidMemberRecord n m' (KV.map 𝔣) (KE.map 𝔤) (r.rename 𝔣 𝔤) = true := by
  simp only [isValidMemberRecord, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  dsimp only [Case3MemberRecord.rename]
  simp only [List.length_map]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1.trans (le_of_injective_orig hinj), h2.map (𝔣).injective⟩, ?_⟩,
    h4.trans hm⟩, h5.map (𝔤).injective⟩, ?_⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact List.mem_map_of_mem (h3 y hy)
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨hK, ha, hb⟩ := h6 e₀ he₀
    rw [origEdgeEmb_apply]
    exact ⟨List.mem_map_of_mem hK, List.mem_map_of_mem ha, List.mem_map_of_mem hb⟩

/-- Renaming keeps the member records distinct. -/
theorem nodup_rename_members (hinj : Injective orig) {rs : List Case3MemberRecord}
    (h : (rs.map (fun r => (r.vList.toFinset, r.eList.toFinset))).Nodup) :
    ((rs.map (Case3MemberRecord.rename 𝔣 𝔤)).map
      (fun r => (r.vList.toFinset, r.eList.toFinset))).Nodup := by
  have hφ : Injective (Prod.map (Finset.image 𝔣) (Finset.image 𝔤)) :=
    Prod.map_injective.2 ⟨Finset.image_injective (𝔣).injective,
      Finset.image_injective (𝔤).injective⟩
  have heq : (rs.map (Case3MemberRecord.rename 𝔣 𝔤)).map
      (fun r => (r.vList.toFinset, r.eList.toFinset)) =
      (rs.map (fun r => (r.vList.toFinset, r.eList.toFinset))).map
        (Prod.map (Finset.image 𝔣) (Finset.image 𝔤)) := by
    simp only [List.map_map]
    refine List.map_congr_left fun r _ => ?_
    simp only [Case3MemberRecord.rename, Function.comp_apply, Prod.map_apply, Prod.mk.injEq]
    constructor <;> ext x <;> simp
  rw [heq]
  exact h.map hφ

/-- The wall section moved along `orig`. -/
def ParsedWallSection.moveOrig (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X) (pw : ParsedWallSection (G'.deleteVertices X) X) :
    ParsedWallSection (G.deleteVertices Y) Y where
  h := pw.h
  h2 := pw.h2
  he := pw.he
  W := pw.W.moveOrig _ orig
  hW := pw.hW.moveOrig orig hinj (adj_deleteVertices_orig hinj hmult hY)
  branch_not_mem u := by
    rw [WallOfHeight.moveOrig_branchVert, hY]
    exact pw.branch_not_mem u
  internal_not_mem k x hx := by
    change x ∈ (pw.W.internalVerts k).map orig at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hY]
    exact pw.internal_not_mem k y hy

/-- **The renamed block.** The parsed block `p` of `G' \ X` with its wall moved along `orig`
and its vertex words and edge triples renamed is a parsed block of `G \ orig(X)`. -/
def ParsedCase3Block.moveOrig (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X) (p : ParsedCase3Block (G'.deleteVertices X) X) :
    ParsedCase3Block (G.deleteVertices Y) Y where
  wallSec := p.wallSec.moveOrig hinj hmult hY
  K_vList := p.K_vList.map 𝔣
  K_eList := p.K_eList.map 𝔤
  corners := p.corners.map 𝔣
  members := p.members.map (Case3MemberRecord.rename 𝔣 𝔤)
  hK_v_len := by
    rw [List.length_map]
    exact p.hK_v_len.trans (le_of_injective_orig hinj)
  hK_v_nodup := p.hK_v_nodup.map (𝔣).injective
  hK_v_valid := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [isDelGraphVert_eq_true_iff (G := G)]
    exact (relabelGraph_delGraph_le hinj hmult hY).vertexSet_mono
      ⟨y, p.K_vList_mem_delGraph hy, rfl⟩
  hK_e_len := by
    rw [List.length_map]
    exact p.hK_e_len.trans (numEdges_deleteVertices_le_orig hinj hmult hY)
  hK_e_nodup := p.hK_e_nodup.map (𝔤).injective
  hK_e_valid := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp he
    obtain ⟨hE, ha, hb⟩ := p.K_eList_mem_delGraph he₀
    refine ⟨isDelGraphEdge_eq_true_iff.mpr
      ((relabelGraph_delGraph_le hinj hmult hY).edgeSet_mono ⟨e₀, hE, rfl⟩), ?_, ?_⟩ <;>
      rw [origEdgeEmb_apply]
    · exact List.mem_map_of_mem ha
    · exact List.mem_map_of_mem hb
  hcorners_eq := by
    rw [p.hcorners_eq, List.map_ofFn]
    congr 1
    funext i
    exact origVertexEmb_apply_val orig hinj _
  hcorners_mem := by
    intro c hc
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
    exact List.mem_map_of_mem (p.hcorners_mem c₀ hc₀)
  hmembers_len := by
    rw [List.length_map]
    have := le_of_injective_orig hinj
    have := numEdges_deleteVertices_le_orig (X := X) hinj hmult hY
    have := p.hmembers_len
    omega
  hmembers_edge_sum := by
    simp only [List.map_map, Function.comp_def, Case3MemberRecord.rename, List.length_map]
    exact p.hmembers_edge_sum.trans (numEdges_deleteVertices_le_orig hinj hmult hY)
  hmembers_valid := by
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
    exact isValidMemberRecord_rename hinj (numEdges_deleteVertices_le_orig hinj hmult hY)
      (p.hmembers_valid r₀ hr₀)
  hmembers_distinct := nodup_rename_members hinj p.hmembers_distinct

/-! ### What the decoder reads from the renamed block -/

/-- For an injective map, the position of `g a` in the mapped list is the position of `a`. -/
theorem idxOf_map_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β] {g : α → β}
    (hg : Injective g) (l : List α) (a : α) : (l.map g).idxOf (g a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [List.idxOf_cons, hg.eq_iff, ih]

/-- The renamed record has the same tree, and its leaf map sends `g e` where the old one sends
`e`. -/
theorem toBranchDecomp_rename_tau (hinj : Injective orig) (r : Case3MemberRecord)
    (e : ℕ × ℕ × ℕ) :
    (r.rename 𝔣 𝔤).toBranchDecomp.2.2 (𝔤 e) = r.toBranchDecomp.2.2 e := by
  simp only [Case3MemberRecord.toBranchDecomp, Case3MemberRecord.rename]
  rw [idxOf_map_of_injective (𝔤).injective]

/-- Two societies with the same graph and the same cyclic order are equal. -/
theorem society_ext {α β : Type*} {S T : Society α β} (hG : S.G = T.G) (hΩ : S.Ω = T.Ω) :
    S = T := by
  cases S
  cases T
  cases hG
  cases hΩ
  rfl

/-- Renaming the lists of `subgraphOfLists` renames the subgraph, when the lists name vertices
and edges of `delGraph G' X`. -/
theorem subgraphOfLists_map (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    (hY : ∀ u, orig u ∈ Y ↔ u ∈ X)
    {L : List ℕ} {E : List (ℕ × ℕ × ℕ)} (hv : ∀ x ∈ L, x ∈ V(delGraph G' X))
    (he : ∀ e ∈ E, e ∈ E(delGraph G' X) ∧ e.1 ∈ L ∧ e.2.1 ∈ L) :
    subgraphOfLists (delGraph G Y) (L.map 𝔣) (E.map 𝔤) =
      relabelGraph 𝔣 𝔤 (subgraphOfLists (delGraph G' X) L E) := by
  have hle := relabelGraph_delGraph_le (X := X) hinj hmult hY
  refine subgraphOfLists_eq_of_vertexSet_edgeSet
    ((relabelGraph_mono _ _ (subgraphOfLists_le _ _ _)).trans hle) ?_ ?_
  · rw [vertexSet_relabelGraph, vertexSet_subgraphOfLists_eq_of_subset hv]
    ext x
    simp
  · rw [edgeSet_relabelGraph, edgeSet_subgraphOfLists_eq_of_valid hv he]
    ext e
    simp

variable (hinj : Injective orig)
  (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
  (hY : ∀ u, orig u ∈ Y ↔ u ∈ X) (p : ParsedCase3Block (G'.deleteVertices X) X)

/-- The decoded wall of the renamed block is the moved wall. -/
theorem ParsedCase3Block.toGMWall_moveOrig :
    (p.moveOrig hinj hmult hY).toGMWall =
      (p.wallSec.W.moveOrig (G.deleteVertices Y) orig).toGMWall p.wallSec.h2
        p.wallSec.he (p.wallSec.hW.moveOrig orig hinj (adj_deleteVertices_orig hinj hmult hY)) :=
  rfl

/-- The compass graph of the renamed block is the renamed compass graph. -/
theorem ParsedCase3Block.toCompassGraph_moveOrig :
    (p.moveOrig hinj hmult hY).toCompassGraph = relabelGraph 𝔣 𝔤 p.toCompassGraph :=
  subgraphOfLists_map hinj hmult hY (fun _ hx => p.K_vList_mem_delGraph hx)
    (fun _ he => p.K_eList_mem_delGraph he)

include hmult hY in
/-- The decoded member of a renamed record is the renamed member. -/
theorem ParsedCase3Block.toSubgraph_rename {r : Case3MemberRecord} (hr : r ∈ p.members) :
    (r.rename 𝔣 𝔤).toSubgraph (delGraph G Y) =
      relabelGraph 𝔣 𝔤 (r.toSubgraph (delGraph G' X)) := by
  have h := p.member_valid_iff hr
  refine subgraphOfLists_map hinj hmult hY (fun x hx => p.K_vList_mem_delGraph (h.2.2.1 x hx)) ?_
  intro e he
  obtain ⟨heK, he1, he2⟩ := h.2.2.2.2.2.1 e he
  exact ⟨(p.K_eList_mem_delGraph heK).1, he1, he2⟩

/-- The decoded division of the renamed block is the renamed division. -/
theorem ParsedCase3Block.toDivision_moveOrig :
    (p.moveOrig hinj hmult hY).toDivision = relabelGraph 𝔣 𝔤 '' p.toDivision := by
  ext A'
  constructor
  · rintro ⟨r', hr', rfl⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    exact ⟨_, ⟨r, hr, rfl⟩, (p.toSubgraph_rename hinj hmult hY hr).symm⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨r.rename 𝔣 𝔤, List.mem_map_of_mem hr, p.toSubgraph_rename hinj hmult hY hr⟩

/-- Flatness of the moved wall in `G \ orig(X)`, from flatness in `G' \ X` and `hcomp`. -/
theorem ParsedCase3Block.isFlatWallIn_moveOrig
    (hcomp : wallCompass (delGraph G Y) (relabelWall 𝔣 𝔤 p.toGMWall) =
      relabelGraph 𝔣 𝔤 (wallCompass (delGraph G' X) p.toGMWall))
    (hflat : IsFlatWallIn (delGraph G' X) p.toGMWall) :
    IsFlatWallIn (delGraph G Y) (p.moveOrig hinj hmult hY).toGMWall := by
  have hadj := adj_deleteVertices_orig (X := X) hinj hmult hY
  have hle := relabelGraph_delGraph_le (X := X) hinj hmult hY
  have hW' : ((p.wallSec.W.moveOrig (G.deleteVertices Y) orig).toGMWall
      p.wallSec.h2 p.wallSec.he (p.wallSec.hW.moveOrig orig hinj hadj)).graph ≤
      delGraph G Y :=
    (p.wallSec.moveOrig hinj hmult hY).toGMWall_le_delGraph
  have hr : IsFlatWallIn (delGraph G Y) (relabelWall 𝔣 𝔤 p.toGMWall) := by
    refine ⟨?_, ?_⟩
    · rw [relabelWall_graph]
      exact (relabelGraph_mono _ _ hflat.1).trans hle
    · rw [hcomp, ← wallCompass_relabelGraph]
      exact ((isFlatWallIn_relabelGraph_iff 𝔣 𝔤 _).2 hflat).2
  exact isFlatWallIn_toGMWall_moveOrig p.wallSec.h2 p.wallSec.he p.wallSec.hW hinj hadj hW' hr

/-- The renamed block as a list of words: the code of `p.moveOrig`. The words do not depend on
the set `Y` (`movedBlock_eq`), so we use `Y = orig(X)` here. -/
def ParsedCase3Block.movedBlock : List ℕ :=
  encCase3Block (p.moveOrig hinj hmult (fun _ => mem_image_orig_iff hinj)).wallSec.W
    (p.moveOrig hinj hmult (fun _ => mem_image_orig_iff hinj)).K_vList
    (p.moveOrig hinj hmult (fun _ => mem_image_orig_iff hinj)).K_eList
    (p.moveOrig hinj hmult (fun _ => mem_image_orig_iff hinj)).corners
    (p.moveOrig hinj hmult (fun _ => mem_image_orig_iff hinj)).members

/-- The code of `p.moveOrig` for any `Y` is `p.movedBlock`. -/
theorem ParsedCase3Block.movedBlock_eq :
    encCase3Block (p.moveOrig hinj hmult hY).wallSec.W (p.moveOrig hinj hmult hY).K_vList
      (p.moveOrig hinj hmult hY).K_eList (p.moveOrig hinj hmult hY).corners
      (p.moveOrig hinj hmult hY).members = p.movedBlock hinj hmult :=
  rfl

/-- What `case3Decoder` reads from a block that parses to `p`. -/
theorem case3Decoder_of_parse {m : ℕ} {D : MultiDigraph m} {Y : Finset (Fin m)} {blk : List ℕ}
    {q : ParsedCase3Block (D.deleteVertices Y) Y}
    (hparse : parseCase3Block (D.deleteVertices Y) Y blk = some q) :
    case3Decoder.wall m D Y blk = q.toGMWall ∧ case3Decoder.society m D Y blk = q.toSociety ∧
      case3Decoder.division m D Y blk = q.toDivision := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [case3Decoder, case3WallOfDel, case3SocietyOfDel, case3DivisionOfDel, hparse]

include hY in
/-- **Output (a) in the labels of `G`.** Let `p` be what the parser reads from a block `blk` of
`G' \ X`, and suppose the decoded wall, society, division and decompositions have the
properties of output (a) (`IsCase3StepsOutputA`). Suppose also that the compass of the renamed
wall in `G \ Y` is the renamed compass (`hcomp`; this is where the closedness of `G'` in
`G` is used, see `wallCompass_relabel_eq`), where `Y` meets the image of `orig` in `orig(X)`.
Then the renamed block `p.movedBlock` has the same properties for `G` and `Y`: for `Y = orig(X)`
these are the conditions of output (iii) of (9.9). -/
theorem isCase3Output_movedBlock {blk : List ℕ}
    (hparse : parseCase3Block (G'.deleteVertices X) X blk = some p)
    (hcomp : wallCompass (delGraph G Y) (relabelWall 𝔣 𝔤 p.toGMWall) =
      relabelGraph 𝔣 𝔤 (wallCompass (delGraph G' X) p.toGMWall))
    {h ω : ℕ} (hH : (case3Decoder.wall v G' X blk).height = h)
    (hflat : IsFlatWallIn (GM09.deleteVertices G'.toGMDigraph.toGraph X.toNatSet)
      (case3Decoder.wall v G' X blk))
    (hsoc : IsWallSociety (GM09.deleteVertices G'.toGMDigraph.toGraph X.toNatSet)
      (case3Decoder.wall v G' X blk) (case3Decoder.society v G' X blk))
    (hrd : IsRuralDivision (case3Decoder.society v G' X blk) (case3Decoder.division v G' X blk))
    (hbd : ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      IsInteriorMember (case3Decoder.wall v G' X blk) (case3Decoder.division v G' X blk) A →
        let bd := case3Decoder.branchDecomp v G' X blk A
        E(A).ncard ≤ 1 ∨
          (IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) :
    let blk' := p.movedBlock hinj hmult
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
  intro blk'
  set p' := p.moveOrig hinj hmult hY with hp'
  have hparse' : parseCase3Block (G.deleteVertices Y) Y blk' = some p' := by
    rw [show blk' = _ from (p.movedBlock_eq hinj hmult hY).symm]
    exact parseCase3Block_encCase3Block p'
  obtain ⟨hw, hs, hd⟩ := case3Decoder_of_parse hparse
  obtain ⟨hw', hs', hd'⟩ := case3Decoder_of_parse hparse'
  rw [hw] at hH hflat hsoc hbd
  rw [hs] at hsoc hrd
  rw [hd] at hrd hbd
  rw [← delGraph_eq_deleteVertices] at hflat hsoc
  simp only
  rw [hw', hs', hd', ← delGraph_eq_deleteVertices]
  have hadj := adj_deleteVertices_orig (X := X) hinj hmult hY
  have hle := relabelGraph_delGraph_le (X := X) hinj hmult hY
  have hcorner := toGMWall_moveOrig_corner p.wallSec.h2 p.wallSec.he p.wallSec.hW hinj hadj
  have hC := wallCompass_toGMWall_moveOrig p.wallSec.h2 p.wallSec.he p.wallSec.hW hinj hadj
    (delGraph G Y)
  have hS' : p'.toSociety = relabelSociety 𝔣 𝔤 p.toSociety := by
    refine society_ext (p.toCompassGraph_moveOrig hinj hmult hY) ?_
    change wallCornerCyclicPerm p'.toGMWall =
      relabelCyclicPerm 𝔣 (wallCornerCyclicPerm p.toGMWall)
    rw [p.toGMWall_moveOrig hinj hmult, wallCornerCyclicPerm_congr hcorner,
      wallCornerCyclicPerm_relabelWall]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the height
    rw [p.toGMWall_moveOrig hinj hmult, WallOfHeight.toGMWall_height]
    rw [ParsedCase3Block.toGMWall, WallOfHeight.toGMWall_height] at hH
    exact hH
  · -- flatness
    exact p.isFlatWallIn_moveOrig hinj hmult hY hcomp hflat
  · -- the society
    refine ⟨?_, rfl⟩
    rw [hS', relabelSociety_G, hsoc.1, p.toGMWall_moveOrig hinj hmult, hC]
    exact hcomp.symm
  · -- the rural division
    rw [hS', p.toDivision_moveOrig hinj hmult]
    exact IsRuralDivision.relabel 𝔣 𝔤 hrd
  · -- the decompositions of the interior members
    intro A' hA'
    obtain ⟨r', hr', rfl⟩ := hA'.1
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    have hA := hA'
    rw [p.toGMWall_moveOrig hinj hmult,
      isInteriorMember_toGMWall_moveOrig_iff p.wallSec.h2 p.wallSec.he p.wallSec.hW hinj hadj,
      p.toDivision_moveOrig hinj hmult] at hA
    change IsInteriorMember _ _ ((r.rename 𝔣 𝔤).toSubgraph (delGraph G Y)) at hA
    rw [p.toSubgraph_rename hinj hmult hY hr] at hA
    have hint := (isInteriorMember_relabelWall_iff 𝔣 𝔤).1 hA
    have hb := hbd hint
    simp only at hb ⊢
    rw [p.branchDecomp_toSubgraph hparse hr] at hb
    rw [show ((G.deleteVertices Y).toGMDigraph.deleteVertices Y.toNatSet).toGraph =
      delGraph G Y from rfl]
    rw [p'.branchDecomp_toSubgraph hparse' hr']
    have hτ := toBranchDecomp_rename_tau hinj r
    rw [p.toSubgraph_rename hinj hmult hY hr, ncard_edgeSet_relabelGraph,
      isGraphBranchDecomposition_relabelGraph_iff 𝔣 𝔤 hτ,
      graphBranchDecompWidth_relabelGraph 𝔣 𝔤 hτ]
    exact hb

/-! ### The compass in `G \ orig(X)` is the renamed compass -/

/-- Disjoint sets of `Fin m` give disjoint sets of words. -/
theorem disjoint_toNatSet {m : ℕ} {A B : Finset (Fin m)} (h : Disjoint A B) :
    Disjoint A.toNatSet B.toNatSet := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ hb
  exact Finset.disjoint_left.mp h ha ((mem_toNatSet_iff B a).mp hb)

/-- **(9.5) for the renamed wall.** For a valid state of (9.9), let `H` be a wall of
`G_i \ X` whose compass there misses `Z_i`. Then the compass of the renamed wall in
`G \ orig(X)` is the renamed compass. This is `wallCompass_eq_of_closed_outside_Z`
(Graph Minors XIII, (9.9) (ii): "no vertex of $G_i \setminus Z_i$ is incident with an
edge of $G$ not in $G_i$") applied to the renamed `G_i`, which is a subgraph of `G`
closed outside the renamed `Z_i`
(`Alg99Iter.IsValid.relabelGraph_le`, `Alg99Iter.IsValid.relabelGraph_closed`). -/
theorem wallCompass_relabel_eq {h' s : ℕ} {st : Alg99Iter h' G} (hst : st.IsValid s)
    {X : Finset (Fin st.v)} {H : Wall ℕ (ℕ × ℕ × ℕ)} (hH : H.graph ≤ delGraph st.Gi X)
    (hZ : Disjoint V(wallCompass (delGraph st.Gi X) H) st.Z.toNatSet) :
    wallCompass (delGraph G (X.image st.orig))
        (relabelWall (origVertexEmb st.orig hst.orig_injective)
          (origEdgeEmb st.orig hst.orig_injective) H) =
      relabelGraph (origVertexEmb st.orig hst.orig_injective)
        (origEdgeEmb st.orig hst.orig_injective) (wallCompass (delGraph st.Gi X) H) := by
  set f := origVertexEmb st.orig hst.orig_injective
  set g := origEdgeEmb st.orig hst.orig_injective
  have hK : relabelGraph f g (delGraph st.Gi X) =
      GM09.deleteVertices (relabelGraph f g st.Gi.toGMDigraph.toGraph) (f '' X.toNatSet) := by
    rw [delGraph_eq_deleteVertices, relabelGraph_deleteVertices]
  have hKG : delGraph G (X.image st.orig) =
      GM09.deleteVertices G.toGMDigraph.toGraph (f '' X.toNatSet) := by
    rw [delGraph_eq_deleteVertices, toNatSet_image_orig hst.orig_injective]
  have hW : (relabelWall f g H).graph ≤
      GM09.deleteVertices (relabelGraph f g st.Gi.toGMDigraph.toGraph) (f '' X.toNatSet) := by
    rw [relabelWall_graph, ← hK]
    exact relabelGraph_mono f g hH
  have hdisj : Disjoint V(wallCompass (GM09.deleteVertices
      (relabelGraph f g st.Gi.toGMDigraph.toGraph) (f '' X.toNatSet)) (relabelWall f g H))
      (f '' st.Z.toNatSet) := by
    rw [← hK, wallCompass_relabelGraph, vertexSet_relabelGraph]
    exact (Set.disjoint_image_iff f.injective).2 hZ
  have hclosed : ∀ x ∈ V(relabelGraph f g st.Gi.toGMDigraph.toGraph) \ f '' st.Z.toNatSet,
      ∀ e ∈ E(G.toGMDigraph.toGraph), G.toGMDigraph.toGraph.Inc e x →
        e ∈ E(relabelGraph f g st.Gi.toGMDigraph.toGraph) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxZ⟩ e he hinc
    have hxv : x < st.v := hx
    have hfx : f x = (st.orig ⟨x, hxv⟩).1 := origVertexEmb_apply_val st.orig _ ⟨x, hxv⟩
    have hu : (⟨x, hxv⟩ : Fin st.v) ∉ st.Z := fun hmem =>
      hxZ ⟨x, (mem_toNatSet_iff st.Z ⟨x, hxv⟩).mpr hmem, rfl⟩
    rw [hfx] at hinc
    exact hst.relabelGraph_closed ⟨x, hxv⟩ hu e he hinc
  rw [hKG, ← wallCompass_eq_of_closed_outside_Z hst.relabelGraph_le hclosed hW hdisj, ← hK,
    wallCompass_relabelGraph]

end GraphMinor.Compute
