module

public import GraphMinor.GM01.CombSegmentModels
public import GraphMinor.GM01.CombSegmentsOutsideRegions
public import GraphMinor.GM01.CombPrefixRoot
public import GraphMinor.GM01.CombConcatenation
import GraphMinor.GM01.RootedPathAttachment

/-!
# The rooted comb model in an initial piece

Graph Minors I, (4.10), page 58, retains the old comb inside `B` with
its original ambient root. Select the initial spine cells and contract
their replacing paths. They avoid the later region, and so does the
separate root path. Attaching that path gives a rooted model wholly
in the initial piece and retains its last spine centre in the last
source branch, ready for the connecting path to `D`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The rooted initial piece retained for GM01 (4.10), page 58.
The last spine centre remains in its own branch after the ambient root
path is attached. -/
theorem exists_rooted_comb_prefix_model {α β : Type*} {γ L : ℕ}
    (hL : 0 < L) (G : RootedGraph α β) {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : ℕ) (hj : 0 < j) (hjL : 2 * j < L) :
    ∃ G₁ : RootedGraph α β, G₁.graph ≤ G.graph ∧
      V(G₁.graph) ⊆ combPrefix hL (subgraphUnion G.graph N R) c j ∧ G₁.root.val = G.root.val ∧
      ∃ M : RootedMinorModel (rootedPathComb γ (2 * j) (by omega)) G₁,
        c ⟨Sum.inl ⟨2 * j - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈
          M.branch (pathCombLastSpine γ (2 * j) (by omega)) := by
  let H := subgraphUnion G.graph N R
  have hm : 0 < 2 * j := by omega
  have hbound : 0 + 2 * j ≤ L := by omega
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hOnly : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hPaths e
    exact ⟨a, b, he, hP, hRange⟩
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hOnly e
    exact ⟨a, b, he, hRange⟩
  let A := rootedCombSegment hm N c P 0 hbound
  obtain ⟨hAN, _, MA, hMCentres⟩ := combSegment_model hm c hc hcentres P hOnly hInter 0 hbound
  have hAG : A.graph ≤ G.graph := hAN.trans hN
  have hRtoA : IsGraphPathWithEnds G.graph R G.root.val A.root.val := hR
  have hmeetA : V(A.graph) ∩ V(R) ⊆ {A.root.val} := by
    intro x hx
    exact hmeet ⟨hAN.vertexSet_mono hx.1, hx.2⟩
  let G₁ : RootedGraph α β :=
    ⟨subgraphUnion G.graph A.graph R, ⟨G.root.val, Or.inr hR.left_mem⟩⟩
  let M₁ : RootedMinorModel (rootedPathComb γ (2 * j) hm) G₁ :=
    MA.attachRootPath hAG G.root.val hRtoA hmeetA
  have hG₁ : G₁.graph ≤ G.graph := subgraphUnion_le hAG hR.le
  have hRPrefix := root_path_subset_combPrefix hL hN hc hcentres hPN hE hRanges
    (fun e f hne ↦ (hInter e f hne).1) G.root.val hR hmeet j hj hjL
  let cut : Fin L := ⟨2 * j - 1, by omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  have hDis := combSegmentSupport_disjoint_later_region hc P hPN hE hRanges
    (fun e f hne ↦ (hInter e f hne).1) 0 hbound cut (by dsimp [cut]; omega)
    (by dsimp [cut]; omega)
  have hRegion : combSpineRegion hL H c (2 * j) = vertexAvoidanceRegion N
      (c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩)
      (c ⟨Sum.inl cut, pathComb_spine_mem γ L cut⟩) := by
    simp only [combSpineRegion, show 2 * j ≠ 0 by omega, hjL, ↓reduceIte, ↓reduceDIte]
    exact comb_root_path_region_eq hN hR.le hc hPN hE hRanges (fun e f hne ↦ (hInter e f hne).1)
      cut last (by dsimp [cut, last]; omega) (hcentres _) hmeet
  have hPrefix : V(G₁.graph) ⊆ combPrefix hL H c j := by
    intro x hx
    rcases hx with hxA | hxR
    · refine ⟨Or.inl (hAN.vertexSet_mono hxA), ?_⟩
      rw [hRegion]
      exact fun h ↦ Set.disjoint_left.mp hDis hxA h
    · exact hRPrefix hxR
  let w := pathCombLastSpine γ (2 * j) hm
  have hCentreEq : combShiftEmbedding 0 hbound w =
      (⟨Sum.inl ⟨2 * j - 1, by omega⟩, pathComb_spine_mem γ L _⟩ : (pathComb γ L).verts) := by
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Fin.ext
    change 0 + (2 * j - 1) = 2 * j - 1
    omega
  have hOwn : c ⟨Sum.inl ⟨2 * j - 1, by omega⟩, pathComb_spine_mem γ L _⟩ ∈ MA.branch w :=
    hCentreEq ▸ hMCentres w
  refine ⟨G₁, hG₁, hPrefix, rfl, M₁, ?_⟩
  exact MA.branch_subset_attachRootPath hAG G.root.val hRtoA hmeetA w hOwn

end GraphMinor.GM01
