module

public import GraphMinor.GM05.FullWebSpider
import GraphMinor.Minor.Basic
import Mathlib.Tactic.Ring

/-!
# Adding edge-disjoint spiders in a multigraph

Delete all old spider edges. The given web remains because a spider meets
each A path in only one vertex and avoids every B edge. Apply (4.4) in the
remaining graph, then restore the old spiders on the selected subweb.
-/

public section
namespace GraphMinor.GM05.Full
open Graph Set SimpleGraph GM01
variable {α β : Type*}

/-- Selecting paths from each family preserves an actual-edge web. -/
theorem IsWeb.subweb {G : Graph α β} {m n p q : ℕ}
    {A : Fin m → Path α β} {B : Fin n → Path α β} (h : IsWeb G A B)
    (embI : Fin p ↪ Fin m) (embJ : Fin q ↪ Fin n) :
    IsWeb G (fun i => A (embI i)) (fun j => B (embJ j)) :=
  ⟨fun i => h.isIn_left _, fun j => h.isIn_right _,
    fun _ _ hij => h.disjoint_left (embI.injective.ne hij),
    fun _ _ hij => h.disjoint_right (embJ.injective.ne hij),
    fun i j => h.meets _ _, fun i j => h.edge_disjoint _ _⟩

/-- A spider remains a spider of a selected subweb. -/
theorem IsSpider.subweb {G : Graph α β} {m n p q : ℕ}
    {A : Fin m → Path α β} {B : Fin n → Path α β} {C : Graph α β}
    (h : IsSpider G A B C) (embI : Fin p ↪ Fin m) (embJ : Fin q ↪ Fin n) :
    IsSpider G (fun i => A (embI i)) (fun j => B (embJ j)) C :=
  ⟨h.le, h.connected, fun j => h.edge_disjoint _, fun i => h.unique_leaf _⟩

/-- A spider cannot share an actual edge with an A path: both ends would
lie in their unique intersection, contradicting looplessness of the path. -/
theorem IsSpider.edge_disjoint_left {G : Graph α β} {m n : ℕ}
    {A : Fin m → Path α β} {B : Fin n → Path α β} {C : Graph α β}
    (hw : IsWeb G A B) (h : IsSpider G A B C) (i : Fin m) :
    Disjoint E(C) (A i).edgeSet := by
  rw [Set.disjoint_left]
  intro e heC heA
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heA
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet heC
  have hG := hxy.mono (hw.isIn_left i)
  have hG' := hab.mono h.le
  have hCx : x ∈ V(C) := by
    rcases hG.left_eq_or_eq hG' with rfl | rfl
    · exact hab.left_mem
    · exact hab.right_mem
  have hCy : y ∈ V(C) := by
    rcases hG.symm.left_eq_or_eq hG' with rfl | rfl
    · exact hab.left_mem
    · exact hab.right_mem
  obtain ⟨z, hz, _⟩ := h.unique_leaf i
  have hxz : x = z := Set.mem_singleton_iff.mp
    (hz ▸ (show x ∈ V(C) ∩ (A i).verts from ⟨hCx, (A i).vertexSet_eq ▸ hxy.left_mem⟩))
  have hyz : y = z := Set.mem_singleton_iff.mp
    (hz ▸ (show y ∈ V(C) ∩ (A i).verts from ⟨hCy, (A i).vertexSet_eq ▸ hxy.right_mem⟩))
  have hxx : (A i).toGraph.IsLink e x x := (hxz.trans hyz.symm).symm ▸ hxy
  exact (A i).no_loops e x hxx

/-- Graph Minors V, (4.5), page 99, with actual edge-disjoint spiders.
The same correction of the printed index `k < θ₁ θ` as in `GM05.theorem_4_5_simple` is used.
Delete the old spider edges, apply full (4.4), and restore the old spiders. -/
theorem theorem_4_5_proof {G : Graph α β} {θ k : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) (hk : k < θ₁ θ)
    (h : HasWebWithSpiders G (φ θ k) (ψ θ k) k) :
    HasWebWithSpiders G (φ θ (k + 1)) (ψ θ (k + 1)) (k + 1) := by
  obtain ⟨A, B, C, hw, hsp, hd⟩ := h
  let F : Set β := ⋃ i : Fin k, E(C i)
  let G' := G.deleteEdges F
  have hle : G' ≤ G := Graph.deleteEdges_le
  have hV' : V(G').Finite := hV.subset hle.vertexSet_mono
  have hE' : E(G').Finite := hE.subset hle.edgeSet_mono
  have hno' : ¬ IsIsoMinor (gridGraph θ) G' := by
    rintro ⟨K, hK, D, hD, hIso⟩
    exact hno ⟨K, hK.trans hle, D, hD, hIso⟩
  have hw' : IsWeb G' A B := by
    refine ⟨?_, ?_, hw.disjoint_left, hw.disjoint_right, hw.meets, hw.edge_disjoint⟩
    · intro i
      refine ⟨(hw.isIn_left i).vertexSet_mono, fun e x y he => ?_⟩
      refine ⟨he.mono (hw.isIn_left i), ?_⟩
      intro heF
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heF
      exact Set.disjoint_left.mp ((hsp j).edge_disjoint_left hw i) hj he.edge_mem
    · intro i
      refine ⟨(hw.isIn_right i).vertexSet_mono, fun e x y he => ?_⟩
      refine ⟨he.mono (hw.isIn_right i), ?_⟩
      intro heF
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heF
      exact Set.disjoint_left.mp ((hsp j).edge_disjoint i) hj he.edge_mem
  let p := φ θ (k + 1)
  let q := ψ θ (k + 1)
  have hp : 0 < p := φ_pos hθ (k + 1)
  have hm : φ θ k = p * 2 ^ (p * θ ^ 2) := φ_of_lt θ hk
  have hn : ψ θ k = p + q + p * 2 ^ (p * θ ^ 2) := by
    rw [ψ_of_lt θ hk, ← hm]
    ring
  let em : Fin (p * 2 ^ (p * θ ^ 2)) ≃ Fin (φ θ k) := (finCongr hm).symm
  let en : Fin (p + q + p * 2 ^ (p * θ ^ 2)) ≃ Fin (ψ θ k) := (finCongr hn).symm
  obtain ⟨embI₀, embJ₀, K, hK⟩ := theorem_4_4_proof hθ heven hV' hE' hno' hp
    (hw'.subweb em.toEmbedding en.toEmbedding)
  let embI := embI₀.trans em.toEmbedding
  let embJ := embJ₀.trans en.toEmbedding
  have hKfull : IsSpider G (fun i => A (embI i)) (fun j => B (embJ j)) K :=
    ⟨hK.le.trans hle, hK.connected, hK.edge_disjoint, hK.unique_leaf⟩
  have hnewdisj : ∀ i : Fin k, Disjoint E(C i) E(K) := by
    intro i
    rw [Set.disjoint_left]
    intro e heC heK
    have he : e ∈ E(G') := hK.le.edgeSet_mono heK
    exact he.2 (Set.mem_iUnion.mpr ⟨i, heC⟩)
  let C' : Fin (k + 1) → Graph α β := Fin.snoc C K
  refine ⟨fun i => A (embI i), fun j => B (embJ j), C', hw.subweb embI embJ, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simpa [C'] using hKfull
    | cast i => simpa [C'] using (hsp i).subweb embI embJ
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast j => simpa [C'] using (hnewdisj j).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [C'] using hnewdisj i
      | cast j =>
        have hne : i ≠ j := fun h => hij (congrArg Fin.castSucc h)
        simpa [C'] using hd hne

end GraphMinor.GM05.Full
