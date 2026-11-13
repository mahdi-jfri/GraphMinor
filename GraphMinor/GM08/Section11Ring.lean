module

public import GraphMinor.GM08.Section11Build
import GraphMinor.GM11.Walks
import GraphMinor.GM22.Section3Disc
import GraphMinor.GM07.Section3

/-!
# One step of the proof of Graph Minors VIII, (11.1), for a sleeve of a drawing

Let `Γ*` contain a sleeve for an O-arc `F`, and let `G` be the graph of `Γ*` induced on a set `W`
of vertices that contains the sleeve. The proof of (11.1) on page 273 contracts the sleeve onto
the `r × s` cylinder, keeping the vertices of `W` that are not inside `F`, and applies the
strengthened III (3.8) to the result. Here we do this (`exists_ring_decomposition`).

* `SleeveData.exists_sleeveDraw` writes the sleeve as sequences.
* `SleeveDraw.adj_step` shows that the radial paths meet all circuits in the same cyclic order.
* `SleeveSeq.exists_decomposition` contracts the sleeve onto the cylinder and applies the
  strengthened III (3.8).

The vertices of `W` not inside `F` meet the sleeve exactly in the ends of the radial paths, the
`r` vertices `V(Γ) ∩ F`: the circuits are inside `F`, and a radial path meets `F` only in its
end.
-/

public section

namespace GraphMinor
namespace GM08

open Set Graph GM03 GM06 GM09 Surface

universe u v w

variable {S : Type u} [TopologicalSpace S] {ι : Type w}

/-- A subgraph of `G` with vertices in `X` is a subgraph of the graph induced on `X`. -/
theorem le_induce_of_le {α : Type u} {β : Type v} {G H : Graph α β} {X : Set α} (hH : H ≤ G)
    (hX : V(H) ⊆ X) : H ≤ G.induce X :=
  ⟨hX, fun _ _ _ he => ⟨he.mono hH, hX he.left_mem, hX he.right_mem⟩⟩

/-- Inducing twice is inducing once on the smaller set. -/
theorem induce_induce_of_subset {α : Type u} {β : Type v} (G : Graph α β) {X Y : Set α}
    (h : Y ⊆ X) : (G.induce X).induce Y = G.induce Y := by
  refine Graph.ext rfl fun e x y => ?_
  simp only [induce_isLink]
  constructor
  · rintro ⟨⟨hl, -, -⟩, hx, hy⟩
    exact ⟨hl, hx, hy⟩
  · rintro ⟨hl, hx, hy⟩
    exact ⟨⟨hl, h hx, h hy⟩, hx, hy⟩

/-- A tree-decomposition of `G` restricts to a tree-decomposition of a subgraph `L`. -/
theorem IsTreeDecomposition.restrict {α : Type u} {β : Type v} {G L : Graph α β}
    {T : SimpleGraph ι} {Y : ι → Set α} (hTD : IsTreeDecomposition G T Y) (hL : L ≤ G) :
    IsTreeDecomposition L T (fun t => Y t ∩ V(L)) where
  isTree := hTD.isTree
  bag_subset _ := inter_subset_right
  iUnion_bags := by
    rw [← iUnion_inter, hTD.iUnion_bags]
    exact inter_eq_right.mpr hL.vertexSet_mono
  edge_in_bag e x y hl := by
    obtain ⟨t, hx, hy⟩ := hTD.edge_in_bag (hl.mono hL)
    exact ⟨t, ⟨hx, hl.left_mem⟩, ⟨hy, hl.right_mem⟩⟩
  inter_subset_on_path t t' t'' hp x hx :=
    ⟨hTD.inter_subset_on_path hp ⟨hx.1.1, hx.2.1⟩, hx.1.2⟩

/-- One step of the proof of Graph Minors VIII, (11.1) (page 273), for a sleeve of `F` contained
in a drawing `Γ*` in the disc `S`. Let `G` be the graph of `Γ*` induced on a set `W` that
contains the sleeve. Then a tree-decomposition of `G` gives one of the graph induced on the
vertices of `W` not inside `F`, of no larger width, with `Y_t ∩ V(H) ⊆ X_t` for every `t`, and
with `V(Γ) ∩ F` in one bag. -/
theorem exists_ring_decomposition (hS : IsClosedDisc (univ : Set S)) {Γ Dstar : Drawing S}
    {F : Set S} (sd : SleeveData Γ univ F)
    (hcirc : ∀ j, (sd.circuitDraw j).IsSubdrawing Dstar)
    (hspoke : ∀ i, (sd.spoke i).IsSubdrawing Dstar) {W : Set S} (hWD : W ⊆ Dstar.V)
    (hsW : ∀ x ∈ (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V), x ∈ W)
    [Fintype ι] {T : SimpleGraph ι} {Y : ι → Set S}
    (hTD : IsTreeDecomposition (Dstar.toGraph.induce W) T Y) :
    ∃ X : ι → Set S,
      IsTreeDecomposition (Dstar.toGraph.induce {x ∈ W | ¬ InsideOArc univ F x}) T X ∧
      (∀ w : ℕ, TreeDecompHasWidthLE Y w → TreeDecompHasWidthLE X w) ∧
      (∀ t, Y t ∩ {x ∈ W | ¬ InsideOArc univ F x} ⊆ X t) ∧ ∃ t₀, Γ.V ∩ F ⊆ X t₀ := by
  classical
  have : T2Space S := by
    obtain ⟨e⟩ := hS
    exact (GM07.isSurface_of_homeo (e.trans (Homeomorph.Set.univ S))
      GM22.isSurface_closedUnitDisc).2.1
  set r := (Γ.V ∩ F).ncard
  set W' : Set S := {x ∈ W | ¬ InsideOArc univ F x}
  have hW'W : W' ⊆ W := fun x hx => hx.1
  have hVG : V(Dstar.toGraph.induce W).Finite := (Dstar.finite_V).subset hWD
  rw [← induce_induce_of_subset Dstar.toGraph hW'W]
  by_cases hr : r = 0
  · -- No vertex on `F`: restrict the bags.
    have hBF : Γ.V ∩ F = ∅ :=
      (ncard_eq_zero (Γ.finite_V.subset inter_subset_left)).mp hr
    have hle : (Dstar.toGraph.induce W).induce W' ≤ Dstar.toGraph.induce W := induce_le hW'W
    obtain ⟨t₀⟩ := hTD.isTree.connected.nonempty
    refine ⟨_, IsTreeDecomposition.restrict hTD hle, fun w hw t => ?_, fun t => subset_rfl,
      t₀, by rw [hBF]; exact empty_subset _⟩
    exact (ncard_le_ncard inter_subset_left (hVG.subset (hTD.bag_subset t))).trans (hw t)
  -- The sleeve as sequences.
  obtain ⟨L, hLd, hLend, hLF, hLc⟩ := sd.exists_sleeveDraw hS hcirc hspoke hWD hsW
  have hsleeve : ∀ {x}, x ∈ (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V) →
      InsideOArc univ F x ∨ x ∈ F := fun hx => sd.inside_or_mem hx
  obtain ⟨X, hX, hXw, hXY, t₀, ht₀⟩ := L.toSleeveSeq.exists_decomposition hVG hTD
    (show W' ⊆ V(Dstar.toGraph.induce W) from hW'W) (by omega) (by omega)
    (fun j hj a b hab h => L.adj_step hS j hj a b hab h)
    (fun i => ⟨L.d_mem i _ le_rfl, not_insideOArc_self (hLend i).2⟩)
    (fun i k hk hkW => by
      rcases hsleeve (Or.inr (mem_iUnion.mpr ⟨i, hLd i k hk.le⟩)) with h | h
      · exact hkW.2 h
      · exact hLF i k hk h)
    (fun j x hxW => hxW.2 (sd.circuit_inside j _ ((sd.isCircuit_draw j).2.2 ▸
      (sd.circuitDraw j).V_subset_U (hLc j x))))
  refine ⟨X, hX, hXw, hXY, t₀, ?_⟩
  -- The ends of the radial paths are all of `V(Γ) ∩ F`.
  have hinj : Function.Injective fun i => L.d i (L.len i) := by
    intro i i' h
    by_contra hne
    exact L.d_disj i i' _ _ hne le_rfl le_rfl h
  have hrange : range (fun i => L.d i (L.len i)) = Γ.V ∩ F := by
    refine eq_of_subset_of_ncard_le ?_ ?_ (Γ.finite_V.subset inter_subset_left)
    · rintro _ ⟨i, rfl⟩
      exact hLend i
    · rw [ncard_range_of_injective hinj, Nat.card_fin]
  rw [← hrange]
  exact ht₀

end GM08
end GraphMinor
