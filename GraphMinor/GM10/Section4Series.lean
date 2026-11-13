module

public import GraphMinor.GM10.Section4Contraction
public import GraphMinor.GM10.Section4EdgeExpansion

/-!
# Restoring a vertex incident with two edges

The induction in Graph Minors X, (4.2)(iii), page 165, suppresses a
vertex of valency two. We show that restoring this vertex preserves the
bound two on branch-width. The two edges form one edge group. Cuts
inside this group have order at most two, and cuts outside the group
have the same boundary after suppression.
-/

public section

namespace GraphMinor.GM10

open Graph Hypergraph Classical

universe u v

/-- Suppressing a vertex incident with just two distinct edges preserves
the branch-width bound two in the reverse direction, as needed in the
induction for Graph Minors X, (4.2)(iii), page 165. -/
theorem branchWidth_le_two_of_suppress_degree_two
    {α : Type u} {β : Type v} (G H : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(H).Finite) (hEH : E(H).Finite)
    {d e : β} {u v : α} (hd : G.IsLink d u v) (_huv : u ≠ v)
    (hed : d ≠ e) (hev : G.Inc e v)
    (honly : ∀ a, G.Inc a v → a = d ∨ a = e)
    (hH : H = (G.map (fun x ↦ if x = v then u else x)).deleteEdges {d})
    (hw : branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2) :
    branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 := by
  classical
  subst H
  let q : α → α := fun x ↦ if x = v then u else x
  let H := (G.map q).deleteEdges {d}
  let G₀ := Hypergraph.ofGraph G hV hE
  let H₀ := Hypergraph.ofGraph H hVH hEH
  let f : β → β := fun a ↦ if a = d then e else a
  have hf_ne : ∀ a, f a ≠ d := by
    intro a
    dsimp [f]
    split_ifs with ha
    · exact hed.symm
    · exact ha
  have hf : Set.MapsTo f G₀.edgeSet H₀.edgeSet := by
    intro a ha
    refine ⟨?_, hf_ne a⟩
    dsimp [f]
    split_ifs
    · exact hev.edge_mem
    · exact ha
  have hincH : ∀ a x, a ≠ d → G.Inc a x → H.Inc a (q x) := by
    intro a x ha hx
    exact Graph.deleteEdges_inc.2 ⟨hx.map q, ha⟩
  have hmapinc : ∀ a x, x ≠ v → G.Inc a x → H.Inc (f a) x := by
    intro a x hxv hax
    by_cases had : a = d
    · subst a
      have hxu : x = u := (hax.eq_or_eq_of_isLink hd).resolve_right hxv
      subst x
      have hm := hincH e v hed.symm hev
      simpa only [f, q, ↓reduceIte] using hm
    · have hm := hincH a x had hax
      simpa only [f, q, had, hxv, ↓reduceIte] using hm
  have hcut : ∀ X ⊆ H₀.edgeSet,
      (branchEdgeBoundary G₀ (G₀.edgeSet ∩ f ⁻¹' X)).ncard ≤
        (branchEdgeBoundary H₀ X).ncard := by
    intro X _
    apply Set.ncard_le_ncard _ (branchEdgeBoundary_finite H₀ X)
    rintro x ⟨_, ⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    have hxv : x ≠ v := by
      intro hx
      subst x
      have hfa : f a = e := by
        rcases honly a hax with rfl | rfl <;> simp [f]
      have hfb : f b = e := by
        rcases honly b hbx with rfl | rfl <;> simp [f]
      apply hb.2
      refine ⟨hb.1, ?_⟩
      change f b ∈ X
      rw [hfb, ← hfa]
      exact ha.2
    have haxH := hmapinc a x hxv hax
    have hbxH := hmapinc b x hxv hbx
    exact ⟨haxH.vertex_mem, ⟨f a, ha.2, haxH⟩,
      f b, ⟨hf hb.1, fun h ↦ hb.2 ⟨hb.1, h⟩⟩, hbxH⟩
  have hsingle : ∀ a : β, (branchEdgeBoundary G₀ {a}).ncard ≤ 2 := by
    intro a
    have hs : branchEdgeBoundary G₀ {a} ⊆ G₀.ends a := by
      rintro x ⟨_, ⟨b, rfl, hbx⟩, _⟩
      exact hbx
    exact (Set.ncard_le_ncard hs (ends_finite G₀ a)).trans
      (edgeSize_ofGraph_le_two G hV hE a)
  obtain ⟨w, hew⟩ := hev
  have hpair : (branchEdgeBoundary G₀ {d, e}).ncard ≤ 2 := by
    have hs : branchEdgeBoundary G₀ {d, e} ⊆ {u, w} := by
      rintro x ⟨_, ⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
      have hxv : x ≠ v := by
        intro hx
        subst x
        exact hb.2 (honly b hbx)
      rcases ha with rfl | rfl
      · exact Or.inl ((hax.eq_or_eq_of_isLink hd).resolve_right hxv)
      · exact Or.inr ((hax.eq_or_eq_of_isLink hew).resolve_left hxv)
    have hcard : ({u, w} : Set α).ncard ≤ 2 := by
      by_cases huw : u = w
      · simp [huw]
      · rw [Set.ncard_pair huw]
    exact (Set.ncard_le_ncard hs (Set.toFinite _)).trans hcard
  have hfiber : ∀ z ∈ H₀.edgeSet, ∀ X ⊆ G₀.edgeSet ∩ f ⁻¹' {z},
      (branchEdgeBoundary G₀ X).ncard ≤ 2 := by
    intro z hz X hX
    by_cases hze : z = e
    · subst z
      have hs : X ⊆ {d, e} := by
        intro a ha
        have hfa : f a = e := (hX ha).2
        by_cases had : a = d
        · exact Or.inl had
        · exact Or.inr (by change a = e; simpa only [f, had, ↓reduceIte] using hfa)
      rcases Set.subset_pair_iff_eq.1 hs with rfl | rfl | rfl | rfl
      · simp [branchEdgeBoundary_empty]
      · exact hsingle d
      · exact hsingle e
      · exact hpair
    · have hs : X ⊆ {z} := by
        intro a ha
        have hfa : f a = z := (hX ha).2
        by_cases had : a = d
        · have hez : e = z := by simpa only [f, had, ↓reduceIte] using hfa
          exact (hze hez.symm).elim
        · change a = z
          simpa only [f, had, ↓reduceIte] using hfa
      have hbd : branchEdgeBoundary G₀ X ⊆ G₀.ends z := by
        rintro x ⟨_, ⟨a, ha, hax⟩, _⟩
        exact (hs ha) ▸ hax
      exact (Set.ncard_le_ncard hbd (ends_finite G₀ z)).trans
        (edgeSize_ofGraph_le_two G hV hE z)
  have hγG : 1 ≤ maxEdgeSize G₀ := one_le_maxEdgeSize_ofGraph ⟨d, hd.edge_mem⟩
  have heH : e ∈ H₀.edgeSet := ⟨hew.edge_mem, hed.symm⟩
  have hγH : 1 ≤ maxEdgeSize H₀ := one_le_maxEdgeSize_ofGraph ⟨e, heH⟩
  have hkG : maxEdgeSize G₀ ≤ 2 :=
    maxEdgeSize_le_iff.2 (fun a _ ↦ edgeSize_ofGraph_le_two G hV hE a)
  have hkH : maxEdgeSize H₀ ≤ 2 :=
    maxEdgeSize_le_iff.2 (fun a _ ↦ edgeSize_ofGraph_le_two H hVH hEH a)
  exact branchWidth_le_of_edge_partition hγG hγH hkG hkH f hf hcut hfiber hw

end GraphMinor.GM10
