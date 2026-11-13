module

public import GraphMinor.GM02.EdgeRouteShortening
public import GraphMinor.GM02.EdgeRouteBase
import GraphMinor.GM02.EdgeRouteCover
import GraphMinor.GM02.EdgeRouteSublists
import Mathlib.Data.Set.Card

/-!
# Suppressing disjoint edge-labelled routes

Follow the suppression argument on II, page 319, while retaining edge
names. If an interior is nonempty, suppress its first vertex and shorten
that route. The other walks remain unchanged. The interiors and edge
lists only lose entries, so all disjointness conditions persist. The
number of vertices outside the pattern decreases. When every interior
is empty, the single-edge routes give an isomorphism fixing the vertices.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface Relation
universe u v

/-- Disjoint edge-labelled routes covering a graph suppress to their pattern, including loops and parallel edges. -/
theorem edgeRoutes_suppress {α : Type u} {β : Type v} {k : ℕ}
    (K H : Graph α β) (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (inner : Fin k → List α) (W : ∀ i, GraphWalk K (ends i).1 (ends i).2)
    (hs : ∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]))
    (hn : ∀ i, (inner i).Nodup)
    (hout : ∀ i y, y ∈ inner i → y ∉ V(H))
    (hdis : ∀ i j, i ≠ j → Disjoint {y | y ∈ inner i} {y | y ∈ inner j})
    (heN : ∀ i, (W i).edges.Nodup) (heNon : ∀ i, (W i).edges ≠ [])
    (heDis : ∀ i j, i ≠ j → Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges})
    (hVH : V(H) ⊆ V(K))
    (hVC : ∀ y ∈ V(K), y ∈ V(H) ∨ ∃ i, y ∈ inner i)
    (hEC : ∀ e ∈ E(K), ∃ i, e ∈ (W i).edges)
    (hfin : (V(K) \ V(H)).Finite) :
    ∃ L, ReflTransGen IsSuppression K L ∧ IsoFix H L := by
  have hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H) :=
    fun i => ⟨(hH i).left_mem, (hH i).right_mem⟩
  induction hsize : (V(K) \ V(H)).ncard using Nat.strong_induction_on generalizing K inner W with
  | h n ih =>
    by_cases hex : ∃ i, inner i ≠ []
    · obtain ⟨i, hiNon⟩ := hex
      obtain ⟨x, rest, hi⟩ := List.exists_cons_of_ne_nil hiNon
      have hxIn : x ∈ inner i := hi ▸ List.mem_cons_self
      have hxH : x ∉ V(H) := hout i x hxIn
      have hsi : (W i).support = (ends i).1 :: (x :: rest ++ [(ends i).2]) := by
        rw [hs i, hi]
      obtain ⟨e₁, e₂, z, tail, h₁, h₂, he, ht⟩ := GraphWalk.exists_first_two (W i) rest hsi
      obtain ⟨d, W', hdx, hdf, hds, hdfresh, hs', he', hother⟩ :=
        exists_edgeRoute_shortening K H ends inner W hends hs hn hout hdis hEC
          i x rest hi e₁ e₂ z tail h₁ h₂ he ht (heN i)
      let inner' : Fin k → List α := fun j => if j = i then rest else inner j
      have hsub : ∀ j, (inner' j).Sublist (inner j) :=
        edgeRoute_inner_sublist inner i x rest hi
      have hOld : (W i).edges = d.first :: d.second :: tail.edges := by
        rw [hdf, hds]; exact he
      have hNew : (W' i).edges = d.fresh :: tail.edges := by
        rw [hdfresh]; exact he'
      have heSub : ∀ j, (W' j).edges.Sublist (W j).edges :=
        edgeRoute_edge_sublist d ends W W' i tail.edges (hdfresh.trans hdf.symm) hOld hNew hother
      have hn' : ∀ j, (inner' j).Nodup := fun j => (hsub j).nodup (hn j)
      have hout' : ∀ j y, y ∈ inner' j → y ∉ V(H) :=
        fun j y hy => hout j y ((hsub j).subset hy)
      have hdis' : ∀ j l, j ≠ l → Disjoint {y | y ∈ inner' j} {y | y ∈ inner' l} :=
        edgeRoute_disjoint_of_sublist inner inner' hsub hdis
      have heN' : ∀ j, (W' j).edges.Nodup := fun j => (heSub j).nodup (heN j)
      have heNon' : ∀ j, (W' j).edges ≠ [] := by
        intro j
        by_cases hji : j = i
        · subst j
          rw [he']
          exact List.cons_ne_nil _ _
        · rw [hother j hji]
          exact heNon j
      have heDis' : ∀ j l, j ≠ l → Disjoint {e | e ∈ (W' j).edges} {e | e ∈ (W' l).edges} :=
        edgeRoute_disjoint_of_sublist (fun j => (W j).edges) (fun j => (W' j).edges) heSub heDis
      have hVH' : V(H) ⊆ V(d.result) := by
        intro y hy
        refine ⟨hVH hy, ?_⟩
        intro hyx
        have hyx' : y = x := hyx.trans hdx
        exact hxH (hyx' ▸ hy)
      have hi' : inner i = d.vertex :: rest := by rw [hdx]; exact hi
      have hVC' := edgeRoute_vertex_cover_after_suppression d inner hVC i rest hi'
      have hEC' := edgeRoute_cover_after_suppression d ends W W' hEC i tail.edges hOld hNew hother
      have hdH : d.vertex ∉ V(H) := hdx.symm ▸ hxH
      have hdK : d.vertex ∈ V(K) := d.first_link.left_mem
      have hset : V(d.result) \ V(H) = (V(K) \ V(H)) \ {d.vertex} := by
        ext y
        change (y ∈ V(K) ∧ y ≠ d.vertex) ∧ y ∉ V(H) ↔
          (y ∈ V(K) ∧ y ∉ V(H)) ∧ y ≠ d.vertex
        tauto
      have hfin' : (V(d.result) \ V(H)).Finite := hset ▸ hfin.subset Set.sdiff_subset
      have hlt : (V(d.result) \ V(H)).ncard < n := by
        rw [hset, ← hsize]
        exact Set.ncard_sdiff_singleton_lt_of_mem ⟨hdK, hdH⟩ hfin
      obtain ⟨L, hL, hIso⟩ := ih _ hlt d.result inner' W' hs' hn' hout' hdis'
        heN' heNon' heDis' hVH' hVC' hEC' hfin' rfl
      exact ⟨L, ReflTransGen.head ⟨d, rfl⟩ hL, hIso⟩
    · have hnil : ∀ i, inner i = [] := by
        intro i
        by_contra hi
        exact hex ⟨i, hi⟩
      have hV : V(H) = V(K) := by
        apply Set.Subset.antisymm hVH
        intro y hy
        rcases hVC y hy with h | ⟨i, hi⟩
        · exact h
        · rw [hnil i] at hi
          exact (List.not_mem_nil hi).elim
      have hs0 : ∀ i, (W i).support = [(ends i).1, (ends i).2] := by
        intro i
        simpa only [hnil i, List.nil_append] using hs i
      exact ⟨K, ReflTransGen.refl, edgeRoute_isoFix_of_inner_eq_nil K H edge ends hH W hs0 hV hEC heDis⟩

end GraphMinor.GM02
