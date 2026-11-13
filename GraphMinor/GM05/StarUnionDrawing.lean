module

public import GraphMinor.GM05.StarSupport
public import GraphMinor.GM05.ClosedPieceSubdrawing
import GraphMinor.GM05.MarkedArcUnionDrawing
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.TriPath
import GraphMinor.Surface.SurfaceGraph

/-!
# Planarizing all stars at one vertex

For GM V, (8.14), put every ray crossing and endpoint among the
vertices before forming the union drawing. Each individual star is
closed and connected. Its meetings with the union of the other
stars are marked vertices, so it gives a connected subdrawing.
An isolated centre is retained as a singleton branch.
-/

public section
namespace GraphMinor.GM05
open Set Surface
universe v

/-- Planarize the local stars of GM V, (8.14), page 113, retaining
one connected branch subdrawing for each copy and all its ports. -/
theorem exists_star_union_drawing {S : Type} [TopologicalSpace S] [T2Space S]
    (m : ℕ) {κ : Type v} [Fintype κ] (x : Fin m → S)
    (p : Fin m × κ → S) (L : Fin m × κ → Set S)
    (hx : ∀ i j, i ≠ j → x i ≠ x j)
    (hL : ∀ a, IsLineWithEnds (L a) (x a.1) (p a))
    (hfin : ∀ a b, a ≠ b → (L a ∩ L b).Finite) :
    ∃ D : Drawing S, ∃ K : Fin m → Drawing S,
      D.U = ⋃ i, starSupport x L i ∧ (∀ i, x i ∈ D.V) ∧ (∀ a, p a ∈ D.V) ∧
      ∀ i, (K i).IsSubdrawing D ∧ (K i).U = starSupport x L i ∧
        (K i).V = starSupport x L i ∩ D.V ∧ GraphConnected (K i).toGraph := by
  classical
  choose a ha har ha0 ha1 using fun q ↦ (hL q).exists_arc
  have hAa : ∀ f ∈ range a, IsArcMap f := by
    rintro f ⟨q,rfl⟩
    exact ha q
  have hAf : ∀ f ∈ range a, ∀ g ∈ range a, f ≠ g → (range f ∩ range g).Finite := by
    rintro f ⟨q,rfl⟩ g ⟨r,rfl⟩ hfg
    rw [har q,har r]
    exact hfin q r (fun he ↦ hfg (he ▸ rfl))
  obtain ⟨D,hDU,hxV,hends,hcross⟩ := exists_marked_arc_union_drawing
    (finite_range a) hAa hAf (finite_range x)
  have hcentre : ∀ i, x i ∈ D.V := fun i ↦ hxV (mem_range_self i)
  have hports : ∀ q, p q ∈ D.V := fun q ↦ ha1 q ▸ (hends (a q) (mem_range_self q)).2
  have hU : D.U = ⋃ i, starSupport x L i := by
    rw [hDU]
    apply subset_antisymm
    · rintro z (⟨i,rfl⟩ | hz)
      · exact mem_iUnion.mpr ⟨i,centre_mem_starSupport x L i⟩
      · obtain ⟨f,⟨q,rfl⟩,hz⟩ := mem_iUnion₂.mp hz
        exact mem_iUnion.mpr ⟨q.1,ray_subset_starSupport x L q.1 q.2 (har q ▸ hz)⟩
    · intro z hz
      obtain ⟨i,hz⟩ := mem_iUnion.mp hz
      rcases hz with rfl | hz
      · exact .inl (mem_range_self i)
      · obtain ⟨e,he⟩ := mem_iUnion.mp hz
        exact .inr (mem_iUnion₂.mpr ⟨a (i,e),mem_range_self (i,e),(har (i,e)).symm ▸ he⟩)
  have hclosed : ∀ i, IsClosed (starSupport x L i) := fun i ↦
    isClosed_starSupport x L i (fun e ↦ (hL (i,e)).isCompact.isClosed)
  have hconn : ∀ i, IsPreconnected (starSupport x L i) := fun i ↦
    isPreconnected_starSupport x L i (fun e ↦ (hL (i,e)).isPreconnected_self)
      (fun e ↦ (hL (i,e)).left_mem)
  have hmeet : ∀ i j, i ≠ j → starSupport x L i ∩ starSupport x L j ⊆ D.V := by
    intro i j hij z hz
    rcases hz.1 with he | hi
    · exact he ▸ hcentre i
    rcases hz.2 with he | hj
    · exact he ▸ hcentre j
    obtain ⟨e,he⟩ := mem_iUnion.mp hi
    obtain ⟨f,hf⟩ := mem_iUnion.mp hj
    have hne : a (i,e) ≠ a (j,f) := by
      intro hh
      exact hx i j hij ((ha0 (i,e)).symm.trans
        ((congrArg (fun z : unitInterval → S ↦ z 0) hh).trans (ha0 (j,f))))
    apply hcross (a (i,e)) (mem_range_self _) (a (j,f)) (mem_range_self _) hne
    rw [har (i,e),har (j,f)]
    exact ⟨he,hf⟩
  have hex : ∀ i, ∃ K : Drawing S, K.IsSubdrawing D ∧ K.U = starSupport x L i ∧
      K.V = starSupport x L i ∩ D.V ∧ GraphConnected K.toGraph := by
    intro i
    let U : Set S := ⋃ j ∈ {j : Fin m | j ≠ i}, starSupport x L j
    have hUc : IsClosed U := (toFinite {j : Fin m | j ≠ i}).isClosed_biUnion fun j _ ↦ hclosed j
    have hsplit : D.U = starSupport x L i ∪ U := by
      rw [hU]
      apply subset_antisymm
      · intro z hz
        obtain ⟨j,hz⟩ := mem_iUnion.mp hz
        by_cases hji : j = i
        · exact .inl (hji ▸ hz)
        · exact .inr (mem_iUnion₂.mpr ⟨j,hji,hz⟩)
      · rintro z (hz | hz)
        · exact mem_iUnion.mpr ⟨i,hz⟩
        · obtain ⟨j,-,hz⟩ := mem_iUnion₂.mp hz
          exact mem_iUnion.mpr ⟨j,hz⟩
    have hcap : starSupport x L i ∩ U ⊆ D.V := by
      rintro z ⟨hz,hzU⟩
      obtain ⟨j,hji,hzj⟩ := mem_iUnion₂.mp hzU
      exact hmeet i j (Ne.symm hji) ⟨hz,hzj⟩
    exact exists_connected_subdrawing_of_closed_pieces D (hclosed i) hUc hsplit hcap (hconn i)
      ⟨x i,centre_mem_starSupport x L i,hcentre i⟩
  choose K hK using hex
  exact ⟨D,K,hU,hcentre,hports,hK⟩

end GraphMinor.GM05
