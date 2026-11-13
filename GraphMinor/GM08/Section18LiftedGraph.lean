module

public import GraphMinor.GM19.CutDrawing
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18LiftedEdgeFamily
import Mathlib.Data.Set.Card.Arithmetic

/-!
# The graph of a cut dissection

Join the one-edge and two-edge families over the old edges. Their
intersections are lifted vertices, and different old edges give
disjoint edge families. The new graph is exactly the preimage of the
old graph, and its edge count is the old count plus the cut-edge count.
This is the graph step in the Euler proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface
open scoped Function

open Classical in
private theorem card_subtype_filter {S : Type*} {E D : Set S} [Fintype E]
    (hDE : D ⊆ E) : (Finset.univ.filter (fun e : E => e.1 ∈ D)).card = D.ncard := by
  classical
  let T : Finset E := Finset.univ.filter (fun e => e.1 ∈ D)
  have himage : Subtype.val '' (↑T : Set E) = D := by
    ext e
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact (Finset.mem_filter.mp hd).2
    · intro he
      exact ⟨⟨e, hDE he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  calc
    T.card = (↑T : Set E).ncard := (ncard_coe_finset T).symm
    _ = (Subtype.val '' (↑T : Set E)).ncard :=
      (ncard_image_of_injective _ Subtype.val_injective).symm
    _ = D.ncard := congrArg Set.ncard himage

/-- The preimage of the source graph is a finite graph with the old
edge count plus the number of cut edges. This constructs the graph in
the dissection count of VIII (18.2), page 286. -/
theorem exists_lifted_graph_of_word_cut {S Y : Type} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] (hY : IsSurface Y)
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {D : Set (Set S)} (hDE : D ⊆ E)
    {ψ : Y → S} (hcm : GM19.IsCutMap ψ (⋃₀ D))
    (hlift : ∀ e ∈ D, ∃ r r', GM19.IsEdgeLift ψ (extI (A e)) (GM19.EndFine A D e) r r') :
    ∃ E' : Set (Set Y), IsGraph (ψ ⁻¹' V) E' ∧
      gr (ψ ⁻¹' V) E' = ψ ⁻¹' gr V E ∧
      ⋃₀ E' ⊆ ψ ⁻¹' ⋃₀ E ∧ E'.ncard = E.ncard + D.ncard := by
  classical
  have : Fintype E := hw.graph.fine.fintype
  choose B hBfin hBcard hBedge hBmeet hBcover using
    (fun e : E => exists_lifted_edge_family hY hw hDE hcm hlift e.2)
  let E' := ⋃ e : E, B e
  have hE'fin : E'.Finite := Set.finite_iUnion hBfin
  have hVfin : (ψ ⁻¹' V).Finite := by
    have heq : ψ ⁻¹' V = ⋃ v ∈ V, ψ ⁻¹' {v} := by ext y; simp
    rw [heq]
    exact hw.graph.fin.biUnion (fun v _ => hcm.2.2.2.1 v)
  have hg : IsGraph (ψ ⁻¹' V) E' := by
    refine ⟨hVfin, hE'fin, ?_, ?_⟩
    · intro L hL
      obtain ⟨e, he⟩ := mem_iUnion.mp hL
      obtain ⟨x, y, hxy, hline, hcap, _⟩ := hBedge e L he
      exact ⟨x, y, hxy, hline, hcap⟩
    · intro L hL K hK hLK z hz
      obtain ⟨e, he⟩ := mem_iUnion.mp hL
      obtain ⟨d, hd⟩ := mem_iUnion.mp hK
      by_cases hed : e = d
      · subst d
        exact hBmeet e L he K hd hLK hz
      · obtain ⟨_, _, _, _, _, hbL⟩ := hBedge e L he
        obtain ⟨_, _, _, _, _, hbK⟩ := hBedge d K hd
        exact hw.graph.disj e.1 e.2 d.1 d.2 (fun hh => hed (Subtype.ext hh))
          ⟨hbL.mapsTo hz.1, hbK.mapsTo hz.2⟩
  have hgr : gr (ψ ⁻¹' V) E' = ψ ⁻¹' gr V E := by
    ext y
    constructor
    · rintro (hyV | ⟨L, hL, hyL⟩)
      · exact Or.inl hyV
      · obtain ⟨e, he⟩ := mem_iUnion.mp hL
        obtain ⟨_, _, _, _, _, hb⟩ := hBedge e L he
        exact Or.inr ⟨e.1, e.2, hb.mapsTo hyL⟩
    · intro hy
      rcases hy with hyV | ⟨e, he, hye⟩
      · exact Or.inl hyV
      · by_cases hyV : ψ y ∈ V
        · exact Or.inl hyV
        · obtain ⟨L, hL, hyL⟩ := hBcover ⟨e, he⟩ ⟨hye, hyV⟩
          exact Or.inr ⟨L, mem_iUnion.mpr ⟨⟨e, he⟩, hL⟩, hyL⟩
  have hpair : Pairwise (Disjoint on B) := by
    intro e d hne
    apply disjoint_left.mpr
    intro L he hd
    obtain ⟨_, _, _, _, _, hbE⟩ := hBedge e L he
    obtain ⟨_, _, _, _, _, hbD⟩ := hBedge d L hd
    exact hne (Subtype.ext (hbE.image_eq.symm.trans hbD.image_eq))
  have hedgesub : ⋃₀ E' ⊆ ψ ⁻¹' ⋃₀ E := by
    rintro y ⟨L, hL, hyL⟩
    obtain ⟨e, he⟩ := mem_iUnion.mp hL
    obtain ⟨_, _, _, _, _, hb⟩ := hBedge e L he
    exact ⟨e.1, e.2, hb.mapsTo hyL⟩
  refine ⟨E', hg, hgr, hedgesub, ?_⟩
  rw [ncard_iUnion_of_finite hBfin hpair, finsum_eq_sum_of_fintype]
  have hsum : (∑ e : E, (B e).ncard) =
      ∑ e : E, (1 + if e.1 ∈ D then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [hBcard e]
    by_cases he : e.1 ∈ D
    · rw [ite_eq_left he, ite_eq_left he]
    · rw [ite_eq_right he, ite_eq_right he]
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_boole,
    card_subtype_filter hDE]
  simp only [Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  simp

end GraphMinor.GM08
