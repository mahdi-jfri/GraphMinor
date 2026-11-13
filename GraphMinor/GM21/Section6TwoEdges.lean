module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM11.Walks
import GraphMinor.GM11.EdgeSides
import GraphMinor.GM17.Basic
import GraphMinor.Surface.ArcTools

/-!
# Graph Minors XXI, Section 6: regions at a vertex with two edges

The choice of a region in the proofs of (6.6) and (6.7) of *Graph Minors XXI* (pages 27–28 of the
preprint) follows the regions along a jump. In the paper's setting `Γ` is part of the linkage, so a
vertex of `Γ` inside the disc has at most two edges. This file proves the local fact used at such a
vertex (`subset_closure_of_two_edges`): if `w` is a vertex of a proper drawing in a disc, not in
`bd(Σ)`, with exactly two edges `e, e'`, then every region whose closure meets `e` contains `e'` in
its closure.

The proof removes `w` from the vertex set. The point set `U(Γ)` does not change, so the regions do
not change, and `e ∪ {w} ∪ e'` becomes one edge. A region whose closure meets an edge contains the
whole edge in its closure (`GM06.disc_edge_subset_closure_of_incident`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace DiscLine

open Set Topology GraphMinor.Surface

universe w

variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-- A point of `U(Γ) \ V(Γ)` in the closure of an edge lies in the edge. -/
theorem closure_inter_sdiff_subset (Γ : Drawing S) {f : Set S} (hf : f ∈ Γ.E) :
    closure f ∩ (Γ.U \ Γ.V) ⊆ f := by
  rintro y ⟨hyc, hyU, hyV⟩
  obtain ⟨g, hg, hyg⟩ := Γ.exists_edge_of_mem hyU hyV
  by_cases hfg : f = g
  · exact hfg ▸ hyg
  · have hsub : f ⊆ Γ.U \ g := fun z hz =>
      ⟨(hf.2.1 hz).1, fun hzg => disjoint_left.mp (GM06.disjoint_edges_of_ne Γ hf hg hfg) hz hzg⟩
    exact (((closure_minimal hsub (GM11.isClosed_U_sdiff_edge Γ hg)) hyc).2 hyg).elim

omit [T2Space S] in
/-- The closure of an edge with two ends `u ≠ w` is a line with ends `u, w`. -/
theorem isLineWithEnds_closure_edge (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) {u w : S}
    (hcl : closure e ∩ Γ.V = {u, w}) (huw : u ≠ w) : IsLineWithEnds (closure e) u w := by
  rcases Γ.edge_cond e he with ⟨a, b, -, hab, hline⟩ | ⟨a, ha, -⟩
  · rw [hcl] at hab
    rcases pair_eq_pair_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hline
    · exact hline.symm
  · rw [hcl] at ha
    have hu : u ∈ ({a} : Set S) := ha ▸ Or.inl rfl
    have hw : w ∈ ({a} : Set S) := ha ▸ Or.inr rfl
    exact (huw (hu.trans hw.symm)).elim

/-- **Regions at a vertex with two edges**, for any space in which a region whose closure meets an
edge with two ends contains the whole edge in its closure (`hedge`). Let `w` be a vertex of a
proper drawing `Γ`, not in `bd(Σ)`, whose only edges are `e` (with ends `u, w`) and `e'` (with ends
`w, v`), where `u, w, v` are distinct. Then every region whose closure meets `e ∪ {w} ∪ e'`
contains all of `e ∪ {w} ∪ e'` in its closure. -/
theorem union_subset_closure_of_two_edges_of_edge
    (hedge : ∀ Γ' : Drawing S, Γ'.IsProper → ∀ E ∈ Γ'.E, ∀ u v : S, u ≠ v →
      closure E ∩ Γ'.V = {u, v} → ∀ r ∈ Γ'.R, (E ∩ closure r).Nonempty → E ⊆ closure r)
    {Γ : Drawing S}
    (hΓ : Γ.IsProper) {e e' : Set S} {u w v : S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (hee : e ≠ e')
    (hcl : closure e ∩ Γ.V = {u, w}) (hcl' : closure e' ∩ Γ.V = {w, v}) (huw : u ≠ w)
    (hvw : v ≠ w) (huv : u ≠ v) (hdeg : ∀ f ∈ Γ.E, w ∈ closure f → f = e ∨ f = e')
    (hwbd : w ∉ bd S) {r : Set S} (hr : r ∈ Γ.R) (her : ((e ∪ {w} ∪ e') ∩ closure r).Nonempty) :
    e ∪ {w} ∪ e' ⊆ closure r := by
  have hmem : ∀ {x : S} {A : Set S} {B : Set S}, B = A → x ∈ A → x ∈ B := fun h hx => h ▸ hx
  have huV : u ∈ Γ.V := (hmem hcl (Or.inl rfl)).2
  have hwV : w ∈ Γ.V := (hmem hcl (Or.inr rfl)).2
  have hvV : v ∈ Γ.V := (hmem hcl' (Or.inr rfl)).2
  have hwe : w ∈ closure e := (hmem hcl (Or.inr rfl)).1
  have hwe' : w ∈ closure e' := (hmem hcl' (Or.inl rfl)).1
  have hEe : e ⊆ Γ.U \ Γ.V := he.2.1
  have hEe' : e' ⊆ Γ.U \ Γ.V := he'.2.1
  have hce : closure e = e ∪ {u, w} :=
    GM06.closure_edge_eq_union_ends Γ ⟨he, huV, hwV, hcl⟩ huw
  have hce' : closure e' = e' ∪ {w, v} :=
    GM06.closure_edge_eq_union_ends Γ ⟨he', hwV, hvV, hcl'⟩ hvw.symm
  have hdisj : Disjoint e e' := GM06.disjoint_edges_of_ne Γ he he' hee
  set V₂ : Set S := Γ.V \ {w}
  set E₂ : Set S := e ∪ {w} ∪ e'
  set L : Set S := closure e ∪ closure e'
  -- The two closures form a line with ends `u, v`.
  have hinter : closure e ∩ closure e' = {w} := by
    rw [hce, hce']
    ext z
    simp only [mem_inter_iff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1 | h1, h2 | h2 | h2⟩
      · exact (disjoint_left.mp hdisj h1 h2).elim
      · exact h2
      · exact ((hEe h1).2 (h2 ▸ hvV)).elim
      · exact ((hEe' h2).2 (h1 ▸ huV)).elim
      · exact (huw (h1.symm.trans h2)).elim
      · exact (huv (h1.symm.trans h2)).elim
      · exact h1
      · exact h1
      · exact h1
    · rintro rfl
      exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
  have hL : IsLineWithEnds L u v :=
    (isLineWithEnds_closure_edge Γ he hcl huw).union
      (isLineWithEnds_closure_edge Γ he' hcl' hvw.symm) hinter
  have hLE : L \ {u, v} = E₂ := by
    show (closure e ∪ closure e') \ {u, v} = E₂
    rw [hce, hce']
    ext z
    simp only [E₂, mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨(h1 | h1 | h1) | (h1 | h1 | h1), h2⟩
      · exact Or.inl (Or.inl h1)
      · exact (h2 (Or.inl h1)).elim
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1
      · exact Or.inl (Or.inr h1)
      · exact (h2 (Or.inr h1)).elim
    · rintro ((h1 | h1) | h1)
      · refine ⟨Or.inl (Or.inl h1), ?_⟩
        rintro (rfl | rfl)
        · exact (hEe h1).2 huV
        · exact (hEe h1).2 hvV
      · subst h1
        exact ⟨Or.inl (Or.inr (Or.inr rfl)), by rintro (h | h); exacts [huw h.symm, hvw h.symm]⟩
      · refine ⟨Or.inr (Or.inl h1), ?_⟩
        rintro (rfl | rfl)
        · exact (hEe' h1).2 huV
        · exact (hEe' h1).2 hvV
  have hEpc : IsPathConnected E₂ := hLE ▸ (GM17.isPathConnected_diff_ends_of_isLineWithEnds hL).2
  have hEsub : E₂ ⊆ Γ.U \ V₂ := by
    rintro z ((h | h) | h)
    · exact ⟨(hEe h).1, fun hz => (hEe h).2 hz.1⟩
    · rw [mem_singleton_iff] at h
      subst h
      exact ⟨Γ.V_subset_U hwV, fun hz => hz.2 rfl⟩
    · exact ⟨(hEe' h).1, fun hz => (hEe' h).2 hz.1⟩
  -- `E₂` is closed in `U \ V₂`.
  have hLsub : L ∩ (Γ.U \ V₂) ⊆ E₂ := by
    rintro z ⟨hzL, hzU, hzV⟩
    rw [← hLE]
    refine ⟨hzL, ?_⟩
    rintro (rfl | rfl)
    · exact hzV ⟨huV, huw⟩
    · exact hzV ⟨hvV, hvw⟩
  -- The other edges, with their closures.
  set X : Set S := ⋃ f ∈ {f | f ∈ Γ.E ∧ f ≠ e ∧ f ≠ e'}, closure f
  have hXc : IsClosed X :=
    (Γ.finite_edges.subset fun f hf => hf.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hX : X ∩ (Γ.U \ V₂) ∩ E₂ = ∅ := by
    ext z
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨⟨hzX, hzU, hzV⟩, hzE⟩
    simp only [X, mem_iUnion] at hzX
    obtain ⟨f, ⟨hf, hfe, hfe'⟩, hzf⟩ := hzX
    have hzw : z ≠ w := by
      rintro rfl
      rcases hdeg f hf hzf with h | h
      exacts [hfe h, hfe' h]
    have hzV' : z ∉ Γ.V := fun h => hzV ⟨h, hzw⟩
    have hz : z ∈ f := closure_inter_sdiff_subset Γ hf ⟨hzf, hzU, hzV'⟩
    rcases hzE with (h | h) | h
    · exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ hf he hfe) hz h
    · exact hzw h
    · exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ hf he' hfe') hz h
  have hcover : Γ.U \ V₂ ⊆ L ∪ X := by
    rintro z ⟨hzU, hzV⟩
    by_cases hzw : z = w
    · exact Or.inl (Or.inl (hzw ▸ hwe))
    have hzV' : z ∉ Γ.V := fun h => hzV ⟨h, hzw⟩
    obtain ⟨f, hf, hzf⟩ := Γ.exists_edge_of_mem hzU hzV'
    by_cases hfe : f = e
    · exact Or.inl (Or.inl (subset_closure (hfe ▸ hzf)))
    by_cases hfe' : f = e'
    · exact Or.inl (Or.inr (subset_closure (hfe' ▸ hzf)))
    exact Or.inr (mem_biUnion ⟨hf, hfe, hfe'⟩ (subset_closure hzf))
  -- `E₂` is a maximal path-connected subset of `U \ V₂`.
  have hEmax : ∀ D : Set S, D ⊆ Γ.U \ V₂ → IsPathConnected D → E₂ ⊆ D → D = E₂ := by
    intro D hD hDpc hED
    refine Subset.antisymm ?_ hED
    have hDX : D ∩ X = ∅ := by
      by_contra hne
      obtain ⟨z, hzD, hzL, hzX⟩ := isPreconnected_closed_iff.mp hDpc.isConnected.isPreconnected
        L X (isClosed_closure.union isClosed_closure) hXc (hD.trans hcover)
        ⟨w, hED (Or.inl (Or.inr rfl)), Or.inl hwe⟩ (nonempty_iff_ne_empty.mpr hne)
      have : z ∈ X ∩ (Γ.U \ V₂) ∩ E₂ := ⟨⟨hzX, hD hzD⟩, hLsub ⟨hzL, hD hzD⟩⟩
      rw [hX] at this
      exact this
    intro z hzD
    rcases hcover (hD hzD) with h | h
    · exact hLsub ⟨h, hD hzD⟩
    · exact ((eq_empty_iff_forall_notMem.mp hDX) z ⟨hzD, h⟩).elim
  have hEcomp : E₂ ∈ arcComponentsIn (Γ.U \ V₂) :=
    ⟨⟨w, Or.inl (Or.inr rfl)⟩, hEsub, hEpc, hEmax⟩
  -- Every other path component of `U \ V₂` is an old edge whose closure misses `w`.
  have hcomp : ∀ C ∈ arcComponentsIn (Γ.U \ V₂), C = E₂ ∨ (C ∈ Γ.E ∧ w ∉ closure C) := by
    rintro C ⟨hCne, hCsub, hCpc, hCmax⟩
    by_cases hCE : (C ∩ E₂).Nonempty
    · left
      have h1 := hCmax (C ∪ E₂) (union_subset hCsub hEsub) (hCpc.union hEpc hCE)
        subset_union_left
      have h2 := hEmax (C ∪ E₂) (union_subset hCsub hEsub) (hCpc.union hEpc hCE)
        subset_union_right
      exact h1.symm.trans h2
    · right
      rw [not_nonempty_iff_eq_empty] at hCE
      have hCnot : ∀ z ∈ C, z ∉ E₂ := fun z hz hzE =>
        (eq_empty_iff_forall_notMem.mp hCE) z ⟨hz, hzE⟩
      have hCV : C ⊆ Γ.U \ Γ.V := fun z hz => by
        refine ⟨(hCsub hz).1, fun hzV => (hCsub hz).2 ⟨hzV, ?_⟩⟩
        rintro rfl
        exact hCnot z hz (Or.inl (Or.inr rfl))
      obtain ⟨x, hx⟩ := hCne
      obtain ⟨f, hf, hxf⟩ := Γ.exists_edge_of_mem (hCV hx).1 (hCV hx).2
      have hfC : f ∪ C = f :=
        hf.2.2.2 (f ∪ C) (union_subset hf.2.1 hCV) (hf.2.2.1.union hCpc ⟨x, hxf, hx⟩)
          subset_union_left
      have hCf : C ⊆ f := hfC ▸ subset_union_right
      have hfeq : f = C := hCmax f (fun z hz => ⟨(hf.2.1 hz).1, fun hzV => (hf.2.1 hz).2 hzV.1⟩)
        hf.2.2.1 hCf
      refine ⟨hfeq ▸ hf, fun hwC => ?_⟩
      rcases hdeg f hf (hfeq ▸ hwC) with h | h
      · exact hCnot x hx (Or.inl (Or.inl (h ▸ hxf)))
      · exact hCnot x hx (Or.inr (h ▸ hxf))
  have hcl₂ : closure E₂ = L := by
    refine Subset.antisymm (closure_minimal (hLE ▸ sdiff_subset)
      (isClosed_closure.union isClosed_closure)) (union_subset ?_ ?_)
    · exact closure_mono fun z hz => Or.inl (Or.inl hz)
    · exact closure_mono fun z hz => Or.inr hz
  have hcap₂ : closure E₂ ∩ V₂ = {u, v} := by
    rw [hcl₂]
    ext z
    simp only [L, mem_inter_iff, mem_union, V₂, mem_sdiff, mem_singleton_iff, mem_insert_iff]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · rcases (hmem hcl.symm ⟨h1, h2⟩ : z ∈ ({u, w} : Set S)) with h | h
        exacts [Or.inl h, (h3 h).elim]
      · rcases (hmem hcl'.symm ⟨h1, h2⟩ : z ∈ ({w, v} : Set S)) with h | h
        exacts [(h3 h).elim, Or.inr h]
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (hmem hcl (Or.inl rfl)).1, huV, huw⟩
      · exact ⟨Or.inr (hmem hcl' (Or.inr rfl)).1, hvV, hvw⟩
  -- The drawing with `w` removed from the vertex set.
  let Γ₂ : Drawing S :=
    { U := Γ.U
      V := V₂
      V_subset_U := fun z hz => Γ.V_subset_U hz.1
      isClosed_U := Γ.isClosed_U
      finite_V := Γ.finite_V.subset sdiff_subset
      finite_edges := by
        refine (Γ.finite_edges.insert E₂).subset fun C hC => ?_
        rcases hcomp C hC with h | h
        · exact Or.inl h
        · exact Or.inr h.1
      edge_cond := by
        intro C hC
        rcases hcomp C hC with rfl | ⟨hCE, hwC⟩
        · left
          exact ⟨u, v, huv, hcap₂, hcl₂ ▸ hL⟩
        · have hC₂ : closure C ∩ V₂ = closure C ∩ Γ.V := by
            ext z
            constructor
            · rintro ⟨h1, h2, -⟩
              exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩
              exact ⟨h1, h2, fun h => hwC (h ▸ h1)⟩
          rw [hC₂]
          exact Γ.edge_cond C hCE }
  have hΓ₂ : Γ₂.IsProper := fun z hz =>
    ⟨hΓ hz, fun h => hwbd (h ▸ hz.1)⟩
  exact hedge Γ₂ hΓ₂ E₂ hEcomp u v huv hcap₂ r hr her

/-- **Regions at a vertex with two edges**, for any space in which a region whose closure meets an
edge with two ends contains the whole edge in its closure (`hedge`). Let `w` be a vertex of a
proper drawing `Γ`, not in `bd(Σ)`, whose only edges are `e` (with ends `u, w`) and `e'` (with ends
`w, v`), where `u, w, v` are distinct. Then every region whose closure meets `e` contains `e'` in
its closure. -/
theorem subset_closure_of_two_edges_of_edge
    (hedge : ∀ Γ' : Drawing S, Γ'.IsProper → ∀ E ∈ Γ'.E, ∀ u v : S, u ≠ v →
      closure E ∩ Γ'.V = {u, v} → ∀ r ∈ Γ'.R, (E ∩ closure r).Nonempty → E ⊆ closure r)
    {Γ : Drawing S}
    (hΓ : Γ.IsProper) {e e' : Set S} {u w v : S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (hee : e ≠ e')
    (hcl : closure e ∩ Γ.V = {u, w}) (hcl' : closure e' ∩ Γ.V = {w, v}) (huw : u ≠ w)
    (hvw : v ≠ w) (huv : u ≠ v) (hdeg : ∀ f ∈ Γ.E, w ∈ closure f → f = e ∨ f = e')
    (hwbd : w ∉ bd S) {r : Set S} (hr : r ∈ Γ.R) (her : (e ∩ closure r).Nonempty) :
    e' ⊆ closure r := by
  obtain ⟨x, hxe, hxr⟩ := her
  have h := union_subset_closure_of_two_edges_of_edge hedge hΓ he he' hee hcl hcl' huw hvw huv
    hdeg hwbd hr ⟨x, Or.inl (Or.inl hxe), hxr⟩
  exact fun z hz => h (Or.inr hz)

/-- **Regions at a vertex with two edges**, in a disc. Let `w` be a vertex of a proper drawing `Γ`
in a disc, not in `bd(Σ)`, whose only edges are `e` (with ends `u, w`) and `e'` (with ends `w, v`),
where `u, w, v` are distinct. Then every region whose closure meets `e` contains `e'` in its
closure. -/
theorem subset_closure_of_two_edges (hS : GM06.IsClosedDiscSpace S) {Γ : Drawing S}
    (hΓ : Γ.IsProper) {e e' : Set S} {u w v : S} (he : e ∈ Γ.E) (he' : e' ∈ Γ.E) (hee : e ≠ e')
    (hcl : closure e ∩ Γ.V = {u, w}) (hcl' : closure e' ∩ Γ.V = {w, v}) (huw : u ≠ w)
    (hvw : v ≠ w) (huv : u ≠ v) (hdeg : ∀ f ∈ Γ.E, w ∈ closure f → f = e ∨ f = e')
    (hwbd : w ∉ bd S) {r : Set S} (hr : r ∈ Γ.R) (her : (e ∩ closure r).Nonempty) :
    e' ⊆ closure r :=
  subset_closure_of_two_edges_of_edge
    (fun _ hΓ' _ hE _ _ _ _ _ hr' hinc => GM06.disc_edge_subset_closure_of_incident hS hΓ' hE hr' hinc)
    hΓ he he' hee hcl hcl' huw hvw huv hdeg hwbd hr her

end DiscLine
end GM21
end GraphMinor
