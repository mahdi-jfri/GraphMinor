module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5BranchToLinkage
import GraphMinor.GM06.Section5PathValency
import GraphMinor.GM06.Section5InitialLoop
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4Overlap
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# An initial branch meets the linkage only at its ends

In the boundary argument of VI (5.1), page 129, an extra initial edge
starts a simple branch back to the linkage. Its internal vertices
miss all linkage paths. It also contains a point of that extra edge,
which lies off every linkage path. The path-overlap lemma therefore
upgrades the vertex condition to the whole point set.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

private theorem disjoint_edge_subdrawing {G P : Drawing ClosedCylinder}
    (hPG : P.IsSubdrawing G) {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ P.E) :
    Disjoint P.U e := by
  apply disjoint_left.mpr
  intro x hxP hxe
  have hxV : x ∉ P.V := fun hv => (he.2.1 hxe).2 (hPG.1 hv)
  obtain ⟨f, hf, hxf⟩ := P.exists_edge_of_mem hxP hxV
  have hfe : f = e := G.edge_eq_of_mem (hPG.2 hf) he hxf hxe
  exact heP (hfe ▸ hf)

/-- An edge at an initial vertex outside its linkage path starts an
arc whose only contacts with the entire linkage are its two ends.
This is the separating branch used in the proof of VI (5.1). -/
theorem exists_initial_branch_arc
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    {e : Set ClosedCylinder} {b : ClosedCylinder}
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) b)
    (hb : b ≠ cylinderM1Point k i) (heP : e ∉ (L.pathDrawing i).E) :
    ∃ j : Fin k, ∃ x ∈ (L.pathDrawing j).V, ∃ Q : Drawing ClosedCylinder,
      IsSubpathOf G Q (cylinderM1Point k i) x ∧ e ∈ Q.E ∧
      Q.U ∩ (⋃ n : Fin k, (L.pathDrawing n).U) ⊆ {cylinderM1Point k i, x} := by
  have heL (n : Fin k) : e ∉ (L.pathDrawing n).E := by
    by_cases hn : n = i
    · subst n
      exact heP
    · intro he
      have hcl : closure e ⊆ (L.pathDrawing n).U :=
        (L.pathDrawing n).isClosed_U.closure_subset_iff.mpr (he.2.1.trans sdiff_subset)
      have hscl : cylinderM1Point k i ∈ closure e ∩ G.V :=
        hl.2.2.2 ▸ mem_insert _ _
      have hsi : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
        (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
      exact disjoint_left.mp (L.pairwise_disjoint hn) (hcl hscl.1) hsi
  have heDis (n : Fin k) : Disjoint (L.pathDrawing n).U e :=
    disjoint_edge_subdrawing (L.isSubdrawing n).1 hl.1 (heL n)
  obtain ⟨j, x, hx, R, hW, hsR, hfirst⟩ := exists_initial_branch_to_linkage L hG hno i hl hb
  let W := GraphWalk.cons hl R
  let Q := walkDrawing G W
  have hQG : Q.IsSubdrawing G := walkDrawing_isSubdrawing G W
  have hsx : cylinderM1Point k i ≠ x := fun he => hsR (he.symm ▸ R.end_mem_support)
  have hQ : IsPathDrawing Q (cylinderM1Point k i) x :=
    isPathDrawing_walkDrawing_of_isSimple G hW hsx
  have heQ : e ∈ Q.E := by
    rw [walkDrawing_E]
    exact List.mem_cons_self
  obtain ⟨p, hp⟩ := hl.1.1
  have hpQ : p ∈ Q.U := (heQ.2.1 hp).1
  refine ⟨j, x, hx, Q, ⟨hQG, hQG.U_subset, hQ⟩, heQ, ?_⟩
  rintro y ⟨hyQ, hyL⟩
  obtain ⟨n, hyn⟩ := mem_iUnion.mp hyL
  apply path_intersection_subset_ends_of_vertices hQG (L.isSubdrawing n).1 hQ ?_
    ⟨p, hpQ, hp⟩ (heDis n) ⟨hyQ, hyn⟩
  rintro z ⟨hzQ, hzn⟩
  have hzW : z ∈ W.support := by
    change z ∈ (walkDrawing G W).V at hzQ
    rw [walkDrawing_V] at hzQ
    exact hzQ
  rcases List.mem_cons.mp hzW with hz | hz
  · exact Or.inl hz
  · exact Or.inr (mem_singleton_iff.mpr (hfirst z hz ⟨n, hzn⟩))

/-- If an initial vertex does not have valency one, it has a non-loop
edge outside its linkage path. Initial loops have already been
excluded by Reduction 2. -/
theorem exists_extra_initial_edge_of_valency_ne_one_of_no_reduction2
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    ∃ e ∈ G.E, ∃ b, b ≠ cylinderM1Point k i ∧
      G.toGraph.IsLink e (cylinderM1Point k i) b ∧ e ∉ (L.pathDrawing i).E := by
  classical
  have hex : ∃ e ∈ G.E, cylinderM1Point k i ∈ closure e ∧ e ∉ (L.pathDrawing i).E := by
    by_contra hn
    apply hval
    apply valency_eq_one_of_incident_edges_in_path (L.isPath i) (L.isSubdrawing i).1
    intro e he hs
    by_contra heP
    exact hn ⟨e, he, hs, heP⟩
  obtain ⟨e, he, hs, heP⟩ := hex
  have hsV : cylinderM1Point k i ∈ G.V :=
    (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
  obtain ⟨a, b, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet he
  have hsEnd : cylinderM1Point k i ∈ ({a, b} : Set ClosedCylinder) :=
    hl.2.2.2 ▸ ⟨hs, hsV⟩
  have hlink : ∃ b, G.toGraph.IsLink e (cylinderM1Point k i) b := by
    rcases mem_insert_iff.mp hsEnd with ha | hb
    · exact ⟨b, ha.symm ▸ hl⟩
    · have hb' := mem_singleton_iff.mp hb
      exact ⟨a, hb'.symm ▸ hl.symm⟩
  obtain ⟨v, hv⟩ := hlink
  have hvs : v ≠ cylinderM1Point k i := by
    intro hvs
    exact not_isLoop_at_initial_of_no_reduction2 L hG hno i e
      (by simpa only [hvs] using hv)
  exact ⟨e, he, v, hvs, hv, heP⟩

/-- The unreduced case follows by excluding the specified reduction. -/
theorem exists_extra_initial_edge_of_valency_ne_one
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    ∃ e ∈ G.E, ∃ b, b ≠ cylinderM1Point k i ∧
      G.toGraph.IsLink e (cylinderM1Point k i) b ∧ e ∉ (L.pathDrawing i).E := by
  exact exists_extra_initial_edge_of_valency_ne_one_of_no_reduction2 L hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) i hval

end GraphMinor.GM06
