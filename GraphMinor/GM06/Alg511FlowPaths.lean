module

public import GraphMinor.GM06.Alg511FlowWalks
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Drawing the paths returned by the initial flow search

The maximum-flow step of VI (5.11), page 134, returns disjoint simple
paths in the finite label graph. Lift their walks through the supplied
bijections, then use their edge closures as path subdrawings. Their
vertex sets are exactly the labelled supports. Two subdrawings with
disjoint vertex sets cannot meet: a shared interior point would force
a shared edge and hence a shared endpoint. Thus the returned paths
are disjoint as subsets of the cylinder, not just at their vertices.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.GM11 GraphMinor.Surface Set

private theorem vertex_of_subdrawing_point {G P : Drawing ClosedCylinder}
    (hPG : P.IsSubdrawing G) {v : ClosedCylinder} (hv : v ∈ P.U) (hvG : v ∈ G.V) :
    v ∈ P.V := by
  by_contra hvP
  obtain ⟨e, he, hve⟩ := P.exists_edge_of_mem hv hvP
  exact ((hPG.2 he).2.1 hve).2 hvG

/-- Disjoint vertex sets of subdrawings imply disjoint point sets. -/
theorem alg511_disjoint_subdrawing_pointSets {G P Q : Drawing ClosedCylinder}
    (hPG : P.IsSubdrawing G) (hQG : Q.IsSubdrawing G) (hV : Disjoint P.V Q.V) :
    Disjoint P.U Q.U := by
  apply disjoint_left.mpr
  intro v hvP hvQ
  by_cases hvG : v ∈ G.V
  · exact disjoint_left.mp hV (vertex_of_subdrawing_point hPG hvP hvG)
      (vertex_of_subdrawing_point hQG hvQ hvG)
  · obtain ⟨e, heP, hve⟩ := P.exists_edge_of_mem hvP (fun h => hvG (hPG.1 h))
    obtain ⟨f, hfQ, hvf⟩ := Q.exists_edge_of_mem hvQ (fun h => hvG (hQG.1 h))
    have hef : e = f := G.edge_eq_of_mem (hPG.2 heP) (hQG.2 hfQ) hve hvf
    subst f
    obtain ⟨a, b, habP⟩ := P.toGraph.exists_isLink_of_mem_edgeSet heP
    have habG := (hPG.isLink_iff heP).mp habP
    have habQ := (hQG.isLink_iff hfQ).mpr habG
    exact disjoint_left.mp hV habP.left_mem habQ.left_mem

/-- A finite simple flow path gives a path subdrawing whose vertices
are exactly the images of the path's supplied labels. -/
theorem alg511_exists_pathDrawing_of_flowPath (x : GM06Alg511Input)
    {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    {a b : Fin x.vertexCount} (p : x.flowGraph.Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    ∃ P : Drawing ClosedCylinder,
      P.IsSubdrawing G ∧ IsPathDrawing P (rep.vertex a).val (rep.vertex b).val ∧
      P.V = {v | ∃ i ∈ p.support, (rep.vertex i).val = v} := by
  obtain ⟨W, hsimple, hW⟩ := alg511_exists_simple_graphWalk_of_flowPath x rep p hp
  have hinj : Function.Injective (fun i => (rep.vertex i).val) :=
    Subtype.val_injective.comp rep.vertex.injective
  refine ⟨walkDrawing G W, walkDrawing_isSubdrawing G W,
    isPathDrawing_walkDrawing_of_isSimple G hsimple (hinj.ne hab), ?_⟩
  rw [walkDrawing_V, hW]
  ext v
  exact List.mem_map

/-- A family of vertex-disjoint finite flow paths gives disjoint
actual path subdrawings, with the same supplied starting and ending labels. -/
theorem alg511_exists_disjoint_pathDrawings {k : ℕ} (x : GM06Alg511Input)
    {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (a b : Fin k → Fin x.vertexCount) (paths : ∀ i, x.flowGraph.Walk (a i) (b i))
    (hsimple : ∀ i, (paths i).IsPath) (hne : ∀ i, a i ≠ b i)
    (hdisj : ∀ i j, i ≠ j → List.Disjoint (paths i).support (paths j).support) :
    ∃ P : Fin k → Drawing ClosedCylinder,
      (∀ i, (P i).IsSubdrawing G ∧
        IsPathDrawing (P i) (rep.vertex (a i)).val (rep.vertex (b i)).val ∧
        (P i).V = {v | ∃ t ∈ (paths i).support, (rep.vertex t).val = v}) ∧
      Pairwise (fun i j => Disjoint (P i).U (P j).U) := by
  classical
  choose P hPG hP hPV using fun i =>
    alg511_exists_pathDrawing_of_flowPath x rep (paths i) (hsimple i) (hne i)
  refine ⟨P, fun i => ⟨hPG i, hP i, hPV i⟩, ?_⟩
  intro i j hij
  apply alg511_disjoint_subdrawing_pointSets (hPG i) (hPG j)
  apply disjoint_left.mpr
  intro v hvi hvj
  rw [hPV i] at hvi
  rw [hPV j] at hvj
  obtain ⟨u, hu, huv⟩ := hvi
  obtain ⟨t, ht, htv⟩ := hvj
  have hut : u = t := rep.vertex.injective (Subtype.val_injective (huv.trans htv.symm))
  exact hdisj i j hij hu (hut ▸ ht)

end GraphMinor.GM06
