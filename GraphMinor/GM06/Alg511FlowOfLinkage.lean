module

public import GraphMinor.GM06.Alg511FlowWalksBack
public import GraphMinor.Compute.GM06Alg511Flow
import Mathlib.Tactic

/-!
# A cylinder linkage gives paths in the initial flow graph

To justify the negative maximum-flow branch of VI (5.11), page 134,
label the simple walks in each actual linkage path. The cuff
interpretation puts their starts and ends in the finite source and
target sets. Their supports are disjoint because the actual linkage
paths are disjoint. A separator smaller than the requested path count
therefore rules out a cylinder linkage by weak Menger duality.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

/-- Label each actual linkage path to obtain the finite path family
sought by the initial maximum-flow search. -/
theorem alg511_exists_flowPaths_of_linkage (x : GM06Alg511Input)
    {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (hsource : ∀ a : Fin x.vertexCount,
      a.val ∈ x.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.pathCount)
    (htarget : ∀ b : Fin x.vertexCount,
      b.val ∈ x.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 x.pathCount)
    (L : CylinderLinkage x.pathCount G) :
    ∃ P : Fin x.pathCount → ABWalk x.flowGraph x.flowInput.A x.flowInput.B,
      PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath := by
  classical
  have hex : ∀ i : Fin x.pathCount,
      ∃ p : ABWalk x.flowGraph x.flowInput.A x.flowInput.B,
        p.walk.IsPath ∧ ∀ a ∈ p.walk.support, (rep.vertex a).val ∈ (L.pathDrawing i).V := by
    intro i
    obtain ⟨W, hs, hV, _⟩ := (L.isPath i).1
    have hstartV : cylinderM1Point x.pathCount i ∈ G.V :=
      (L.isSubdrawing i).1.1 (W.mem_vertexSet_of_mem_support W.start_mem_support)
    have hendV : L.curve i 1 ∈ G.V :=
      (L.isSubdrawing i).1.1 (W.mem_vertexSet_of_mem_support W.end_mem_support)
    obtain ⟨a, ha⟩ := rep.vertex.surjective ⟨cylinderM1Point x.pathCount i, hstartV⟩
    obtain ⟨b, hb⟩ := rep.vertex.surjective ⟨L.curve i 1, hendV⟩
    have ha' : (rep.vertex a).val = cylinderM1Point x.pathCount i := congrArg Subtype.val ha
    have hb' : (rep.vertex b).val = L.curve i 1 := congrArg Subtype.val hb
    obtain ⟨W', hsupport, _⟩ := (L.isSubdrawing i).1.exists_walk_up W
    have hs' : W'.IsSimple := by
      change W'.support.Nodup
      rw [hsupport]
      exact hs
    obtain ⟨p, hp, hpsupport⟩ :=
      alg511_exists_flowPath_of_simple_graphWalk x rep W' a b ha' hb' hs'
    have haA : a ∈ x.flowInput.A := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hsource a).mpr ?_⟩
      rw [ha']
      exact ⟨i, rfl⟩
    have hbB : b ∈ x.flowInput.B := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (htarget b).mpr ?_⟩
      rw [hb']
      exact L.curve_one_mem i
    refine ⟨⟨a, b, haA, hbB, p⟩, hp, ?_⟩
    intro c hc
    rw [hV]
    rw [← hsupport, ← hpsupport]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  choose P hP hPV using hex
  refine ⟨P, ?_, hP⟩
  intro i j hij a hai haj
  exact disjoint_left.mp (L.pairwise_disjoint hij)
    ((L.pathDrawing i).V_subset_U (hPV i a hai))
    ((L.pathDrawing j).V_subset_U (hPV j a haj))

/-- A smaller separator returned by the initial flow search rules out
an actual cylinder linkage under the supplied cuff interpretation. -/
theorem alg511_no_linkage_of_flow_separator (x : GM06Alg511Input)
    {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (hsource : ∀ a : Fin x.vertexCount,
      a.val ∈ x.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.pathCount)
    (htarget : ∀ b : Fin x.vertexCount,
      b.val ∈ x.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 x.pathCount)
    (C : Finset (Fin x.vertexCount)) (hcard : C.card < x.pathCount)
    (hsep : IsABSeparator x.flowGraph x.flowInput.A x.flowInput.B C) :
    ¬ Nonempty (CylinderLinkage x.pathCount G) := by
  rintro ⟨L⟩
  obtain ⟨P, hP, _⟩ := alg511_exists_flowPaths_of_linkage x rep hsource htarget L
  exact Nat.not_le_of_gt hcard (card_le_of_disjoint_walks_and_separator P hP hsep)

end GraphMinor.GM06
