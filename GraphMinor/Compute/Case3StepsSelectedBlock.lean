module

public import GraphMinor.Compute.Algorithm99Case3Claim
public import GraphMinor.Compute.Case3StepsParsedBlock
public import GraphMinor.Compute.Case3StepsCompassGraph
public import GraphMinor.Compute.Case3StepsGatherBitsProg
import GraphMinor.Compute.Case3StepsParsedRuralDivision
import GraphMinor.Compute.Case3StepsParsedInterior
import GraphMinor.Compute.Case3StepsBlockSize
import GraphMinor.Compute.Case3StepsBlockWords
import GraphMinor.Compute.Case3StepsGroupingBounds
import GraphMinor.Compute.Algorithm99Handoff

/-!
# Semantics of a completed selected-member block

A valid (8.6) output and a complete retained record history determine the
block. Its parser restores the original wall, its society, the full rural
division, and the decompositions of its interior members. Its length is
linear and every word is bounded by the ambient counts. These facts give
the exact frozen output-(a) specification once the arrays are written.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The complete permitted record history gives the exact frozen
output-(a) semantics, together with the bounds needed to write it. -/
theorem case3SelectedBlock_outputA {h N w B : ℕ} (G : MultiDigraph N)
    (X : Finset (Fin N)) (W : WallOfHeight h (G.deleteVertices X))
    (h2 : 2 ≤ h) (heven : Even h) (hW : W.IsValid) (hflat : W.IsFlatWall h2)
    (S : Finset (Fin N)) (hS : S = W.compassFinset)
    (D : MultiDigraph S.card) (hD : HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W))
    (om : List (Fin S.card)) (hom : om.Nodup)
    (homEq : HEq om (List.ofFn (compactCorner W h2 heven))) :
    let x := case3SimpleSocietyInput D om hom
    ∀ (d : Alg86DivisionOutput x), IsValidAlg86DivisionOutput x d →
    ∀ entries : List (Case3SelectedGroup x d.core.Z × List ℕ),
    (entries.map Prod.fst).Nodup →
    (∀ i, i ∈ entries.map Prod.fst) →
    (∀ q ∈ entries,
      (Disjoint (case3SelectedMember x d.core.Z q.1).verts
          (case3PullbackBits (S.orderEmbOfFin rfl) W.perimeterFinset) ∧
        IsValidBranchDecompCode B (case3CompactMember x D d.core.Z q.1) q.2) ∨
      (¬ Disjoint (case3SelectedMember x d.core.Z q.1).verts
          (case3PullbackBits (S.orderEmbOfFin rfl) W.perimeterFinset) ∧
        q.2 = case3PlaceholderCode (case3CompactMember x D d.core.Z q.1).numEdges)) →
    let members := case3SelectedRecordList x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding entries
    let Kv := List.ofFn (fun u : Fin S.card => ((S.orderEmbOfFin rfl).toEmbedding u).1)
    let Ke := D.multiEdgeTriples.map (origEdgeEmb (S.orderEmbOfFin rfl).toEmbedding (S.orderEmbOfFin rfl).toEmbedding.injective)
    let corners := List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)
    let block := encCase3Block W Kv Ke corners members
    (members.flatMap Case3MemberRecord.enc).length ≤ 24 * (N + (G.deleteVertices X).numEdges + 1) →
    N < 2 ^ w → (G.deleteVertices X).numEdges < 2 ^ w →
    2 * (G.deleteVertices X).numEdges + 1 < 2 ^ w →
    N + (G.deleteVertices X).numEdges + 1 < 2 ^ w →
    h < 2 ^ w → elemWallNumVerts h < 2 ^ w → (elemWallEdges h).length < 2 ^ w →
    block.length ≤ 40 * (N + (G.deleteVertices X).numEdges + 1) ∧
    (∀ z ∈ block, z < 2 ^ w) ∧
    ∀ (a_out a_wall : ℕ) (s : State),
      s.arrs a_out = 2 :: (bitSetList X ++ block) → s.arrs a_wall = block →
      IsCase3StepsOutputA h B G X W h2 heven hW 40 w a_out a_wall s := by
  intro x d hd entries hnd hcover hcodes members Kv Ke corners block hrec hN hm ht hc hh hv he
  classical
  let pw := W.toParsedWallSection h2 heven hW rfl
  have hR : GM13.IsRuralDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z) := by
    subst S
    cases hD
    cases homEq
    exact case3CompactSelectedMembers_isRuralDivision (G.deleteVertices X) W h2 heven hW d hd
  have hbase : relabelGraph (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective) D.toGMDigraph.toGraph ≤ delGraph G X := by
    subst S
    cases hD
    exact case3ParsedWall_compass_le G X pw
  have hDc : D.numEdges ≤ (G.deleteVertices X).numEdges := by
    subst S
    cases hD
    exact case3NumEdges_induce_le (G.deleteVertices X) (compassEmb W).toEmbedding
  have hcorner : ∀ i : Fin 4, ∃ u : Fin S.card,
      (S.orderEmbOfFin rfl u).1 = (pw.W.branchVert (elemWallCornerIdx pw.h2 i)).1 := by
    subst S
    intro i
    exact ⟨compactCorner W h2 heven i, congrArg Fin.val (compassEmb_compactCorner W h2 heven i)⟩
  have hcodeforms : ∀ q ∈ entries,
      IsValidBranchDecompCode B (case3CompactMember x D d.core.Z q.1) q.2 ∨
        q.2 = case3PlaceholderCode (case3CompactMember x D d.core.Z q.1).numEdges := by
    intro q hq
    rcases hcodes q hq with hq | hq
    · exact Or.inl hq.2
    · exact Or.inr hq.2
  obtain ⟨p, hpw, hpv, hpe, hpc, hpm, hparse⟩ :=
    case3SelectedBlock_parses G X pw x D rfl d.core.Z hR.isDivision
      (S.orderEmbOfFin rfl).toEmbedding hbase hDc hcorner entries hnd hcodeforms
  have hpc' : p.corners = corners := hpc
  have hparse' : parseCase3Block (G.deleteVertices X) X block = some p := by
    simpa only [block, Kv, Ke, members, pw, WallOfHeight.toParsedWallSection, hpv, hpe, hpc', hpm] using hparse
  have hblocklen : block.length ≤ 40 * (N + (G.deleteVertices X).numEdges + 1) :=
    case3Block_length_le W hW Kv Ke corners members
      (by simpa only [Kv, List.length_ofFn, Fintype.card_fin] using Finset.card_le_univ S)
      (by simpa only [Ke, List.length_map, D.length_multiEdgeTriples] using hDc)
      (List.length_ofFn ..) hrec
  have hpheight : p.wallSec.h = h := congrArg (fun q => q.h) hpw
  have hpwallenc : p.wallSec.W.encList = W.encList := congrArg (fun q => q.W.encList) hpw
  have hblockwords : ∀ z ∈ block, z < 2 ^ w := by
    have hpwords := case3ParsedBlock_words G X p hN hm ht hc
      (by rw [hpheight]; exact hh) (by rw [hpheight]; exact hv) (by rw [hpheight]; exact he)
    simpa only [block, Kv, Ke, members, encCase3Block, hpwallenc, hpv, hpe, hpc', hpm] using hpwords
  refine ⟨hblocklen, hblockwords, ?_⟩
  intro a_out a_wall s hout hwall
  have hpwall : p.toGMWall = W.toGMWall h2 heven hW := by
    exact congrArg (fun q => q.W.toGMWall q.h2 q.he q.hW) hpw
  have hpv' : p.K_vList = List.ofFn (fun u : Fin (compassCard p.wallSec.W) => (compassEmb p.wallSec.W u).1) := by
    subst S
    have hq := congrArg (fun q : ParsedWallSection (G.deleteVertices X) X =>
      List.ofFn (fun u : Fin (compassCard q.W) => (compassEmb q.W u).1)) hpw
    exact hpv.trans hq.symm
  have hpe' : p.K_eList = (case3CompactCompassMultigraph (G.deleteVertices X) p.wallSec.W).multiEdgeTriples.map
      (origEdgeEmb (compassEmb p.wallSec.W) (compassEmb p.wallSec.W).injective) := by
    subst S
    cases hD
    have hq := congrArg (fun q : ParsedWallSection (G.deleteVertices X) X =>
      (case3CompactCompassMultigraph (G.deleteVertices X) q.W).multiEdgeTriples.map
        (origEdgeEmb (compassEmb q.W) (compassEmb q.W).injective)) hpw
    exact hpe.trans hq.symm
  have hsoc : p.toSociety = relabelSociety
      (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective) (case3MultigraphSociety D om hom) := by
    have hpSoc := case3ParsedBlock_toSociety G X p hpv' hpe'
    subst S
    cases hD
    cases homEq
    have hq := congrArg (fun q : ParsedWallSection (G.deleteVertices X) X =>
      case3CompassSociety (G.deleteVertices X) q.W q.h2 q.he q.hW) hpw
    exact hpSoc.trans hq
  have hrural := case3ParsedBlock_isRuralDivision D om hom d.core.Z hR
    (S.orderEmbOfFin rfl).toEmbedding G X p hbase entries hcover hpm
  change GM13.IsRuralDivision (relabelSociety
    (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
    (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
    (case3MultigraphSociety D om hom)) p.toDivision at hrural
  rw [← hsoc] at hrural
  have hinterior := case3ParsedBlock_interior_decompositions D om hom d.core.Z hR.isDivision
    (S.orderEmbOfFin rfl).toEmbedding G X p W h2 heven hW hpwall hbase entries hpm
    (fun q hq hint => by
      rcases hcodes q hq with hq | hq
      · exact hq.2
      · exact False.elim (hq.1 hint)) block hparse'
  have hdel : delGraph G X = GM09.deleteVertices G.toGMDigraph.toGraph X.toNatSet := by
    rw [delGraph_eq, GM13.Digraph.toGraph_deleteVertices]
  refine ⟨Kv, Ke, corners, members, hout, hwall, hblocklen, hblockwords, ?_⟩
  unfold case3Decoder case3WallOfDel case3SocietyOfDel case3DivisionOfDel
  dsimp only
  rw [hparse']
  dsimp only
  refine ⟨hpwall, ?_, ?_, ?_, hrural, ?_⟩
  · rw [hpwall]
    rfl
  · rw [hpwall, ← hdel]
    exact W.isFlatWallIn_delGraph_of_isFlatWall h2 heven hW hflat rfl
  · rw [← hdel]
    exact case3ParsedBlock_isWallSociety G X p hpv' hpe'
  · intro A hA
    exact hinterior A hA

end GraphMinor.Compute
