module

public import GraphMinor.Compute.GM06Alg511BinaryGraphSetup
public import GraphMinor.Compute.GM06Alg511StoredPathRows
public import GraphMinor.GM06.Alg511BinaryInputRep
public import GraphMinor.GM06.Alg511StoredPathEncoding
public import GraphMinor.GM06.Alg511NormalizedWalk
import GraphMinor.GM06.Alg511PathStarts
import GraphMinor.GM06.Alg511ChosenLinkage
import GraphMinor.GM06.Alg511CuffIndices
import Mathlib.Tactic

/-!
# Storing the computed initial linkage from binary input

Prepare the ordinary graph keys and select an actual directed edge
for every raw-flow successor. Assemble the corresponding actual
paths, then run the verified path-table program in the given source
order. The returned ordinary-dart table encodes that same linkage.
The selected first path retains its actual curve, normalized turn
and terminal label for the binary winding calculation.

All geometric witnesses interpret computed paths. None is supplied
in the input. This is the initial-linkage step of VI (5.11), page 134,
with graph-size word bounds and no integer-magnitude word premise.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Select all initial linkage edges from raw maximum flow and
store the corresponding ordinary path rows in source cuff order. -/
def gm06Alg511BinaryStoredPathsProg : Cmd :=
  .seq gm06Alg511BinaryLinkageEdgesProg gm06Alg511StoredPathRowsProg

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface GraphMinor.GM11

/-- The executed initial path-table construction returns an actual
encoded linkage and the exact first path used to compute its winding.
Every supplied drawing and binary table is retained. -/
theorem alg511_binary_storedPaths_exec {w : ℕ} (x : GM06Alg511BinaryInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511BinaryDrawingRep x G) (hk : 0 < x.pathCount)
    (out : List ℕ)
    (hsys : IsValidPathSystem x.toWindingInput.drawing.flowGraph
      x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (hcount : (pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out)).card = x.pathCount)
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w) (hends : x.endpoints.length < 2 ^ w)
    (hcap : 1 + x.pathCount + x.pathCount * x.vertexCount < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount) (hout : s.arrs outArr = out)
    (htables : gm06Alg511BinaryLoadedTables x s) (hkReg : s.regs 52 = x.pathCount) :
    ∃ (t : State) (u : ℕ) (L : CylinderLinkage x.pathCount G) (rows : List (List ℕ))
      (b : Fin x.vertexCount)
      (W : GraphWalk (gm06Alg511LabelGraph rep.graphTurn.graph.pairs) (rep.graphTurn.source ⟨0, hk⟩) b)
      (actual : GraphWalk G.toGraph (rep.graphTurn.graph.vertex (rep.graphTurn.source ⟨0, hk⟩)).val
        (rep.graphTurn.graph.vertex b).val),
      Exec w gm06Alg511BinaryStoredPathsProg s t u ∧
      u ≤ 48 + 37 * x.endpoints.length + 12 * x.outerCuff.length +
        x.vertexCount * (38 + 13 * x.endpoints.length) +
        x.pathCount * (208 + 150 * x.vertexCount + 100 * (1 + x.pathCount + x.pathCount * x.vertexCount)) ∧
      gm06Alg511BinaryLoadedTables x t ∧ t.regs 52 = x.pathCount ∧ t.regs 41 = x.vertexCount ∧
      t.arrs outArr = out ∧ t.arrs 1006 = x.outerCuff ∧ t.arrs 8 = gm06EncodeRows rows ∧
      GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows ∧
      rows[0]?.getD [] = gm06Alg511LabelWalkDarts rep.graphTurn.graph.pairs W ∧
      b = (traceWalk hsys x.vertexCount (rep.graphTurn.source ⟨0, hk⟩)).1 ∧
      b ∈ x.toWindingInput.drawing.flowInput.B ∧ actual.IsSimple ∧
      alg511InterpretedWalkTurn rep.graphTurn.graph x.toWindingInput.edgeTurns actual =
        gm06Alg511LabelWalkTurn rep.graphTurn.graph.pairs x.toWindingInput.edgeTurns W ∧
      ParametrizesSet (L.curve ⟨0, hk⟩) (walkDrawing G actual).U
        (rep.graphTurn.graph.vertex (rep.graphTurn.source ⟨0, hk⟩)).val (rep.graphTurn.graph.vertex b).val ∧ t.regs 90 = s.regs 90 := by
  classical
  have hn : x.vertexCount < 2 ^ w := by omega
  have hkfit : x.pathCount < 2 ^ w := (rep.graphTurn.pathCount_le_vertexCount hk).trans_lt hn
  have houter : x.outerCuff = List.ofFn (fun i => (rep.graphTurn.target i).val) := rep.graphTurn.outer
  have hinner : x.innerCuff = List.ofFn (fun i => (rep.graphTurn.source i).val) := rep.graphTurn.inner
  have houterLen : x.outerCuff.length = x.pathCount := by rw [houter, List.length_ofFn]; rfl
  have houterWords : ∀ v ∈ x.outerCuff, v < 2 ^ w := by
    intro v hv
    rw [houter] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.graphTurn.target i).isLt.trans hn
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, htables₁, hN₁, ho₁, hchoiceLen, hchoice⟩ :=
    gm06Alg511BinaryLinkageEdgesProg_exec x rep.graphTurn.graph out hsys s hw hword hsquare hends
      (houterLen ▸ hkfit) houterWords hlen hout htables
  obtain ⟨W, actual, L, hW, hactual, hL⟩ := alg511_linkage_of_chosen_edges x.toWindingInput rep.graphTurn hk out
    (s₁.arrs 1300) hsys hcount hchoice
  have hchoiceWords : ∀ d ∈ s₁.arrs 1300, d < 2 ^ w := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
    have hin : i < x.vertexCount := by rw [← hchoiceLen]; exact hi
    have hh := hchoice ⟨i, hin⟩
    have hget : (s₁.arrs 1300).getD i x.endpoints.length = (s₁.arrs 1300)[i] := by simp [hi]
    simp only [hget] at hh
    split_ifs at hh with hs
    · exact hh.1.trans hends
    · rw [hh]; exact hends
  have hstarts := alg511_pathStarts_eq_cuff x.toWindingInput.drawing hk rep.graphTurn.graph rep.graphTurn.source
    rep.graphTurn.flowA_exists_source rep.graphTurn.source_point rep.graphTurn.inner_mem_iff hsys hcount
  have hu (i : Fin x.pathCount) : rep.graphTurn.source i ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out) := by
    have hA : rep.graphTurn.source i ∈ x.toWindingInput.drawing.flowInput.A :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have hmem : (rep.graphTurn.source i).val ∈ List.ofFn (fun j => (rep.graphTurn.source j).val) :=
          List.mem_ofFn.mpr ⟨i, rfl⟩
        exact rep.graphTurn.inner ▸ hmem⟩
    exact hstarts.symm ▸ hA
  let sources := List.ofFn rep.graphTurn.source
  have hsourceWords : s₁.arrs 1210 = sources.map Fin.val := by
    have hinput : s₁.arrs 1210 = x.innerCuff := htables₁.1 ⟨3, by decide⟩
    rw [hinput, hinner]
    simp only [sources, List.map_ofFn, Function.comp_def]
  have hus : ∀ u ∈ sources, u ∈ pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out) := by
    intro u hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
    exact hu i
  obtain ⟨t, u₂, he₂, ht₂, hk₂, hrows₂⟩ := gm06Alg511StoredPathRowsProg_exec x.toWindingInput.drawing out (s₁.arrs 1300)
    hsys sources hus s₁ (by omega) hword (by simpa only [sources, List.length_ofFn, GM06Alg511BinaryInput.toWindingInput] using hcap)
    hchoiceLen hchoiceWords hlen ((hk₁.2 outArr (by decide)).trans hout) rfl hsourceWords hN₁
  let finish := fun i => (traceWalk hsys x.vertexCount (rep.graphTurn.source i)).1
  have hsimple (i : Fin x.pathCount) : (W i).IsSimple := (hW i).2.1
  have hflow (i : Fin x.pathCount) : (W i).support = (abWalkOfStart hsys (rep.graphTurn.source i) (hu i)).walk.support := (hW i).1
  have hdarts (i : Fin x.pathCount) : gm06Alg511LabelWalkDarts rep.graphTurn.graph.pairs (W i) =
      gm06Alg511ChosenDarts x.toWindingInput.drawing (s₁.arrs 1300) (W i).support := by
    rw [(hW i).1]
    exact (hW i).2.2
  have hfinish (i : Fin x.pathCount) : L.curve i 1 = (rep.graphTurn.graph.vertex (finish i)).val := (hL i).2.2.2.2
  let rows := gm06Alg511StoredPathRows x.toWindingInput.drawing out (s₁.arrs 1300) sources
  have henc : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels
      rep.graphTurn.graph.edgeLabels rows := alg511_storedPathRows_encode_linkage rep.graphTurn out _ hsys hu finish W actual L hsimple
    (fun i => (hactual i).1) (fun i => (hactual i).2.2) (fun i => (hL i).1) hfinish hflow hdarts
  have hrow0 : rows[0]?.getD [] = gm06Alg511LabelWalkDarts rep.graphTurn.graph.pairs (W ⟨0, hk⟩) := by
    have hrowCount : rows.length = x.pathCount := by
      simpa only [GM06Alg511BinaryInput.toWindingInput] using henc.1
    rw [List.getElem?_eq_getElem (by omega : 0 < rows.length), Option.getD_some]
    change ((List.ofFn rep.graphTurn.source).map (fun u => gm06Alg511StoredPathRow x.toWindingInput.drawing out (s₁.arrs 1300) u.val))[0]'(by simpa only [List.length_map, List.length_ofFn, GM06Alg511BinaryInput.toWindingInput] using hk) = _
    simp only [List.getElem_map, List.getElem_ofFn]
    change gm06Alg511StoredPathRow x.toWindingInput.drawing out (s₁.arrs 1300) (rep.graphTurn.source ⟨0, hk⟩).val = _
    exact (gm06Alg511StoredPathRow_eq_chosen x.toWindingInput.drawing out (s₁.arrs 1300) hsys _ (hu ⟨0, hk⟩)).trans
      ((congrArg (gm06Alg511ChosenDarts x.toWindingInput.drawing (s₁.arrs 1300)) (hflow ⟨0, hk⟩).symm).trans (hdarts ⟨0, hk⟩).symm)
  have hsimpleActual : (actual ⟨0, hk⟩).IsSimple := by
    change (actual ⟨0, hk⟩).support.Nodup
    rw [(hactual ⟨0, hk⟩).1]
    exact (hsimple ⟨0, hk⟩).map (Subtype.val_injective.comp rep.graphTurn.graph.vertex.injective)
  have htables₂ : gm06Alg511BinaryLoadedTables x t := htables₁.frame
    (by intro i; apply hk₂.2; fin_cases i <;> decide) (hk₂.2 1000 (by decide)) (hk₂.2 1001 (by decide))
  refine ⟨t, u₁ + u₂, L, rows, finish ⟨0, hk⟩, W ⟨0, hk⟩, actual ⟨0, hk⟩, .seq he₁ he₂, ?_, htables₂,
    (hk₂.1 52 (by decide)).trans ((hk₁.1 52 (by decide)).trans hkReg),
    (hk₂.1 41 (by decide)).trans hN₁, (hk₂.2 outArr (by decide)).trans ((hk₁.2 outArr (by decide)).trans hout),
    (hk₂.2 1006 (by decide)).trans ho₁, hrows₂, henc, hrow0, rfl,
    (abWalkOfStart hsys (rep.graphTurn.source ⟨0, hk⟩) (hu ⟨0, hk⟩)).finish_mem,
    hsimpleActual, (hactual ⟨0, hk⟩).2.1, (hL ⟨0, hk⟩).2,
    (hk₂.1 90 (by decide)).trans (hk₁.1 90 (by decide))⟩
  simp only [sources, List.length_ofFn] at ht₂
  change u₂ ≤ 12 + x.pathCount * (208 + 150 * x.vertexCount + 100 * (1 + x.pathCount + x.pathCount * x.vertexCount)) at ht₂
  omega

end GraphMinor.GM06
