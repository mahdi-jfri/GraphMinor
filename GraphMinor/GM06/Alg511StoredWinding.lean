module

public import GraphMinor.Compute.GM06Alg511StoredWinding
public import GraphMinor.GM06.Alg511ChosenWinding
import GraphMinor.GM06.Alg511CuffIndices
import GraphMinor.GM06.Alg511PathStarts
import Mathlib.Tactic

/-!
# The winding and realization of the fully stored initial linkage

For VI (5.11), page 134, select every linkage edge from the actual
flow successor pairs before computing any winding. The resulting
array determines all finite paths. Their actual interpretations form
one disjoint linkage, and the winding program reads precisely its
stored first path. Both the full linkage and its computed winding
are thus obtained from the same finite output.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- The actual RAM phase stores the full initial linkage and computes
its winding. Every path drawing retains its computed finite edges. -/
theorem alg511_storedWinding_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (c : Fin x.drawing.pathCount) (out : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (s : State) (hw : 2 < 2 ^ w) (hword : 1 + 3 * x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hends : x.drawing.endpoints.length < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.drawing.vertexCount) (hout : s.arrs outArr = out)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x.drawing)
    (hwords : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hcuff : s.arrs 1006 = x.drawing.outerCuff)
    (hcur : s.regs 40 = (rep.source c).val) (hN : s.regs 41 = x.drawing.vertexCount) :
    ∃ (s' : State) (t : ℕ)
      (W : ∀ i : Fin x.drawing.pathCount,
        GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i)
          (traceWalk hsys x.drawing.vertexCount (rep.source i)).1)
      (actual : ∀ i : Fin x.drawing.pathCount,
        GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val
          (rep.graph.vertex (traceWalk hsys x.drawing.vertexCount (rep.source i)).1).val)
      (L : CylinderLinkage x.drawing.pathCount G),
      Exec w gm06Alg511StoredWindingProg s s' t ∧
      t ≤ 49 + x.drawing.vertexCount * (127 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ≠ 1300 → arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      (s'.arrs 1300).length = x.drawing.vertexCount ∧ s'.regs 46 < x.drawing.pathCount ∧
      L.HasTheta ((((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
        (s'.regs 46 : ℤ) - (c.val : ℤ) : ℤ) : ℝ) / x.drawing.pathCount) ∧
      (∀ i, (W i).support = (traceWalk hsys x.drawing.vertexCount (rep.source i)).2.support ∧
        gm06Alg511LabelWalkDarts rep.graph.pairs (W i) =
          gm06Alg511ChosenDarts x.drawing (s'.arrs 1300) (W i).support) ∧
      (∀ i, (actual i).support = (W i).support.map (fun v => (rep.graph.vertex v).val) ∧
        alg511InterpretedWalkTurn rep.graph x.edgeTurns (actual i) =
          gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns (W i) ∧
        (actual i).edges = (W i).edges.map (fun e => (rep.graph.edge e).val) ∧
        L.pathDrawing i = walkDrawing G (actual i) ∧
        ParametrizesSet (L.curve i) (walkDrawing G (actual i)).U
          (rep.graph.vertex (rep.source i)).val
          (rep.graph.vertex (traceWalk hsys x.drawing.vertexCount (rep.source i)).1).val) := by
  classical
  have hn : x.drawing.vertexCount < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hchoiceLen, hchoice⟩ :=
    gm06Alg511LinkageEdgesProg_exec x.drawing rep.graph out hsys s (by omega)
      hword hsquare hends hlen hout hkeys hN
  obtain ⟨W, actual, L, hW, hactual, hL⟩ :=
    alg511_linkage_of_chosen_edges x rep hk out (s₁.arrs 1300) hsys hcount hchoice
  have hstarts := alg511_pathStarts_eq_cuff x.drawing hk rep.graph rep.source
    rep.flowA_exists_source rep.source_point rep.inner_mem_iff hsys hcount
  have hu : rep.source c ∈ pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out) := by
    rw [hstarts]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [rep.inner]
    exact List.mem_ofFn.mpr ⟨c, rfl⟩
  let p := abWalkOfStart hsys (rep.source c) hu
  have hchoiceWords : ∀ d ∈ s₁.arrs 1300, d < 2 ^ w := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hd
    have hjn : j < x.drawing.vertexCount := by rw [← hchoiceLen]; exact hj
    have hc := hchoice ⟨j, hjn⟩
    have hget : (s₁.arrs 1300).getD j x.drawing.endpoints.length = (s₁.arrs 1300)[j] := by simp [hj]
    simp only [hget] at hc
    split_ifs at hc with hsucc
    · exact hc.1.trans hends
    · rw [hc]
      exact hends
  have hturnlen : x.edgeTurns.length = rep.graph.pairs.length := by
    obtain ⟨_, _, _, _, h, _⟩ := rep.turns
    exact h
  have hendlen : x.drawing.endpoints.length = 2 * rep.graph.pairs.length := by
    have h := rep.graph.endpoints
    change x.drawing.endpoints = _ at h
    rw [h, gm06EndpointWords_length, List.length_map]
  have hsupport : (W c).support = p.walk.support := (hW c).1
  have hdarts : gm06Alg511LabelWalkDarts rep.graph.pairs (W c) =
      gm06Alg511ChosenDarts x.drawing (s₁.arrs 1300) (W c).support := by
    rw [hsupport]
    exact (hW c).2.2
  obtain ⟨s₂, t₂, he₂, ht₂, harr₂, hfinish, hpath, hturn⟩ :=
    gm06Alg511TraceChosenTurnProg_exec x.drawing rep.graph x.edgeTurns hturnlen out
      (s₁.arrs 1300) hsys (rep.source c) hu (W c) hsupport hdarts s₁ hw hword
      (by rw [hturnlen, ← hendlen]; exact hends) hproduct hchoiceLen hchoiceWords hlen
      ((hk₁.2 outArr (by decide)).trans hout) rfl
      ((hk₁.2 11 (by decide)).trans hwords) ((hk₁.1 40 (by decide)).trans hcur)
      ((hk₁.1 41 (by decide)).trans hN)
  have hactualSimple : (actual c).IsSimple := by
    change (actual c).support.Nodup
    rw [(hactual c).1]
    exact (hW c).2.1.map (Subtype.val_injective.comp rep.graph.vertex.injective)
  obtain ⟨j, hj, htheta⟩ := alg511_linkage_hasTheta_of_labelled_path x rep hk c
    p.finish p.finish_mem (W c) (actual c) hactualSimple (hactual c).2.1 L (hL c).2
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hindex⟩ := alg511_finishIndex_exec x rep hk j s₂
    (by omega) hn
    ((harr₂ 1006 (by decide) (by decide)).trans ((hk₁.2 1006 (by decide)).trans hcuff))
    (hfinish.trans (congrArg (fun v => v.val) hj.symm))
  have hchoicesFinal : s₃.arrs 1300 = s₁.arrs 1300 :=
    (hk₃.2 1300 (by simp)).trans (harr₂ 1300 (by decide) (by decide))
  refine ⟨s₃, t₁ + (t₂ + t₃), W, actual, L, .seq he₁ (.seq he₂ he₃), ?_, ?_,
    by rw [hchoicesFinal]; exact hchoiceLen, by rw [hindex]; exact j.isLt, ?_, ?_, ?_⟩
  · have hkn := rep.pathCount_le_vertexCount hk
    nlinarith only [ht₁, ht₂, ht₃, hkn]
  · intro arr ha₀ ha₁ ha₂
    rw [hk₃.2 arr (by simp), harr₂ arr ha₁ ha₂, hk₁.2 arr (by simpa using ha₀)]
  · simpa only [hindex, hk₃.1 21 (by decide), hk₃.1 22 (by decide), hturn] using htheta
  · intro i
    refine ⟨(hW i).1, ?_⟩
    rw [hchoicesFinal, (hW i).1]
    exact (hW i).2.2
  · intro i
    exact ⟨(hactual i).1, (hactual i).2.1, (hactual i).2.2, (hL i).1, (hL i).2⟩

end GraphMinor.GM06
