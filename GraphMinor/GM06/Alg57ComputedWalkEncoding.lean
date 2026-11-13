module

public import GraphMinor.GM06.Alg57CurrentPhaseInputs

/-!
# Exact encodings of projected and spliced walks

In VI (5.7), page 133, APPLY_4 writes the projected directed
candidate row followed by the old path's suffix. The following
walk constructions keep those exact rows. Splitting an encoded
walk takes and drops the same number of words. Appending walks
appends their encodings. A numeric dart walk with the stated
active endpoints gives an encoded graph walk with exactly its
listed support and edges.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Surface
universe u v

namespace GM06WalkDartEncoding
variable {n : ℕ} {α : Type u} {β : Type v} {Gr : Graph α β}
  {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
  {edge : Fin tagged.length → β}

/-- Concatenating encoded walks concatenates their directed rows. -/
theorem append {a b c : α} {A : GraphWalk Gr a b} {B : GraphWalk Gr b c}
    {ra rb : List ℕ} (hA : GM06WalkDartEncoding Gr tagged vertex edge A ra)
    (hB : GM06WalkDartEncoding Gr tagged vertex edge B rb) :
    GM06WalkDartEncoding Gr tagged vertex edge (A.append B) (ra ++ rb) := by
  induction hA with
  | nil => exact hB
  | cons hd ha he ht hh hr ih => exact .cons hd ha he ht hh (ih hB)

/-- Splitting an encoded walk at a position retains exactly the
prefix and suffix of its directed row and support. -/
theorem exists_split_take_drop {a b : α} {W : GraphWalk Gr a b} {row : List ℕ}
    (h : GM06WalkDartEncoding Gr tagged vertex edge W row) (q : ℕ) (hq : q ≤ row.length) :
    ∃ (z : α) (A : GraphWalk Gr a z) (B : GraphWalk Gr z b),
      GM06WalkDartEncoding Gr tagged vertex edge A (row.take q) ∧
      GM06WalkDartEncoding Gr tagged vertex edge B (row.drop q) ∧
      W.support[q]? = some z ∧ A.support = W.support.take (q + 1) ∧
      B.support = W.support.drop q ∧ A.edges = W.edges.take q ∧ B.edges = W.edges.drop q := by
  induction h generalizing q with
  | nil hx =>
    have hq0 : q = 0 := by simpa only [List.length_nil, Nat.le_zero] using hq
    subst q
    exact ⟨_, .nil hx, .nil hx, .nil hx, .nil hx, rfl, rfl, rfl, rfl, rfl⟩
  | @cons a b c e hl R row d hd ha he ht hh hr ih =>
    cases q with
    | zero =>
      refine ⟨a, .nil hl.left_mem, .cons hl R, .nil hl.left_mem,
        .cons hd ha he ht hh hr, rfl, rfl, rfl, rfl, rfl⟩
    | succ q =>
      obtain ⟨z, A, B, hA, hB, hz, hAS, hBS, hAE, hBE⟩ := ih q (by
        simpa only [List.length_cons, Nat.succ_le_succ_iff] using hq)
      refine ⟨z, .cons hl A, B, .cons hd ha he ht hh hA, hB, ?_, ?_, ?_, ?_, ?_⟩
      · exact hz
      · simpa only [GraphWalk.support_cons, List.take_succ_cons] using congrArg (List.cons a) hAS
      · exact hBS
      · simpa only [GraphWalk.edges_cons, List.take_succ_cons] using congrArg (List.cons e) hAE
      · exact hBE

/-- A numeric dart walk with active, oriented permanent labels is
realized by a graph walk with that exact projected word row. -/
theorem exists_of_dartWalk {tail head : ℕ → ℕ} {lab : ℕ → α} {edgeOf : ℕ → β}
    {project : ℕ → ℕ} {s t : ℕ} {ds : List ℕ}
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      Gr.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hw : GM06DartWalk tail head s ds t) (ht : lab t ∈ Gr.vertexSet)
    (hlabels : ∀ d ∈ ds, ∃ hd : project d < 2 * tagged.length,
      (tagged[project d / 2]'(by omega)).2 = 1 ∧
      edge ⟨project d / 2, by omega⟩ = edgeOf d ∧
      vertex (gm06DartTail tagged ⟨project d, hd⟩) = lab (tail d) ∧
      vertex (gm06DartHead tagged ⟨project d, hd⟩) = lab (head d)) :
    ∃ W : GraphWalk Gr (lab s) (lab t),
      GM06WalkDartEncoding Gr tagged vertex edge W (ds.map project) ∧
      W.support = (gm06WalkVertices head s ds).map lab ∧ W.edges = ds.map edgeOf := by
  induction hw with
  | nil z => exact ⟨.nil ht, .nil ht, rfl, rfl⟩
  | @cons s t d ds htail hwalk ih =>
    obtain ⟨W, hW, hWS, hWE⟩ := ih ht (fun q hq => hlabels q (List.mem_cons_of_mem _ hq))
    obtain ⟨hd, ha, he, htd, hhd⟩ := hlabels d List.mem_cons_self
    have hl := gm06Dart_isLink Gr tagged vertex edge hlinks ⟨project d, hd⟩ ha
    rw [he, htd, hhd, htail] at hl
    refine ⟨.cons hl W, .cons hd ha he (htd.trans (congrArg lab htail)) hhd hW, ?_, ?_⟩
    · simp only [GraphWalk.support_cons, gm06WalkVertices, List.map_cons, hWS]
    · simp only [GraphWalk.edges_cons, List.map_cons, hWE]

end GM06WalkDartEncoding
end GraphMinor.Compute

namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute
namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)

/-- An active ordinary copied dart projects to its actual active
permanent word, with its edge and both oriented endpoints intact. -/
theorem cut_dart_encoding_data (hG : IsCylinderSection5Drawing k G) {q : ℕ}
    (hq : q ∈ (currentCut).activeDarts) (hd : gm06UncutDart q < 2 * rep.tagged.length) :
    ∃ h : gm06ProjectCutDart q < 2 * rep.tagged.length,
      (rep.tagged[gm06ProjectCutDart q / 2]'(by omega)).2 = 1 ∧
      rep.edge ⟨gm06ProjectCutDart q / 2, by omega⟩ = rep.cutEdgePoint (q / 2) ∧
      rep.vertex (gm06DartTail rep.tagged ⟨gm06ProjectCutDart q, h⟩) =
        rep.cutPoint ((currentCut).origins[q]?.getD 0) ∧
      rep.vertex (gm06DartHead rep.tagged ⟨gm06ProjectCutDart q, h⟩) =
        rep.cutPoint ((currentCut).origins[gm06DartMate q]?.getD 0) := by
  have hmq := (rep.cut_data_face_encoding hG (List.range x.vertexCount)).2.2.2.2 q hq
  have ho := rep.cut_ordinary_origin hG hq hd
  have hmd : gm06UncutDart (gm06DartMate q) < 2 * rep.tagged.length := by
    rw [gm06UncutDart_mate]
    exact gm06DartMate_lt hd
  have hmo := rep.cut_ordinary_origin hG hmq hmd
  rw [gm06UncutDart_mate] at hmo
  let u : Fin (2 * x.vertexCount) := ⟨_, (rep.cut_origins_valid q hq).1⟩
  let w : Fin (2 * x.vertexCount) := ⟨_, (rep.cut_origins_valid _ hmq).1⟩
  let d : Fin (2 * rep.tagged.length) := ⟨gm06UncutDart q, hd⟩
  have hread := gm06Dart_endpoint_words rep.tagged d
  rw [← rep.endpoints] at hread
  have hact := (gm06CutDataOfLinkage_active_iff _ _ _ _ _ _ _ _ _).mp hq
  have hrow := cutOrigins_project_mem _ x.rotations rep.rows_flatten_nodup hact.2 hact.1
  have hslot : u.val / 2 < x.vertexCount := by have hu := u.isLt; omega
  have ha := rep.row_ordinary_active hG ⟨u.val / 2, hslot⟩ hrow.2 hd
  refine ⟨hd, ha, ?_, ?_, ?_⟩
  · have hindex : q / 2 / 2 = gm06ProjectCutDart q / 2 := by
      unfold gm06ProjectCutDart
      omega
    simp only [cutEdgePoint, hindex, show gm06ProjectCutDart q / 2 < rep.tagged.length by
      change gm06UncutDart q / 2 < rep.tagged.length; omega, dite_true]
  · change rep.vertex (gm06DartTail rep.tagged d) = rep.cutPoint u.val
    rw [rep.cutPoint_fin]
    apply congrArg rep.vertex
    exact Fin.ext (ho.trans hread.1).symm
  · change rep.vertex (gm06DartHead rep.tagged d) = rep.cutPoint w.val
    rw [rep.cutPoint_fin]
    apply congrArg rep.vertex
    exact Fin.ext (hmo.trans hread.2).symm

/-- A computed ordinary dart row has an actual graph walk encoded
by precisely the projected row written by APPLY_4. -/
theorem exists_encoded_cut_walk (hG : IsCylinderSection5Drawing k G) {s t : ℕ} {ds : List ℕ}
    (hw : GM06DartWalk (fun d => (currentCut).origins[d]?.getD 0)
      (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) s ds t)
    (ht : rep.cutPoint t ∈ G.V)
    (hds : ∀ d ∈ ds, d ∈ (currentCut).activeDarts ∧ gm06UncutDart d < 2 * rep.tagged.length) :
    ∃ W : GraphWalk G.toGraph (rep.cutPoint s) (rep.cutPoint t),
      GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge W (ds.map gm06ProjectCutDart) ∧
      W.support = (gm06WalkVertices (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) s ds).map
        rep.cutPoint ∧ W.edges = ds.map (fun d => rep.cutEdgePoint (d / 2)) := by
  exact GM06WalkDartEncoding.exists_of_dartWalk rep.links hw ht
    (fun d hd => rep.cut_dart_encoding_data hG (hds d hd).1 (hds d hd).2)

end GM06CurrentDrawingRep
end GraphMinor.GM06
