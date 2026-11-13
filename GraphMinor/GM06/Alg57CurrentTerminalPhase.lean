module

public import GraphMinor.GM06.Alg57CurrentCandidateRows
public import GraphMinor.GM06.Alg57CurrentTerminalRep
public import GraphMinor.GM06.Alg57TerminalSplice
public import GraphMinor.Compute.GM06TerminalSuccessorRows
import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM11.Walks

/-!
# The terminal phase of VI (5.7) in the current drawing

When no reduction applies and no `sᵢ` has valency one, the algorithm
on page 133 builds a linkage of winding `θ + 1/k`. Its rows are
`gm06TerminalSuccessorRows`: for each `i`, the projected darts of the
path `Qᵢ` returned by `TERMINAL_PATH` on the selected face, followed by
the old row of `Pᵢ₊₁` after the end of `Qᵢ`.

We prove that these rows encode such a linkage, for at least two
paths (`GM06CurrentDrawingRep.terminalPhase_linkage`). The steps are:

* the arrays given to `TERMINAL_PATH` are the arrays of the drawing
  representation `TerminalRep` proved in `Alg57CurrentTerminalRep.lean`
  (`terminalPath_eq_erase`);
* by `terminal_erased_walk`, the erased trace is a simple walk to a
  vertex `u` of `Pᵢ₊₁`, other than `sᵢ₊₁`, inside `Σᵢ ∪ {sᵢ, u}`;
* its end is marked, and it is not on `Pᵢ`, so its label is in the
  right boundary list of `Pᵢ₊₁`; its position there splits the old row
  of `Pᵢ₊₁` at `u`;
* joining the two walks gives a simple walk confined as in VI (5.1)
  (`exists_terminal_joined_walk`), and `exists_encoded_spliced_linkage`
  builds the linkage with exactly these rows.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-- A dart walk keeps its darts when the head map changes only off them. -/
theorem GM06DartWalk.congr_head {D V : Type*} {tail head head' : D → V} {s t : V}
    {ds : List D} (h : GM06DartWalk tail head s ds t) (he : ∀ d ∈ ds, head d = head' d) :
    GM06DartWalk tail head' s ds t := by
  induction h with
  | nil v => exact .nil v
  | @cons s t d ds ht hw ih =>
    have hd := he d List.mem_cons_self
    refine .cons ht ?_
    rw [← hd]
    exact ih fun q hq => he q (List.mem_cons_of_mem _ hq)

/-- The last listed vertex of a dart walk is its end. -/
theorem GM06DartWalk.walkVertices_getLast {D V : Type*} {tail head : D → V} {s t : V}
    {ds : List D} (h : GM06DartWalk tail head s ds t) :
    (gm06WalkVertices head s ds).getLast (List.cons_ne_nil _ _) = t := by
  induction h with
  | nil v => rfl
  | @cons s t d ds ht hw ih =>
    simp only [gm06WalkVertices, List.map_cons] at ih ⊢
    rw [List.getLast_cons (List.cons_ne_nil _ _)]
    exact ih

/-- **Joining `Qᵢ` with the tail of `Pᵢ₊₁`.** A simple walk `Wq` from
`sᵢ` to a vertex `b ≠ sᵢ₊₁` of `Pᵢ₊₁`, whose drawing lies in
`Σᵢ ∪ {sᵢ, b}` and meets `Pᵢ₊₁` only at `b`, followed by a simple walk
of `Pᵢ₊₁` from `b` that misses `sᵢ₊₁`, is a simple walk confined as in
VI (5.1), page 129. Its encoding is the concatenation of the two. -/
theorem exists_terminal_joined_walk {L : CylinderLinkage k G} {i : Fin k}
    {m : ℕ} {tagged : List ((Fin m × Fin m) × ℕ)} {vertex : Fin m → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder}
    {a b z : ClosedCylinder} (Wq : GraphWalk G.toGraph a b)
    (B : GraphWalk G.toGraph z (L.curve (finSuccCycle i) 1))
    (ha : a = cylinderM1Point k i) (hz : z = b) (hWq : Wq.IsSimple) (hB : B.IsSimple)
    {Q : Drawing ClosedCylinder} (hQV : Q.V = {y | y ∈ Wq.support})
    (hQE : Q.E = {e | e ∈ Wq.edges})
    (hQ3 : Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, b})
    (hQ4 : Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {b})
    (hbP : b ∈ (L.pathDrawing (finSuccCycle i)).V)
    (hbne : b ≠ cylinderM1Point k (finSuccCycle i))
    (hBP : (walkDrawing G B).U ⊆ (L.pathDrawing (finSuccCycle i)).U)
    (hBs : cylinderM1Point k (finSuccCycle i) ∉ B.support)
    {r₁ r₂ : List ℕ} (h₁ : GM06WalkDartEncoding G.toGraph tagged vertex edge Wq r₁)
    (h₂ : GM06WalkDartEncoding G.toGraph tagged vertex edge B r₂) :
    ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve (finSuccCycle i) 1),
      W.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge W (r₁ ++ r₂) ∧
      (walkDrawing G W).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
        (L.pathDrawing (finSuccCycle i)).U ∧
      cylinderM1Point k (finSuccCycle i) ∉ (walkDrawing G W).U := by
  subst ha
  cases hz
  have hQU : ∀ y, y ∈ (walkDrawing G Wq).U ↔ y ∈ Q.U := by
    intro y
    rw [mem_walkDrawing_U, Q.U_eq, hQV, hQE]
    simp
  have hBnd : B.support.Nodup := hB
  have hbB : B.support = b :: B.support.tail := B.support_eq_cons
  have hUW : ∀ y, y ∈ (walkDrawing G (Wq.append B)).U →
      y ∈ (walkDrawing G Wq).U ∨ y ∈ (walkDrawing G B).U := by
    intro y hy
    rw [mem_walkDrawing_U, GraphWalk.mem_support_append, GraphWalk.edges_append] at hy
    rw [mem_walkDrawing_U, mem_walkDrawing_U]
    rcases hy with (h | h) | ⟨e, he, hye⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · rcases List.mem_append.mp he with he | he
      · exact Or.inl (Or.inr ⟨e, he, hye⟩)
      · exact Or.inr (Or.inr ⟨e, he, hye⟩)
  have hsnext : cylinderM1Point k (finSuccCycle i) ∈ (L.pathDrawing (finSuccCycle i)).V :=
    (isPathDrawing_end_vertices (L.isPath _)).1
  refine ⟨Wq.append B, ?_, h₁.append h₂, ?_, ?_⟩
  · unfold GraphWalk.IsSimple
    rw [GraphWalk.support_append]
    refine List.Nodup.append hWq (hBnd.sublist (List.tail_sublist _)) ?_
    intro y hyq hyB
    have hyU : y ∈ Q.U := (hQU y).mp ((mem_walkDrawing_U G Wq).mpr (Or.inl hyq))
    have hyP : y ∈ (L.pathDrawing (finSuccCycle i)).U :=
      hBP ((mem_walkDrawing_U G B).mpr (Or.inl (List.mem_of_mem_tail hyB)))
    have hyz : y = b := hQ4 ⟨hyU, hyP⟩
    rw [hyz] at hyB
    rw [hbB] at hBnd
    exact (List.nodup_cons.mp hBnd).1 hyB
  · intro y hy
    rcases hUW y hy with h | h
    · rcases hQ3 ((hQU y).mp h) with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · rw [mem_singleton_iff.mp h]
        exact Or.inr ((L.pathDrawing _).V_subset_U hbP)
    · exact Or.inr (hBP h)
  · intro hs
    rcases hUW _ hs with h | h
    · exact hbne (hQ4 ⟨(hQU _).mp h, (L.pathDrawing _).V_subset_U hsnext⟩).symm
    · rw [mem_walkDrawing_U] at h
      rcases h with h | ⟨e, he, hse⟩
      · exact hBs h
      · obtain ⟨y, y', hy, hy', hl⟩ := walk_exists_isLink_of_mem_edges B he
        have hsG : cylinderM1Point k (finSuccCycle i) ∈ G.V :=
          (L.isSubdrawing (finSuccCycle i)).1.1 hsnext
        have hmem : cylinderM1Point k (finSuccCycle i) ∈ closure e ∩ G.V := ⟨hse, hsG⟩
        rw [hl.2.2.2] at hmem
        rcases hmem with h | h
        · exact hBs (h ▸ hy)
        · exact hBs ((mem_singleton_iff.mp h) ▸ hy')

namespace GM06CurrentDrawingRep
variable {x : GM06SuccessorInput} {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "edgeCount" => 2 * (rep.tagged.length + (k + k))
local notation "heads" => gm06TerminalHeadWords edgeCount (GM06CutData.origins currentCut)

/-- The full head table of the cut is the head table used by the
terminal representation. -/
theorem dartHeads_eq_headWords :
    gm06DartHeads (currentCut).origins = heads := by
  apply List.ext_getElem
  · rw [gm06DartHeads_length, rep.cut_origin_table_length, gm06TerminalHeadWords,
      List.length_ofFn]
  · intro d h1 h2
    simp only [gm06DartHeads, gm06TerminalHeadWords, List.getElem_map, List.getElem_range,
      List.getElem_ofFn]

/-- The head of the selected reversed inner cuff end is the left copy
of `sᵢ`. -/
theorem neighbourHead_gap (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    gm06CutNeighbourHead (currentCut).origins (4 * (rep.tagged.length + i.val) + 1) =
      gm06CutVertex (x.innerCuff[i.val]?.getD 0) true := by
  have hcode : gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0 =
      4 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  have hmate : gm06DartMate (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) =
      gm06CutDart (2 * (rep.tagged.length + i.val)) 0 := by
    rw [← gm06CutDart_mate]
    simp [gm06DartMate]
  have hsource : x.innerCuff[i.val]?.getD 0 = (rep.source i).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  rw [← hcode, gm06CutNeighbourHead, hmate, (rep.inner_copied_origins hG i).1, hsource]

/-- **The arrays of TERMINAL_PATH are those of the representation.**
On the selected face row, the output of `gm06TerminalPath` is the
erased first-contact trace for the head, target and dart lists of
`component_terminal_rep_facts`. -/
theorem terminalPath_eq_erase (hn : 0 < x.vertexCount) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ) (hgap : 4 * (rep.tagged.length + i.val) + 1 ∈ row) :
    gm06TerminalPath (2 * x.vertexCount) (currentCut).origins row
        (gm06PhaseBoundaryVertices x i.val 0)
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
        (4 * (rep.tagged.length + i.val) + 1) =
      gm06EraseClosedSubwalks (fun d => (heads)[d]?.getD 0)
        (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
        (gm06TerminalTrace heads
          (gm06TerminalTargetBits (2 * x.vertexCount) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
            ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD [])
              (x.innerCuff[i.val]?.getD 0) true).map Fin.val)
            ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(finSuccCycle i).val]?.getD [])
              (x.innerCuff[(finSuccCycle i).val]?.getD 0) false).map Fin.val))
          (gm06TerminalFaceDarts (4 * (rep.tagged.length + i.val) + 1) row)).1 := by
  have hlow := rep.computed_path_labels_phase hn i true
  have hup := rep.computed_path_labels_phase hn (finSuccCycle i) false
  simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.toNat_true] at hlow hup
  have hwalk : gm06TerminalFaceWalk row (4 * (rep.tagged.length + i.val) + 1) =
      gm06TerminalFaceDarts (4 * (rep.tagged.length + i.val) + 1) row := by
    unfold gm06TerminalFaceDarts
    rw [← gm06TerminalFaceWalk_rotate row _ hgap, List.dropLast_concat]
  unfold gm06TerminalPath gm06TerminalFaceTrace
  rw [rep.dartHeads_eq_headWords, rep.neighbourHead_gap hG i, hwalk, rep.phase_next_eq i,
    hlow, hup]
  rfl

/-- **The terminal successor walk of one path** (`k ≥ 2`). The row
computed for path `i` encodes a simple walk from `sᵢ` to the end of
`Pᵢ₊₁` inside `Σᵢ ∪ {sᵢ} ∪ Pᵢ₊₁` that misses `sᵢ₊₁`. -/
theorem terminal_successor_walk (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {θ : ℝ} (hθ : L.HasTheta θ) (i : Fin k) :
    ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve (finSuccCycle i) 1),
      W.IsSimple ∧ GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge W
        (gm06TerminalSuccessorRow x rep.tagged.length i.val) ∧
      (walkDrawing G W).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
        (L.pathDrawing (finSuccCycle i)).U ∧
      cylinderM1Point k (finSuccCycle i) ∉ (walkDrawing G W).U := by
  classical
  have hn : 0 < x.vertexCount := Nat.zero_lt_of_lt (rep.source i).isLt
  obtain ⟨root, hroot, row, hout, hgap, -, hact, hord, trep⟩ :=
    rep.component_terminal_rep_facts hn hk hG hno i
  obtain ⟨root', hroot', hpart⟩ := rep.phase_component_at hG i
  have hrr : root' = root := Fin.ext (hroot'.trans hroot.symm)
  subst root'
  have hcode : gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0 =
      4 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06CutDart, Nat.add_div, Nat.add_mod]
  rw [hcode] at hgap hact hord trep
  have hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (rep.tagged.length + x.innerCuff.length + x.outerCuff.length))
      (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + i.val) + 1) =
        some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row, gm06IncE edgeCount row) := by
    rw [rep.cuff_lengths.1, rep.cuff_lengths.2, Nat.add_assoc]
    exact hout
  rw [gm06TerminalSuccessorRow_eq hpart hface]
  change ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) (L.curve (finSuccCycle i) 1),
    W.IsSimple ∧ GM06WalkDartEncoding G.toGraph rep.tagged rep.vertex rep.edge W
      (gm06TerminalRowOfPath x rep.tagged.length i.val (currentCut).origins
        (gm06TerminalPath (2 * x.vertexCount) (currentCut).origins row
          (gm06PhaseBoundaryVertices x i.val 0)
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i.val) 1)
          (4 * (rep.tagged.length + i.val) + 1))) ∧ _ ∧ _
  rw [rep.terminalPath_eq_erase hn hG i row hgap]
  -- the erased trace
  obtain ⟨t, hwQ, hndQ, hQd, hmark, hu1, hu2, Q, hQV, hQE, hu3, hu4⟩ :=
    terminal_erased_walk hk hG hθ hno (hval i) trep
  set Qd := gm06EraseClosedSubwalks (fun d => (heads)[d]?.getD 0)
    (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
    (gm06TerminalTrace heads
      (gm06TerminalTargetBits (2 * x.vertexCount) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
        ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD [])
          (x.innerCuff[i.val]?.getD 0) true).map Fin.val)
        ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(finSuccCycle i).val]?.getD [])
          (x.innerCuff[(finSuccCycle i).val]?.getD 0) false).map Fin.val))
      (gm06TerminalFaceDarts (4 * (rep.tagged.length + i.val) + 1) row)).1 with hQdDef
  set s₀ := gm06CutVertex (x.innerCuff[i.val]?.getD 0) true with hs₀
  obtain ⟨_, hkeys, _, hc, _⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hbound : ∀ d ∈ Qd, d < 2 * edgeCount := fun d hd =>
    hkeys d ((hc d).mp (hact d (hQd d hd).1))
  have hheadEq : ∀ d ∈ Qd, (heads)[d]?.getD 0 = gm06CutNeighbourHead (currentCut).origins d :=
    fun d hd => terminalHeadWords_get _ (hbound d hd)
  have hw' : GM06DartWalk (fun q => (currentCut).origins[q]?.getD 0)
      (gm06CutNeighbourHead (currentCut).origins) s₀ Qd t := GM06DartWalk.congr_head hwQ hheadEq
  have hvl : gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd =
      gm06WalkVertices (fun d => (currentCut).origins[gm06DartMate d]?.getD 0) s₀ Qd := by
    simp only [gm06WalkVertices]
    congr 1
    exact List.map_congr_left hheadEq
  -- the end lies on the right boundary of the next path
  have hpath (j : Fin k) : x.linkage[j.val]?.getD [] =
      x.linkage[j.val]'(by rw [rep.linkage.1]; exact j.isLt) := by
    rw [List.getElem?_eq_getElem (show j.val < x.linkage.length by rw [rep.linkage.1]; exact j.isLt)]
    rfl
  have hsource (j : Fin k) : x.innerCuff[j.val]?.getD 0 = (rep.source j).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  have htlt : t < 2 * x.vertexCount := by
    by_contra hge
    apply hmark
    simp only [gm06TerminalTargetBits, gm06IncidenceBits, List.getElem?_ofFn]
    simp [show ¬ t < 2 * x.vertexCount from hge]
  have htcases := (terminalTargetBits_ne_zero_iff _ _ _ _ ⟨t, htlt⟩).mp hmark
  obtain ⟨WPi, -, -, -, hWPiV, hWPisupp, -⟩ := rep.computed_encoded_path_walk hn i true
  rw [← hpath i, ← hsource i] at hWPisupp
  have hupper : t ∈ (gm06CutPathLabels x.vertexCount hn x.endpoints
      (x.linkage[(finSuccCycle i).val]?.getD []) (x.innerCuff[(finSuccCycle i).val]?.getD 0)
        false).map Fin.val := by
    rcases htcases with ⟨hlow, -⟩ | hup
    · exfalso
      obtain ⟨l, hl, hlt⟩ := List.mem_map.mp hlow
      have hlt' : l.val = t := hlt
      have hPi : rep.cutPoint t ∈ (L.pathDrawing i).V := by
        rw [hWPiV, mem_ofPred_eq, hWPisupp, ← hlt', rep.cutPoint_fin]
        exact List.mem_map_of_mem hl
      exact disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i).symm)
        ((L.pathDrawing i).V_subset_U hPi) ((L.pathDrawing _).V_subset_U hu1)
    · exact hup
  -- the tail of the next path
  obtain ⟨WPn, hWPns, hWPnenc, hWPnD, -, hWPnsupp, -⟩ :=
    rep.computed_encoded_path_walk hn (finSuccCycle i) false
  rw [← hpath (finSuccCycle i), ← hsource (finSuccCycle i)] at hWPnsupp
  rw [← hpath (finSuccCycle i)] at hWPnenc
  set labelsN := gm06CutPathLabels x.vertexCount hn x.endpoints
    (x.linkage[(finSuccCycle i).val]?.getD []) (x.innerCuff[(finSuccCycle i).val]?.getD 0) false
    with hlabelsN
  set p := (labelsN.map Fin.val).idxOf t with hp
  have hplt : p < (labelsN.map Fin.val).length := List.idxOf_lt_length_of_mem hupper
  have hpget : (labelsN.map Fin.val)[p] = t := List.getElem_idxOf hplt
  have hlabLen : labelsN.length = (x.linkage[(finSuccCycle i).val]?.getD []).length + 1 := by
    simp only [hlabelsN, gm06CutPathLabels, find4PathLabels, gm06CutPathSteps, List.length_cons,
      List.length_map]
  have hpl : p ≤ (x.linkage[(finSuccCycle i).val]?.getD []).length := by
    rw [List.length_map] at hplt
    omega
  have hsuppP : WPn.support[p]? = some (rep.cutPoint t) := by
    rw [hWPnsupp, List.getElem?_map]
    rw [List.length_map] at hplt
    rw [List.getElem?_eq_getElem hplt, Option.map_some]
    rw [List.getElem_map] at hpget
    rw [← hpget, rep.cutPoint_fin]
  obtain ⟨z, -, Bw, -, hBenc, hz, -, hBS, -, hBE⟩ := hWPnenc.exists_split_take_drop p hpl
  have hzt : z = rep.cutPoint t := Option.some.inj (hz.symm.trans hsuppP)
  have hWPnnd : WPn.support.Nodup := hWPns
  -- the computed row is exactly the joined encoding
  have hlast : (gm06WalkVertices (gm06CutNeighbourHead (currentCut).origins)
      (gm06CutNeighbourHead (currentCut).origins (4 * (rep.tagged.length + i.val) + 1)) Qd).getLast
        (List.cons_ne_nil _ _) = t := by
    rw [rep.neighbourHead_gap hG i]
    exact GM06DartWalk.walkVertices_getLast hw'
  have hphase := rep.phase_next_eq i
  have hupB := rep.computed_path_labels_phase hn (finSuccCycle i) false
  simp only [Bool.not_false, Bool.toNat_true] at hupB
  unfold gm06TerminalRowOfPath
  rw [hlast, hphase, ← hupB]
  -- the encoded walk of the erased trace
  have htG : rep.cutPoint t ∈ G.V := (L.isSubdrawing (finSuccCycle i)).1.1 hu1
  obtain ⟨Wq, hWqenc, hWqsupp, hWqedges⟩ := rep.exists_encoded_cut_walk hG hw' htG
    fun d hd => ⟨hact d (hQd d hd).1, hord d (hQd d hd).1 (hQd d hd).2⟩
  have hvert : ∀ v ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀ Qd,
      v ∈ gm06WalkVertices (fun d => (heads)[d]?.getD 0) s₀
        (gm06TerminalFaceDarts (4 * (rep.tagged.length + i.val) + 1) row) := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, (hQd d hd).1, rfl⟩)
  have hWqs : Wq.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hWqsupp]
    have hnd' := hndQ
    rw [hvl] at hnd'
    refine hnd'.map_on fun v hv w hw h => trep.inj v ?_ w ?_ h
    · rw [← hvl] at hv; exact hvert v hv
    · rw [← hvl] at hw; exact hvert w hw
  have hBnot : cylinderM1Point k (finSuccCycle i) ∉ Bw.support := by
    intro hs
    rw [hBS] at hs
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs
    rw [List.getElem?_drop] at hj
    have h0 := GraphWalk.support_getElem?_zero WPn
    have := nodup_index_eq_of_getElem? hWPnnd hj h0
    have hp0 : p = 0 := by omega
    rw [hp0, h0] at hsuppP
    exact hu2 (Option.some.inj hsuppP).symm
  have hBP : (walkDrawing G Bw).U ⊆ (L.pathDrawing (finSuccCycle i)).U := by
    rw [← hWPnD]
    intro y hy
    rw [mem_walkDrawing_U] at hy ⊢
    rcases hy with hy | ⟨e, he, hye⟩
    · rw [hBS] at hy
      exact Or.inl (List.mem_of_mem_drop hy)
    · rw [hBE] at he
      exact Or.inr ⟨e, List.mem_of_mem_drop he, hye⟩
  have hBs : Bw.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hBS]
    exact hWPnnd.sublist (List.drop_sublist _ _)
  have hQV' : Q.V = {y | y ∈ Wq.support} := by
    rw [hQV, hWqsupp, hvl]
  have hQE' : Q.E = {e | e ∈ Wq.edges} := by
    rw [hQE, hWqedges]
  exact exists_terminal_joined_walk Wq Bw trep.start_lab hzt hWqs hBs hQV' hQE' hu3 hu4 hu1 hu2
    hBP hBnot hWqenc hBenc

/-- **The terminal phase gives the next linkage** (VI (5.7), page 133,
`k ≥ 2`). If no reduction applies and no `sᵢ` has valency one, the
rows `gm06TerminalSuccessorRows` encode a linkage `L'` of `G` with
winding `θ + 1/k`, whose path `i` ends at the end of `Pᵢ₊₁`. -/
theorem terminalPhase_linkage (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {θ : ℝ} (hθ : L.HasTheta θ) :
    ∃ L' : CylinderLinkage k G, L'.HasTheta (θ + 1 / (k : ℝ)) ∧
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      GM06LinkageRowsEncoding L' rep.tagged rep.vertex rep.edge
        (gm06TerminalSuccessorRows x rep.tagged.length) := by
  choose W hWs hWenc hWconf hWav using rep.terminal_successor_walk hk hG hno hval hθ
  refine exists_encoded_spliced_linkage L hG hk hθ _
    (by rw [gm06TerminalSuccessorRows_length, rep.cuff_lengths.1]) W hWs (fun i => ?_) hWconf hWav
  rw [gm06TerminalSuccessorRows_getD _ _ (by rw [rep.cuff_lengths.1]; exact i.isLt)]
  exact hWenc i

/-- `terminalPhase_linkage` for the rows `gm06TerminalPhase` written by
the terminal phase program; they equal `gm06TerminalSuccessorRows` by
`gm06TerminalPhase_eq_successorRows`. -/
theorem terminalPhase_linkage_phase (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {θ : ℝ} (hθ : L.HasTheta θ) :
    ∃ L' : CylinderLinkage k G, L'.HasTheta (θ + 1 / (k : ℝ)) ∧
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      GM06LinkageRowsEncoding L' rep.tagged rep.vertex rep.edge
        (gm06TerminalPhase x rep.tagged.length) := by
  rw [gm06TerminalPhase_eq_successorRows]
  exact rep.terminalPhase_linkage hk hG hno hval hθ

end GM06CurrentDrawingRep
end GraphMinor.GM06
