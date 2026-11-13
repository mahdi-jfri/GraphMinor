module

public import GraphMinor.GM06.Defs
public import GraphMinor.Compute.GM06FirstContact
public import GraphMinor.Compute.GM06LoopErasure
import GraphMinor.GM06.Alg57StripPathContact
import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM06.Alg57TerminalLinkage
import GraphMinor.GM06.Section5RegionContact
import GraphMinor.GM06.Section5FirstContactPoints
import GraphMinor.GM06.Section5NextContact
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# `TERMINAL_PATH` gives the terminal linkage, for `k ≥ 2`

Section 15 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) traces the face walk of
`c̄ᵢ` from `sᵢ` to its first vertex in `Tᵢ = (V(Pᵢ) - {sᵢ}) ∪ V(Pᵢ₊₁)` (`gm06TerminalTrace`) and
erases closed subwalks (`gm06EraseClosedSubwalks`). Lemma 15 says the result is a path `Qᵢ` from
`sᵢ` to a vertex `uᵢ ≠ sᵢ₊₁` of `Pᵢ₊₁`, inside the strip apart from its ends. Lemma 16 then gives a
linkage of winding `θ + 1/k`.

* `lemma15_of_region_path`: the drawing part of Lemma 15. A path of `G` from `sᵢ` in `closure Rᵢ`
  whose inner vertices are off the linkage and whose end is on the linkage has the properties of
  Lemma 15. The end is not on `Pᵢ`, because `closure Rᵢ` meets `Pᵢ` only at `sᵢ` when no reduction
  applies (`closure_region_inter_path_subset_start`, and this is where Lemma 14 and Reduction 4
  enter). It is not `sᵢ₊₁`, because its last edge would allow Reduction 1.
* `TerminalRep`: when the dart lists of `TERMINAL_PATH` represent the drawing.
* `terminal_path_spec`: the output of `TERMINAL_PATH` is a path with the properties of Lemma 15.
* `isThetaFeasible_next_of_terminal_paths`: with such lists for every `i`, the winding
  `θ + 1/k` is feasible (Lemma 16).
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-- The target set `Tᵢ` of the terminal trace: the vertices of `Pᵢ` other than `sᵢ`, and those of
`Pᵢ₊₁`. -/
def terminalTargets (L : CylinderLinkage k G) (i : Fin k) : Set ClosedCylinder :=
  ((L.pathDrawing i).V \ {cylinderM1Point k i}) ∪ (L.pathDrawing (finSuccCycle i)).V

/-- **Lemma 15, the drawing part** (`k ≥ 2`). Suppose no reduction applies and `sᵢ` does not have
valency one. Let `Q` be a path of `G` from `sᵢ` to a linkage vertex `u`, in `closure Rᵢ`, whose
other vertices are off the linkage. Then `u` is a vertex of `Pᵢ₊₁` other than `sᵢ₊₁`, `Q` lies in
`Σᵢ` apart from its ends, and `Q` meets `Pᵢ₊₁` only at `u`. -/
theorem lemma15_of_region_path {θ : ℝ} (L : CylinderLinkage k G) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {u : ClosedCylinder} {Q : Drawing ClosedCylinder}
    (hQ : IsSubpathOf G Q (cylinderM1Point k i) u)
    (hQR : Q.U ⊆ closure (cylinderRegion k G i))
    (hint : Q.V ∩ (⋃ j : Fin k, (L.pathDrawing j).V) ⊆ {cylinderM1Point k i, u})
    (hu : u ∈ ⋃ j : Fin k, (L.pathDrawing j).V) :
    u ∈ (L.pathDrawing (finSuccCycle i)).V ∧ u ≠ cylinderM1Point k (finSuccCycle i) ∧
      Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, u} ∧
      Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {u} := by
  have hQG : Q.IsSubdrawing G := hQ.1
  have hsu : cylinderM1Point k i ≠ u := isPathDrawing_start_ne_end hQ.2.2
  have huQ : u ∈ Q.U := Q.V_subset_U (isPathDrawing_end_vertices hQ.2.2).2
  have huR : u ∈ closure (cylinderRegion k G i) := hQR huQ
  have hcontact := closure_region_inter_path_subset_start L hk hG hθ hno i hval
  obtain ⟨j, huj⟩ := mem_iUnion.mp hu
  have hjU : u ∈ (L.pathDrawing j).U := (L.pathDrawing j).V_subset_U huj
  have hj : j = finSuccCycle i := by
    rcases mem_path_of_mem_closure_strip L hG hθ i j
      (closure_mono (cylinderRegion_subset_strip L i) huR) hjU with rfl | h
    · exact absurd (mem_singleton_iff.mp (hcontact ⟨huR, hjU⟩)).symm hsu
    · exact h
  subst hj
  obtain ⟨hmeet, hconf⟩ := first_contact_prefix_point_contact_and_strip L hk hG hθ hno i hval
    hQG hQ.2.2 hQR hint
  have hsU : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have hsOff : cylinderM1Point k i ∉ (L.pathDrawing (finSuccCycle i)).U := fun hh =>
    disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i).symm) hsU hh
  have hfirst : Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {u} := by
    rintro x ⟨hxQ, hxP⟩
    rcases hmeet ⟨hxQ, mem_iUnion.mpr ⟨_, hxP⟩⟩ with rfl | hx
    · exact absurd hxP hsOff
    · exact hx
  refine ⟨huj, ?_, hconf, hfirst⟩
  obtain ⟨e, heQ, hue⟩ := exists_terminal_edge hQ.2.2
  have heG := hQG.2 heQ
  have heStrip : e ⊆ cylinderStrip L i := by
    intro x hx
    rcases hconf ((heQ.2.1 hx).1) with hxS | hxEnds
    · exact hxS
    · apply False.elim
      apply (heG.2.1 hx).2
      rcases hxEnds with heq | heq
      · rw [heq]
        exact (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
      · rw [mem_singleton_iff.mp heq]
        exact (L.isSubdrawing (finSuccCycle i)).1.1 huj
  intro heq
  apply hno
  apply reduction1_applies_of_incident_edge_in_strip L hk hG heG (heq ▸ hue)
  rw [finPredCycle_finSuccCycle]
  exact heStrip

/-! ### Dart walks -/

section DartWalk

variable {D V : Type*} {tail head : D → V}

theorem GM06DartWalk.of_append {s t : V} {xs ys : List D}
    (h : GM06DartWalk tail head s (xs ++ ys) t) : ∃ u, GM06DartWalk tail head s xs u := by
  induction xs generalizing s with
  | nil => exact ⟨s, .nil s⟩
  | cons x xs ih =>
    cases h with
    | cons ht hw =>
      obtain ⟨u, hu⟩ := ih hw
      exact ⟨u, .cons ht hu⟩

theorem GM06DartWalk.end_eq {s t : V} {ds : List D} (h : GM06DartWalk tail head s ds t)
    (hne : ds ≠ []) : t = head (ds.getLast hne) := by
  induction h with
  | nil => exact absurd rfl hne
  | @cons s t d ds ht hw ih =>
    cases ds with
    | nil => cases hw; rfl
    | cons d' ds' =>
      rw [List.getLast_cons (List.cons_ne_nil d' ds')]
      exact ih (List.cons_ne_nil d' ds')

theorem GM06DartWalk.tail_mem {s t : V} {ds : List D} (h : GM06DartWalk tail head s ds t) :
    ∀ d ∈ ds, tail d ∈ s :: ds.dropLast.map head := by
  induction h with
  | nil => simp
  | @cons s t d ds ht hw ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [ht]; exact List.mem_cons_self
    · have := ih x hx
      cases ds with
      | nil => simp at hx
      | cons d' ds' =>
        rw [List.dropLast_cons_cons, List.map_cons]
        exact List.mem_cons_of_mem _ this

/-- A dart walk whose darts are edges of a drawing gives a walk of the drawing. -/
theorem GM06DartWalk.exists_graphWalk {S : Type*} [TopologicalSpace S] {Γ : Drawing S}
    {lab : V → S} {edgeOf : D → Set S} {s t : V} {ds : List D}
    (h : GM06DartWalk tail head s ds t)
    (hl : ∀ d ∈ ds, Γ.toGraph.IsLink (edgeOf d) (lab (tail d)) (lab (head d)))
    (ht : lab t ∈ Γ.V) :
    ∃ W : GraphWalk Γ.toGraph (lab s) (lab t),
      W.support = (gm06WalkVertices head s ds).map lab ∧ W.edges = ds.map edgeOf := by
  induction h with
  | nil v => exact ⟨.nil ht, rfl, rfl⟩
  | @cons s t d ds hts hw ih =>
    obtain ⟨W, hW, hE⟩ := ih (fun d' hd' => hl d' (List.mem_cons_of_mem _ hd')) ht
    have hd := hl d List.mem_cons_self
    rw [hts] at hd
    refine ⟨.cons hd W, ?_, ?_⟩
    · simp [GraphWalk.support, hW, gm06WalkVertices]
    · simp [GraphWalk.edges, hE]

end DartWalk

/-- **The dart lists of `TERMINAL_PATH` represent the drawing** at `Pᵢ` (`k ≥ 2`). Darts and
vertices are labels; `heads[d]` is the head of `d`, `tail d` its tail, `targets` marks `Tᵢ`.

* `start_lab`, `start_tgt`: the start label is `sᵢ`, and it is not a target.
* `walk`: the face row `ds` (rotated to end with `c̄ᵢ`, which is removed) is a walk.
* `contact`: some dart of the row ends in `Tᵢ` (the whole walk ends at the start of `Pᵢ₊₁`).
* `target_iff`: a head is marked exactly when its vertex is in `Tᵢ`.
* `edge`: a dart of the row with unmarked tail is an edge of `G` in `closure Rᵢ` joining its ends.
  (Cuff darts of the row start in `Tᵢ`.)
* `inj`: distinct vertex labels of the row are distinct points. -/
structure TerminalRep (L : CylinderLinkage k G) (i : Fin k) (heads targets ds : List ℕ) (s₀ : ℕ)
    (tail : ℕ → ℕ) (lab : ℕ → ClosedCylinder) (edgeOf : ℕ → Set ClosedCylinder) : Prop where
  start_lab : lab s₀ = cylinderM1Point k i
  start_tgt : targets[s₀]?.getD 0 = 0
  walk : ∃ t, GM06DartWalk tail (fun d => heads[d]?.getD 0) s₀ ds t
  contact : ∃ d ∈ ds, targets[heads[d]?.getD 0]?.getD 0 ≠ 0
  target_iff : ∀ d ∈ ds,
    (targets[heads[d]?.getD 0]?.getD 0 ≠ 0 ↔ lab (heads[d]?.getD 0) ∈ terminalTargets L i)
  edge : ∀ d ∈ ds, targets[tail d]?.getD 0 = 0 →
    G.toGraph.IsLink (edgeOf d) (lab (tail d)) (lab (heads[d]?.getD 0)) ∧
      edgeOf d ⊆ closure (cylinderRegion k G i)
  inj : ∀ v ∈ gm06WalkVertices (fun d => heads[d]?.getD 0) s₀ ds,
    ∀ w ∈ gm06WalkVertices (fun d => heads[d]?.getD 0) s₀ ds, lab v = lab w → v = w

/-- **Lemma 15** (`k ≥ 2`). The output of `TERMINAL_PATH` (the first-contact trace, then loop
erasure) is a path `Q` of `G` from `sᵢ` to a vertex `u ≠ sᵢ₊₁` of `Pᵢ₊₁`, inside `Σᵢ` apart from its
ends and meeting `Pᵢ₊₁` only at `u`. Its vertices and edges are those listed by the output. -/
theorem terminal_path_spec {θ : ℝ} {L : CylinderLinkage k G} (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) {i : Fin k}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {heads targets ds : List ℕ} {s₀ : ℕ} {tail : ℕ → ℕ} {lab : ℕ → ClosedCylinder}
    {edgeOf : ℕ → Set ClosedCylinder}
    (rep : TerminalRep L i heads targets ds s₀ tail lab edgeOf) :
    ∃ (u : ClosedCylinder) (Q : Drawing ClosedCylinder),
      Q.V = {x | x ∈ (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1)).map lab} ∧
      Q.E = {e | e ∈ (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1).map edgeOf} ∧
      u ∈ (L.pathDrawing (finSuccCycle i)).V ∧ u ≠ cylinderM1Point k (finSuccCycle i) ∧
      IsSubpathOf G Q (cylinderM1Point k i) u ∧
      Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, u} ∧
      Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {u} := by
  set H : ℕ → ℕ := fun d => heads[d]?.getD 0 with hH
  set trace := (gm06TerminalTrace heads targets ds).1 with htrace
  obtain ⟨hpre, hinternal, hfalse⟩ := gm06TerminalTrace_spec heads targets ds
  have hflag : (gm06TerminalTrace heads targets ds).2 = true := by
    by_contra hf
    obtain ⟨d, hd, hdt⟩ := rep.contact
    exact hdt ((hfalse.mp (Bool.eq_false_iff.mpr hf)) d hd)
  obtain ⟨dl, hlast, hstop⟩ := gm06FirstContact_last (gm06TerminalContact heads targets) ds hflag
  change trace.getLast? = some dl at hlast
  have hne : trace ≠ [] := by
    intro h; rw [h] at hlast; cases hlast
  have hdl : dl = trace.getLast hne := by
    rw [List.getLast?_eq_getLast hne] at hlast
    exact (Option.some.inj hlast).symm
  have hstop' : targets[H dl]?.getD 0 ≠ 0 := by
    simpa [gm06TerminalContact] using hstop
  have htrace_ds : ∀ d ∈ trace, d ∈ ds := fun d hd => hpre.subset hd
  -- the trace is a walk to the head of its last dart
  obtain ⟨t, hw⟩ := rep.walk
  obtain ⟨rest, hrest⟩ := hpre
  obtain ⟨u₀, hwt⟩ : ∃ u, GM06DartWalk tail H s₀ trace u :=
    GM06DartWalk.of_append (hrest ▸ hw)
  have hu₀ : u₀ = H dl := by rw [GM06DartWalk.end_eq hwt hne, hdl]
  subst hu₀
  -- every traced dart starts at an unmarked vertex
  have htails : ∀ d ∈ trace, targets[tail d]?.getD 0 = 0 := by
    intro d hd
    rcases List.mem_cons.mp (GM06DartWalk.tail_mem hwt d hd) with h | h
    · rw [h]; exact rep.start_tgt
    · obtain ⟨d', hd', hdd⟩ := List.mem_map.mp h
      rw [← hdd]
      exact hinternal d' hd'
  have hedge : ∀ d ∈ trace, G.toGraph.IsLink (edgeOf d) (lab (tail d)) (lab (H d)) ∧
      edgeOf d ⊆ closure (cylinderRegion k G i) := fun d hd =>
    rep.edge d (htrace_ds d hd) (htails d hd)
  -- loop erasure
  obtain ⟨hwQ, hndQ, hsubQ⟩ := gm06EraseClosedSubwalks_spec hwt
  set Qd := gm06EraseClosedSubwalks H s₀ trace with hQd
  have hQd_trace : ∀ d ∈ Qd, d ∈ trace := fun d hd => hsubQ.subset hd
  have hlabu : lab (H dl) ∈ G.V := (hedge dl (by rw [hdl]; exact List.getLast_mem hne)).1.2.2.1
  obtain ⟨W, hWs, hWe⟩ : ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) (lab (H dl)),
      W.support = (gm06WalkVertices H s₀ Qd).map lab ∧ W.edges = Qd.map edgeOf := by
    rw [← rep.start_lab]
    exact GM06DartWalk.exists_graphWalk hwQ (fun d hd => (hedge d (hQd_trace d hd)).1) hlabu
  -- vertices of the erased walk are vertices of the row
  have hvert : ∀ v ∈ gm06WalkVertices H s₀ Qd, v ∈ gm06WalkVertices H s₀ ds := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, htrace_ds d (hQd_trace d hd), rfl⟩)
  have hWsimple : W.IsSimple := by
    unfold GraphWalk.IsSimple
    rw [hWs]
    exact hndQ.map_on (fun v hv w hw h => rep.inj v (hvert v hv) w (hvert w hw) h)
  have hdl_ds : dl ∈ ds := htrace_ds dl (by rw [hdl]; exact List.getLast_mem hne)
  have huT : lab (H dl) ∈ terminalTargets L i := (rep.target_iff dl hdl_ds).mp hstop'
  have hsU : cylinderM1Point k i ∈ (L.pathDrawing i).V := (isPathDrawing_end_vertices (L.isPath i)).1
  have hsne : cylinderM1Point k i ≠ lab (H dl) := by
    intro h
    rw [← h] at huT
    rcases huT with ⟨-, hs⟩ | hs
    · exact hs rfl
    · exact disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i).symm)
        ((L.pathDrawing i).V_subset_U hsU) ((L.pathDrawing _).V_subset_U hs)
  have hQsub : IsSubpathOf G (walkDrawing G W) (cylinderM1Point k i) (lab (H dl)) :=
    ⟨walkDrawing_isSubdrawing G W, (walkDrawing_isSubdrawing G W).U_subset,
      isPathDrawing_walkDrawing_of_isSimple G hWsimple hsne⟩
  have hsR : cylinderM1Point k i ∈ closure (cylinderRegion k G i) :=
    (initial_vertices_mem_closure_cylinderRegion hG i).1
  have hheadR : ∀ d ∈ trace, lab (H d) ∈ closure (cylinderRegion k G i) := by
    intro d hd
    obtain ⟨hl, hR⟩ := hedge d hd
    have : lab (H d) ∈ closure (edgeOf d) ∩ G.V := by
      rw [hl.2.2.2]; exact mem_insert_of_mem _ (mem_singleton _)
    exact closure_minimal hR isClosed_closure this.1
  have hQR : (walkDrawing G W).U ⊆ closure (cylinderRegion k G i) := by
    rw [walkDrawing_U_subset_iff G W isClosed_closure, hWs, hWe]
    refine ⟨fun y hy => ?_, fun e he => ?_⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [rep.start_lab]; exact hsR
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
        exact hheadR d (hQd_trace d hd)
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
      exact (hedge d (hQd_trace d hd)).2
  have hint : (walkDrawing G W).V ∩ (⋃ j : Fin k, (L.pathDrawing j).V) ⊆
      {cylinderM1Point k i, lab (H dl)} := by
    rintro x ⟨hx, hxL⟩
    rw [walkDrawing_V, mem_ofPred_eq, hWs] at hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Or.inl rep.start_lab
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hv
    have hdt := hQd_trace d hd
    rw [← List.dropLast_append_getLast hne] at hdt
    rcases List.mem_append.mp hdt with hdrop | hlastd
    · -- an inner vertex: unmarked, so off the targets
      have h0 : targets[H d]?.getD 0 = 0 := hinternal d hdrop
      have hnotT : lab (H d) ∉ terminalTargets L i := fun h =>
        ((rep.target_iff d (htrace_ds d (List.mem_of_mem_dropLast hdrop))).mpr h) h0
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxL
      rcases mem_path_of_mem_closure_strip L hG hθ i j
        (closure_mono (cylinderRegion_subset_strip L i)
          (hheadR d (List.mem_of_mem_dropLast hdrop))) ((L.pathDrawing j).V_subset_U hj)
        with rfl | rfl
      · by_cases hs : lab (H d) = cylinderM1Point k j
        · exact Or.inl hs
        · exact absurd (Or.inl ⟨hj, hs⟩) hnotT
      · exact absurd (Or.inr hj) hnotT
    · rw [List.mem_singleton.mp hlastd, ← hdl]
      exact Or.inr rfl
  have hu : lab (H dl) ∈ ⋃ j : Fin k, (L.pathDrawing j).V := by
    rcases huT with ⟨h, -⟩ | h
    · exact mem_iUnion.mpr ⟨i, h⟩
    · exact mem_iUnion.mpr ⟨_, h⟩
  obtain ⟨hu1, hu2, hu3, hu4⟩ :=
    lemma15_of_region_path L hk hG hθ hno i hval hQsub hQR hint hu
  refine ⟨lab (H dl), walkDrawing G W, ?_, ?_, hu1, hu2, hQsub, hu3, hu4⟩
  · rw [walkDrawing_V, hWs]
  · rw [walkDrawing_E, hWe]

/-- **`TERMINAL_PATH` gives a linkage of winding `θ + 1/k`** (`k ≥ 2`, Lemmas 15 and 16). If no
reduction applies, no `sᵢ` has valency one, and for every `i` the lists of `TERMINAL_PATH`
represent the drawing, then `θ + 1/k` is feasible: the paths `Qᵢ` it returns, followed by the
tails of `Pᵢ₊₁`, form a linkage. -/
theorem isThetaFeasible_next_of_terminal_paths {θ : ℝ} {L : CylinderLinkage k G} (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hval : ∀ i, vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    (hrep : ∀ i, ∃ (heads targets ds : List ℕ) (s₀ : ℕ) (tail : ℕ → ℕ)
      (lab : ℕ → ClosedCylinder) (edgeOf : ℕ → Set ClosedCylinder),
      TerminalRep L i heads targets ds s₀ tail lab edgeOf) :
    IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
  apply isThetaFeasible_next_of_strip_paths L hG hk hθ
  intro i
  obtain ⟨heads, targets, ds, s₀, tail, lab, edgeOf, rep⟩ := hrep i
  obtain ⟨u, Q, -, -, hu1, hu2, hQ, hu3, hu4⟩ := terminal_path_spec hk hG hθ hno (hval i) rep
  exact ⟨u, hu1, hu2, Q, hQ, hu3, hu4⟩

end GraphMinor.GM06
