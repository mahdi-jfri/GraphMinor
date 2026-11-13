module

public import GraphMinor.GM06.Alg57TerminalPathLink
import all GraphMinor.GM06.Alg57TerminalPathLink
import GraphMinor.GM06.Section5NextContact
public import GraphMinor.Compute.GM06LinkageRowsEncoding
import GraphMinor.GM06.Section5SpliceWinding
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section5StripDisjoint
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The terminal splice of VI (5.7) with exact rows

When no reduction applies, the algorithm on page 133 traces each face
from `sᵢ` to its first contact with the target set, erases closed
subwalks, and follows the result by the tail of the next path. The new
paths form a linkage of winding `θ + 1/k`.

This file gives two steps of that argument in a form that keeps the
rows.

* `terminal_erased_walk`: the loop-erased trace is a dart walk that
  ends at a numeric vertex `t` whose point is the contact `u` of
  Lemma 15. The point `u` is a vertex of `Pᵢ₊₁` other than `sᵢ₊₁`.
  The end of the trace is a marked head, so its point is a target. A
  target is on a linkage path, hence not in the strip `Σᵢ`, and it is
  not `sᵢ`. Lemma 15 puts the path inside `Σᵢ ∪ {sᵢ, u}`, so the end
  must be `u`.
* `exists_encoded_spliced_linkage`: given, for each `i`, a simple walk
  from `sᵢ` to the end of `Pᵢ₊₁` inside `Σᵢ ∪ {sᵢ} ∪ Pᵢ₊₁` and missing
  `sᵢ₊₁`, these walks are the paths of a linkage of winding `θ + 1/k`,
  and their encodings are its rows. Disjointness is the case analysis
  of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-- **The end of the loop-erased trace** (`k ≥ 2`). In the setting of
Lemma 15, the erased trace is a simple dart walk from `s₀` whose darts
are darts of the face row with unmarked tails. Its end `t` is marked,
its point is a vertex of `Pᵢ₊₁` other than `sᵢ₊₁`, and the drawing `Q`
listed by the erased walk lies in `Σᵢ ∪ {sᵢ, t}` and meets `Pᵢ₊₁` only
at `t`. -/
theorem terminal_erased_walk {θ : ℝ} {L : CylinderLinkage k G} (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) {i : Fin k}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {heads targets ds : List ℕ} {s₀ : ℕ} {tail : ℕ → ℕ} {lab : ℕ → ClosedCylinder}
    {edgeOf : ℕ → Set ClosedCylinder}
    (rep : TerminalRep L i heads targets ds s₀ tail lab edgeOf) :
    ∃ t, GM06DartWalk tail (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1) t ∧
      (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
        (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1)).Nodup ∧
      (∀ d ∈ gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1, d ∈ ds ∧ targets[tail d]?.getD 0 = 0) ∧
      targets[t]?.getD 0 ≠ 0 ∧
      lab t ∈ (L.pathDrawing (finSuccCycle i)).V ∧
      lab t ≠ cylinderM1Point k (finSuccCycle i) ∧
      ∃ Q : Drawing ClosedCylinder,
        Q.V = {x | x ∈ (gm06WalkVertices (fun d => heads[d]?.getD 0) s₀
          (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
            (gm06TerminalTrace heads targets ds).1)).map lab} ∧
        Q.E = {e | e ∈ (gm06EraseClosedSubwalks (fun d => heads[d]?.getD 0) s₀
          (gm06TerminalTrace heads targets ds).1).map edgeOf} ∧
        Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, lab t} ∧
        Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {lab t} := by
  obtain ⟨u, Q, hQV, hQE, hu1, hu2, -, hu3, hu4⟩ := terminal_path_spec hk hG hθ hno hval rep
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
    rw [List.getLast?_eq_some_getLast hne] at hlast
    exact (Option.some.inj hlast).symm
  have hstop' : targets[H dl]?.getD 0 ≠ 0 := by
    simpa [gm06TerminalContact] using hstop
  have htrace_ds : ∀ d ∈ trace, d ∈ ds := fun d hd => hpre.subset hd
  obtain ⟨t, hw⟩ := rep.walk
  obtain ⟨rest, hrest⟩ := hpre
  obtain ⟨u₀, hwt⟩ : ∃ u, GM06DartWalk tail H s₀ trace u :=
    GM06DartWalk.of_append (hrest ▸ hw)
  have hu₀ : u₀ = H dl := by rw [GM06DartWalk.end_eq hwt hne, hdl]
  subst hu₀
  have htails : ∀ d ∈ trace, targets[tail d]?.getD 0 = 0 := by
    intro d hd
    rcases List.mem_cons.mp (GM06DartWalk.tail_mem hwt d hd) with h | h
    · rw [h]; exact rep.start_tgt
    · obtain ⟨d', hd', hdd⟩ := List.mem_map.mp h
      rw [← hdd]
      exact hinternal d' hd'
  obtain ⟨hwQ, hndQ, hsubQ⟩ := gm06EraseClosedSubwalks_spec hwt
  have hdl_ds : dl ∈ ds := htrace_ds dl (by rw [hdl]; exact List.getLast_mem hne)
  have huT : lab (H dl) ∈ terminalTargets L i := (rep.target_iff dl hdl_ds).mp hstop'
  -- the end of the erased walk is a vertex of `Q`
  have hst : ∀ {a b : ℕ}, GM06DartWalk tail H a [] b → a = b := fun h => by cases h; rfl
  have hQdne : gm06EraseClosedSubwalks H s₀ trace ≠ [] := by
    intro h
    rw [h] at hwQ
    exact hstop' (hst hwQ ▸ rep.start_tgt)
  have htQ : H dl ∈ gm06WalkVertices H s₀ (gm06EraseClosedSubwalks H s₀ trace) := by
    rw [GM06DartWalk.end_eq hwQ hQdne]
    exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.getLast_mem hQdne))
  have hlabQ : lab (H dl) ∈ Q.U := by
    apply Q.V_subset_U
    rw [hQV]
    exact List.mem_map_of_mem htQ
  -- so the end is the contact of Lemma 15
  have hsP : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have hnotStrip : lab (H dl) ∉ cylinderStrip L i := by
    intro hS
    obtain ⟨j, hj⟩ : ∃ j, lab (H dl) ∈ (L.pathDrawing j).U := by
      rcases huT with ⟨h, -⟩ | h
      · exact ⟨i, (L.pathDrawing i).V_subset_U h⟩
      · exact ⟨_, (L.pathDrawing _).V_subset_U h⟩
    exact (connectedComponentIn_subset _ _ hS).2 (mem_iUnion.mpr ⟨j, hj⟩)
  have hnots : lab (H dl) ≠ cylinderM1Point k i := by
    intro h
    rw [h] at huT
    rcases huT with ⟨-, hs⟩ | hs
    · exact hs rfl
    · exact disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i).symm)
        hsP ((L.pathDrawing _).V_subset_U hs)
  have hut : lab (H dl) = u := by
    rcases hu3 hlabQ with hS | hS
    · exact absurd hS hnotStrip
    · rcases hS with h | h
      · exact absurd h hnots
      · exact h
  subst hut
  exact ⟨H dl, hwQ, hndQ, fun d hd => ⟨htrace_ds d (hsubQ.subset hd), htails d (hsubQ.subset hd)⟩,
    hstop', hu1, hu2, Q, hQV, hQE, hu3, hu4⟩

private theorem strip_point_not_mem_path' (L : CylinderLinkage k G)
    (i j : Fin k) {x : ClosedCylinder} (hx : x ∈ cylinderStrip L i) :
    x ∉ (L.pathDrawing j).U := by
  intro hxj
  exact (connectedComponentIn_subset _ _ hx).2 (mem_iUnion.mpr ⟨j, hxj⟩)

/-- Point sets confined as in VI (5.1), page 129, are pairwise disjoint:
each lies in its strip, its start and the next old path, and misses the
start of that next path. -/
theorem pairwise_disjoint_of_strip_confinement' {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (R : Fin k → Set ClosedCylinder)
    (hconf : ∀ i, R i ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
      (L.pathDrawing (finSuccCycle i)).U)
    (havoid : ∀ i, cylinderM1Point k (finSuccCycle i) ∉ R i) :
    Pairwise fun i j => Disjoint (R i) (R j) := by
  intro i j hij
  have hs (a : Fin k) : cylinderM1Point k a ∈ (L.pathDrawing a).U :=
    (L.pathDrawing a).V_subset_U (isPathDrawing_end_vertices (L.isPath a)).1
  have hsucc : finSuccCycle i ≠ finSuccCycle j := by
    intro he
    apply hij
    have hp := congrArg finPredCycle he
    simpa only [finPredCycle_finSuccCycle] using hp
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases hconf i hxi with (hxiS | hxiS) | hxiP
  · rcases hconf j hxj with (hxjS | hxjS) | hxjP
    · exact disjoint_left.mp (disjoint_cylinderStrip L hG hθ hij) hxiS hxjS
    · exact strip_point_not_mem_path' L i j hxiS
        ((mem_singleton_iff.mp hxjS).symm ▸ hs j)
    · exact strip_point_not_mem_path' L i (finSuccCycle j) hxiS hxjP
  · have he : x = cylinderM1Point k i := mem_singleton_iff.mp hxiS
    subst x
    rcases hconf j hxj with (hxjS | hxjS) | hxjP
    · exact strip_point_not_mem_path' L j i hxjS (hs i)
    · exact hij (cylinderM1Point_injective hG.1 (mem_singleton_iff.mp hxjS))
    · by_cases he : i = finSuccCycle j
      · apply havoid j
        rw [← he]
        exact hxj
      · exact disjoint_left.mp (L.pairwise_disjoint he) (hs i) hxjP
  · rcases hconf j hxj with (hxjS | hxjS) | hxjP
    · exact strip_point_not_mem_path' L j (finSuccCycle i) hxjS hxiP
    · have he : x = cylinderM1Point k j := mem_singleton_iff.mp hxjS
      subst x
      by_cases he : j = finSuccCycle i
      · apply havoid i
        rw [← he]
        exact hxi
      · exact disjoint_left.mp (L.pairwise_disjoint he) (hs j) hxiP
    · exact disjoint_left.mp (L.pairwise_disjoint hsucc) hxiP hxjP

/-- **The spliced linkage with exact rows** (`k ≥ 2`, VI (5.1), page
129). Simple encoded walks from each `sᵢ` to the end of `Pᵢ₊₁`, inside
`Σᵢ ∪ {sᵢ} ∪ Pᵢ₊₁` and missing `sᵢ₊₁`, are the paths of a linkage of
winding `θ + 1/k` whose rows are their encodings. -/
theorem exists_encoded_spliced_linkage {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hk : 1 < k) (hθ : L.HasTheta θ)
    {m : ℕ} {tagged : List ((Fin m × Fin m) × ℕ)} {vertex : Fin m → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} (rows : List (List ℕ))
    (hlen : rows.length = k)
    (W : ∀ i : Fin k, GraphWalk G.toGraph (cylinderM1Point k i) (L.curve (finSuccCycle i) 1))
    (hW : ∀ i, (W i).IsSimple)
    (henc : ∀ i : Fin k, GM06WalkDartEncoding G.toGraph tagged vertex edge (W i)
      (rows[i.val]?.getD []))
    (hconf : ∀ i, (walkDrawing G (W i)).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
      (L.pathDrawing (finSuccCycle i)).U)
    (havoid : ∀ i, cylinderM1Point k (finSuccCycle i) ∉ (walkDrawing G (W i)).U) :
    ∃ L' : CylinderLinkage k G, L'.HasTheta (θ + 1 / (k : ℝ)) ∧
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      GM06LinkageRowsEncoding L' tagged vertex edge rows := by
  classical
  have hne : ∀ i : Fin k, cylinderM1Point k i ≠ L.curve (finSuccCycle i) 1 := by
    intro i h
    have hs : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
      (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
    have ht : L.curve (finSuccCycle i) 1 ∈ (L.pathDrawing (finSuccCycle i)).U :=
      (L.pathDrawing _).V_subset_U (isPathDrawing_end_vertices (L.isPath _)).2
    rw [h] at hs
    exact disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i).symm) hs ht
  have hPD : ∀ i, IsPathDrawing (walkDrawing G (W i)) (cylinderM1Point k i)
      (L.curve (finSuccCycle i) 1) := fun i =>
    isPathDrawing_walkDrawing_of_isSimple G (hW i) (hne i)
  choose f hf using fun i => (hPD i).2
  have hdisj := pairwise_disjoint_of_strip_confinement' L hG hθ (fun i => (walkDrawing G (W i)).U)
    hconf havoid
  let L' : CylinderLinkage k G := {
    pathDrawing := fun i => walkDrawing G (W i)
    curve := f
    isSubdrawing i := ⟨walkDrawing_isSubdrawing G (W i), (walkDrawing_isSubdrawing G (W i)).U_subset⟩
    isPath i := by
      rw [(hf i).2.2.2]
      exact hPD i
    curve_parametrizes i := ⟨(hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
    curve_one_mem i := by
      rw [(hf i).2.2.2]
      exact L.curve_one_mem (finSuccCycle i)
    pairwise_disjoint := hdisj }
  have hend : ∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1 := fun i => (hf i).2.2.2
  refine ⟨L', theta_next_of_spliced_linkage L L' hG hk hθ hend hconf, hend, hlen, fun j => ?_⟩
  change ∃ A : GraphWalk G.toGraph (cylinderM1Point k j) (f j 1),
    A.IsSimple ∧ GM06WalkDartEncoding G.toGraph tagged vertex edge A (rows[j.val]?.getD []) ∧
      walkDrawing G A = walkDrawing G (W j)
  rw [(hf j).2.2.2]
  exact ⟨W j, hW j, henc j, rfl⟩

end GraphMinor.GM06
