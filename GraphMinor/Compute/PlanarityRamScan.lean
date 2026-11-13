module

public import GraphMinor.Compute.PlanarityRamVisited
public import GraphMinor.Compute.PlanarityRamTreeChild
public import GraphMinor.Compute.PlanarityRamNeighbor
public import GraphMinor.Compute.PlanarityRamStepInvariant
import Mathlib.Tactic.SplitIfs

/-!
# Scanning one adjacency entry on the RAM

The program reads the next neighbor, advances the top frame, and selects
the fresh-child or visited-neighbor action. The record budget guarantees
an edge slot whenever an incidence is still unscanned. Vertex ownership
guarantees a frame slot whenever the neighbor is fresh.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- One scan branch takes at most 150 steps. Its hypotheses are the input
representation, search/frame representations, proved data invariants,
remaining-record budget, the loaded frame, and linear-size word bounds. -/
theorem scanNeighborProg_refines {N M w : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : State} {search : Search} {stack : List Frame} {f : Frame}
    (hadj : IsAdjList G 30 31 32 lists s)
    (h : DfsSearchAt N M s search) (hf : FramesAt N s (f :: stack))
    (hb : SearchBounded N search)
    (hs : FrameInvariant (List.ofFn lists).toArray search (f :: stack))
    (hv : f.vertex < N) (hscan : f.next < (lists ⟨f.vertex, hv⟩).length)
    (hrv : s.regs 41 = f.vertex) (hrk : s.regs 42 = f.next)
    (hbudget : search.edges.size + searchWork (List.ofFn lists).toArray 0 search (f :: stack) ≤ M)
    (hw : 2 * (N + M + 2) < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w) :
    ∃ next nextStack s' t,
      frameStep (List.ofFn lists).toArray search f stack = some (next, nextStack) ∧
      Exec w scanNeighborProg s s' t ∧ t ≤ 150 ∧
      FramesAt N s' nextStack ∧ DfsSearchAt N M s' next := by
  let adj := (List.ofFn lists).toArray
  let vertex : Fin N := ⟨f.vertex, hv⟩
  let u := (lists vertex)[f.next]
  let advanced : Frame := { f with next := f.next + 1 }
  have hadjsize : adj.size = N := by simp [adj]
  have hlist : adj[f.vertex]! = lists vertex := by
    rw [getElem!_pos adj f.vertex (by rw [hadjsize]; exact hv)]
    simp [adj, vertex]
  have hscanAdj : f.next < adj[f.vertex]!.length := by rw [hlist]; exact hscan
  have hdone : ¬f.next ≥ adj[f.vertex]!.length := by omega
  have hueq : adj[f.vertex]![f.next]! = u := by rw [hlist, getElem!_pos (lists vertex) f.next hscan]
  have hu : u < N := (hadj.2 vertex).1 _ (List.getElem_mem hscan)
  have huAdj : u < adj.size := by rw [hadjsize]; exact hu
  have hurange : ¬u ≥ adj.size := by omega
  have hlen : (lists vertex).length ≤ N := (hadj.2 vertex).2.2.1
  have hkN : f.next < N := Nat.lt_of_lt_of_le hscan hlen
  change search.edges.size + searchWork adj 0 search (f :: stack) ≤ M at hbudget
  have hfree : search.edges.size < M := by
    have hh := searchWork_advance adj 0 search f stack hscanAdj
    omega
  have hcapacity : (f :: stack).length + search.postorder.length ≤ N := by
    simpa only [List.size_toArray, List.length_ofFn] using hs.capacity
  have hvd : f.vertex < search.depth.size := by rw [hb.1]; exact hv
  have hud : u < search.depth.size := by rw [hb.1]; exact hu
  have hvtag : optionWord search.depth[f.vertex] ≤ N := by
    have hh := hb.depth_tag_le vertex
    change optionWord (search.depth[f.vertex]?.join) ≤ N at hh
    simpa only [Array.getElem?_eq_getElem hvd, Option.join_some] using hh
  have hutag : optionWord search.depth[u] ≤ N := by
    have hh := hb.depth_tag_le ⟨u, hu⟩
    simpa only [Array.getElem?_eq_getElem hud, Option.join_some] using hh
  have hnword : N < 2 ^ w := by omega
  have huword : u < 2 ^ w := by omega
  have hx1 := readNeighborProg_exec hadj.1 vertex f.next hscan hrv hrk hnword hentries huword
  let s1 := s.setReg 43 u
  have h1 : DfsSearchAt N M s1 search := h.setReg 43 u (by decide) (by decide)
  have hf1 : FramesAt N s1 (f :: stack) := hf.setReg 43 u (by decide)
  obtain ⟨s2, hx2, hf2, h2⟩ := advanceFrameProg_refines (w := w) hf1 h1
    (by simpa [s1] using hrk) (by simp only [List.length_cons] at hcapacity; omega) (by omega)
  have hr2 (r : ℕ) : s2.regs r = s1.regs r := hx2.regs_eq_of_not_mem_writtenRegs
    (by simp [advanceFrameProg])
  have hrv2 : s2.regs 41 = f.vertex := (hr2 41).trans (by simpa [s1] using hrv)
  have hru2 : s2.regs 43 = u := by rw [hr2]; simp [s1]
  have dPrefix : PrefixAt s2 Field.depth.array N (search.depth.toList.map optionWord) := h2.2.2.2.2.2.1
  have hread : (Expr.read Field.depth.array (.reg 43)).eval w s2 = some (optionWord search.depth[u]) :=
    dPrefix.read_option_reg hud hru2 huword (by omega)
  cases hdepth : search.depth[u]?.join with
  | none =>
    have hraw : search.depth[u] = none := by
      simpa only [Array.getElem?_eq_getElem hud, Option.join_some] using hdepth
    have eread : (Expr.read Field.depth.array (.reg 43)).eval w s2 = some 0 := by
      simpa only [hraw, optionWord] using hread
    have hroom := hs.fresh_capacity ⟨u, huAdj⟩ hdepth
    have hnewDepth := hs.child_depth_lt ⟨u, huAdj⟩ hdepth
    have hframe : (advanced :: stack).length < N := by
      simp only [List.length_cons] at hroom ⊢
      rw [hadjsize] at hroom
      omega
    obtain ⟨s3, t3, hx3, ht3, hf3, h3⟩ := treeChildProg_refines (w := w) h2 hf2 f.vertex u hvd hud hrv2 hru2
      hfree hframe (by omega) (by omega) huword (by omega) (by omega) (by omega)
      (by simp only [List.length_cons] at hroom ⊢; rw [hadjsize] at hroom; omega) (by
        rw [hadjsize] at hnewDepth
        omega)
    refine ⟨discoverChild (addEdge search f.vertex u true).1 f.vertex u search.edges.size,
      ⟨u, 0⟩ :: advanced :: stack, s3, 6 + (7 + (2 + t3)), ?_,
      Exec.seq hx1 (Exec.seq hx2 (Exec.ite_false eread hx3)), by omega, hf3, h3⟩
    change frameStep adj search f stack = _
    simp only [frameStep, hdone, hueq, hurange, hdepth, Option.isNone_none, ↓reduceIte]
    rfl
  | some du =>
    have hraw : search.depth[u] = some du := by
      simpa only [Array.getElem?_eq_getElem hud, Option.join_some] using hdepth
    have eduN := hb.2.2.2.1 ⟨u, hu⟩ du hdepth
    have eread : (Expr.read Field.depth.array (.reg 43)).eval w s2 = some (du + 1) := by
      simpa only [hraw, optionWord] using hread
    obtain ⟨s3, t3, hx3, ht3, hf3, h3⟩ := visitedNeighborProg_refines (w := w) h2 hf2 hb f.vertex u stack.length du
      hv hu hs.top_depth hdepth hrv2 hru2 hfree hw
    refine ⟨visitedSearch search f.vertex u, advanced :: stack, s3, 6 + (7 + (2 + t3)), ?_,
      Exec.seq hx1 (Exec.seq hx2 (Exec.ite_true eread (by omega) hx3)), by omega, hf3, h3⟩
    change frameStep adj search f stack = _
    simp only [frameStep, hdone, hueq, hurange, hdepth, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    unfold visitedSearch
    simp only [hdepth, Option.getD_some]
    split_ifs <;> rfl

end GraphMinor.Compute.PlanarityRam
