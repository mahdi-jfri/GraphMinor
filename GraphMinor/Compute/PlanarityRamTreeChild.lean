module

public import GraphMinor.Compute.PlanarityRamFrameKeep

/-!
# The tree-child branch of a frame step

When the scanned neighbor is undiscovered, the program creates its tree
edge, marks its vertex data, and pushes its initial frame. This proof
composes the three local refinements. Frame preservation during the first
two calls ensures that the final push extends the same live stack.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The complete tree-child branch takes at most sixty-two steps. Its local
input conditions give available edge/frame slots, valid endpoints in their
registers, and word bounds for the labels, depths, and counters. Freshness
is tested by the caller and is not needed for this storage refinement. -/
theorem treeChildProg_refines {N M w : ℕ} {s : State} {search : Search}
    {stack : List Frame} (h : DfsSearchAt N M s search) (hf : FramesAt N s stack)
    (v u : ℕ) (hv : v < search.depth.size) (hu : u < search.depth.size)
    (hrv : s.regs 41 = v) (hru : s.regs 43 = u)
    (hedge : search.edges.size < M) (hframe : stack.length < N)
    (hw : 2 < 2 ^ w) (hvw : v + 1 < 2 ^ w) (huw : u < 2 ^ w)
    (hvd : optionWord search.depth[v] < 2 ^ w) (hud : optionWord search.depth[u] < 2 ^ w)
    (hecount : search.edges.size + 1 < 2 ^ w) (hfcount : stack.length + 1 < 2 ^ w)
    (hnew : (search.depth[v]?.join).getD 0 + 2 < 2 ^ w) :
    ∃ s' t, Exec w treeChildProg s s' t ∧ t ≤ 62 ∧ FramesAt N s' (⟨u, 0⟩ :: stack) ∧
      DfsSearchAt N M s'
        (discoverChild (addEdge search v u true).1 v u search.edges.size) := by
  obtain ⟨s1, t1, hx1, ht1, hs1⟩ := addEdgeProg_refines h v u true hv hu hrv hru
    hedge (by omega) (by omega) huw hvd hud hecount
  have hs1' : SearchAt N M s1 (reversePostorder (addEdge search v u true).1) := by
    rw [reversePostorder_addEdge]
    exact hs1
  have hf1 := hf.addEdge_exec true hx1
  have hr1 := addEdgeProg_endpoints true hx1
  have hrv1 : s1.regs 41 = v := hr1.1.trans hrv
  have hru1 : s1.regs 43 = u := hr1.2.trans hru
  obtain ⟨s2, hx2, hs2⟩ := discoverChildProg_refines hs1' v u search.edges.size hv hu hrv1 hru1
    (by simp [reversePostorder, addEdge]) hw hvw huw hecount hvd hnew
  have hf2 := hf1.discoverChild_exec hx2
  have hr2 := discoverChildProg_endpoints hx2
  obtain ⟨s3, hx3, hf3, hs3⟩ := pushFrameProg_refines hf2 hs2 hframe u
    (hr2.2.trans hru1) hfcount huw
  exact ⟨s3, t1 + (16 + 10), Exec.seq hx1 (Exec.seq hx2 hx3), by omega, hf3, hs3⟩

end GraphMinor.Compute.PlanarityRam
