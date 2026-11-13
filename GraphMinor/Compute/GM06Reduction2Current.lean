module

public import GraphMinor.GM06.Alg57DeletionCurrentMasks
public import GraphMinor.Compute.GM06Reduction2Scan
public import GraphMinor.Compute.GM06PruneRotations
import GraphMinor.GM06.Section5NoComputedReduction2
import GraphMinor.GM06.Section5ComputedReduction2Masks
import GraphMinor.GM06.Section5InitialLoop

/-!
# Reduction 2 preserves the current drawing relation

The branch in VI (5.7), page 133, scans the actual initial vertices.
A loop deletion clears one ordinary flag. A component deletion
retains an induced live set. The literal mask lemmas construct the
full new geometric relation in both cases, including positive
filtered rotations and the unchanged-row undo step. The following
RAM command also installs those filtered rotations before returning
to the main loop. Failed scans preserve the input fields.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Perform the first Reduction 2 update and prune rotations exactly
when the scan changed the graph. Register 294 reports success. -/
@[expose] def gm06Reduction2CurrentProg : Cmd :=
  .seq gm06Reduction2ScanProg (.ite (.reg 294) gm06PruneCurrentRotationsProg .skip)

/-- The bound for the existing dense component scan. -/
@[expose] def gm06Reduction2ScanCost (n m k : ℕ) : ℕ :=
  7 + k * (137 + n * (53 * (n * n) + 64 * n + 48 * m + 78) +
    53 * (n * n) + 93 * n + 129 * m)

/-- Scanning the actual current drawing either excludes every
Reduction 2 or computes masks for a complete new current relation.
The new rotations are the literal filters to be installed next. -/
theorem gm06Reduction2ScanProg_current
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (Q : Finset (Fin x.vertexCount))
    (hQ : rep.vertex '' (Q : Set (Fin x.vertexCount)) = ⋃ i : Fin k, (L.pathDrawing i).V)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hm : 2 * rep.tagged.length < 2 ^ w) (hk : k < 2 ^ w)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1) {s : State}
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits rep.live)
    (h17 : s.arrs 17 = gm02VertexBits Q) (hN : s.regs 100 = x.vertexCount) :
    ∃ s' t, Exec w gm06Reduction2ScanProg s s' t ∧
      t ≤ gm06Reduction2ScanCost x.vertexCount rep.tagged.length k ∧
      (∀ a : ℕ, a < 28 → a ≠ 12 → a ≠ 14 → a ≠ 15 → a ≠ 16 → a ≠ 22 → a ≠ 23 →
        s'.arrs a = s.arrs a) ∧ s'.regs 100 = x.vertexCount ∧
      ((s'.regs 294 = 0 ∧ s'.arrs 12 = rep.tagged.map Prod.snd ∧
          s'.arrs 14 = gm02VertexBits rep.live ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction2Step k G L H M) ∨
       ∃ (mask : List ℕ) (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
         (cur : GM06CurrentDrawingRep (gm06RestrictSuccessorInput x mask) H M),
         s'.regs 294 ≠ 0 ∧ s'.regs 294 < 3 ∧
         s'.arrs 12 = mask ∧ s'.arrs 14 = gm02VertexBits cur.live ∧
         mask.length = rep.tagged.length ∧ (∀ z ∈ mask, z ≤ 1) ∧
         cur.tagged = gm06RetagEdges rep.tagged mask ∧ cur.vertex = rep.vertex ∧
         IsCylinderSection5Drawing k H ∧ Section5Reduction2Step k G L H M ∧
         cur.live.card + mask.count 1 < rep.live.card + (rep.tagged.map Prod.snd).count 1 ∧
         GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
           ⟨H, cur.tagged, cur.vertex, cur.edge⟩ none) := by
  classical
  let vertex : Fin x.vertexCount ↪ ClosedCylinder := ⟨rep.vertex, hvinj⟩
  have hV : G.V = vertex '' (rep.live : Set (Fin x.vertexCount)) := by
    ext v
    exact ⟨fun hv => rep.vertex_cover v hv, fun ⟨a, ha, hav⟩ => hav ▸ rep.vertex_mem a ha⟩
  have hcuts : (List.ofFn rep.source).map Fin.val = x.innerCuff := by
    rw [List.map_ofFn]
    exact rep.inner.symm
  obtain ⟨s', t, he, ht, hframe, hN', hout⟩ := gm06Reduction2ScanProg_exec rep.tagged
    (List.ofFn rep.source) Q rep.live hw hn hsquare hm
    (by simpa only [List.length_ofFn] using hk) hbits
    (h3.trans rep.endpoints) h12 (h6.trans hcuts.symm) h17 h14 hN
  refine ⟨s', t, he, by simpa only [gm06Reduction2ScanCost, List.length_ofFn] using ht,
    hframe, hN', ?_⟩
  rcases hout with ⟨hflag, hA, hmask, hfailed⟩ | ⟨cut, hcutMem, _, hloop | hcomponent⟩
  · left
    refine ⟨hflag, hmask, hA, ?_⟩
    intro H M
    exact not_reduction2_of_finite_tests L M rep.tagged vertex rep.edge rep.links rep.edge_cover
      rep.live hV rep.source rep.source_point Q hQ.subset
      (fun i => (hfailed (rep.source i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).1)
      (fun i => (hfailed (rep.source i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).2)
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hcutMem
    have hcutGeom : rep.vertex cut = cylinderM1Point k i :=
      (congrArg rep.vertex hi.symm).trans (rep.source_point i)
    obtain ⟨hflag, hA, j, hactive, hu, hv, hmask, hprogress⟩ := hloop
    have hl := rep.links j hactive
    rw [hu, hv, hcutGeom] at hl
    obtain ⟨M, hH, hred⟩ := exists_reduction2_of_initial_loop L hG i (rep.edge j) hl
    obtain ⟨cur, hcurA, hvertex, htag, hundo⟩ := rep.exists_deleted_currentDrawingRep
      hG j hactive M hH hred.pathDrawing_eq hred.curve_eq
    right
    refine ⟨(rep.tagged.map Prod.snd).set j.val 0, G.deleteEdge (rep.edge j), M, cur,
      by omega, by omega, hmask, hA.trans (congrArg gm02VertexBits hcurA).symm, by simp, ?_, htag, hvertex, hH, hred, ?_, hundo⟩
    · intro z hz
      rcases List.mem_or_eq_of_mem_set hz with hz | hz
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
        exact hbits p hp
      · exact hz ▸ Nat.zero_le 1
    · have hedrop : ((rep.tagged.map Prod.snd).set j.val 0).count 1 <
          (rep.tagged.map Prod.snd).count 1 := by
        rw [hmask] at hprogress
        omega
      exact (congrArg (fun A : Finset (Fin x.vertexCount) => A.card +
        ((rep.tagged.map Prod.snd).set j.val 0).count 1) hcurA) ▸
        Nat.add_lt_add_left hedrop rep.live.card
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hcutMem
    have hcutGeom : vertex cut = cylinderM1Point k i :=
      (congrArg rep.vertex hi.symm).trans (rep.source_point i)
    obtain ⟨hflag, source, hsource, hzero, hA, hmask, hprogress⟩ := hcomponent
    let C := rep.live \ reachSet (gm06PuncturedGraphData rep.tagged cut).vertexGraph source
    have hprotect : ∀ j : Fin k, (L.pathDrawing j).V ⊆ vertex '' (Q : Set (Fin x.vertexCount)) := by
      intro j v hv
      change v ∈ rep.vertex '' (Q : Set (Fin x.vertexCount))
      rw [hQ]
      exact mem_iUnion.mpr ⟨j, hv⟩
    obtain ⟨M, hH, hred⟩ := exists_reduction2_of_computed_live_masks L hG rep.tagged vertex rep.edge
      rep.links rep.edge_cover rep.live hV cut source i hcutGeom hsource Q hprotect hzero
    obtain ⟨cur, hcurA, hvertex, htag, hundo⟩ := rep.exists_induced_currentDrawingRep
      hvinj hG C Finset.sdiff_subset M hH hred.pathDrawing_eq hred.curve_eq
    right
    refine ⟨gm06InducedEdgeBits rep.tagged C, _, M, cur, by omega, by omega, hmask,
      hA.trans (congrArg gm02VertexBits hcurA).symm, gm06InducedEdgeBits_length _ _, gm06InducedEdgeBits_le_one _ _ hbits,
      htag, hvertex, hH, hred, ?_, hundo⟩
    have hedge := gm06InducedEdgeBits_count_le rep.tagged C
    change C.card < rep.live.card at hprogress
    exact (congrArg (fun A : Finset (Fin x.vertexCount) =>
      A.card + (gm06InducedEdgeBits rep.tagged C).count 1) hcurA) ▸
      Nat.add_lt_add_of_lt_of_le hprogress hedge

/-- Installing the rotation filters after a successful scan returns
an actual complete current drawing and a strict decrease of live
vertices plus active edges. Failed scans leave all instance arrays
unchanged. The history and the loop bit are preserved. -/
theorem gm06Reduction2CurrentProg_exec
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hvinj : Function.Injective rep.vertex) (hG : IsCylinderSection5Drawing k G)
    (Q : Finset (Fin x.vertexCount))
    (hQ : rep.vertex '' (Q : Set (Fin x.vertexCount)) = ⋃ i : Fin k, (L.pathDrawing i).V)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (hsquare : x.vertexCount * x.vertexCount < 2 ^ w)
    (hm : 2 * rep.tagged.length < 2 ^ w) (hk : k < 2 ^ w)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1)
    (hrotLen : 4 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hrotWords : ∀ z ∈ gm06EncodeRows x.rotations, z < 2 ^ w)
    (haug : rep.tagged.length + 2 * x.innerCuff.length < 2 ^ w)
    (hdarts : ∀ row ∈ x.rotations, ∀ d ∈ row, d < 2 * (rep.tagged.length + 2 * x.innerCuff.length))
    {s : State} (h3 : s.arrs 3 = x.endpoints) (h4 : s.arrs 4 = gm06EncodeRows x.rotations)
    (h6 : s.arrs 6 = x.innerCuff) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits rep.live)
    (h17 : s.arrs 17 = gm02VertexBits Q) (hN : s.regs 100 = x.vertexCount) :
    ∃ s' t, Exec w gm06Reduction2CurrentProg s s' t ∧
      t ≤ gm06Reduction2ScanCost x.vertexCount rep.tagged.length k + 28 +
        16 * rep.tagged.length + 30 * x.innerCuff.length +
        x.rotations.length * (260 + 34 * x.rotations.length + 300 * (gm06EncodeRows x.rotations).length) ∧
      (∀ a ∈ [2, 3, 6, 7, 8, 9, 17, 19], s'.arrs a = s.arrs a) ∧
      (∀ r ∈ [309, 329, 900], s'.regs r = s.regs r) ∧
      ((s'.regs 294 = 0 ∧ s'.arrs 4 = gm06EncodeRows x.rotations ∧
          s'.arrs 12 = rep.tagged.map Prod.snd ∧ s'.arrs 14 = gm02VertexBits rep.live ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction2Step k G L H M) ∨
       ∃ (mask : List ℕ) (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
         (cur : GM06CurrentDrawingRep (gm06RestrictSuccessorInput x mask) H M),
         s'.regs 294 ≠ 0 ∧ s'.regs 294 < 3 ∧ s'.arrs 3 = (gm06RestrictSuccessorInput x mask).endpoints ∧
         s'.arrs 4 = gm06EncodeRows (gm06RestrictSuccessorInput x mask).rotations ∧
         s'.arrs 8 = gm06EncodeRows (gm06RestrictSuccessorInput x mask).linkage ∧
         s'.arrs 12 = cur.tagged.map Prod.snd ∧ s'.arrs 14 = gm02VertexBits cur.live ∧
         mask.length = rep.tagged.length ∧ (∀ z ∈ mask, z ≤ 1) ∧
         cur.tagged = gm06RetagEdges rep.tagged mask ∧ cur.vertex = rep.vertex ∧
         IsCylinderSection5Drawing k H ∧ Section5Reduction2Step k G L H M ∧
         cur.live.card + (cur.tagged.map Prod.snd).count 1 <
           rep.live.card + (rep.tagged.map Prod.snd).count 1 ∧
         GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
           ⟨H, cur.tagged, cur.vertex, cur.edge⟩ none) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hf₁, _, hout⟩ := gm06Reduction2ScanProg_current rep hvinj hG Q hQ
    hw hn hsquare hm hk hbits h3 h6 h12 h14 h17 hN
  have hframe (a : ℕ) (ha : a ∈ [2, 3, 6, 7, 8, 9, 17, 19]) : s₁.arrs a = s.arrs a := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hf₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h4₁ := (hf₁ 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4
  have hreg₁ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₁.regs r = s.regs r := by
    apply he₁.regs_eq_of_not_mem_writtenRegs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide +kernel
  rcases hout with ⟨hflag, hmask, hA, hno⟩ |
      ⟨mask, H, M, cur, hflag, hflagLt, h12₁, h14₁, hlen, hmaskBits, htag, hvertex, hH, hred, hprogress, hundo⟩
  · have hi : Exec w (.ite (.reg 294) gm06PruneCurrentRotationsProg .skip) s₁ s₁ 2 :=
      .ite_false (Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.skip _)
    refine ⟨s₁, t₁ + 2, .seq he₁ hi, by omega, hframe, hreg₁, Or.inl ?_⟩
    exact ⟨hflag, h4₁, hmask, hA, hno⟩
  · obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h4₂, _, _, _⟩ := gm06PruneCurrentRotationsProg_exec
      mask x.innerCuff x.rotations s₁ hw hrotLen hrotWords (by rw [hlen]; exact haug) hmaskBits
      (by simpa only [hlen] using hdarts) h4₁ h12₁ ((hframe 6 (by simp)).trans h6)
    have hi : Exec w (.ite (.reg 294) gm06PruneCurrentRotationsProg .skip) s₁ s₂ (1 + t₂) :=
      .ite_true (Crossing.eval_reg rfl (hflagLt.trans_le (by omega))) hflag he₂
    have hf₂ (a : ℕ) (ha : a ∈ [2, 3, 6, 7, 8, 9, 17, 19]) : s₂.arrs a = s.arrs a := by
      apply (hk₂.2 a ?_).trans (hframe a ha)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hr₂ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₂.regs r = s.regs r := by
      apply (hk₂.1 r ?_).trans (hreg₁ r hr)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    have hflags : cur.tagged.map Prod.snd = mask := by
      rw [htag]
      exact gm06RetagEdges_activity _ _ hlen
    refine ⟨s₂, t₁ + (1 + t₂), .seq he₁ hi, ?_, hf₂, hr₂, Or.inr ?_⟩
    · rw [hlen] at ht₂
      omega
    · refine ⟨mask, H, M, cur, ?_, ?_, (hf₂ 3 (by simp)).trans h3, h4₂,
        (hf₂ 8 (by simp)).trans h8, ?_, (hk₂.2 14 (by decide)).trans h14₁,
        hlen, hmaskBits, htag, hvertex, hH, hred, ?_, hundo⟩
      · exact ((hk₂.1 294 (by decide)).trans rfl) ▸ hflag
      · exact ((hk₂.1 294 (by decide)).trans rfl) ▸ hflagLt
      · exact (hk₂.2 12 (by decide)).trans (h12₁.trans hflags.symm)
      · simpa only [hflags] using hprogress

end GraphMinor.Compute
