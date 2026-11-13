module

public import GraphMinor.GM06.Alg57CurrentClockwiseTest
public import GraphMinor.GM06.Alg57DeletionCurrentMasks
public import GraphMinor.Compute.GM06Reduction1Scan
public import GraphMinor.Compute.GM06PruneRotations
import GraphMinor.GM06.Section5NoReduction1

/-!
# The current-state clockwise deletion branch

For VI (5.7), page 133, the actual current rotations supply the
signed clockwise predicate read by the finite scan. On success,
deleting the selected edge and filtering the rows preserves every
field of the current drawing relation. The RAM program installs
that filter before returning to the reduction loop. The linkage
rows and recovery history are unchanged.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

/-- Scan for a clockwise edge and install the retained rotation table. -/
@[expose] def gm06Reduction1CurrentProg : Cmd :=
  .seq gm06Reduction1ScanProg (.ite (.reg 60) gm06PruneCurrentRotationsProg .skip)

/-- The current positive rows give exactly the finite scan's
markers and its complete side test, without extra chart premises. -/
theorem gm06Reduction1ScanProg_current
    {w k B : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hw : 2 < 2 ^ w) (hsize : 2 * (rep.tagged.length + k) + 1 < 2 ^ w)
    (hpLen : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (hrLen : (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows x.linkage, v < 2 ^ w)
    (hrWords : ∀ v ∈ gm06EncodeRows x.rotations, v < 2 ^ w)
    (hkB : k ≤ B) (hnB : x.rotations.length ≤ B)
    (hpathsB : ∀ row ∈ x.linkage, row.length ≤ B)
    (hrotsB : ∀ row ∈ x.rotations, row.length ≤ B)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1) {s : State}
    (h6 : s.arrs 6 = x.innerCuff) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h12 : s.arrs 12 = rep.tagged.map Prod.snd) :
    ∃ s' t, Exec w gm06Reduction1ScanProg s s' t ∧
      t ≤ 7 + k * (131 + 117 * B + rep.tagged.length * (120 + 104 * B)) ∧
      Keeps [295, 297, 7, 8, 9, 11, 31, 37, 296, 36, 39, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
        [12, 24, 25] s s' ∧
      ((s'.regs 60 = 0 ∧ s'.arrs 12 = rep.tagged.map Prod.snd ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction1Step k G L H M) ∨
       ∃ (j : Fin rep.tagged.length) (M : CylinderLinkage k (G.deleteEdge (rep.edge j)))
         (cur : GM06CurrentDrawingRep
           (gm06RestrictSuccessorInput x ((rep.tagged.map Prod.snd).set j.val 0)) (G.deleteEdge (rep.edge j)) M),
         s'.regs 60 = 1 ∧ rep.tagged[j].2 = 1 ∧
         s'.arrs 12 = (rep.tagged.map Prod.snd).set j.val 0 ∧
         cur.live = rep.live ∧ cur.vertex = rep.vertex ∧
         cur.tagged = gm06RetagEdges rep.tagged ((rep.tagged.map Prod.snd).set j.val 0) ∧
         IsCylinderSection5Drawing k (G.deleteEdge (rep.edge j)) ∧
         Section5Reduction1Step k G L (G.deleteEdge (rep.edge j)) M ∧
         (s'.arrs 12).count 1 + 1 = (rep.tagged.map Prod.snd).count 1 ∧
         GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
           ⟨G.deleteEdge (rep.edge j), cur.tagged, cur.vertex, cur.edge⟩ none) := by
  let cs := List.ofFn (fun i : Fin k => (rep.source i).val)
  let ix : Fin cs.length → Fin k := fun j => ⟨j.val, by simpa only [cs, List.length_ofFn] using j.isLt⟩
  have hcs : cs.length = k := List.length_ofFn
  have hip : cs.length ≤ x.linkage.length := by rw [hcs, rep.linkage.1]
  have hvertex (i : Fin cs.length) : cs[i.val] < x.rotations.length := by
    have hh : cs[i.val] = (rep.source (ix i)).val := by
      simp only [cs, List.getElem_ofFn, ix]
    rw [hh, rep.rows_length]
    exact (rep.source (ix i)).isLt
  have hne (i : Fin cs.length) : 0 < x.linkage[i.val].length := rep.linkage.row_nonempty (ix i)
  have hdata (i : Fin cs.length) :
      (x.rotations[cs[i.val]]'(hvertex i)).Nodup ∧
      2 * (rep.tagged.length + gm06PreviousCuffIndex cs.length i.val) + 1 ∈ x.rotations[cs[i.val]]'(hvertex i) ∧
      (x.linkage[i.val]'(i.isLt.trans_le hip))[0]'(hne i) ∈ x.rotations[cs[i.val]]'(hvertex i) ∧
      2 * (rep.tagged.length + i.val) ∈ x.rotations[cs[i.val]]'(hvertex i) ∧
      ∀ j : Fin rep.tagged.length, rep.tagged[j].2 = 1 →
        (IsClockwiseInitialEdge L (ix i) (rep.edge j) ↔
          gm06CalibratedSectorFlag (x.rotations[cs[i.val]]'(hvertex i))
            (2 * (rep.tagged.length + gm06PreviousCuffIndex cs.length i.val) + 1)
            ((x.linkage[i.val]'(i.isLt.trans_le hip))[0]'(hne i)) (2 * (rep.tagged.length + i.val)) (2 * j.val) = 1 ∨
          gm06CalibratedSectorFlag (x.rotations[cs[i.val]]'(hvertex i))
            (2 * (rep.tagged.length + gm06PreviousCuffIndex cs.length i.val) + 1)
            ((x.linkage[i.val]'(i.isLt.trans_le hip))[0]'(hne i)) (2 * (rep.tagged.length + i.val)) (2 * j.val + 1) = 1) := by
    obtain ⟨first, rest, hrow, _, hnd, hn, hf, hp, _, _, _, ht⟩ := rep.source_row_clockwise_test hG hθ (ix i)
    have hrow' : x.linkage[i.val] = first :: rest :=
      (List.getD_eq_getElem _ [] (i.isLt.trans_le hip)).symm.trans hrow
    have hsource : cs[i.val] = (rep.source (ix i)).val := by
      simp only [cs, List.getElem_ofFn, ix]
    have hget : x.rotations[cs[i.val]]'(hvertex i) = x.rotations.getD (rep.source (ix i)).val [] := by
      exact (List.getD_eq_getElem _ [] (hvertex i)).symm.trans
        (congrArg (fun a => x.rotations.getD a []) hsource)
    simpa only [hget, hrow', List.getElem_cons_zero, hcs, ix, Fin.val_mk] using ⟨hnd, hn, hf, hp, ht⟩
  obtain ⟨s', t, he, ht, hframe, hout⟩ := gm06Reduction1ScanProg_exec
    cs (rep.tagged.map Prod.snd) x.linkage x.rotations hip hvertex hne hw
    (by simpa only [List.length_map, hcs] using hsize) hpLen hrLen hpWords hrWords
    (hcs ▸ hkB) hnB hpathsB hrotsB (by simpa only [List.forall_mem_map] using hbits)
    (fun i => (hdata i).1) (fun i => by simpa only [List.length_map] using (hdata i).2.1)
    (fun i => (hdata i).2.2.1) (fun i => by simpa only [List.length_map] using (hdata i).2.2.2.1)
    (h6.trans rep.inner) h8 h4 h12
  refine ⟨s', t, he, by simpa only [hcs, List.length_map] using ht, hframe, ?_⟩
  rcases hout with ⟨hflag, hmask, hfailed⟩ | ⟨i, j, hflag, _, _, hmask, ⟨hactive, hsector⟩, hprogress⟩
  · left
    refine ⟨hflag, hmask, ?_⟩
    rintro H M ⟨i, e, heG, hclock, _⟩
    obtain ⟨j, hj, hje⟩ := rep.edge_cover e heG
    let i' : Fin cs.length := ⟨i.val, hcs.symm ▸ i.isLt⟩
    let j' : Fin (rep.tagged.map Prod.snd).length := ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
    apply hfailed i' j'
    refine ⟨by simpa only [List.getElem_map, j', Fin.getElem_fin] using hj, ?_⟩
    have hh := ((hdata i').2.2.2.2 j hj).mp (hje.symm ▸ hclock)
    simpa only [List.length_map] using hh
  · let d : Fin rep.tagged.length := ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
    have hd : rep.tagged[d].2 = 1 := by simpa only [List.getElem_map, d, Fin.getElem_fin] using hactive
    have hclock := ((hdata i).2.2.2.2 d hd).mpr (by simpa only [List.length_map] using hsector)
    obtain ⟨M, hH, hred, hpaths, hcurves⟩ :=
      exists_reduction1_on_deleted_drawing L hG (rep.links d hd).edge_mem hclock
    obtain ⟨cur, hA, hv, htag, hundo⟩ := rep.exists_deleted_currentDrawingRep hG d hd M hH hpaths hcurves
    exact Or.inr ⟨d, M, cur, hflag, hd, hmask, hA, hv, htag, hH, hred, hprogress, hundo⟩

/-- The successful clockwise branch installs all current fields
and an actual undo step, and removes exactly one active edge.
It preserves all other instance arrays, the history and the loop bit. -/
theorem gm06Reduction1CurrentProg_exec
    {w k B : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hw : 2 < 2 ^ w) (hsize : 2 * (rep.tagged.length + k) + 1 < 2 ^ w)
    (hpLen : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (hrLen : 4 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows x.linkage, v < 2 ^ w)
    (hrWords : ∀ v ∈ gm06EncodeRows x.rotations, v < 2 ^ w)
    (hkB : k ≤ B) (hnB : x.rotations.length ≤ B)
    (hpathsB : ∀ row ∈ x.linkage, row.length ≤ B)
    (hrotsB : ∀ row ∈ x.rotations, row.length ≤ B)
    (hbits : ∀ p ∈ rep.tagged, p.2 ≤ 1)
    (haug : rep.tagged.length + 2 * x.innerCuff.length < 2 ^ w)
    (hdarts : ∀ row ∈ x.rotations, ∀ d ∈ row, d < 2 * (rep.tagged.length + 2 * x.innerCuff.length))
    {s : State} (h3 : s.arrs 3 = x.endpoints) (h4 : s.arrs 4 = gm06EncodeRows x.rotations)
    (h6 : s.arrs 6 = x.innerCuff) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h12 : s.arrs 12 = rep.tagged.map Prod.snd) (h14 : s.arrs 14 = gm02VertexBits rep.live) :
    ∃ s' t, Exec w gm06Reduction1CurrentProg s s' t ∧
      t ≤ 7 + k * (131 + 117 * B + rep.tagged.length * (120 + 104 * B)) + 28 +
        16 * rep.tagged.length + 30 * x.innerCuff.length +
        x.rotations.length * (260 + 34 * x.rotations.length + 300 * (gm06EncodeRows x.rotations).length) ∧
      (∀ a ∈ [2, 3, 6, 7, 8, 9, 14, 17, 19], s'.arrs a = s.arrs a) ∧
      (∀ r ∈ [309, 329, 900], s'.regs r = s.regs r) ∧
      ((s'.regs 60 = 0 ∧ s'.arrs 4 = gm06EncodeRows x.rotations ∧
          s'.arrs 12 = rep.tagged.map Prod.snd ∧
          ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage k H),
            ¬ Section5Reduction1Step k G L H M) ∨
       ∃ (j : Fin rep.tagged.length) (M : CylinderLinkage k (G.deleteEdge (rep.edge j)))
         (cur : GM06CurrentDrawingRep
           (gm06RestrictSuccessorInput x ((rep.tagged.map Prod.snd).set j.val 0)) (G.deleteEdge (rep.edge j)) M),
         s'.regs 60 = 1 ∧
         s'.arrs 3 = (gm06RestrictSuccessorInput x ((rep.tagged.map Prod.snd).set j.val 0)).endpoints ∧
         s'.arrs 4 = gm06EncodeRows (gm06RestrictSuccessorInput x ((rep.tagged.map Prod.snd).set j.val 0)).rotations ∧
         s'.arrs 8 = gm06EncodeRows (gm06RestrictSuccessorInput x ((rep.tagged.map Prod.snd).set j.val 0)).linkage ∧
         s'.arrs 12 = cur.tagged.map Prod.snd ∧ s'.arrs 14 = gm02VertexBits cur.live ∧
         cur.live = rep.live ∧ cur.vertex = rep.vertex ∧
         cur.tagged = gm06RetagEdges rep.tagged ((rep.tagged.map Prod.snd).set j.val 0) ∧
         IsCylinderSection5Drawing k (G.deleteEdge (rep.edge j)) ∧
         Section5Reduction1Step k G L (G.deleteEdge (rep.edge j)) M ∧
         (s'.arrs 12).count 1 + 1 = (rep.tagged.map Prod.snd).count 1 ∧
         GM06UndoStep x.vertexCount k ⟨G, rep.tagged, rep.vertex, rep.edge⟩
           ⟨G.deleteEdge (rep.edge j), cur.tagged, cur.vertex, cur.edge⟩ none) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout⟩ := gm06Reduction1ScanProg_current rep hG hθ hw hsize hpLen
    (by omega) hpWords hrWords hkB hnB hpathsB hrotsB hbits h6 h8 h4 h12
  have hf₁ (a : ℕ) (ha : a ∈ [2, 3, 6, 7, 8, 9, 14, 17, 19]) : s₁.arrs a = s.arrs a := by
    apply hk₁.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr₁ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₁.regs r = s.regs r := by
    apply hk₁.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  have h4₁ := (hk₁.2 4 (by decide)).trans h4
  rcases hout with ⟨hflag, hmask, hno⟩ | ⟨j, M, cur, hflag, hj, hmask, hA, hv, htag, hH, hred, hprogress, hundo⟩
  · refine ⟨s₁, t₁ + 2, .seq he₁ (.ite_false (Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.skip _)),
      by omega, hf₁, hr₁, Or.inl ⟨hflag, h4₁, hmask, hno⟩⟩
  · let mask := (rep.tagged.map Prod.snd).set j.val 0
    have hlen : mask.length = rep.tagged.length := by simp only [mask, List.length_set, List.length_map]
    have hmaskBits : ∀ z ∈ mask, z ≤ 1 := by
      intro z hz
      rcases List.mem_or_eq_of_mem_set hz with hz | hz
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hz
        exact hbits p hp
      · exact hz ▸ Nat.zero_le 1
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h4₂, _, _, _⟩ := gm06PruneCurrentRotationsProg_exec
      mask x.innerCuff x.rotations s₁ hw hrLen hrWords (by rw [hlen]; exact haug) hmaskBits
      (by simpa only [hlen] using hdarts) h4₁ hmask ((hf₁ 6 (by simp)).trans h6)
    have hf₂ (a : ℕ) (ha : a ∈ [2, 3, 6, 7, 8, 9, 14, 17, 19]) : s₂.arrs a = s.arrs a := by
      apply (hk₂.2 a ?_).trans (hf₁ a ha)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hr₂ (r : ℕ) (hr : r ∈ [309, 329, 900]) : s₂.regs r = s.regs r := by
      apply (hk₂.1 r ?_).trans (hr₁ r hr)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
    have hflags : cur.tagged.map Prod.snd = mask := by
      rw [htag]
      exact gm06RetagEdges_activity _ _ hlen
    refine ⟨s₂, t₁ + (1 + t₂), .seq he₁ (.ite_true
      (Crossing.eval_reg hflag (by omega)) (by decide) he₂), ?_, hf₂, hr₂, Or.inr ?_⟩
    · rw [hlen] at ht₂
      omega
    · refine ⟨j, M, cur, (hk₂.1 60 (by decide)).trans hflag,
        (hf₂ 3 (by simp)).trans h3, h4₂, (hf₂ 8 (by simp)).trans h8,
        (hk₂.2 12 (by decide)).trans (hmask.trans hflags.symm), ?_, hA, hv, htag, hH, hred, ?_, hundo⟩
      · exact (hf₂ 14 (by simp)).trans (h14.trans (congrArg gm02VertexBits hA).symm)
      · simpa only [(hk₂.2 12 (by decide))] using hprogress

end GraphMinor.Compute
