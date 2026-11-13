module

public import GraphMinor.Compute.GM06Reduction2Scan
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5NoComputedReduction2
import GraphMinor.GM06.Section5ComputedReduction2Masks
import GraphMinor.GM06.Section5InitialLoop
import GraphMinor.GM06.Section5InducedMaskGraph
import GraphMinor.GM06.Section5DeletedMaskGraph

/-!
# Correctness of the Reduction 2 scan on the drawing

The finite component and loop tests are complete for Reduction 2
in VI (5.7), page 133. On success their mask update represents
an actual reduced drawing with the unchanged linkage. On failure
no such reduction applies. The original endpoint labels interpret
the returned live and active masks, and every success strictly
lowers the sum of live vertices and active edges.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06

/-- The actual scan either excludes Reduction 2 or returns masks
for an actual proper reduced drawing, with a strict size decrease. -/
theorem gm06Reduction2ScanProg_drawing {w k n : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hinj : Set.InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (A : Finset (Fin n)) (hV : G.V = vertex '' (A : Set (Fin n)))
    (cuts : Fin k → Fin n) (hcuts : ∀ i, vertex (cuts i) = cylinderM1Point k i)
    (Q : Finset (Fin n)) (hQ : vertex '' (Q : Set (Fin n)) = ⋃ i : Fin k, (L.pathDrawing i).V)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hk : k < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd) (hc : s.arrs 6 = (List.ofFn cuts).map Fin.val)
    (hp : s.arrs 17 = gm02VertexBits Q) (hA : s.arrs 14 = gm02VertexBits A) (hN : s.regs 100 = n) :
    ∃ s' t, Exec w gm06Reduction2ScanProg s s' t ∧
      t ≤ 7 + k * (137 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
        53 * (n * n) + 93 * n + 129 * tagged.length) ∧
      (∀ a : ℕ, a < 28 → a ≠ 12 → a ≠ 14 → a ≠ 15 → a ≠ 16 → a ≠ 22 → a ≠ 23 →
        s'.arrs a = s.arrs a) ∧ s'.regs 100 = n ∧
      ((s'.regs 294 = 0 ∧ ∀ (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G'),
        ¬ Section5Reduction2Step k G L G' M) ∨
       ∃ (C : Finset (Fin n)) (mask : List ℕ) (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G'),
        s'.regs 294 ≠ 0 ∧ s'.arrs 14 = gm02VertexBits C ∧ s'.arrs 12 = mask ∧
        mask.length = tagged.length ∧ G'.V = vertex '' (C : Set (Fin n)) ∧
        IsCylinderSection5Drawing k G' ∧ Section5Reduction2Step k G L G' M ∧
        (∀ j : Fin tagged.length, mask[j.val]? = some 1 →
          G'.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2)) ∧
        (∀ e ∈ G'.E, ∃ j : Fin tagged.length, mask[j.val]? = some 1 ∧ edge j = e) ∧
        C.card + mask.count 1 < A.card + (tagged.map Prod.snd).count 1) := by
  classical
  obtain ⟨s', t, he, ht, hframe, hN', hout⟩ := gm06Reduction2ScanProg_exec tagged (List.ofFn cuts) Q A
    hw hn hsquare hm (by simpa only [List.length_ofFn] using hk) hbits ha hb hc hp hA hN
  refine ⟨s', t, he, by simpa only [List.length_ofFn] using ht, hframe, hN', ?_⟩
  rcases hout with ⟨hflag, _, _, hfailed⟩ | ⟨cut, hcutMem, _, hloop | hcomponent⟩
  · left
    refine ⟨hflag, ?_⟩
    intro G' M
    exact not_reduction2_of_finite_tests L M tagged vertex edge hlinks hcover A hV cuts hcuts Q hQ.subset
      (fun i => (hfailed (cuts i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).1)
      (fun i => (hfailed (cuts i) (List.mem_ofFn.mpr ⟨i, rfl⟩)).2)
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hcutMem
    have hcutGeom : vertex cut = cylinderM1Point k i := (congrArg vertex hi.symm).trans (hcuts i)
    obtain ⟨hflag, hA', j, hactive, hu, hv, hmask, hprogress⟩ := hloop
    have hl := hlinks j hactive
    rw [hu, hv, hcutGeom] at hl
    obtain ⟨M, hG', hRed⟩ := exists_reduction2_of_initial_loop L hG i (edge j) hl
    obtain ⟨hnewLinks, hnewCover⟩ := deleted_mask_links_and_cover G tagged vertex edge hinj hlinks hcover j hactive
    right
    refine ⟨A, (tagged.map Prod.snd).set j.val 0, G.deleteEdge (edge j), M,
      by omega, hA', hmask, by simp, ?_, hG', hRed, ?_, ?_, ?_⟩
    · exact (GraphMinor.GM11.deleteEdge_V G (edge j)).trans hV
    · intro q hq
      apply hnewLinks q
      have hbound : q.val < ((tagged.map Prod.snd).set j.val 0).length := by
        simpa only [List.length_set, List.length_map] using q.isLt
      rw [List.getElem?_eq_getElem hbound] at hq
      exact Option.some.inj hq
    · intro e he'
      obtain ⟨q, hq, hqe⟩ := hnewCover e he'
      have hbound : q.val < ((tagged.map Prod.snd).set j.val 0).length := by
        simpa only [List.length_set, List.length_map] using q.isLt
      exact ⟨q, by rw [List.getElem?_eq_getElem hbound, hq], hqe⟩
    · have hh : ((tagged.map Prod.snd).set j.val 0).count 1 + 1 = (tagged.map Prod.snd).count 1 := by
        simpa only [hmask] using hprogress
      omega
  · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hcutMem
    have hcutGeom : vertex cut = cylinderM1Point k i := (congrArg vertex hi.symm).trans (hcuts i)
    obtain ⟨hflag, source, hsource, hzero, hA', hmask, hprogress⟩ := hcomponent
    let H : SimpleGraph (Fin n) := (gm06PuncturedGraphData tagged cut).vertexGraph
    let C : Finset (Fin n) := A \ reachSet H source
    have hC : vertex '' (C : Set (Fin n)) ⊆ G.V := by
      rintro a ⟨v, hv, rfl⟩
      rw [hV]
      exact ⟨v, (Finset.mem_sdiff.mp hv).1, rfl⟩
    have hprotect : ∀ j : Fin k, (L.pathDrawing j).V ⊆ vertex '' (Q : Set (Fin n)) := by
      intro j a ha'
      rw [hQ]
      exact mem_iUnion.mpr ⟨j, ha'⟩
    obtain ⟨M, hG', hRed⟩ := exists_reduction2_of_computed_live_masks L hG tagged vertex edge hlinks hcover
      A hV cut source i hcutGeom hsource Q hprotect hzero
    obtain ⟨hnewLinks, hnewCover⟩ := induced_mask_links_and_cover G tagged vertex edge hlinks hcover C hC
    right
    refine ⟨C, gm06InducedEdgeBits tagged C, induceDrawing G (vertex '' (C : Set (Fin n))), M,
      by omega, hA', hmask, gm06InducedEdgeBits_length tagged C, induceDrawing_V G hC,
      hG', hRed, ?_, ?_, ?_⟩
    · intro q hq
      apply hnewLinks q
      have hbound : q.val < (gm06InducedEdgeBits tagged C).length := by
        rw [gm06InducedEdgeBits_length]
        exact q.isLt
      rw [List.getElem?_eq_getElem hbound] at hq
      exact Option.some.inj hq
    · intro e he'
      obtain ⟨q, hq, hqe⟩ := hnewCover e he'
      have hbound : q.val < (gm06InducedEdgeBits tagged C).length := by
        rw [gm06InducedEdgeBits_length]
        exact q.isLt
      exact ⟨q, by rw [List.getElem?_eq_getElem hbound, hq], hqe⟩
    · have hedge := gm06InducedEdgeBits_count_le tagged C
      change C.card < A.card at hprogress
      omega

end GraphMinor.Compute
