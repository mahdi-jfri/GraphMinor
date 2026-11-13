module

public import GraphMinor.Compute.GM06Reduction1Scan
public import GraphMinor.GM06.Section5SignedRotationClockwise
public import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM06.Section5DeletedMaskGraph

/-!
# Correctness of the complete Reduction 1 scan on the drawing

Each supplied initial rotation labels the actual signed cuff ends
and first path end. The proved clockwise criterion identifies the
finite tests with the corrected side condition. The all-vertex RAM
scan therefore either excludes every Reduction 1 or returns one
proper deleted drawing with the linkage unchanged. The updated
mask still interprets every link and covers all remaining edges.
This implements the first reduction branch of VI (5.7), page 133.
-/

public section
namespace GraphMinor.Compute
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06 unitInterval

set_option maxHeartbeats 40000 in
/-- The actual scan over supplied rotations either excludes
Reduction 1 or returns its concrete drawing, masks and strict progress. -/
theorem gm06Reduction1ScanProg_drawing {w n B : ℕ}
    (cs : List ℕ) (paths rots : List (List ℕ))
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage cs.length G) (hG : IsCylinderSection5Drawing cs.length G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U) (hθ : L.HasTheta θ)
    (hip : cs.length ≤ paths.length)
    (hvertex : ∀ i : Fin cs.length, (cs[i.val]'i.isLt) < rots.length)
    (hne : ∀ i : Fin cs.length, 0 < (paths[i.val]'(i.isLt.trans_le hip)).length)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (Φ : Fin cs.length → C(ClosedUnitDisc, OnePoint EuclideanPlane))
    (hpolar : ∀ i, IsPolar (cylinderSphereDrawing F)
      (cylinderToSphere (cylinderM1Point cs.length i)) (Φ i))
    (a b c : ∀ i : Fin cs.length, halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point cs.length i)))
    (d : ∀ i : Fin cs.length, halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point cs.length i)) → Circle)
    (hd : ∀ i e, ∀ t : I, 0 < t → (Φ i) (polarDiscPoint t (d i e)) ∈ range (spoke γ e.1))
    (ha : ∀ i, (a i).1.2 = true) (hc : ∀ i, (c i).1.2 = false)
    (haAngle : ∀ i t, γ (a i).1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift cs.length i).2 - 2 * π / cs.length + 2 * π * (t : ℝ) / cs.length)))
    (hcAngle : ∀ i t, γ (c i).1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift cs.length i).2 + 2 * π * (t : ℝ) / cs.length)))
    (hb : ∀ i, (b i).1.1 ∈ (cylinderSphereDrawing (L.pathDrawing i)).E)
    (hinj : Set.InjOn edge {j | (tagged[j.val]'j.isLt).2 = 1})
    (hlinks : ∀ j : Fin tagged.length, (tagged[j.val]'j.isLt).2 = 1 →
      G.toGraph.IsLink (edge j) (vertex (tagged[j.val]'j.isLt).1.1) (vertex (tagged[j.val]'j.isLt).1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, (tagged[j.val]'j.isLt).2 = 1 ∧ edge j = e)
    (z : Fin cs.length → ℕ → Circle)
    (hz : ∀ i, Set.InjOn (z i) {r | r ∈ (rots[(cs[i.val]'i.isLt)]'(hvertex i))})
    (hs : ∀ i, (rots[(cs[i.val]'i.isLt)]'(hvertex i)).Pairwise
      (fun u v => circleStdCoord.angle (z i u) < circleStdCoord.angle (z i v)))
    (hp : ∀ i : Fin cs.length,
      2 * (tagged.length + gm06PreviousCuffIndex cs.length i.val) + 1 ∈ (rots[(cs[i.val]'i.isLt)]'(hvertex i)))
    (hq : ∀ i : Fin cs.length, ((paths[i.val]'(i.isLt.trans_le hip))[0]'(hne i)) ∈ (rots[(cs[i.val]'i.isLt)]'(hvertex i)))
    (hpos : ∀ i : Fin cs.length, 2 * (tagged.length + i.val) ∈ (rots[(cs[i.val]'i.isLt)]'(hvertex i)))
    (hzp : ∀ i, z i (2 * (tagged.length + gm06PreviousCuffIndex cs.length i.val) + 1) = d i (a i))
    (hzq : ∀ i, z i ((paths[i.val]'(i.isLt.trans_le hip))[0]'(hne i)) = d i (b i))
    (hzc : ∀ i, z i (2 * (tagged.length + i.val)) = d i (c i))
    (hlabel : ∀ i (j : Fin tagged.length), (tagged[j.val]'j.isLt).2 = 1 → ∀ u : Circle,
      polarRimMap (Φ i) u ∈ cylinderToSphere '' edge j ↔
        ∃ r ∈ (rots[(cs[i.val]'i.isLt)]'(hvertex i)), z i r = u ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1))
    (hw : 2 < 2 ^ w) (hsize : 2 * (tagged.length + cs.length) + 1 < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hrLen : (gm06EncodeRows rots).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (hrWords : ∀ v ∈ gm06EncodeRows rots, v < 2 ^ w)
    (hcsB : cs.length ≤ B) (hrotB : rots.length ≤ B)
    (hpathsB : ∀ row ∈ paths, row.length ≤ B) (hrotsB : ∀ row ∈ rots, row.length ≤ B)
    (hbits : ∀ t ∈ tagged, t.2 ≤ 1)
    (hnd : ∀ i : Fin cs.length, (rots[(cs[i.val]'i.isLt)]'(hvertex i)).Nodup)
    {s : State} (h6 : s.arrs 6 = cs) (h8 : s.arrs 8 = gm06EncodeRows paths)
    (h4 : s.arrs 4 = gm06EncodeRows rots) (h12 : s.arrs 12 = tagged.map Prod.snd) :
    ∃ s' t, Exec w gm06Reduction1ScanProg s s' t ∧
      t ≤ 7 + cs.length * (131 + 117 * B + tagged.length * (120 + 104 * B)) ∧
      TwoPaths.Keeps
        [295, 297, 7, 8, 9, 11, 31, 37, 296, 36, 39, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
        [12, 24, 25] s s' ∧
      ((s'.regs 60 = 0 ∧ s'.arrs 12 = tagged.map Prod.snd ∧
        ∀ (G' : Drawing ClosedCylinder) (M : CylinderLinkage cs.length G'),
          ¬ Section5Reduction1Step cs.length G L G' M) ∨
       ∃ (i : Fin cs.length) (j : Fin tagged.length)
         (M : CylinderLinkage cs.length (G.deleteEdge (edge j))),
        s'.regs 60 = 1 ∧ s'.regs 297 = i.val ∧ s'.regs 55 = j.val ∧ (tagged[j.val]'j.isLt).2 = 1 ∧
        s'.arrs 12 = (tagged.map Prod.snd).set j.val 0 ∧
        IsCylinderSection5Drawing cs.length (G.deleteEdge (edge j)) ∧
        Section5Reduction1Step cs.length G L (G.deleteEdge (edge j)) M ∧
        M.pathDrawing = L.pathDrawing ∧ M.curve = L.curve ∧
        (∀ u : Fin tagged.length, (s'.arrs 12)[u.val]? = some 1 →
          (G.deleteEdge (edge j)).toGraph.IsLink
            (edge u) (vertex (tagged[u.val]'u.isLt).1.1) (vertex (tagged[u.val]'u.isLt).1.2)) ∧
        (∀ e ∈ (G.deleteEdge (edge j)).E,
          ∃ u : Fin tagged.length, (s'.arrs 12)[u.val]? = some 1 ∧ edge u = e) ∧
        (s'.arrs 12).count 1 + 1 = (tagged.map Prod.snd).count 1) := by
  have htest (i : Fin cs.length) := clockwise_edge_iff_calibrated_signed_rotation
    edge (fun j => (tagged[j.val]'j.isLt).2 = 1) L hG hGF hbdF hθ i hγ (hpolar i) (a i) (b i) (c i)
      (d i) (hd i) (ha i) (hc i) (haAngle i) (hcAngle i) (hb i)
      (fun j hj => (hlinks j hj).edge_mem) (rots[(cs[i.val]'i.isLt)]'(hvertex i)) (z i) (hz i) (hs i)
      (2 * (tagged.length + gm06PreviousCuffIndex cs.length i.val) + 1)
      ((paths[i.val]'(i.isLt.trans_le hip))[0]'(hne i)) (2 * (tagged.length + i.val))
      (hp i) (hq i) (hpos i) (hzp i) (hzq i) (hzc i) (hlabel i)
  obtain ⟨s', t, hex, ht, hframe, hout⟩ := gm06Reduction1ScanProg_exec
    cs (tagged.map Prod.snd) paths rots hip hvertex hne hw
      (by simpa only [List.length_map] using hsize) hpLen hrLen hpWords hrWords
      hcsB hrotB hpathsB hrotsB (by simpa only [List.forall_mem_map] using hbits) hnd
      (by simpa only [List.length_map] using hp) hq
      (by simpa only [List.length_map] using hpos) h6 h8 h4 h12
  refine ⟨s', t, hex, by simpa only [List.length_map] using ht, hframe, ?_⟩
  rcases hout with ⟨hflag, hmask, hfailed⟩ | ⟨i, j, hflag, hi, hj, hmask, ⟨hactive, hsector⟩, hprogress⟩
  · left
    refine ⟨hflag, hmask, ?_⟩
    rintro G' M ⟨i, e, he, hcw, _⟩
    obtain ⟨j, hjactive, hje⟩ := hcover e he
    let j' : Fin (tagged.map Prod.snd).length := ⟨j.val, by simpa using j.isLt⟩
    apply hfailed i j'
    refine ⟨by simpa [j'] using hjactive, ?_⟩
    have hh := (htest i).2.2.2 j hjactive |>.mp (hje.symm ▸ hcw)
    simpa only [List.length_map] using hh
  · let v : Fin tagged.length := ⟨j.val, by simpa using j.isLt⟩
    have hvactive : (tagged[v.val]'v.isLt).2 = 1 := by simpa [v] using hactive
    have hcw := (htest i).2.2.2 v hvactive |>.mpr (by simpa only [List.length_map] using hsector)
    obtain ⟨M, hG', hRed, hpaths, hcurves⟩ :=
      exists_reduction1_on_deleted_drawing L hG (hlinks v hvactive).edge_mem hcw
    obtain ⟨hnewLinks, hnewCover⟩ :=
      deleted_mask_links_and_cover G tagged vertex edge hinj hlinks hcover v hvactive
    right
    refine ⟨i, v, M, hflag, hi, hj, hvactive, hmask, hG', hRed, hpaths, hcurves, ?_, ?_, hprogress⟩
    · intro u hu
      apply hnewLinks u
      rw [hmask] at hu
      have hbound : u.val < ((tagged.map Prod.snd).set j.val 0).length := by
        simpa only [List.length_set, List.length_map] using u.isLt
      rw [List.getElem?_eq_getElem hbound] at hu
      exact Option.some.inj hu
    · intro e he
      obtain ⟨u, hu, hue⟩ := hnewCover e he
      refine ⟨u, ?_, hue⟩
      rw [hmask]
      have hbound : u.val < ((tagged.map Prod.snd).set j.val 0).length := by
        simpa only [List.length_set, List.length_map] using u.isLt
      rw [List.getElem?_eq_getElem hbound, hu]

end GraphMinor.Compute
