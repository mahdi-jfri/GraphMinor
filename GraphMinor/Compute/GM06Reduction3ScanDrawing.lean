module

public import GraphMinor.Compute.GM06Reduction3Scan
public import GraphMinor.Compute.GM06LinkageRowsEncoding
import GraphMinor.Compute.GM06ActiveValencyRepresentation
import GraphMinor.Compute.GM06ActiveDartLink
import GraphMinor.GM06.Section5InitialNeighbourUnique
import GraphMinor.GM06.Section5Reduction3Apply

/-!
# The complete contraction scan on an actual cylinder drawing

The ordinary linkage-row encoding supplies the first edge, its
activity and its source label. The endpoint counter computes actual
valency, and the outer-cuff row computes actual cuff membership.
At valency one the given first edge has the unique neighbour.
Thus the finite scan of VI (5.7), page 133, either finds an actual
Reduction 3 or excludes every such reduction in the drawing.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06

private theorem finite_contraction_condition_iff {n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (i : Fin k)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (a : Fin n) (hpoint : vertex a = cylinderM1Point k i)
    (d : ℕ) (hd : d < 2 * tagged.length) (hactive : (tagged[d / 2]'(by omega)).2 = 1)
    (hpath : edge ⟨d / 2, by omega⟩ ∈ (L.pathDrawing i).E)
    (outer : List ℕ) (hcuff : ∀ b : Fin n, vertex b ∈ G.V → (vertex b ∈ cylinderCuff2 ↔ b.val ∈ outer))
    (hstart : (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[d]?.getD 0 = a.val) :
    let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
    ((gm06ActiveEndpointBits xs (tagged.map Prod.snd) a.val).sum = 1 ∧
      xs[gm06DartMate d]?.getD 0 ∉ outer) ↔
      ∃ e v, vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
        G.toGraph.IsLink e (cylinderM1Point k i) v ∧ v ≠ cylinderM1Point k i ∧ v ∉ cylinderCuff2 := by
  dsimp only
  obtain ⟨a', b, ha', hb, hl⟩ := gm06ActiveDart_isLink G.toGraph vertex tagged edge hlinks d hd hactive
  have haa : a' = a := Fin.ext (ha'.symm.trans hstart)
  cases haa
  have hl' : G.toGraph.IsLink (edge ⟨d / 2, by omega⟩) (cylinderM1Point k i) (vertex b) := by
    simpa only [hpoint] using hl
  have hP := ((L.isSubdrawing i).1.isLink_iff hpath).mpr hl'
  have hbne : vertex b ≠ cylinderM1Point k i := (isPathDrawing_ne_of_isLink (L.isPath i) hP).symm
  have hval := gm06ActiveLabelledVertexValency G.toGraph vertex vertex.injective tagged edge hinj hlinks hcover a
  rw [hpoint] at hval
  rw [← hval, hb]
  have hc := not_congr (hcuff b hl.right_mem)
  constructor
  · rintro ⟨hdegree, hoff⟩
    exact ⟨_, vertex b, hdegree, hl', hbne, hc.mpr hoff⟩
  · rintro ⟨e, v, hdegree, hlink, _, hoff⟩
    have hvb := (initial_link_unique_of_valency_one hdegree hl' hbne hlink).2
    exact ⟨hdegree, hc.mp (hvb ▸ hoff)⟩

/-- On an interpreted ordinary graph and linkage input, the full
RAM scan retains its actual selected first edge and both endpoint
labels. Failure excludes Reduction 3 at every initial vertex. -/
theorem gm06Reduction3ScanProg_selected {w n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (start : Fin k → Fin n) (hstart : ∀ i, vertex (start i) = cylinderM1Point k i)
    (outer : List ℕ) (hcuff : ∀ b : Fin n, vertex b ∈ G.V → (vertex b ∈ cylinderCuff2 ↔ b.val ∈ outer))
    (paths : List (List ℕ)) (hpaths : GM06LinkageRowsEncoding L tagged vertex edge paths)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1) (hk : k < 2 ^ w)
    (ho : outer.length < 2 ^ w) (hoWords : ∀ x ∈ outer, x < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (h3 : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (h12 : s.arrs 12 = tagged.map Prod.snd)
    (h6 : s.arrs 6 = List.ofFn (fun i : Fin k => (start i).val))
    (h7 : s.arrs 7 = outer) (h8 : s.arrs 8 = gm06EncodeRows paths) :
    ∃ s' t, Exec w gm06Reduction3ScanProg s s' t ∧
      t ≤ 7 + k * (73 + 42 * tagged.length + 17 * k + 22 * (gm06EncodeRows paths).length + 13 * outer.length) ∧
      TwoPaths.Keeps [327, 328, 295, 22, 20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306] [24] s s' ∧
      ((s'.regs 327 = 0 ∧ ∀ (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G'),
        ¬ Section5Reduction3Step k G L G' M) ∨
       ∃ (i : Fin k) (d : ℕ) (rest : List ℕ) (b : Fin n) (hd : d < 2 * tagged.length),
         paths[i.val]'(by rw [hpaths.1]; exact i.isLt) = d :: rest ∧
         s'.regs 327 = 1 ∧ s'.regs 328 = i.val ∧ s'.regs 22 = (start i).val ∧
         s'.regs 23 = d ∧ s'.regs 24 = gm06DartMate d ∧ s'.regs 301 = b.val ∧
         s'.regs 306 = 1 ∧ (tagged[d / 2]'(by omega)).2 = 1 ∧
         vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
         G.toGraph.IsLink (edge ⟨d / 2, by omega⟩) (cylinderM1Point k i) (vertex b) ∧
         vertex b ≠ cylinderM1Point k i ∧ vertex b ∉ cylinderCuff2) := by
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  let cs := List.ofFn (fun i : Fin k => (start i).val)
  let ix : Fin cs.length → Fin k := fun j => ⟨j.val, by simpa only [cs, List.length_ofFn] using j.isLt⟩
  have hcs : cs.length = k := List.length_ofFn
  have hip : cs.length ≤ paths.length := by rw [hcs, hpaths.1]
  have hne : ∀ j : Fin cs.length, 0 < (paths[j.val]'(j.isLt.trans_le hip)).length :=
    fun j => hpaths.row_nonempty (ix j)
  have hdata : ∀ j : Fin cs.length, ∃ (d : ℕ) (rest : List ℕ) (hd : d < 2 * tagged.length),
      (paths[j.val]'(j.isLt.trans_le hip)) = d :: rest ∧
      (tagged[d / 2]'(by omega)).2 = 1 ∧ edge ⟨d / 2, by omega⟩ ∈ (L.pathDrawing (ix j)).E ∧
      xs[d]?.getD 0 = (start (ix j)).val := by
    intro j
    exact hpaths.first_word_data (ix j) vertex.injective (start (ix j)) (hstart (ix j))
  have hfirst : ∀ j : Fin cs.length, (paths[j.val][0]'(hne j)) < 2 * (tagged.map Prod.snd).length := by
    intro j
    obtain ⟨d, rest, hd, hrow, _, _, _⟩ := hdata j
    simpa only [hrow, List.getElem_cons_zero, List.length_map] using hd
  have hlen : xs.length = 2 * (tagged.map Prod.snd).length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have hx : ∀ x ∈ xs, x < 2 ^ w := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact q.1.1.isLt.trans hn
    · exact q.1.2.isLt.trans hn
  have hpathsB : ∀ row ∈ paths, row.length ≤ (gm06EncodeRows paths).length := by
    intro row hr
    have hh := (List.sublist_flatten_of_mem hr).length_le
    rw [gm06EncodeRows_length]
    omega
  obtain ⟨s', t, hex, ht, hframe, hout⟩ := gm06Reduction3ScanProg_exec xs (tagged.map Prod.snd) cs outer paths
    hip hne hfirst s hw (by simpa only [List.length_map] using hm) hlen hx
    (by simpa only [List.forall_mem_map] using hbits) (hcs ▸ hk)
    (by intro x hx; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx; exact (start j).isLt.trans hn)
    ho hoWords hpLen hpWords hpathsB h3 h12 h6 h7 h8
  let P := fun j : Fin cs.length =>
    (gm06ActiveEndpointBits xs (tagged.map Prod.snd) cs[j.val]).sum = 1 ∧
      xs[gm06DartMate (paths[j.val][0]'(hne j))]'(hlen ▸ gm06DartMate_lt (hfirst j)) ∉ outer
  have hP : ∀ j : Fin cs.length, P j ↔
      ∃ e v, vertexValency G.toGraph (cylinderM1Point k (ix j)) = 1 ∧
        G.toGraph.IsLink e (cylinderM1Point k (ix j)) v ∧ v ≠ cylinderM1Point k (ix j) ∧ v ∉ cylinderCuff2 := by
    intro j
    obtain ⟨d, rest, hd, hrow, hactive, hpath, hword⟩ := hdata j
    have htest := finite_contraction_condition_iff L (ix j) tagged vertex edge hinj hlinks hcover
      (start (ix j)) (hstart (ix j)) d hd hactive hpath outer hcuff hword
    change ((gm06ActiveEndpointBits xs (tagged.map Prod.snd) (start (ix j)).val).sum = 1 ∧
      xs[gm06DartMate d]?.getD 0 ∉ outer) ↔ _ at htest
    have hmate : gm06DartMate d < xs.length := by
      have hh := gm06DartMate_lt hd
      simpa only [hlen, List.length_map] using hh
    have hcsj : cs[j.val] = (start (ix j)).val := by simp only [cs, List.getElem_ofFn]; rfl
    simpa only [P, hrow, List.getElem_cons_zero, hcsj, List.getElem?_eq_getElem hmate,
      Option.getD_some] using htest
  refine ⟨s', t, hex, ?_, hframe, ?_⟩
  · simpa only [hcs, List.length_map] using ht
  · rcases hout with ⟨hz, hfailed⟩ | ⟨j, hone, hindex, h22, h23, h24, h301, h306, htest⟩
    · refine Or.inl ⟨hz, ?_⟩
      intro G' M hred
      obtain ⟨i, e, v, π, H, hval, he, hv, hvs, hoff, hlink, _⟩ := hred
      let j : Fin cs.length := ⟨i.val, by rw [hcs]; exact i.isLt⟩
      have hi : ix j = i := Fin.ext rfl
      have htest := (hP j).mpr (by rw [hi]; exact ⟨e, v, hval, hlink, hvs, hoff⟩)
      exact hfailed j htest
    · obtain ⟨e, v, hval, _, _, _⟩ := (hP j).mp htest
      obtain ⟨d, rest, hd, hrow, hactive, hpath, hword⟩ := hdata j
      obtain ⟨a, b, ha, hb, hl⟩ :=
        gm06ActiveDart_isLink G.toGraph vertex tagged edge hlinks d hd hactive
      have haa : a = start (ix j) := Fin.ext (ha.symm.trans hword)
      cases haa
      have hl' : G.toGraph.IsLink (edge ⟨d / 2, by omega⟩)
          (cylinderM1Point k (ix j)) (vertex b) := by
        simpa only [hstart] using hl
      have hPedge := ((L.isSubdrawing (ix j)).1.isLink_iff hpath).mpr hl'
      have hvs : vertex b ≠ cylinderM1Point k (ix j) :=
        (isPathDrawing_ne_of_isLink (L.isPath (ix j)) hPedge).symm
      have hcsj : cs[j.val] = (start (ix j)).val := by
        simp only [cs, List.getElem_ofFn]; rfl
      have hword23 : s'.regs 23 = d := by
        simpa only [hrow, List.getElem_cons_zero] using h23
      have hword24 : s'.regs 24 = gm06DartMate d := by
        simpa only [hrow, List.getElem_cons_zero] using h24
      have hmate : gm06DartMate d < xs.length := by
        have hh := gm06DartMate_lt hd
        simpa only [hlen, List.length_map] using hh
      have hnbWord : xs[gm06DartMate d] = b.val := by
        change xs[gm06DartMate d]?.getD 0 = b.val at hb
        simpa only [List.getElem?_eq_getElem hmate, Option.getD_some] using hb
      have h301' : s'.regs 301 = xs[gm06DartMate d] := by
        simpa only [hrow, List.getElem_cons_zero] using h301
      have hnb : s'.regs 301 = b.val := h301'.trans hnbWord
      have hoff : vertex b ∉ cylinderCuff2 := by
        apply (not_congr (hcuff b hl.right_mem)).mpr
        have hnot := htest.2
        change xs[gm06DartMate (paths[j.val][0]'(hne j))] ∉ outer at hnot
        simpa only [hrow, List.getElem_cons_zero, hnbWord] using hnot
      exact Or.inr ⟨ix j, d, rest, b, hd, hrow, hone, hindex,
        h22.trans hcsj, hword23, hword24, hnb, h306, hactive, hval, hl', hvs, hoff⟩

/-- On an interpreted ordinary graph and linkage input, the full
RAM scan finds a genuine proper Reduction 3 or proves no such
reduction applies at any initial vertex. Its selected edge is the
one read from the given path, as proved by the stronger scan result. -/
theorem gm06Reduction3ScanProg_drawing {w n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hinj : InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (start : Fin k → Fin n) (hstart : ∀ i, vertex (start i) = cylinderM1Point k i)
    (outer : List ℕ) (hcuff : ∀ b : Fin n, vertex b ∈ G.V → (vertex b ∈ cylinderCuff2 ↔ b.val ∈ outer))
    (paths : List (List ℕ)) (hpaths : GM06LinkageRowsEncoding L tagged vertex edge paths)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1) (hk : k < 2 ^ w)
    (ho : outer.length < 2 ^ w) (hoWords : ∀ x ∈ outer, x < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (h3 : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (h12 : s.arrs 12 = tagged.map Prod.snd)
    (h6 : s.arrs 6 = List.ofFn (fun i : Fin k => (start i).val))
    (h7 : s.arrs 7 = outer) (h8 : s.arrs 8 = gm06EncodeRows paths) :
    ∃ s' t, Exec w gm06Reduction3ScanProg s s' t ∧
      t ≤ 7 + k * (73 + 42 * tagged.length + 17 * k + 22 * (gm06EncodeRows paths).length + 13 * outer.length) ∧
      TwoPaths.Keeps [327, 328, 295, 22, 20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306] [24] s s' ∧
      ((s'.regs 327 = 0 ∧ ∀ (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G'),
        ¬ Section5Reduction3Step k G L G' M) ∨
       ∃ i : Fin k, s'.regs 327 = 1 ∧ s'.regs 328 = i.val ∧
         ∃ (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G'),
           IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M) := by
  obtain ⟨s', t, he, ht, hk', hout⟩ := gm06Reduction3ScanProg_selected L tagged vertex edge
    hinj hlinks hcover start hstart outer hcuff paths hpaths s hw hn hm hbits hk ho hoWords
    hpLen hpWords h3 h12 h6 h7 h8
  refine ⟨s', t, he, ht, hk', ?_⟩
  rcases hout with hnone | ⟨i, d, rest, b, hd, hrow, hone, hindex, h22, h23,
    h24, h301, h306, hactive, hval, hl, hvs, hoff⟩
  · exact Or.inl hnone
  · obtain ⟨G', M, hG', hred⟩ :=
      exists_section5_reduction3_of_interior_neighbour L hG i hval hl hvs hoff
    exact Or.inr ⟨i, hone, hindex, G', M, hG', hred⟩

end GraphMinor.Compute
