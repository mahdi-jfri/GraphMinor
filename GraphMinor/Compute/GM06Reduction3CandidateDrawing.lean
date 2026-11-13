module

public import GraphMinor.Compute.GM06Reduction3Candidate
public import GraphMinor.GM06.Defs
import GraphMinor.Compute.GM06ActiveValencyRepresentation
import GraphMinor.Compute.GM06ActiveDartLink
import GraphMinor.GM06.Section5InitialNeighbourUnique
import GraphMinor.GM06.Section5Reduction3Apply
import GraphMinor.GM11.Walks

/-!
# The computed contraction test is the printed Reduction 3 condition

The active counter gives the current valency. The first supplied
path edge is non-loop and its opposite endpoint is the computed
neighbour. The supplied outer-cuff labels identify the membership
test. At valency one, uniqueness of that incident link makes the
test complete for the printed contraction condition. A positive
flag gives the actual topological contraction of VI (5.7), page 133.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06

/-- At a supplied initial vertex, the actual RAM flag is equivalent
to the printed Reduction 3 local condition, and success gives a proper
reduced drawing and linkage. -/
theorem gm06Reduction3CandidateProg_drawing {w n k : ℕ} {G : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hinj : Set.InjOn edge {j | tagged[j.val].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j.val].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j.val].1.1) (vertex tagged[j.val].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j.val].2 = 1 ∧ edge j = e)
    (paths : List (List ℕ)) (hi : i.val < paths.length) (hne : 0 < paths[i.val].length)
    (hfirst : paths[i.val][0] < 2 * tagged.length)
    (hactive : (tagged[paths[i.val][0] / 2]'(by omega)).2 = 1)
    (hpath : edge ⟨paths[i.val][0] / 2, by omega⟩ ∈ (L.pathDrawing i).E)
    (a : Fin n) (hpoint : vertex a = cylinderM1Point k i)
    (hstart : (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[paths[i.val][0]]?.getD 0 = a.val)
    (cs : List ℕ) (hcuff : ∀ b : Fin n, vertex b ∈ G.V →
      (vertex b ∈ cylinderCuff2 ↔ b.val ∈ cs))
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1) (hcLen : cs.length < 2 ^ w)
    (hcWords : ∀ x ∈ cs, x < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (h3 : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (h12 : s.arrs 12 = tagged.map Prod.snd) (h7 : s.arrs 7 = cs)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h22 : s.regs 22 = a.val) (h295 : s.regs 295 = i.val) :
    ∃ s' t, Exec w gm06Reduction3CandidateProg s s' t ∧
      t ≤ 57 + 42 * tagged.length + 17 * i.val + 22 * paths[i.val].length + 13 * cs.length ∧
      TwoPaths.Keeps [20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306] [24] s s' ∧
      s'.regs 23 = paths[i.val][0] ∧ s'.regs 24 = gm06DartMate paths[i.val][0] ∧
      ∃ b : Fin n, s'.regs 301 = b.val ∧
        G.toGraph.IsLink (edge ⟨paths[i.val][0] / 2, by omega⟩) (cylinderM1Point k i) (vertex b) ∧
        vertex b ≠ cylinderM1Point k i ∧
        (s'.regs 306 = 1 ↔ ∃ e v, vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
          G.toGraph.IsLink e (cylinderM1Point k i) v ∧ v ≠ cylinderM1Point k i ∧ v ∉ cylinderCuff2) ∧
        (s'.regs 306 = 1 → ∃ (G' : Drawing ClosedCylinder) (M : CylinderLinkage k G'),
          IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' M) ∧
        (s'.regs 306 = 0 ∨ s'.regs 306 = 1) := by
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  have hlen : xs.length = 2 * tagged.length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have hx : ∀ x ∈ xs, x < 2 ^ w := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact q.1.1.isLt.trans hn
    · exact q.1.2.isLt.trans hn
  obtain ⟨s', t, hex, ht, hframe, hcount, h23, h24, h301, hflag, hbit⟩ :=
    gm06Reduction3CandidateProg_exec xs (tagged.map Prod.snd) cs paths i.val a.val hi hne
      (by simpa only [List.length_map] using hfirst) s hw
      (by simpa only [List.length_map] using hm)
      (by simpa only [List.length_map] using hlen) hx
      (by simpa only [List.forall_mem_map] using hbits) (a.isLt.trans hn)
      hcLen hcWords hpLen hpWords h3 h12 h7 h8 h22 h295
  obtain ⟨a', b, ha', hb, hl⟩ := gm06ActiveDart_isLink G.toGraph vertex tagged edge hlinks
    paths[i.val][0] hfirst hactive
  have haa : a' = a := Fin.ext (ha'.symm.trans hstart)
  subst a'
  have hlG : G.toGraph.IsLink (edge ⟨paths[i.val][0] / 2, by omega⟩)
      (cylinderM1Point k i) (vertex b) := by simpa only [hpoint] using hl
  have hlP := ((L.isSubdrawing i).1.isLink_iff hpath).mpr hlG
  have hbne : vertex b ≠ cylinderM1Point k i := (isPathDrawing_ne_of_isLink (L.isPath i) hlP).symm
  have hmate : gm06DartMate paths[i.val][0] < xs.length := hlen ▸ gm06DartMate_lt hfirst
  change xs[gm06DartMate paths[i.val][0]]?.getD 0 = b.val at hb
  rw [List.getElem?_eq_getElem hmate, Option.getD_some] at hb
  have hval := gm06ActiveLabelledVertexValency G.toGraph vertex vertex.injective tagged edge hinj hlinks hcover a
  change vertexValency G.toGraph (vertex a) = (gm06ActiveEndpointBits xs (tagged.map Prod.snd) a.val).sum at hval
  rw [← hval, hpoint, hb] at hflag
  have hactual : s'.regs 306 = 1 ↔ vertexValency G.toGraph (cylinderM1Point k i) = 1 ∧
      vertex b ∉ cylinderCuff2 :=
    hflag.trans (and_congr Iff.rfl (not_congr (hcuff b hl.right_mem)).symm)
  refine ⟨s', t, hex, by simpa only [List.length_map] using ht, hframe, h23, h24,
    b, h301.trans hb, hlG, hbne, ?_, ?_, hbit⟩
  · constructor
    · intro hf
      obtain ⟨hval, hoff⟩ := hactual.mp hf
      exact ⟨_, vertex b, hval, hlG, hbne, hoff⟩
    · rintro ⟨e, v, hval, hlv, _, hoff⟩
      have hvb := (initial_link_unique_of_valency_one hval hlG hbne hlv).2
      exact hactual.mpr ⟨hval, hvb ▸ hoff⟩
  · intro hf
    obtain ⟨hval, hoff⟩ := hactual.mp hf
    exact exists_section5_reduction3_of_interior_neighbour L hG i hval hlG hbne hoff

end GraphMinor.Compute
