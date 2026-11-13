module

public import GraphMinor.Compute.GM06PuncturedEdgeRead
public import GraphMinor.Compute.GM06PuncturedGraphData
public import GraphMinor.Compute.GM06EndpointLookup
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning all active edges away from one removed vertex

The component search for Reduction 2 in VI (5.7), page 133, builds
its adjacency marks by scanning the ordinary endpoint and activity
arrays. A prefix invariant records exactly the rows marked so far.
The scan preserves the input arrays and takes linear time in the
number of supplied edges, including inactive edges and loops.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Scan all original edge indices and mark their punctured adjacencies. -/
def gm06PuncturedEdgeLoopProg (ends active : Arr) : Cmd :=
  .seq (.assign 136 (.const 0))
    (forUp 136 (.len active) (gm06PuncturedEdgeReadProg ends active))

/-- The scan writes exactly the guarded row fold, with a linear time
bound and no requirement on the initial contents of its scratch registers. -/
theorem gm06PuncturedEdgeLoopProg_exec {w n : ℕ} (ends active : Arr)
    (he28 : ends ≠ 28) (ha28 : active ≠ 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val)
    (hcap : (s.arrs 28).length = n * n) :
    ∃ s' t, Exec w (gm06PuncturedEdgeLoopProg ends active) s s' t ∧
      t ≤ 5 + 48 * tagged.length ∧ Keeps [136, 132, 133, 134] [28] s s' ∧
      s'.arrs 28 = (tagged.flatMap (fun p => gm06PuncturedEdgeRows p.1 p.2 cut)).foldl
        (gm06MatrixMarkRow n) (s.arrs 28) := by
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  let mask := tagged.map Prod.snd
  let rows := fun p : (Fin n × Fin n) × ℕ => gm06PuncturedEdgeRows p.1 p.2 cut
  let R := [136, 132, 133, 134]
  let Inv : ℕ → State → Prop := fun i st => st.regs 136 = i ∧ Keeps R [28] s st ∧
    st.arrs 28 = ((tagged.take i).flatMap rows).foldl (gm06MatrixMarkRow n) (s.arrs 28)
  have hlen : xs.length = 2 * mask.length := by
    simp only [xs, mask, gm06EndpointWords_length, List.length_map]
  have hxw : xs.length < 2 ^ w := by simpa only [xs, gm06EndpointWords_length, List.length_map] using hm
  have hmw : tagged.length < 2 ^ w := by omega
  have hmbits : ∀ b ∈ mask, b ≤ 1 := by
    intro b hb'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb'
    exact hbits p hp
  let s₀ := s.setReg 136 0
  have he₀ : Exec w (.assign 136 (.const 0)) s s₀ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₀ := by
    refine ⟨by simp [s₀], (Keeps.refl R [28] s).setReg (by simp [R]) _, ?_⟩
    simp [s₀]
  obtain ⟨s', t, hex, ht, hInv⟩ := forUp_exec' (r_i := 136) (hi := .len active)
    (body := gm06PuncturedEdgeReadProg ends active) Inv tagged.length 41 (by omega) hmw
    (fun i _ st h => ⟨h.1, by simpa only [List.length_map] using (eval_len ((h.2.1.2 active (by simpa using ha28)).trans hb)
      (by simpa only [List.length_map] using hmw))⟩)
    (fun i hi st h => by
      have hiM : i < mask.length := by simpa only [mask, List.length_map] using hi
      have hfirst : xs[2 * i]'(by omega) = tagged[i].1.1.val := by
        change (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[2 * i]'(by rw [gm06EndpointWords_length, List.length_map]; omega) = _
        rw [gm06EndpointWords_getElem_even, List.getElem_map]
        simpa only [List.length_map] using hi
      have hsecond : xs[2 * i + 1]'(by omega) = tagged[i].1.2.val := by
        change (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[2 * i + 1]'(by rw [gm06EndpointWords_length, List.length_map]; omega) = _
        rw [gm06EndpointWords_getElem_odd, List.getElem_map]
        simpa only [List.length_map] using hi
      have hcapSt : (st.arrs 28).length = n * n := by
        rw [h.2.2, gm06MatrixMarkRows_length, hcap]
      obtain ⟨st₁, t₁, he₁, ht₁, hk₁, hmat₁⟩ := gm06PuncturedEdgeReadProg_exec ends active
        xs mask i hiM tagged[i].1 cut hw hn hsquare hlen hxw hmbits hfirst hsecond
        ((h.2.1.2 ends (by simpa using he28)).trans ha)
        ((h.2.1.2 active (by simpa using ha28)).trans hb) h.1
        ((h.2.1.1 100 (by simp [R])).trans hN)
        ((h.2.1.1 135 (by simp [R])).trans hcut) hcapSt
      have hk₁' : Keeps R [28] st st₁ := hk₁.mono (by simp [R]) (by simp)
      have hk : Keeps R [28] s st₁ := h.2.1.trans hk₁' (by simp) (by simp)
      have hiReg : st₁.regs 136 = i := (hk₁.1 136 (by decide)).trans h.1
      refine ⟨st₁, t₁, he₁, ht₁, ⟨by simp, hk.setReg (by simp [R]) _, ?_⟩, hiReg⟩
      change st₁.arrs 28 = _
      rw [hmat₁, h.2.2]
      have htakes : (tagged.take (i + 1)).flatMap rows =
          (tagged.take i).flatMap rows ++ rows tagged[i] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [htakes, List.foldl_append]
      simp only [mask, List.getElem_map, rows]) s₀ hInv₀
  refine ⟨s', 2 + t, .seq he₀ hex, by simp only [Expr.cost] at ht; omega, hInv.2.1, ?_⟩
  simpa only [List.take_length] using hInv.2.2

end GraphMinor.Compute
