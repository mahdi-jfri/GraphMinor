module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.GM02CopyLabelBits
public import GraphMinor.Compute.GM06EndpointLookup

/-!
# Updating active edges for an induced retained drawing

For Reduction 2 in VI (5.7), page 133, an edge survives exactly
when it was active and both endpoints remain live. Read the two
consecutive endpoint words and their live bits, then write their
product with the old activity bit. Both ends of a loop are read,
and the same criterion keeps or deletes that loop correctly.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

private theorem read_vertex_bit_of_index {n w : ℕ} (A : Finset (Fin n)) (v : Fin n)
    (arr : Arr) (index : Expr) (s : State) (hw : 1 < 2 ^ w)
    (hidx : index.eval w s = some v.val) (harr : s.arrs arr = gm02VertexBits A) :
    (Expr.read arr index).eval w s = some (if v ∈ A then 1 else 0) := by
  have he := eval_read (a := arr) hidx
    (by simpa only [harr, gm02VertexBits, List.length_ofFn] using v.isLt)
    (by simp only [harr, gm02VertexBits, List.getElem_ofFn]; split <;> omega)
  simpa only [harr, gm02VertexBits, List.getElem_ofFn, Fin.eta] using he

/-- Activity bits after retaining an induced set of live vertices. -/
def gm06InducedEdgeBits {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ)) (A : Finset (Fin n)) : List ℕ :=
  tagged.map fun p => p.2 * (if p.1.1 ∈ A then 1 else 0) * (if p.1.2 ∈ A then 1 else 0)

/-- Retaining vertices leaves one activity word per original edge. -/
theorem gm06InducedEdgeBits_length {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (A : Finset (Fin n)) :
    (gm06InducedEdgeBits tagged A).length = tagged.length := by
  simp only [gm06InducedEdgeBits, List.length_map]

/-- An induced activity word is one exactly for an active edge with two retained ends. -/
theorem gm06InducedEdgeBits_getElem_eq_one {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (A : Finset (Fin n))
    {i : ℕ} (hi : i < tagged.length) :
    (gm06InducedEdgeBits tagged A)[i]'(by rw [gm06InducedEdgeBits_length]; exact hi) = 1 ↔
      tagged[i].2 = 1 ∧ tagged[i].1.1 ∈ A ∧ tagged[i].1.2 ∈ A := by
  have hget : (gm06InducedEdgeBits tagged A)[i]'(by rw [gm06InducedEdgeBits_length]; exact hi) =
      tagged[i].2 * (if tagged[i].1.1 ∈ A then 1 else 0) * (if tagged[i].1.2 ∈ A then 1 else 0) :=
    List.getElem_map _
  rw [hget]
  by_cases hu : tagged[i].1.1 ∈ A <;> by_cases hv : tagged[i].1.2 ∈ A <;> simp [hu, hv]

/-- The induced edge mask still consists only of zero-one activity words. -/
theorem gm06InducedEdgeBits_le_one {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (A : Finset (Fin n))
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1) : ∀ b ∈ gm06InducedEdgeBits tagged A, b ≤ 1 := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
  have hflag := hbits p hp
  by_cases hu : p.1.1 ∈ A <;> by_cases hv : p.1.2 ∈ A <;> simp [hu, hv, hflag]

/-- Retaining an induced vertex set cannot increase the number of active edges. -/
theorem gm06InducedEdgeBits_count_le {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (A : Finset (Fin n)) :
    (gm06InducedEdgeBits tagged A).count 1 ≤ (tagged.map Prod.snd).count 1 := by
  induction tagged with
  | nil => simp [gm06InducedEdgeBits]
  | cons p tagged ih =>
    change ((p.2 * (if p.1.1 ∈ A then 1 else 0) * (if p.1.2 ∈ A then 1 else 0)) ::
      gm06InducedEdgeBits tagged A).count 1 ≤ (p.2 :: tagged.map Prod.snd).count 1
    by_cases hu : p.1.1 ∈ A <;> by_cases hv : p.1.2 ∈ A <;> by_cases hp : p.2 = 1 <;>
      simp [hu, hv, hp, List.count_cons] <;> omega

/-- Write a fresh edge mask retaining exactly active edges with two live ends. -/
def gm06InducedEdgeBitsProg (ends active vertices dst : Arr) : Cmd :=
  gm13TabulateProg 181 (.len active)
    (.op .mul (.read active (.reg 181))
      (.op .mul (.read vertices (.read ends (.op .mul (.reg 181) (.const 2))))
        (.read vertices (.read ends (.op .add (.op .mul (.reg 181) (.const 2)) (.const 1)))))) dst

/-- The induced-edge mask is computed from ordinary endpoints and
activity bits, in linear edge time, without changing the source arrays. -/
theorem gm06InducedEdgeBitsProg_exec {n w : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (A : Finset (Fin n))
    (ends active vertices dst : Arr) (hed : ends ≠ dst) (had : active ≠ dst) (hvd : vertices ≠ dst)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    (hends : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hactive : s.arrs active = tagged.map Prod.snd) (hvertices : s.arrs vertices = gm02VertexBits A) :
    ∃ s' t, Exec w (gm06InducedEdgeBitsProg ends active vertices dst) s s' t ∧
      t ≤ 6 + 28 * tagged.length ∧ Keeps [181] [dst] s s' ∧
      s'.arrs dst = gm06InducedEdgeBits tagged A := by
  classical
  let xs := gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))
  have hxlen : xs.length = 2 * tagged.length := by simp only [xs, gm06EndpointWords_length, List.length_map]
  have hmw : tagged.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s', t, hex, ht, hk, hout⟩ := gm13TabulateProg_exec 181 (.len active)
    (.op .mul (.read active (.reg 181))
      (.op .mul (.read vertices (.read ends (.op .mul (.reg 181) (.const 2))))
        (.read vertices (.read ends (.op .add (.op .mul (.reg 181) (.const 2)) (.const 1))))))
    dst (gm06InducedEdgeBits tagged A) s hw1
    (by simpa only [gm06InducedEdgeBits, List.length_map] using hmw)
    (fun st hk => by
      simpa only [gm06InducedEdgeBits, List.length_map] using
        (eval_len ((hk.2 active (by simpa using had)).trans hactive)
          (by simpa only [List.length_map] using hmw)))
    (fun st i hi hk hidx => by
      have hin : i < tagged.length := by simpa only [gm06InducedEdgeBits, List.length_map] using hi
      have hinw := hin.trans hmw
      have h2i : 2 * i < xs.length := by omega
      have h2i1 : 2 * i + 1 < xs.length := by omega
      have hfirst : xs[2 * i] = tagged[i].1.1.val := by
        change (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[2 * i]'(by omega) = _
        rw [gm06EndpointWords_getElem_even, List.getElem_map]
        simpa only [List.length_map] using hin
      have hsecond : xs[2 * i + 1] = tagged[i].1.2.val := by
        change (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))[2 * i + 1]'(by omega) = _
        rw [gm06EndpointWords_getElem_odd, List.getElem_map]
        simpa only [List.length_map] using hin
      have hends' : st.arrs ends = xs := (hk.2 ends (by simpa using hed)).trans hends
      have hactive' : st.arrs active = tagged.map Prod.snd :=
        (hk.2 active (by simpa using had)).trans hactive
      have hvertices' : st.arrs vertices = gm02VertexBits A :=
        (hk.2 vertices (by simpa using hvd)).trans hvertices
      have haddr : (Expr.op .mul (.reg 181) (.const 2)).eval w st = some (2 * i) := by
        simpa only [Nat.mul_comm] using eval_mul (eval_reg hidx hinw) (eval_const hw)
          (by omega : i * 2 < 2 ^ w)
      have hreadA := eval_read (a := ends) haddr (by simpa only [hends'] using h2i)
        (by simpa only [hends', hfirst] using tagged[i].1.1.isLt.trans hn)
      simp only [hends', hfirst] at hreadA
      have haddrB := eval_add haddr (eval_const hw1) (by omega : 2 * i + 1 < 2 ^ w)
      have hreadB := eval_read (a := ends) haddrB (by simpa only [hends'] using h2i1)
        (by simpa only [hends', hsecond] using tagged[i].1.2.isLt.trans hn)
      simp only [hends', hsecond] at hreadB
      have hu := read_vertex_bit_of_index A tagged[i].1.1 vertices _ st hw1 hreadA hvertices'
      have hv := read_vertex_bit_of_index A tagged[i].1.2 vertices _ st hw1 hreadB hvertices'
      have hflag : tagged[i].2 ≤ 1 := hbits _ (List.getElem_mem hin)
      have hreadM := eval_read (a := active) (eval_reg hidx hinw)
        (by simpa only [hactive', List.length_map] using hin)
        (by simpa only [hactive', List.getElem_map] using hflag.trans_lt hw1)
      simp only [hactive', List.getElem_map] at hreadM
      have huvFit : (if tagged[i].1.1 ∈ A then 1 else 0) *
          (if tagged[i].1.2 ∈ A then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      have hvalueFit : tagged[i].2 * ((if tagged[i].1.1 ∈ A then 1 else 0) *
          (if tagged[i].1.2 ∈ A then 1 else 0)) < 2 ^ w := by split_ifs <;> omega
      have he := eval_mul hreadM (eval_mul hu hv huvFit) hvalueFit
      simpa only [gm06InducedEdgeBits, List.getElem_map, Nat.mul_assoc] using he)
  refine ⟨s', t, hex, ?_, hk, hout⟩
  simpa only [Expr.cost, gm06InducedEdgeBits, List.length_map, Nat.mul_comm] using ht

end GraphMinor.Compute
