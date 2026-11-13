module

public import GraphMinor.Compute.GM06MarkEdgeEnds
public import GraphMinor.Compute.TwoPathsNorm
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing vertices incident with marked linkage edges

Scan the ordinary endpoint array once. Each edge with a marked
forward or reverse label contributes its two endpoints to the
vertex mask. A prefix invariant tracks the vertices already marked.
The source arrays are preserved and the scan has linear edge time.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- The endpoint row contributed by each edge whose direction is marked. -/
def gm06UsedEndpointRows {n : ℕ} (es : List (Fin n × Fin n))
    (D : Finset (Fin (2 * es.length))) : List (List (Fin n)) :=
  List.ofFn fun i : Fin es.length =>
    if (⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D
      then [es[i.val].1, es[i.val].2] else []

/-- Mark endpoints of all edges represented by marked directed labels. -/
def gm06MarkUsedEndpointsProg (ends darts dst : Arr) : Cmd :=
  .seq (.assign 285 (.const 0))
    (forUp 285 (.op .div (.len ends) (.const 2)) (gm06MarkEdgeEndsProg ends darts dst))

/-- The endpoint scan adds exactly the vertices of marked edges to
the existing mask and preserves all other arrays and registers. -/
theorem gm06MarkUsedEndpointsProg_exec {w n : ℕ} (es : List (Fin n × Fin n))
    (D : Finset (Fin (2 * es.length))) (Q : Finset (Fin n))
    (ends darts dst : Arr) (hed : ends ≠ dst) (hdd : darts ≠ dst)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * es.length < 2 ^ w)
    {s : State}
    (he : s.arrs ends = gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)))
    (hd : s.arrs darts = bitSetList D) (hq : s.arrs dst = bitSetList Q) :
    ∃ s' t, Exec w (gm06MarkUsedEndpointsProg ends darts dst) s s' t ∧
      t ≤ 7 + 34 * es.length ∧ Keeps [285] [dst] s s' ∧
      s'.arrs dst = bitSetList (Q ∪ (gm06UsedEndpointRows es D).flatten.toFinset) := by
  let rows := gm06UsedEndpointRows es D
  let Inv : ℕ → State → Prop := fun i st => st.regs 285 = i ∧ Keeps [285] [dst] s st ∧
    st.arrs dst = bitSetList (Q ∪ (rows.take i).flatten.toFinset)
  have hrows : rows.length = es.length := List.length_ofFn
  have hmw : es.length < 2 ^ w := by omega
  let s₀ := s.setReg 285 0
  have he₀ : Exec w (.assign 285 (.const 0)) s s₀ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₀ := by
    refine ⟨by simp [s₀], (Keeps.refl [285] [dst] s).setReg (by simp) _, ?_⟩
    simpa [s₀] using hq
  obtain ⟨s', t, hex, ht, hInv⟩ := forUp_exec' (r_i := 285)
    (hi := .op .div (.len ends) (.const 2)) (body := gm06MarkEdgeEndsProg ends darts dst)
    Inv es.length 25 (by omega) hmw
    (fun i _ st h => by
      refine ⟨h.1, ?_⟩
      have heSt := (h.2.1.2 ends (by simpa using hed)).trans he
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, heSt,
        gm06EndpointWords_length, hm, hmw, hw])
    (fun i hi st h => by
      obtain ⟨st₁, t₁, he₁, ht₁, hb₁, ha₁, hg₁⟩ := gm06MarkEdgeEndsProg_exec es D
        (Q ∪ (rows.take i).flatten.toFinset) ⟨i, hi⟩ ends darts dst hed hw hn hm h.1
        ((h.2.1.2 ends (by simpa using hed)).trans he)
        ((h.2.1.2 darts (by simpa using hdd)).trans hd) h.2.2
      have hk₁ : Keeps [285] [dst] st st₁ :=
        ⟨fun r _ => hg₁ r, fun a ha => ha₁ a (by simpa using ha)⟩
      have hk : Keeps [285] [dst] s st₁ := h.2.1.trans hk₁ (by simp) (by simp)
      have hrow : rows[i]'(by omega) =
          if (⟨2 * i, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
              (⟨2 * i + 1, by omega⟩ : Fin (2 * es.length)) ∈ D
            then [es[i].1, es[i].2] else [] := by
        simp only [rows, gm06UsedEndpointRows, List.getElem_ofFn]
      have htakes : rows.take (i + 1) = rows.take i ++ [rows[i]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
      refine ⟨st₁, t₁, he₁, ht₁, ⟨by simp, hk.setReg (by simp) _, ?_⟩, hg₁ 285 |>.trans h.1⟩
      change st₁.arrs dst = _
      rw [hb₁, htakes, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.toFinset_append, hrow]
      congr 1
      split_ifs <;> ext v <;> simp only [Finset.mem_insert, Finset.mem_union,
        List.toFinset_cons, List.toFinset_nil, Finset.notMem_empty] <;> tauto) s₀ hInv₀
  refine ⟨s', 2 + t, .seq he₀ hex, by simp only [Expr.cost] at ht; omega, hInv.2.1, ?_⟩
  simpa only [← hrows, List.take_length] using hInv.2.2

end GraphMinor.Compute
