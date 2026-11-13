module

public import GraphMinor.Compute.GM06EndpointLookup
public import GraphMinor.Compute.Algorithm91Parse
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Marking both ends of a linkage edge

After the given path rows have marked their directed edge labels,
scan the original endpoint pairs. If either direction of an edge
is marked, mark both its vertices. The two writes also handle loops.
This supplies the protected vertices for Reduction 2 in VI (5.7).
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Inspect the two directed labels of edge 285 and mark both ends when used. -/
def gm06MarkEdgeEndsProg (ends darts dst : Arr) : Cmd :=
  .ite (.op .add (.read darts (.op .mul (.reg 285) (.const 2)))
    (.read darts (.op .add (.op .mul (.reg 285) (.const 2)) (.const 1))))
    (.seq (.write dst (.read ends (.op .mul (.reg 285) (.const 2))) (.const 1))
      (.write dst (.read ends (.op .add (.op .mul (.reg 285) (.const 2)) (.const 1))) (.const 1)))
    .skip

private theorem read_label_bit {w M : ℕ} (D : Finset (Fin M)) (d : Fin M)
    (a : Arr) (index : Expr) {s : State} (hw : 1 < 2 ^ w)
    (hi : index.eval w s = some d.val) (ha : s.arrs a = bitSetList D) :
    (Expr.read a index).eval w s = some (if d ∈ D then 1 else 0) := by
  have he := eval_read (a := a) hi
    (by simpa only [ha, length_bitSetList] using d.isLt)
    (by simp only [ha, bitSetList, List.getElem_ofFn]; split <;> omega)
  simpa only [ha, bitSetList, List.getElem_ofFn, Fin.eta] using he

/-- The endpoint step adds exactly the two vertices of an edge whose
forward or reverse label occurs in the given linkage rows. -/
theorem gm06MarkEdgeEndsProg_exec {w n : ℕ} (es : List (Fin n × Fin n))
    (D : Finset (Fin (2 * es.length))) (Q : Finset (Fin n)) (i : Fin es.length)
    (ends darts dst : Arr) (hed : ends ≠ dst)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * es.length < 2 ^ w)
    {s : State} (hi : s.regs 285 = i.val)
    (he : s.arrs ends = gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)))
    (hd : s.arrs darts = bitSetList D) (hq : s.arrs dst = bitSetList Q) :
    ∃ s' t, Exec w (gm06MarkEdgeEndsProg ends darts dst) s s' t ∧ t ≤ 25 ∧
      s'.arrs dst = bitSetList
        (if (⟨2 * i.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
            (⟨2 * i.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D
          then insert es[i.val].2 (insert es[i.val].1 Q) else Q) ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  let d₀ : Fin (2 * es.length) := ⟨2 * i.val, by omega⟩
  let d₁ : Fin (2 * es.length) := ⟨2 * i.val + 1, by omega⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hidx₀ : (Expr.op .mul (.reg 285) (.const 2)).eval w s = some d₀.val := by
    simpa only [d₀, Nat.mul_comm] using
      eval_mul (eval_reg hi (by omega)) (eval_const hw) (by omega)
  have hidx₁ : (Expr.op .add (.op .mul (.reg 285) (.const 2)) (.const 1)).eval w s = some d₁.val :=
    eval_add hidx₀ (eval_const hw1) (by omega)
  have hb₀ := read_label_bit D d₀ darts _ hw1 hidx₀ hd
  have hb₁ := read_label_bit D d₁ darts _ hw1 hidx₁ hd
  have hsum := eval_add hb₀ hb₁ (by split_ifs <;> omega)
  by_cases hused : d₀ ∈ D ∨ d₁ ∈ D
  · have hnz : (if d₀ ∈ D then 1 else 0) + (if d₁ ∈ D then 1 else 0) ≠ 0 := by
      rcases hused with h | h <;> simp [h]
    have hget₀ : (s.arrs ends)[d₀.val]'(by simp only [he, gm06EndpointWords_length, List.length_map]; exact d₀.isLt) =
        es[i.val].1.val := by
      simp only [he, d₀]
      change (gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)))[2 * i.val]'_ = _
      rw [gm06EndpointWords_getElem_even, List.getElem_map]
      simpa only [List.length_map] using i.isLt
    have hget₁ : (s.arrs ends)[d₁.val]'(by simp only [he, gm06EndpointWords_length, List.length_map]; exact d₁.isLt) =
        es[i.val].2.val := by
      simp only [he, d₁]
      change (gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)))[2 * i.val + 1]'_ = _
      rw [gm06EndpointWords_getElem_odd, List.getElem_map]
      simpa only [List.length_map] using i.isLt
    have hread₀ := eval_read (a := ends) hidx₀
      (by simp only [he, gm06EndpointWords_length, List.length_map]; exact d₀.isLt)
      (by rw [hget₀]; exact (es[i.val].1).isLt.trans hn)
    rw [hget₀] at hread₀
    let s₁ := s.writeArr dst es[i.val].1.val 1
    have he₁ : Exec w (.write dst (.read ends (.op .mul (.reg 285) (.const 2))) (.const 1)) s s₁ 6 :=
      .write hread₀ (eval_const hw1) (by rw [hq, length_bitSetList]; exact (es[i.val].1).isLt)
    have hidx₁' : (Expr.op .add (.op .mul (.reg 285) (.const 2)) (.const 1)).eval w s₁ = some d₁.val := hidx₁
    have heq : s₁.arrs ends = s.arrs ends := State.writeArr_arrs_ne _ _ _ hed
    have hget₁' : (s₁.arrs ends)[d₁.val]'(by rw [heq]; simp only [he, gm06EndpointWords_length, List.length_map]; exact d₁.isLt) = es[i.val].2.val := by
      simpa only [heq] using hget₁
    have hread₁ : (Expr.read ends (.op .add (.op .mul (.reg 285) (.const 2)) (.const 1))).eval w s₁ =
        some es[i.val].2.val := by
      have hh := eval_read (a := ends) hidx₁'
        (by rw [heq]; simp only [he, gm06EndpointWords_length, List.length_map]; exact d₁.isLt)
        (by rw [hget₁']; exact (es[i.val].2).isLt.trans hn)
      simpa only [hget₁'] using hh
    have hq₁ : s₁.arrs dst = bitSetList (insert es[i.val].1 Q) := by
      simp only [s₁, State.writeArr_arrs_self, hq, Alg91.bitSetList_set_one]
    let s₂ := s₁.writeArr dst es[i.val].2.val 1
    have he₂ : Exec w (.write dst (.read ends (.op .add (.op .mul (.reg 285) (.const 2)) (.const 1))) (.const 1))
        s₁ s₂ 8 :=
      .write hread₁ (eval_const hw1) (by rw [hq₁, length_bitSetList]; exact (es[i.val].2).isLt)
    refine ⟨s₂, 11 + (6 + 8), .ite_true hsum hnz (.seq he₁ he₂), by omega, ?_, ?_, fun _ => rfl⟩
    · simp only [s₂, State.writeArr_arrs_self, hq₁, Alg91.bitSetList_set_one]
      simp only [d₀, d₁] at hused
      rw [if_pos hused]
    · intro a ha
      exact (State.writeArr_arrs_ne _ _ _ ha).trans (State.writeArr_arrs_ne _ _ _ ha)
  · have hz : (if d₀ ∈ D then 1 else 0) + (if d₁ ∈ D then 1 else 0) = 0 := by
      simp only [not_or] at hused
      simp [hused.1, hused.2]
    have hzero := hsum
    rw [hz] at hzero
    refine ⟨s, 12, .ite_false hzero (.skip s), by omega, ?_, fun _ _ => rfl, fun _ => rfl⟩
    simp only [d₀, d₁] at hused
    simpa only [if_neg hused] using hq

end GraphMinor.Compute
