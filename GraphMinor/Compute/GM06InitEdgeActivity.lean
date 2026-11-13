module

public import GraphMinor.Compute.Array
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Creating the initial edge-activity array

The edge list has two endpoint words per original edge. Divide its
length by two, allocate that many activity entries, and fill them with
ones. Thus the activity array is computed from the supplied instance
rather than included as extra input. The initialization takes linear
time and preserves the other arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Allocate one active flag per pair of supplied endpoints. -/
def gm06InitEdgeActivityProg (ends active : Arr) : Cmd :=
  .seq (.alloc active (.op .div (.len ends) (.const 2)))
    (fillArr active (.len active) (.const 1) 57)

/-- Activity initialization creates exactly the all-one array for the supplied edges. -/
theorem gm06InitEdgeActivityProg_exec {w m : ℕ} (ends active : ℕ)
    (xs : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hlen : xs.length = 2 * m) (hn : xs.length < 2 ^ w) (ha : s.arrs ends = xs) :
    ∃ s' t, Exec w (gm06InitEdgeActivityProg ends active) s s' t ∧
      t ≤ 13 * m + 8 ∧ Keeps [57] [active] s s' ∧
      s'.arrs active = List.replicate m 1 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : m < 2 ^ w := by omega
  have h2mw : 2 * m < 2 ^ w := hlen ▸ hn
  have hsize : (Expr.op .div (.len ends) (.const 2)).eval w s = some m := by
    simp [Expr.eval, ha, hlen, checkWord, hw, h2mw, hmw, BinOp.eval, BinOp.raw]
  let s₀ := s.setArr active (List.replicate m 0)
  have he₀ : Exec w (.alloc active (.op .div (.len ends) (.const 2))) s s₀ (3 + m) :=
    .alloc hsize
  obtain ⟨s', t, he, ht, hd, _⟩ :=
    Triple.fillArr_const active 1 57 (List.replicate m 0) hw1
      (by simpa only [List.length_replicate] using hmw) hw1 s₀ (by simp [s₀])
  have hex : Exec w (gm06InitEdgeActivityProg ends active) s s' (3 + m + t) := .seq he₀ he
  refine ⟨s', _, hex, ?_, ⟨?_, ?_⟩, ?_⟩
  · simp only [List.length_replicate] at ht
    omega
  · intro r hr
    apply hex.regs_eq_of_not_mem_writtenRegs
    simpa [gm06InitEdgeActivityProg, fillArr, forUp, Cmd.writtenRegs] using hr
  · intro a ha'
    apply hex.arrs_eq_of_not_mem_writtenArrs
    simpa [gm06InitEdgeActivityProg, fillArr, forUp, Cmd.writtenArrs] using ha'
  · simpa only [List.length_replicate] using hd

end GraphMinor.Compute
