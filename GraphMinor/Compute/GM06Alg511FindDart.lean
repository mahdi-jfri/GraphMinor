module

public import GraphMinor.Compute.GM06Alg511DartKeys
public import GraphMinor.Compute.GM06FindLabel
import Mathlib.Tactic

/-!
# Selecting an edge of a path returned by maximum flow

For VI (5.11), page 134, a vertex path must be given actual edge
labels before its winding is summed. Form the endpoint-pair key and
scan the directed edge table. Parallel edges may give several matches.
Every returned match has the required endpoints, and the scan preserves
all input arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read endpoints from registers 43 and 44 and the vertex count from
41. Find a matching dart key in array 1100 and return its position in
47, using registers 48 and 20 for the key and the scan index. -/
def gm06Alg511FindDartProg : Cmd :=
  .seq (.assign 48 (.op .add (.op .mul (.reg 43) (.reg 41)) (.reg 44)))
    (gm06FindLabelProg 1100 48 20 47)

/-- The edge scan finds an actual directed edge whenever its pair key
occurs. Its running time is linear in the supplied directed edge table. -/
theorem gm06Alg511FindDartProg_exec {w : ℕ} (keys : List ℕ)
    (n a b : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : n < 2 ^ w) (ha : a < n) (hb : b < n)
    (hsquare : n * n < 2 ^ w) (hlen : keys.length < 2 ^ w)
    (hkeys : ∀ v ∈ keys, v < 2 ^ w)
    (hmem : a * n + b ∈ keys) (harr : s.arrs 1100 = keys)
    (hrn : s.regs 41 = n) (hra : s.regs 43 = a) (hrb : s.regs 44 = b) :
    ∃ s' t, Exec w gm06Alg511FindDartProg s s' t ∧
      t ≤ 13 + 13 * keys.length ∧ Keeps [48, 20, 47] [] s s' ∧
      ∃ (d : ℕ) (hd : d < keys.length), s'.regs 47 = d ∧ keys[d] = a * n + b := by
  have hkey : a * n + b < 2 ^ w := (gm06Alg511PairKey_lt ha hb).trans hsquare
  have hmul : a * n < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hkey
  have heval := Crossing.eval_add
    (Crossing.eval_mul (Crossing.eval_reg hra (ha.trans hn))
      (Crossing.eval_reg hrn hn) hmul)
    (Crossing.eval_reg hrb (hb.trans hn)) hkey
  let s₁ := s.setReg 48 (a * n + b)
  have he₁ : Exec w (.assign 48 (.op .add (.op .mul (.reg 43) (.reg 41)) (.reg 44)))
      s s₁ 6 := .assign heval
  obtain ⟨s', t, he, ht, hk, hd⟩ := gm06FindLabelProg_exec
    1100 48 20 47 (by decide) (by decide) (by decide)
    keys (a * n + b) s₁ hw hlen hkeys hkey (by simpa [s₁] using harr) (by simp [s₁])
  have hk₁ : Keeps [48, 20, 47] [] s s₁ := (Keeps.refl _ _ s).setReg (by simp) _
  refine ⟨s', 6 + t, .seq he₁ he, by omega,
    hk₁.trans hk (by simp) (by simp), ?_⟩
  rcases hd with hnone | hsome
  · obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hmem
    exact False.elim (hnone.2 j hj heq)
  · exact hsome

/-- Equality with a bounded pair key recovers both directed endpoints.
Thus parallel-edge choices made by the scan cannot change its endpoints. -/
theorem gm06Alg511DartKeys_match (x : GM06Alg511Input)
    (a b d : ℕ) (hb : b < x.vertexCount)
    (hd : d < (gm06Alg511DartKeys x).length)
    (hend : x.endpoints.getD (gm06DartMate d) 0 < x.vertexCount)
    (he : (gm06Alg511DartKeys x)[d] = a * x.vertexCount + b) :
    x.endpoints.getD d 0 = a ∧ x.endpoints.getD (gm06DartMate d) 0 = b := by
  have hd' : d < x.endpoints.length := by simpa [gm06Alg511DartKeys_length] using hd
  have he' : x.endpoints.getD d 0 * x.vertexCount +
      x.endpoints.getD (gm06DartMate d) 0 = a * x.vertexCount + b := by
    simpa [gm06Alg511DartKeys, List.getElem_map, List.getElem_range] using he
  exact gm06Alg511PairKey_injective hend hb he'

end GraphMinor.Compute
