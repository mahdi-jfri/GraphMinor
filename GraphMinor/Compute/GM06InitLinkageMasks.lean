module

public import GraphMinor.Compute.GM06MarkLabelRows
public import GraphMinor.Compute.GM06MarkUsedEndpoints
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing the working linkage masks

The ordinary input fields contain endpoint pairs in array 3 and
the given linkage rows in array 8. First mark the directed labels
from those rows in array 19. Then mark their incident vertices in
array 17. The masks used by the reduction scans are thus computed
from the instance rather than supplied as extra input.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Compute the directed-label and vertex masks of the given linkage rows. -/
def gm06InitLinkageMasksProg : Cmd :=
  .seq (.assign 40 (.len 3))
    (.seq (gm06MarkLabelRowsProg 8 19)
      (.seq (.alloc 17 (.reg 100)) (gm06MarkUsedEndpointsProg 3 19 17)))

/-- Linkage-mask initialization reads only the ordinary endpoint and
path fields and has linear time in their sizes and the vertex count. -/
theorem gm06InitLinkageMasksProg_exec {w n : ℕ} (es : List (Fin n × Fin n))
    (rows : List (List (Fin (2 * es.length))))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * es.length < 2 ^ w)
    (hcw : rows.length < 2 ^ w)
    (hlen : (gm06EncodeRows (rows.map (List.map Fin.val))).length < 2 ^ w)
    {s : State} (hsize : s.regs 100 = n)
    (he : s.arrs 3 = gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)))
    (hr : s.arrs 8 = gm06EncodeRows (rows.map (List.map Fin.val))) :
    ∃ s' t, Exec w gm06InitLinkageMasksProg s s' t ∧
      t ≤ n + 36 * es.length + 22 * rows.length + 14 * rows.flatten.length + 22 ∧
      Keeps [40, 280, 281, 282, 283, 285] [17, 19] s s' ∧
      s'.arrs 19 = bitSetList rows.flatten.toFinset ∧
      s'.arrs 17 = bitSetList (gm06UsedEndpointRows es rows.flatten.toFinset).flatten.toFinset := by
  let s₁ := s.setReg 40 (2 * es.length)
  have he₁ : Exec w (.assign 40 (.len 3)) s s₁ 2 := .assign
    (by simpa only [gm06EndpointWords_length, List.length_map] using
      (eval_len he (by simpa only [gm06EndpointWords_length, List.length_map] using hm)))
  obtain ⟨s₂, t₂, he₂, ht₂, hd₂, ha₂, hg₂⟩ := gm06MarkLabelRowsProg_exec 8 19
    (by decide) rows (by omega) hm hcw hlen (s := s₁) (by simp [s₁]) hr
  have hn₂ : s₂.regs 100 = n := (hg₂ 100 (by decide) (by decide) (by decide) (by decide)).trans hsize
  let s₃ := s₂.setArr 17 (List.replicate n 0)
  have he₃ : Exec w (.alloc 17 (.reg 100)) s₂ s₃ (1 + n) := .alloc (eval_reg hn₂ hn)
  have hv₃ : s₃.arrs 17 = bitSetList (∅ : Finset (Fin n)) := by
    simp [s₃, Alg91.bitSetList_empty]
  have hd₃ : s₃.arrs 19 = bitSetList rows.flatten.toFinset := by simpa [s₃] using hd₂
  have he₃arr : s₃.arrs 3 = gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)) := by
    simpa [s₃] using (ha₂ 3 (by decide)).trans he
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hv₄⟩ := gm06MarkUsedEndpointsProg_exec es rows.flatten.toFinset ∅
    3 19 17 (by decide) (by decide) hw hn hm he₃arr hd₃ hv₃
  have hex : Exec w gm06InitLinkageMasksProg s s₄ (2 + (t₂ + ((1 + n) + t₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s₄, _, hex, by omega, ⟨?_, ?_⟩,
    (hk₄.2 19 (by decide)).trans hd₃, by simpa using hv₄⟩
  · intro r hr'
    have hrparts : r ≠ 40 ∧ r ≠ 280 ∧ r ≠ 281 ∧ r ≠ 282 ∧ r ≠ 283 ∧ r ≠ 285 := by
      simpa using hr'
    rcases hrparts with ⟨h40, h280, h281, h282, h283, h285'⟩
    have h285 : r ∉ [285] := by simpa using h285'
    rw [hk₄.1 r h285]
    exact (hg₂ r h280 h281 h282 h283).trans (State.setReg_regs_ne _ _ h40)
  · intro a ha
    have haparts : a ≠ 17 ∧ a ≠ 19 := by
      simpa using ha
    rcases haparts with ⟨ha17, ha19⟩
    rw [hk₄.2 a (by simpa using ha17)]
    exact (State.setArr_arrs_ne _ _ ha17).trans (ha₂ a ha19)

end GraphMinor.Compute
