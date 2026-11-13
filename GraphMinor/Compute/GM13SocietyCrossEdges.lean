module

public import GraphMinor.Compute.GM13SocietyPathEdges
public import GraphMinor.Compute.GM13SocietyCrossCall

/-!
# Reading both cross paths and restoring their actual edges

The simple cross record has both path lengths followed by the vertex lists.
We copy those lists to separate arrays, then write the tails and heads of
all their actual edges. The original society and the cross record remain
available throughout.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
open GraphMinor.Compute.Crossing

/-- Copy the two vertex lists from the simple cross record in array 65. -/
def gm13CrossListsProg : Cmd :=
  .seq (.assign 20 (.read 65 (.const 1)))
    (.seq (.assign 21 (.read 65 (.const 2)))
      (.seq (readSliceProg 65 (.const 3) 8 (.reg 20) 30)
        (readSliceProg 65 (.op .add (.const 3) (.reg 20)) 9 (.reg 21) 30)))

/-- Reading the cross record takes linear time in the two path lengths. -/
theorem gm13CrossListsProg_exec {w n : ℕ} (L Q : List (Fin n))
    (hw : 8 + n + L.length + Q.length < 2 ^ w)
    {s : State} (hin : s.arrs 65 =
      [1, L.length, Q.length] ++ L.map Fin.val ++ Q.map Fin.val) :
    ∃ s' t, Exec w gm13CrossListsProg s s' t ∧
      t ≤ 16 * (L.length + Q.length) + 30 ∧
      s'.arrs 8 = L.map Fin.val ∧ s'.arrs 9 = Q.map Fin.val ∧
      (∀ a : ℕ, a ≠ 8 → a ≠ 9 → s'.arrs a = s.arrs a) ∧
      s'.regs 0 = s.regs 0 := by
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h3 : 3 < 2 ^ w := by omega
  have hLw : ∀ z ∈ L.map Fin.val, z < 2 ^ w := by
    intro z hz
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact v.2.trans (by omega)
  have hQw : ∀ z ∈ Q.map Fin.val, z < 2 ^ w := by
    intro z hz
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
    exact v.2.trans (by omega)
  let s₁ := s.setReg 20 L.length
  have he₁ : Exec w (.assign 20 (.read 65 (.const 1))) s s₁ 3 := by
    apply Exec.assign
    apply gm13_read_eval (eval_const h1)
    · simp [hin]
    · omega
  let s₂ := s₁.setReg 21 Q.length
  have he₂ : Exec w (.assign 21 (.read 65 (.const 2))) s₁ s₂ 3 := by
    apply Exec.assign
    apply gm13_read_eval (eval_const h2)
    · simp [s₁, hin]
    · omega
  obtain ⟨s₃, t₃, he₃, ht₃, hd₃, ha₃, hr₃⟩ :=
    readSliceProg_exec (s := s₂) (n := L.length) (off := 3) 65 8 (.const 3) 20 30
      (by decide) (by decide) [1, L.length, Q.length] (L.map Fin.val) (Q.map Fin.val)
      rfl (List.length_map ..) hLw h1 (by omega) (eval_const h3)
      (by simpa [s₂, s₁] using hin) (by simp [s₂, s₁])
  have hL₃ : s₃.regs 20 = L.length := by rw [hr₃ 20 (by decide)]; simp [s₂, s₁]
  have hQ₃ : s₃.regs 21 = Q.length := by rw [hr₃ 21 (by decide)]; simp [s₂]
  obtain ⟨s₄, t₄, he₄, ht₄, hd₄, ha₄, hr₄⟩ :=
    readSliceProg_exec (s := s₃) (n := Q.length) (off := 3 + L.length) 65 9
      (.op .add (.const 3) (.reg 20)) 21 30 (by decide) (by decide)
      ([1, L.length, Q.length] ++ L.map Fin.val) (Q.map Fin.val) []
      (by simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]) (List.length_map ..) hQw h1 (by omega)
      (eval_add (eval_const h3) (eval_reg hL₃ (by omega)) (by omega))
      (by rw [ha₃ 65 (by decide)]; simpa [s₂, s₁, List.append_nil] using hin) hQ₃
  refine ⟨s₄, 3 + (3 + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    ?_, (ha₄ 8 (by decide)).trans hd₃, hd₄, ?_, ?_⟩
  · simp only [Expr.cost] at ht₃ ht₄
    omega
  · intro a ha8 ha9
    rw [ha₄ a ha9, ha₃ a ha8]
    rfl
  · rw [hr₄ 0 (by decide), hr₃ 0 (by decide)]
    rfl

/-- Write the actual tails and heads of one path into two output arrays. -/
def gm13PathEdgesProg (a_path a_tail a_head : Arr) : Cmd :=
  .seq (gm13PathEdgeEndsProg a_path a_tail false)
    (gm13PathEdgeEndsProg a_path a_head true)

/-- Both endpoint arrays are written in linear time, preserving all other
arrays and register zero, which holds the vertex count. -/
theorem gm13PathEdgesProg_exec {w n : ℕ} (G : MultiDigraph n)
    (L : List (Fin n)) (a_path a_tail a_head : ℕ)
    (hpt : a_path ≠ a_tail) (hph : a_path ≠ a_head) (hth : a_tail ≠ a_head)
    (ht5 : a_tail ≠ 5) (hh5 : a_head ≠ 5)
    (hw : 8 + n * n + n + L.length < 2 ^ w)
    {s : State} (hpath : s.arrs a_path = L.map Fin.val)
    (hmat : GM13DirectionMatrix G (s.arrs 5)) (hn : s.regs 0 = n) :
    ∃ s' t, Exec w (gm13PathEdgesProg a_path a_tail a_head) s s' t ∧
      t ≤ 200 * L.length + 40 ∧
      s'.arrs a_tail = gm13PathEdgeEnds G L false ∧
      s'.arrs a_head = gm13PathEdgeEnds G L true ∧
      (∀ a : ℕ, a ≠ a_tail → a ≠ a_head → s'.arrs a = s.arrs a) ∧
      s'.regs 0 = s.regs 0 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ :=
    gm13PathEdgeEndsProg_exec G L a_path a_tail false hpt ht5 hw hpath hmat hn
  have hp₁ : s₁.arrs a_path = L.map Fin.val :=
    (hk₁.2 a_path (by simpa using hpt)).trans hpath
  have hm₁ : GM13DirectionMatrix G (s₁.arrs 5) := by
    rw [hk₁.2 5 (by simp [Ne.symm ht5])]
    exact hmat
  have hn₁ : s₁.regs 0 = n := (hk₁.1 0 (by simp)).trans hn
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ :=
    gm13PathEdgeEndsProg_exec G L a_path a_head true hph hh5 hw hp₁ hm₁ hn₁
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega,
    (hk₂.2 a_tail (by simpa using hth)).trans hd₁, hd₂, ?_, ?_⟩
  · intro a hat hah
    rw [hk₂.2 a (by simpa using hah), hk₁.2 a (by simpa using hat)]
  · exact (hk₂.1 0 (by simp)).trans (hk₁.1 0 (by simp))

end GraphMinor.Compute
