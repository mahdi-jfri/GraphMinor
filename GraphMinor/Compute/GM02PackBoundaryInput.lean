module

public import GraphMinor.Compute.GM02BoundaryEncoding
public import GraphMinor.Compute.GM02PackTerminatedArrays
public import GraphMinor.Compute.GM02ConcatArrays
public import GraphMinor.Compute.GM02TerminatedWords

/-!
# Packing the finite boundary input on the Word RAM

Read the numbered vertex count from the inverse-name array and the index
from the compact pair-word length. Pack an empty-graph termination
prefix and append the two numbered side-bit arrays. The resulting words
are exactly the plain boundary encoding used by the catalogue program.
Every allocation length is computed by the program.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Pack prepared boundary data into array `a+12`, using `a+9` through
`a+11` as fresh buffers. -/
def gm02PackBoundaryInputProg (a : Arr) : Cmd :=
  .seq (.alloc (a + 9) (.const 0))
    (.seq (.assign 260 (.len (a + 4)))
      (.seq (.assign 261 (.const 0))
        (.seq (.assign 262 (.op .div (.len (a + 5)) (.const 2)))
          (.seq (gm02PackTerminatedArraysProg (a + 9) (a + 5) (a + 10))
            (.seq (gm02ConcatArraysProg (a + 10) (a + 7) (a + 11))
              (gm02ConcatArraysProg (a + 11) (a + 8) (a + 12)))))))

/-- Prepared endpoint words and side bits are packed into the exact
boundary encoding in linear boundary-and-terminal size. -/
theorem gm02PackBoundaryInputProg_exec {w : ℕ} (B : GM02BoundaryInput) (a : Arr) (s : State)
    (horig : (s.arrs (a + 4)).length = B.n)
    (hpairs : s.arrs (a + 5) = flatEdges (edgeListOf B.A.pairGraph))
    (hleft : s.arrs (a + 7) = bitSetList B.left) (hright : s.arrs (a + 8) = bitSetList B.right)
    (hlen : B.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02PackBoundaryInputProg a) s s' t ∧
      t ≤ 200 + 100 * B.A.index + 50 * B.n ∧ s'.arrs (a + 12) = B.enc ∧
      (∀ b, b ≤ a + 8 ∨ a + 12 < b → s'.arrs b = s.arrs b) := by
  have hl := B.enc_length
  have hn : B.n < 2 ^ w := by omega
  have hk : B.A.index < 2 ^ w := by omega
  have h2k : 2 * B.A.index < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  let P := flatEdges (edgeListOf B.A.pairGraph)
  have hP : P.length = 2 * B.A.index := by
    simp only [P, length_flatEdges, gm02Termination_pairList_length]
  let s₁ := s.setArr (a + 9) []
  have he₁ : Exec w (.alloc (a + 9) (.const 0)) s s₁ 1 :=
    Exec.alloc (m := 0) (by simp [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)])
  let s₂ := s₁.setReg 260 B.n
  have he₂ : Exec w (.assign 260 (.len (a + 4))) s₁ s₂ 2 := by
    apply Exec.assign
    simp [Expr.eval, s₁, horig, checkWord_of_lt hn]
  let s₃ := s₂.setReg 261 0
  have he₃ : Exec w (.assign 261 (.const 0)) s₂ s₃ 2 :=
    Exec.assign (by simp [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)])
  let s₄ := s₃.setReg 262 B.A.index
  have he₄ : Exec w (.assign 262 (.op .div (.len (a + 5)) (.const 2))) s₃ s₄ 4 := by
    apply Exec.assign
    have hdiv : 2 * B.A.index / 2 = B.A.index := by omega
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₃, s₂, s₁,
      hpairs,
      length_flatEdges, gm02Termination_pairList_length, hdiv,
      checkWord_of_lt h2k, checkWord_of_lt h2, checkWord_of_lt hk]
  have hframe₄ (b : Arr) (hb : b ≠ a + 9) : s₄.arrs b = s.arrs b := by
    simp [s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ hb]
  have hPwords : ∀ v ∈ P, v < 2 ^ w := all_lt_flatEdges (edgeListOf B.A.pairGraph) hn
  obtain ⟨s₅, t₅, he₅, ht₅, hPrefix₅, ha₅, _⟩ := gm02PackTerminatedArraysProg_exec
    (a + 9) (a + 5) (a + 10) (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega) [] P s₄
    (by simp [s₄, s₃, s₂, s₁])
    ((hframe₄ _ (by dsimp only [Arr]; omega)).trans hpairs)
    (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃]) (by simp [s₄])
    (by simp only [List.length_nil, hP]; omega) hn (Nat.two_pow_pos _) hk
    (by simp) hPwords
  have hPrefix : s₅.arrs (a + 10) = B.prefix.enc := by
    rw [B.prefix_enc]
    simpa only [List.append_nil, List.nil_append, List.cons_append] using hPrefix₅
  have hleft₅ : s₅.arrs (a + 7) = bitSetList B.left :=
    (ha₅ _ (by dsimp only [Arr]; omega)).trans
      ((hframe₄ _ (by dsimp only [Arr]; omega)).trans hleft)
  have hright₅ : s₅.arrs (a + 8) = bitSetList B.right :=
    (ha₅ _ (by dsimp only [Arr]; omega)).trans
      ((hframe₄ _ (by dsimp only [Arr]; omega)).trans hright)
  have hprefixlen : B.prefix.enc.length < 2 ^ w := by rw [B.prefix_length]; omega
  have hPrefixWords := B.prefix.enc_all_lt hn hprefixlen
  have hbits (S : Finset (Fin B.n)) : ∀ v ∈ bitSetList S, v < 2 ^ w := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    split_ifs <;> omega
  obtain ⟨s₆, t₆, he₆, ht₆, hTemp₆, ha₆, _⟩ := gm02ConcatArraysProg_exec
    (a + 10) (a + 7) (a + 11) (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
    B.prefix.enc (bitSetList B.left) s₅ hPrefix hleft₅ hw
    (by rw [B.prefix_length, length_bitSetList]; omega) hPrefixWords (hbits B.left)
  have hright₆ : s₆.arrs (a + 8) = bitSetList B.right :=
    (ha₆ _ (by dsimp only [Arr]; omega)).trans hright₅
  obtain ⟨s₇, t₇, he₇, ht₇, hOut₇, ha₇, _⟩ := gm02ConcatArraysProg_exec
    (a + 11) (a + 8) (a + 12) (by dsimp only [Arr]; omega) (by dsimp only [Arr]; omega)
    (B.prefix.enc ++ bitSetList B.left) (bitSetList B.right) s₆ hTemp₆ hright₆ hw
    (by rw [List.length_append, B.prefix_length, length_bitSetList, length_bitSetList]; omega)
    (by intro v hv; rcases List.mem_append.1 hv with hv | hv
        · exact hPrefixWords v hv
        · exact hbits B.left v hv) (hbits B.right)
  refine ⟨s₇, _, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ he₇))))),
    ?_, hOut₇, ?_⟩
  · simp only [List.length_nil, hP] at ht₅
    simp only [List.length_append, B.prefix_length, length_bitSetList] at ht₆ ht₇
    omega
  · intro b hb
    rw [ha₇ b (by dsimp only [Arr] at *; omega), ha₆ b (by dsimp only [Arr] at *; omega),
      ha₅ b (by dsimp only [Arr] at *; omega)]
    exact hframe₄ b (by dsimp only [Arr] at *; omega)

end GraphMinor.Compute
