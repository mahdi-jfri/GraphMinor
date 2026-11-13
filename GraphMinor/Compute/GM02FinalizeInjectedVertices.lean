module

public import GraphMinor.Compute.GM02InjectedVertexPrefix
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Copying the used vertex words into the labelled-input suffix

After the host-order scan, the used buffer consists of the fixed pattern
vertex count followed by its sorted injected vertices. Copy just those
words into a separate array, discarding the unused allocation suffix.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Extract the exact used vertex words into array 30. -/
@[expose] def gm02FinalizeInjectedVerticesProg : Cmd :=
  readSliceProg 29 (.const 0) 30 (.reg 195) 196

/-- The extracted array is the canonical vertex part of the labelled pattern input. -/
theorem gm02FinalizeInjectedVerticesProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hw : 1 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hp : H.n + 1 < 2 ^ W)
    (hbuf : s.arrs 29 = gm02InjectedVertexBuffer G H f G.n)
    (hpos : s.regs 195 = H.n + 1) :
    ∃ s' t, Exec W gm02FinalizeInjectedVerticesProg s s' t ∧
      t ≤ 16 * (H.n + 1) + 9 ∧
      s'.arrs 30 = [H.n] ++ ((gm02InjectedPattern G H f).vertices.sort).map Fin.val ∧
      (∀ a, a ≠ 30 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 196 ∨ 198 < r → s'.regs r = s.regs r) := by
  let words := [H.n] ++ ((gm02InjectedPattern G H f).vertices.sort).map Fin.val
  have hlength : words.length = H.n + 1 := by
    dsimp only [words]
    change ([H.n] ++ ((Finset.univ.image f).sort).map Fin.val).length = H.n + 1
    rw [List.length_append, List.length_singleton, List.length_map, Finset.length_sort,
      Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]
    exact Nat.add_comm _ _
  have hprefix : (gm02InjectedVertexPrefix G H f G.n).length = H.n := by
    have h := gm02InjectedVertexPrefix_full G H f
    have hh := congrArg List.length h
    have : words.length = 1 + (gm02InjectedVertexPrefix G H f G.n).length := by
      dsimp only [words]
      rw [← gm02InjectedVertexPrefix_full G H f]
      simp only [List.length_append, List.length_singleton]
    omega
  have harr : s.arrs 29 = [] ++ words ++ List.replicate (G.n - H.n) 0 := by
    change s.arrs 29 = words ++ List.replicate (G.n - H.n) 0
    rw [hbuf, gm02InjectedVertexBuffer, hprefix, gm02InjectedVertexWords,
      gm02InjectedVertexPrefix_full]

  have hall : ∀ a ∈ words, a < 2 ^ W := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · have heq := List.mem_singleton.1 ha
      exact heq ▸ (by omega : H.n < 2 ^ W)
    · obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
      have hv : v.val < G.n := v.isLt
      exact hv.trans (by omega)
  obtain ⟨s', t, he, ht, hout, ha, hr⟩ := readSliceProg_exec_full 29 30 (.const 0) 195 196
    (by decide) (by decide) [] words (List.replicate (G.n - H.n) 0) rfl hlength hall hw
    (by simpa only [List.length_nil, Nat.zero_add] using hp)
    (s := s) (eval_const (by omega)) harr hpos
  exact ⟨s', t, he, ht, hout, ha, hr⟩

end GraphMinor.Compute
