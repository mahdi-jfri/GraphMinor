module

public import GraphMinor.Compute.GM02InitInjectedVertices
public import GraphMinor.Compute.GM02InjectedVertexScan
public import GraphMinor.Compute.GM02FinalizeInjectedVertices
import Mathlib.Tactic.Ring

/-!
# Building the vertex part of a labelled pattern input

Initialize the buffer, scan host positions, and copy the used words.
This computes the exact canonical vertex suffix from the decoded
injection. Its time is linear in the host count for a fixed pattern,
and the original host input and candidate counter remain unchanged.
-/

public section
namespace GraphMinor.Compute

/-- Build the canonical vertex-count and vertex-name suffix in array 30. -/
@[expose] def gm02BuildInjectedVerticesProg (p : ℕ) : Cmd :=
  .seq (gm02InitInjectedVerticesProg p)
    (.seq (gm02InjectedVertexScanProg p) gm02FinalizeInjectedVerticesProg)

private theorem frame_bounds (r : ℕ) (hr : r < 194 ∨ 198 < r) :
    r ≠ 194 ∧ r ≠ 195 ∧ (r < 196 ∨ 198 < r) := by omega

/-- The full vertex builder computes the labelled input's exact vertex suffix in linear time. -/
theorem gm02BuildInjectedVerticesProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hw : 1 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hrn : s.regs 40 = G.n)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val) :
    ∃ s' t, Exec W (gm02BuildInjectedVerticesProg H.n) s s' t ∧
      t ≤ 39 + 16 * H.n + G.n * ((gm02InjectionMembershipExpr H.n).cost + 15) ∧
      s'.arrs 30 = [H.n] ++ ((gm02InjectedPattern G H f).vertices.sort).map Fin.val ∧
      (∀ a, a ≠ 29 → a ≠ 30 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 194 ∨ 198 < r → s'.regs r = s.regs r) := by
  have hpn : H.n ≤ G.n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f f.injective
  have hp : H.n + 1 < 2 ^ W := (Nat.add_le_add_right hpn 1).trans_lt hn
  obtain ⟨s₀, he₀, hb₀, hz₀, hp₀, ha₀, hr₀⟩ :=
    gm02InitInjectedVerticesProg_exec G H f s hrn hw hn (by omega)
  have hslots₀ (i : Fin H.n) : s₀.regs (200 + i.val) = (f i).val := by
    have h194 : 200 + i.val ≠ 194 := Nat.ne_of_gt
      ((by decide : 194 < 200).trans_le (Nat.le_add_right 200 i.val))
    have h195 : 200 + i.val ≠ 195 := Nat.ne_of_gt
      ((by decide : 195 < 200).trans_le (Nat.le_add_right 200 i.val))
    exact (hr₀ _ h194 h195).trans (hslots i)
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hr₁⟩ :=
    gm02InjectedVertexScanProg_exec G H f s₀ hw hn
      ((hr₀ 40 (by decide) (by decide)).trans hrn) hz₀ hp₀ hslots₀ hb₀
  obtain ⟨s₂, t₂, he₂, ht₂, hout, ha₂, hr₂⟩ :=
    gm02FinalizeInjectedVerticesProg_exec G H f s₁ hw hn hp hb₁ hp₁
  refine ⟨s₂, (G.n + 11) + (t₁ + t₂), .seq he₀ (.seq he₁ he₂), ?_, hout, ?_, ?_⟩
  · have h := Nat.add_le_add_left (Nat.add_le_add ht₁ ht₂) (G.n + 11)
    convert h using 1 <;> ring
  · intro a ha29 ha30
    exact (ha₂ a ha30).trans ((ha₁ a ha29).trans (ha₀ a ha29))
  · intro r hr
    obtain ⟨hr194, hr195, hrfinal⟩ := frame_bounds r hr
    exact (hr₂ r hrfinal).trans ((hr₁ r hr194 hr195).trans (hr₀ r hr194 hr195))

end GraphMinor.Compute
