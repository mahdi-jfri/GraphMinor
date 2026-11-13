module

public import GraphMinor.Compute.GM06RemoveVertexBits
public import GraphMinor.Compute.GM06InducedEdgeBits
public import GraphMinor.Compute.TwoPathsNorm

/-!
# Installing the retained vertex and edge masks

For Reduction 2 in VI (5.7), page 133, the component marks are
in array 33. Build the retained live mask and its induced edge
mask in fresh arrays, then copy them into the working live and
activity arrays. The endpoint labels, linkage rows, rotations,
and component marks remain available for the other updates.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Retain the live vertices outside component 33 and their active induced edges. -/
def gm06RetainComponentMasksProg : Cmd :=
  .seq (gm06RemoveVertexBitsProg 14 33 15)
    (.seq (gm06InducedEdgeBitsProg 3 12 15 16)
      (.seq (copyProg 14 15) (copyProg 12 16)))

/-- The mask update installs exact induced-drawing masks in linear
vertex and edge time and preserves all other instance arrays. -/
theorem gm06RetainComponentMasksProg_exec {n w : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (A R : Finset (Fin n)) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    (hends : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hactive : s.arrs 12 = tagged.map Prod.snd) (hlive : s.arrs 14 = gm02VertexBits A)
    (hremoved : s.arrs 33 = gm02VertexBits R) :
    ∃ s' t, Exec w gm06RetainComponentMasksProg s s' t ∧
      t ≤ 24 + 31 * n + 40 * tagged.length ∧
      Keeps [180, 181, rI3] [12, 14, 15, 16] s s' ∧
      s'.arrs 14 = gm02VertexBits (A \ R) ∧ s'.arrs 12 = gm06InducedEdgeBits tagged (A \ R) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : tagged.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hlive₁⟩ := gm06RemoveVertexBitsProg_exec A R
    14 33 15 (by decide) (by decide) s hw1 hn hlive hremoved
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hedge₂⟩ := gm06InducedEdgeBitsProg_exec tagged (A \ R)
    3 12 15 16 (by decide) (by decide) (by decide) s₁ hw hn hm hbits
    ((hk₁.2 3 (by decide)).trans hends) ((hk₁.2 12 (by decide)).trans hactive) hlive₁
  have hlive₂ : s₂.arrs 15 = gm02VertexBits (A \ R) := (hk₂.2 15 (by decide)).trans hlive₁
  have hwordLive : ∀ b ∈ gm02VertexBits (A \ R), b < 2 ^ w := by
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    split <;> omega
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hlive₃⟩ := copyProg_exec (dst := 14) (src := 15)
    (by decide) (gm02VertexBits (A \ R)) s₂ hw1
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn) hwordLive hlive₂
  have hedge₃ : s₃.arrs 16 = gm06InducedEdgeBits tagged (A \ R) := (hk₃.2 16 (by decide)).trans hedge₂
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hedge₄⟩ := copyProg_exec (dst := 12) (src := 16)
    (by decide) (gm06InducedEdgeBits tagged (A \ R)) s₃ hw1
    (by simpa only [gm06InducedEdgeBits_length] using hmw)
    (fun b hb => (gm06InducedEdgeBits_le_one tagged (A \ R) hbits b hb).trans_lt hw1) hedge₃
  let regs := [180, 181, rI3]
  let arrays := [12, 14, 15, 16]
  have hk₁' : Keeps regs arrays s s₁ := hk₁.mono (by simp [regs]) (by simp [arrays])
  have hk₂' : Keeps regs arrays s₁ s₂ := hk₂.mono (by simp [regs]) (by simp [arrays])
  have hk₃' : Keeps regs arrays s₂ s₃ := hk₃.mono (by simp [regs]) (by simp [arrays])
  have hk₄' : Keeps regs arrays s₃ s₄ := hk₄.mono (by simp [regs]) (by simp [arrays])
  have hframe := ((hk₁'.trans hk₂' (by simp) (by simp)).trans hk₃' (by simp) (by simp)).trans
    hk₄' (by simp) (by simp)
  simp only [gm02VertexBits, List.length_ofFn] at ht₃
  rw [gm06InducedEdgeBits_length] at ht₄
  exact ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega,
    hframe, (hk₄.2 14 (by decide)).trans hlive₃, hedge₄⟩

end GraphMinor.Compute
