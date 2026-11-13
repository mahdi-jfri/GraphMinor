module

public import GraphMinor.Compute.GM06CutAdjacencyInit
public import GraphMinor.Compute.GM06CutCSR

/-!
# Constructing the cut graph's complete adjacency representation

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes
components from the copied graph data. This program makes its own live-vertex
bitmap and permanent vertex range, initializes CSR storage, and reads
all copied rotations. Its output is the exact neighbour family proved
to represent the cut graph. All bounds are polynomial in the input
lists, and no adjacency answer is supplied to the machine.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Build live bits and the label range, then compute every adjacency row. -/
def gm06CutAdjacencyProg : Cmd :=
  .seq (gm06IncidenceBitsProg 629 619 620)
    (.seq (gm13TabulateProg 650 (.reg 620) (.reg 650) 618)
      (.seq gm06CutAdjacencyInitProg gm06CutAdjacencyRowsLoop))

/-- Registers used by the initialized adjacency construction. -/
def gm06CutAdjacencyRegs : List ℕ := [610, 611, 612] ++ gm06CutAdjacencyRowsRegs

/-- Arrays used by the initialized adjacency construction. -/
def gm06CutAdjacencyArrs : List ℕ := [611, 614, 618, 619, 620, 621, 622]

/-- Exact complete CSR construction from copied rotations and endpoint
data, with a quadratic bound in the permanent vertex count. -/
theorem gm06CutAdjacencyProg_exec {w n m : ℕ} (data : GM06CutData) (padding : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : n * n + 2 < 2 ^ w) (hlen : data.rotations.length = n)
    (horgLen : data.origins.length = 2 * m) (hvalues : ∀ v ∈ data.origins, v < n)
    (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hlive : ∀ v ∈ data.vertices, v < n) (hliveFit : data.vertices.length < 2 ^ w)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins)
    (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) data.activeDarts)
    (h629 : s.arrs 629 = data.vertices) (h620 : s.regs 620 = n) :
    let rows := gm06CutAdjacencyRowsFrom n 0 data.origins data.activeDarts data.vertices data.rotations
    ∃ sf t, Exec w gm06CutAdjacencyProg s sf t ∧
      t ≤ 30 + 57 * n + 21 * (n * n) + 14 * data.vertices.length + 129 * data.rotations.flatten.length ∧
      Keeps gm06CutAdjacencyRegs gm06CutAdjacencyArrs s sf ∧
      sf.arrs 620 = gm06CSRStarts 0 rows ∧ sf.arrs 621 = gm06CSREnds 0 rows ∧
      GraphMinor.Compute.Crossing.IsBuf 622 655 rows.flatten (n * n - rows.flatten.length) sf := by
  have hw1 : 1 < 2 ^ w := by omega
  let verts : List (Fin n) := data.vertices.attach.map (fun v => ⟨v.val, hlive v.val v.property⟩)
  have hverts : verts.map Fin.val = data.vertices := by simp [verts, List.map_map]
  have hvertsLen : verts.length = data.vertices.length := by simp only [verts, List.length_map, List.length_attach]
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06IncidenceBitsProg_exec
    629 619 620 (by decide) verts s hw1 hn (by simpa only [hvertsLen] using hliveFit)
    h620 (by simpa only [hverts] using h629)
  have hbits : s₁.arrs 619 = gm06IncidenceBits n data.vertices := by simpa only [hverts] using hd₁
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm13TabulateProg_exec
    650 (.reg 620) (.reg 650) 618 (List.range n) s₁ hw1 (by simpa using hn)
    (fun z hk => by simpa only [List.length_range] using (GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 620 (by decide)).trans ((hk₁.1 620 (by decide)).trans h620)) hn))
    (fun _ i hi _ hr => by simpa only [List.getElem_range] using
      GraphMinor.Compute.Crossing.eval_reg hr (by simpa only [List.length_range] using hi.trans (by simpa using hn)))
  have hk₁₂ : Keeps gm06CutAdjacencyRegs gm06CutAdjacencyArrs s s₂ :=
    (hk₁.mono (by simp [gm06CutAdjacencyRegs]) (by simp [gm06CutAdjacencyArrs])).trans hk₂
      (by simp [gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs]) (by simp [gm06CutAdjacencyArrs])
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hs₃, he₃tab, hb₃, hp₃, hc₃, hv₃⟩ :=
    gm06CutAdjacencyInitProg_exec s₂ hw1 hn (by omega) ((hk₁₂.1 620 (by decide)).trans h620)
  have hk₁₃ : Keeps gm06CutAdjacencyRegs gm06CutAdjacencyArrs s s₃ :=
    hk₁₂.trans hk₃ (by simp [gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs]) (by simp [gm06CutAdjacencyArrs])
  have hsource : s₃.arrs 625 = [n] ++ gm06EncodeRowsPayload data.rotations ++ padding := by
    rw [hk₁₃.2 625 (by decide), h625]
    simp only [gm06EncodeRows, hlen, List.singleton_append]
  obtain ⟨sf, tf, hef, htf, hkf, hbf, hsf, hefTab, _, _, _⟩ := gm06CutAdjacencyRowsLoop_exec
    (base := 0) (cap := n * n) data.origins data.activeDarts data.vertices data.rotations
    [n] padding [] [] [] s₃ hw hn hm (by omega) (by simpa only [hlen] using (le_refl (n * n))) (by simpa using hfit)
    horgLen hvalues hsource (by rw [hk₁₃.2 625 (by decide)]; exact hcode)
    (by rw [hk₁₃.2 625 (by decide)]; exact hwords) hkeys
    ((hk₁₃.2 626 (by decide)).trans h626) ((hk₁₃.2 627 (by decide)).trans h627)
    ((hk₃.2 619 (by decide)).trans ((hk₂.2 619 (by decide)).trans hbits))
    ((hk₃.2 618 (by decide)).trans hd₂) ((hk₁₃.1 620 (by decide)).trans h620)
    (by simpa using hp₃) (by simpa only [hlen] using hc₃) (by simpa using hv₃)
    rfl rfl (by simpa using hs₃) (by simpa using he₃tab) hb₃
  refine ⟨sf, t₁ + (t₂ + (t₃ + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    hk₁₃.trans hkf (by simp [gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs]) (by simp [gm06CutAdjacencyArrs]), ?_, ?_, ?_⟩
  · simp only [Expr.cost, List.length_range] at ht₂
    rw [hvertsLen] at ht₁
    rw [hlen] at htf
    nlinarith only [ht₁, ht₂, ht₃, htf]
  · simpa only [List.nil_append, List.length_nil, hlen, Nat.zero_add, Nat.sub_self, List.replicate_zero, List.append_nil] using hsf
  · simpa only [List.nil_append, List.length_nil, hlen, Nat.zero_add, Nat.sub_self, List.replicate_zero, List.append_nil] using hefTab
  · simpa only [List.nil_append] using hbf

end GraphMinor.Compute
