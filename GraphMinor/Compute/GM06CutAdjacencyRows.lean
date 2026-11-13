module

public import GraphMinor.Compute.GM06CutAdjacencyRow
public import GraphMinor.Compute.GM06CutOriginRows
import GraphMinor.Compute.Join13Adapter101Defs

/-!
# Reading all copied rotations into adjacency arrays

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) searches the
components after constructing all copied rotations. This loop reads
those rotations in permanent vertex order and constructs CSR rows
from their reverse-end origins. Its invariant tracks the unread
rotation cursor, the two offset prefixes and the entries prefix.
The quadratic entries buffer allows a simple polynomial bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
open GraphMinor.Compute.Crossing

/-- Read one copied row, append its neighbours, and advance the vertex. -/
def gm06CutAdjacencyRowsLoop : Cmd :=
  .while (.reg 665)
    (.seq gm06ReadCutOriginRowProg
      (.seq gm06CutAdjacencyRowProg
        (.seq (.assign 666 (.op .add (.reg 666) (.const 1)))
          (.assign 665 (.op .sub (.reg 665) (.const 1))))))

/-- Registers changed by the complete copied-row adjacency loop. -/
def gm06CutAdjacencyRowsRegs : List ℕ := [650, 651, 652, 653, 655, 660, 661, 662, 664, 665, 666]

/-- Exact adjacency rows and offsets for every unread copied rotation.
The source may retain zero padding beyond its last encoded row. -/
theorem gm06CutAdjacencyRowsLoop_exec {w n m base cap : ℕ}
    (origins active live : List ℕ) (rows : List (List ℕ))
    (pre tail output starts ends : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hbase : base + rows.length ≤ n) (hcap : n * rows.length ≤ cap)
    (hfit : output.length + cap + 2 < 2 ^ w)
    (horgLen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (ha : s.arrs 625 = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * m)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h619 : s.arrs 619 = gm06IncidenceBits n live) (h618 : s.arrs 618 = List.range n)
    (h620 : s.regs 620 = n) (h661 : s.regs 661 = pre.length)
    (h665 : s.regs 665 = rows.length) (h666 : s.regs 666 = base)
    (hstartsLen : starts.length = base) (hendsLen : ends.length = base)
    (hstarts : s.arrs 620 = starts ++ List.replicate (n - base) 0)
    (hends : s.arrs 621 = ends ++ List.replicate (n - base) 0)
    (hbuf : IsBuf 622 655 output cap s) :
    let adj := gm06CutAdjacencyRowsFrom n base origins active live rows
    ∃ sf t, Exec w gm06CutAdjacencyRowsLoop s sf t ∧
      t ≤ 1 + rows.length * (41 + 20 * n) + 129 * rows.flatten.length ∧
      Keeps gm06CutAdjacencyRowsRegs [611, 614, 620, 621, 622] s sf ∧
      IsBuf 622 655 (output ++ adj.flatten) (cap - adj.flatten.length) sf ∧
      sf.arrs 620 = starts ++ gm06CSRStarts output.length adj ++ List.replicate (n - (base + rows.length)) 0 ∧
      sf.arrs 621 = ends ++ gm06CSREnds output.length adj ++ List.replicate (n - (base + rows.length)) 0 ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload rows).length ∧
      sf.regs 665 = 0 ∧ sf.regs 666 = base + rows.length := by
  induction rows generalizing base cap pre output starts ends s with
  | nil =>
    refine ⟨s, 1, .while_false (eval_reg h665 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, ?_, ?_, ?_, ?_, h665, ?_⟩
    · simpa [gm06CutAdjacencyRowsFrom] using hbuf
    · simpa [gm06CutAdjacencyRowsFrom, gm06CSRStarts] using hstarts
    · simpa [gm06CutAdjacencyRowsFrom, gm06CSREnds] using hends
    · simpa [gm06EncodeRowsPayload] using h661
    · simpa using h666
  | cons row rows ih =>
    simp only [List.length_cons] at hbase hcap h665
    have hu : base < n := by omega
    have hc : rows.length + 1 < 2 ^ w := by omega
    have hrowSrc : s.arrs 625 = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    have hlen : (s.arrs 625).length = pre.length + (1 + row.length) +
        (gm06EncodeRowsPayload rows).length + tail.length := by
      rw [hrowSrc]
      simp [gm06EncodeNatList, List.length_append]
      omega
    have hrow : row.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ := gm06ReadCutOriginRowProg_exec
      pre row (gm06EncodeRowsPayload rows ++ tail) s (by omega) hrowSrc hcode hwords h661
    have hcapRow : n ≤ cap := by
      have hsum : n * rows.length + n ≤ cap := by simpa only [Nat.mul_add, Nat.mul_one] using hcap
      omega
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hb₂, hs₂, he₂tab⟩ := gm06CutAdjacencyRowProg_exec
      origins active live row output (starts ++ List.replicate (n - base) 0)
      (ends ++ List.replicate (n - base) 0) s₁ hw hm hu hrow horgLen
      (fun d hd => hkeys d (by simp [hd])) hvalues hcapRow hfit hd₁
      ((hk₁.2 626 (by decide)).trans h626) ((hk₁.2 627 (by decide)).trans h627)
      ((hk₁.2 619 (by decide)).trans h619) ((hk₁.2 618 (by decide)).trans h618)
      ((hk₁.1 620 (by decide)).trans h620) ((hk₁.1 666 (by decide)).trans h666)
      ((hk₁.2 620 (by decide)).trans hstarts) ((hk₁.2 621 (by decide)).trans hends)
      (by simp only [List.length_append, List.length_replicate, hstartsLen]; omega)
      (by simp only [List.length_append, List.length_replicate, hendsLen]; omega)
      ⟨(hk₁.2 622 (by decide)).trans hbuf.1, (hk₁.1 655 (by decide)).trans hbuf.2⟩
    have hk₁₂ : Keeps gm06CutAdjacencyRowsRegs [611, 614, 620, 621, 622] s s₂ :=
      (hk₁.mono (by simp [gm06CutAdjacencyRowsRegs]) (by simp)).trans hk₂
        (by simp [gm06CutAdjacencyRowsRegs]) (by simp)
    have hv₂ : s₂.regs 666 = base := (hk₂.1 666 (by decide)).trans ((hk₁.1 666 (by decide)).trans h666)
    have hc₂ : s₂.regs 665 = rows.length + 1 := (hk₂.1 665 (by decide)).trans ((hk₁.1 665 (by decide)).trans h665)
    let s₃ := s₂.setReg 666 (base + 1)
    let s₄ := s₃.setReg 665 rows.length
    have he₃ : Exec w (.assign 666 (.op .add (.reg 666) (.const 1))) s₂ s₃ 4 :=
      .assign (eval_add (eval_reg hv₂ (hu.trans hn)) (GraphMinor.Compute.Crossing.eval_const (by omega)) (by omega))
    have he₄ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        have hr : (Expr.reg 665).eval w s₃ = some (rows.length + 1) :=
          eval_reg (by simpa [s₃] using hc₂) hc
        have he := GraphMinor.Compute.Crossing.eval_sub hr
          (GraphMinor.Compute.Crossing.eval_const (c := 1) (by omega))
        have hsub : rows.length + 1 - 1 = rows.length := by omega
        rw [hsub] at he
        exact he)
    have hk₁₄ : Keeps gm06CutAdjacencyRowsRegs [611, 614, 620, 621, 622] s s₄ :=
      (hk₁₂.setReg (by simp [gm06CutAdjacencyRowsRegs]) _).setReg (by simp [gm06CutAdjacencyRowsRegs]) _
    let neighbours := gm06CutRowNeighbours n origins active live base row
    have hneigh : neighbours.length ≤ n := gm06CutRowNeighbours_length_le n origins active live base row
    let pre' := pre ++ gm06EncodeNatList row
    let output' := output ++ neighbours
    let starts' := starts ++ [output.length]
    let ends' := ends ++ [output.length + neighbours.length]
    have hs' : s₄.arrs 620 = starts' ++ List.replicate (n - (base + 1)) 0 := by
      change s₂.arrs 620 = _
      rw [hs₂]
      have hstep := list_set_append_replicate_zero_step starts (n - base) output.length (by omega)
      simpa only [hstartsLen, starts', List.append_assoc, Nat.sub_sub] using hstep
    have he' : s₄.arrs 621 = ends' ++ List.replicate (n - (base + 1)) 0 := by
      change s₂.arrs 621 = _
      rw [he₂tab]
      have hstep := list_set_append_replicate_zero_step ends (n - base) (output.length + neighbours.length) (by omega)
      simpa only [hendsLen, ends', List.append_assoc, Nat.sub_sub, neighbours] using hstep
    have hsrc' : s₄.arrs 625 = pre' ++ gm06EncodeRowsPayload rows ++ tail := by
      rw [hk₁₄.2 625 (by decide)]
      simpa only [pre', List.append_assoc] using hrowSrc
    have hcursor : s₄.regs 661 = pre'.length := by
      have hh := (hk₂.1 661 (by decide)).trans hp₁
      simpa [s₄, s₃, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    have hcap' : n * rows.length ≤ cap - neighbours.length := by
      simp only [Nat.mul_add, Nat.mul_one] at hcap
      omega
    obtain ⟨sf, tf, hef, htf, hkf, hbf, hsf, hefTab, hpf, hcf, hvf⟩ := ih
      (base := base + 1) (cap := cap - neighbours.length) pre' output' starts' ends' s₄
      (by omega) hcap' (by simp only [output', List.length_append]; omega)
      hsrc' (by rw [hk₁₄.2 625 (by decide)]; exact hcode)
      (by rw [hk₁₄.2 625 (by decide)]; exact hwords)
      (fun d hd => hkeys d (by simp [hd]))
      ((hk₁₄.2 626 (by decide)).trans h626) ((hk₁₄.2 627 (by decide)).trans h627)
      ((hk₁₄.2 619 (by decide)).trans h619) ((hk₁₄.2 618 (by decide)).trans h618)
      ((hk₁₄.1 620 (by decide)).trans h620) hcursor (by simp [s₄]) (by simp [s₄, s₃])
      (by simp [starts', hstartsLen]) (by simp [ends', hendsLen]) hs' he' hb₂
    refine ⟨sf, 1 + (t₁ + (t₂ + (4 + 4))) + tf,
      .while_true (eval_reg h665 hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ (.seq he₃ he₄))) hef, ?_,
      hk₁₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, ?_, ?_, hcf, ?_⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append, Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [gm06CutAdjacencyRowsFrom_cons, List.flatten_cons, List.length_append,
        output', neighbours, List.append_assoc, Nat.sub_sub] using hbf
    · simpa only [gm06CutAdjacencyRowsFrom_cons, gm06CSRStarts, starts', output', neighbours,
        List.length_append, List.singleton_append, List.append_assoc, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsf
    · simpa only [gm06CutAdjacencyRowsFrom_cons, gm06CSREnds, ends', output', neighbours,
        List.length_append, List.singleton_append, List.append_assoc, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hefTab
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvf

end GraphMinor.Compute
