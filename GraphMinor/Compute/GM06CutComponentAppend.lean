module

public import GraphMinor.Compute.GM06CutComponentRotations

/-!
# Appending one materialized cut component

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns each
component with the induced rotations on all permanent copied vertex
slots. This file interprets a dense component row, proves that its
bits encode exactly the selected vertices, and appends all actual
induced rotation rows after their row-count header. No reachability
or induced-row certificate is supplied to this materialization pass.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Reading a dense component row selects exactly its one bits. -/
theorem gm06CutBitVertices_mem_iff {n : ℕ} (bits : List ℕ) (v : Fin n) :
    v.val ∈ gm06CutBitVertices n bits ↔ bits[v.val]?.getD 0 = 1 := by
  simp only [gm06CutBitVertices, List.mem_map, List.mem_filter, List.mem_finRange, true_and, beq_iff_eq]
  constructor
  · rintro ⟨u, hu, heq⟩
    exact (Fin.ext heq) ▸ hu
  · intro h
    exact ⟨v, h, rfl⟩

/-- A zero/one row of the right length is exactly the incidence
encoding of the vertices selected by reading that row. -/
theorem gm06CutBitVertices_incidence {n : ℕ} (bits : List ℕ) (hlen : bits.length = n)
    (hbits : ∀ x ∈ bits, x = 0 ∨ x = 1) : gm06IncidenceBits n (gm06CutBitVertices n bits) = bits := by
  apply List.ext_getElem
  · simp only [gm06IncidenceBits, List.length_ofFn, hlen]
  · intro i hi hi'
    have hin : i < n := hlen ▸ hi'
    have hm : i ∈ gm06CutBitVertices n bits ↔ bits[i] = 1 := by
      simpa only [List.getElem?_eq_getElem hi', Option.getD_some] using gm06CutBitVertices_mem_iff bits ⟨i, hin⟩
    have hv := hbits _ (List.getElem_mem hi')
    simp only [gm06IncidenceBits, List.getElem_ofFn]
    by_cases h : i ∈ gm06CutBitVertices n bits
    · simp only [h, ↓reduceIte]
      exact (hm.mp h).symm
    · simp only [h, ↓reduceIte]
      exact hv.resolve_right (mt hm.mpr h) |>.symm

/-- Exact induced rotation lists interpreted from a returned component mask. -/
def gm06CutMaterializedRows (n : ℕ) (data : GM06CutData) (bits : List ℕ) : List (List ℕ) :=
  gm06CutComponentRotations data.origins data.activeDarts (gm06CutBitVertices n bits) data.rotations

/-- Materializing a computed component row gives precisely its pure
component rotations, including empty slots. -/
theorem gm06CutMaterializedRows_component {n : ℕ} (data : GM06CutData) (root : Fin n) :
    gm06CutMaterializedRows n data (gm06ComponentBits (gm06CutGraph n data) root) =
      (gm06CutComponentData data root).rotations := by
  unfold gm06CutMaterializedRows gm06CutComponentRotations
  rw [gm06CutBitVertices_eq, gm06CutComponentRotation_rows, gm06CutInducedByVertices_component]

/-- Emit the component row count, reset the cut-row reader, and append all rows. -/
def gm06CutComponentAppendProg : Cmd :=
  .seq (GraphMinor.Compute.Crossing.emitProg 601 655 (.reg 620))
    (.seq (.assign 661 (.const 1))
      (.seq (.assign 665 (.reg 620)) gm06CutComponentRotationsLoop))

/-- Exact physical rotation record of one component from its vertex
bits and common copied graph data, with a linear scan bound. -/
theorem gm06CutComponentAppendProg_exec {w n m cap : ℕ} (data : GM06CutData)
    (vertices pre padding : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hlen : data.rotations.length = n) (horgLen : data.origins.length = 2 * m)
    (hvalues : ∀ v ∈ data.origins, v < n) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hcap : 1 + n + data.rotations.flatten.length ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) data.activeDarts)
    (h630 : s.arrs 630 = gm06IncidenceBits n vertices) (h620 : s.regs 620 = n)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 601 655 pre cap s) :
    let out := gm06CutComponentRotations data.origins data.activeDarts vertices data.rotations
    ∃ sf t, Exec w gm06CutComponentAppendProg s sf t ∧
      t ≤ 12 + 2100 * n + 2100 * data.rotations.flatten.length ∧
      Keeps gm06CutComponentRotationsRegs [601, 611, 615, 616] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 601 655 (pre ++ gm06EncodeRows out)
        (cap - (gm06EncodeRows out).length) sf := by
  have hw1 : 1 < 2 ^ w := by omega
  have hcapPos : cap = (cap - 1) + 1 := by omega
  obtain ⟨he₀, hb₀⟩ := GraphMinor.Compute.Crossing.emitProg_exec (w := w) 601 655 (.reg 620)
    (by rw [← hcapPos]; exact hbuf) (GraphMinor.Compute.Crossing.eval_reg h620 hn) (by omega)
  let s₀ := (s.writeArr 601 pre.length n).setReg 655 (pre.length + 1)
  let s₁ := s₀.setReg 661 1
  let s₂ := s₁.setReg 665 n
  have he₁ : Exec w (.assign 661 (.const 1)) s₀ s₁ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw1)
  have he₂ : Exec w (.assign 665 (.reg 620)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁, s₀, State.writeArr] using h620) hn)
  have hk₀₂ : Keeps gm06CutComponentRotationsRegs [601, 611, 615, 616] s s₂ :=
    (((((Keeps.refl _ _ s).writeArr (by simp) _ _).setReg (by simp [gm06CutComponentRotationsRegs]) _).setReg
      (by simp [gm06CutComponentRotationsRegs]) _).setReg (by simp [gm06CutComponentRotationsRegs]) _)
  have hb₂ : GraphMinor.Compute.Crossing.IsBuf 601 655 (pre ++ [n]) (cap - 1) s₂ := by
    simpa [s₂, s₁, s₀, State.writeArr, GraphMinor.Compute.Crossing.IsBuf] using hb₀
  have hsource : s₂.arrs 625 = [n] ++ gm06EncodeRowsPayload data.rotations ++ padding := by
    rw [hk₀₂.2 625 (by decide), h625]
    simp only [gm06EncodeRows, hlen, List.singleton_append]
  obtain ⟨sf, tf, hef, htf, hkf, hbf, _, _⟩ := gm06CutComponentRotationsLoop_exec
    (cap := cap - 1) data.origins data.activeDarts vertices data.rotations [n] padding (pre ++ [n]) s₂
    hw hn hm (by simpa only [hlen] using hn) horgLen hvalues hkeys
    (by rw [hlen]; omega) (by simp only [List.length_append, List.length_singleton]; omega)
    hsource (by rw [hk₀₂.2 625 (by decide)]; exact hcode)
    (by rw [hk₀₂.2 625 (by decide)]; exact hwords)
    ((hk₀₂.2 626 (by decide)).trans h626) ((hk₀₂.2 627 (by decide)).trans h627)
    ((hk₀₂.2 630 (by decide)).trans h630) (by simp [s₂, s₁]) (by simpa only [hlen] using (show s₂.regs 665 = n by simp [s₂])) hb₂
  refine ⟨sf, 7 + (2 + (2 + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), by rw [hlen] at htf; omega,
    hk₀₂.trans hkf (fun _ h => h) (fun _ h => h), ?_⟩
  simpa only [gm06EncodeRows, gm06CutComponentRotations_length, hlen, List.singleton_append,
    List.append_assoc, List.length_cons, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbf

end GraphMinor.Compute
