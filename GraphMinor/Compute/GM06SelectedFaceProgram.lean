module

public import GraphMinor.Compute.GM06SelectedFaceRead
import GraphMinor.Compute.GM06CutOriginFacts

/-!
# Computing the selected face directly from component rotations

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) runs
FACE_ROWS on the cut component and selects the row containing the reverse inner
cuff end. This file composes those actual programs. The owner table
and face code are computed internally. Orbit nonemptiness and distinct
darts give all output word and size bounds needed for the row lookup.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Computed face rows have distinct darts and a bounded word encoding. -/
theorem gm06ActiveFaceRows_code_bounds {w m : ℕ} (rotations : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (hnd : rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ active ↔ d ∈ rotations.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active)
    (hcap : 1 + 2 * (2 * m) < 2 ^ w) :
    let rows := gm06ActiveFaceRows rotations active
    let words := rows.map (List.map Fin.val)
    (gm06EncodeRows words).length ≤ 1 + 2 * (2 * m) ∧
      (∀ x ∈ gm06EncodeRows words, x < 2 ^ w) ∧ words.flatten.Nodup := by
  let rows := gm06ActiveFaceRows rotations active
  have hs := gm06ActiveFaceRows_spec rotations active hnd hcover hmate
  have hne : ∀ row ∈ rows, row ≠ [] := by
    intro row hr
    obtain ⟨start, _, heq, _⟩ := hs.2.2.2 row hr
    rw [heq]
    exact gm06OrbitTrace_ne_nil _ _ _ (by simp)
  have hcapacity := gm06FaceCode_capacity rows hs.1 hne
  have hn : 2 * m < 2 ^ w := by omega
  have hrowWords : ∀ row ∈ rows.map (List.map Fin.val), row.length < 2 ^ w := by
    intro row hr
    obtain ⟨r, hrSource, rfl⟩ := List.mem_map.mp hr
    have hndRow : r.Nodup := hs.1.sublist (List.sublist_flatten_of_mem hrSource)
    have hlen : r.length ≤ 2 * m := by simpa using hndRow.length_le_card
    simpa only [List.length_map] using hlen.trans_lt hn
  have hDarts : ∀ d ∈ (rows.map (List.map Fin.val)).flatten, d < 2 ^ w := by
    intro d hd
    rw [← List.map_flatten] at hd
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hd
    exact e.isLt.trans hn
  have hcount : (rows.map (List.map Fin.val)).length < 2 ^ w := by
    have hl := gm06FaceCode_length (rows.map (List.map Fin.val))
    omega
  refine ⟨hcapacity, gm06EncodeRows_words _ hcount hrowWords hDarts, ?_⟩
  rw [← List.map_flatten]
  exact hs.1.map Fin.val_injective

/-- Compute all component faces and load the row named by target dart 667. -/
def gm06SelectedFaceProg : Cmd := .seq gm06FaceRowsProg gm06SelectFaceRowProg

/-- Registers changed by full selected-face construction. -/
def gm06SelectedFaceRegs : List ℕ := gm06FaceRowsRegs ++ [668]

/-- Exact reverse-inner-cuff face from component rotations and active
ends. No face row, successor table or row owner is supplied as input. -/
theorem gm06SelectedFaceProg_exec {w m : ℕ} (rotations : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (reverseInner : Fin (2 * m)) (s : State)
    (hnd : rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ active ↔ d ∈ rotations.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active)
    (hw : 2 < 2 ^ w) (hcap : 1 + 2 * (2 * m) < 2 ^ w)
    (hcode : (gm06EncodeRows (rotations.map (List.map Fin.val))).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows (rotations.map (List.map Fin.val)), x < 2 ^ w)
    (hl : active.length < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows (rotations.map (List.map Fin.val)))
    (h604 : s.arrs 604 = active.map Fin.val) (h648 : s.regs 648 = 2 * m) (h667 : s.regs 667 = reverseInner.val) :
    ∃ sf t, Exec w gm06SelectedFaceProg s sf t ∧
      t ≤ 118 + 148 * (2 * m) + 29 * rotations.length + 37 * rotations.flatten.length +
        active.length * (40 + 18 * (2 * m)) ∧
      Keeps gm06SelectedFaceRegs [600, 601, 602, 603, 605, 606, 607] s sf ∧
      gm06SelectFaceRowResult sf = (gm06SelectedFace rotations active reverseInner).map (List.map Fin.val) ∧
      sf.arrs 600 = ((gm06SelectedFace rotations active reverseInner).map (List.map Fin.val)).getD [] := by
  have hn : 2 * m < 2 ^ w := by omega
  have hb := gm06ActiveFaceRows_code_bounds rotations active hnd hcover hmate hcap
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, howner₁, hrows₁⟩ := gm06FaceRowsProg_exec rotations active s
    hnd hw hcap hcode hwords hl h600 h604 h648
  let rows := (gm06ActiveFaceRows rotations active).map (List.map Fin.val)
  obtain ⟨sf, tf, hef, htf, hkf, hresult, hrow⟩ := gm06SelectFaceRowProg_exec rows s₁
    (by omega) hn reverseInner.isLt hb.2.2 howner₁ hrows₁
    (by rw [hrows₁]; exact hb.1.trans_lt hcap) (by rw [hrows₁]; exact hb.2.1)
    ((hk₁.1 667 (by simp [gm06FaceRowsRegs, gm06PredecessorRegs])).trans h667)
  have hselected : gm06SelectFaceRow rows reverseInner.val =
      (gm06SelectedFace rotations active reverseInner).map (List.map Fin.val) :=
    gm06SelectFaceRow_map Fin.val Fin.val_injective _ _
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_,
    (hk₁.mono (by intro r hr; exact List.mem_append_left _ hr) (by simp)).trans hkf
      (by simp [gm06SelectedFaceRegs, gm06FaceRowsRegs, gm06PredecessorRegs]) (by simp),
    hresult.trans hselected, hrow.trans (congrArg (fun r => r.getD []) hselected)⟩
  have hL : (s₁.arrs 607).length ≤ 1 + 2 * (2 * m) := by rw [hrows₁]; exact hb.1
  omega

/-- Uniform quadratic bound for the full selected-face cost. -/
theorem gm06SelectedFace_cost_le_polynomial (q r d a : ℕ) :
    118 + 148 * q + 29 * r + 37 * d + a * (40 + 18 * q) ≤
      500 * (q + r + d + a + 1) ^ 2 := by
  have hface := gm06FaceRows_cost_le_polynomial q r d a
  let N := q + r + d + a + 1
  have h1 : 1 ≤ N := by dsimp only [N]; omega
  have hq : q ≤ N := by dsimp only [N]; omega
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N h1
  change _ ≤ 500 * N ^ 2
  change _ ≤ 300 * N ^ 2 at hface
  rw [pow_two] at hface ⊢
  omega

end GraphMinor.Compute
