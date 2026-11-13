module

public import GraphMinor.Compute.GM06FaceRows
public import GraphMinor.Compute.Algorithm94Unpack
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.Algorithm91Parse
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Vertex and edge incidence of a selected face row

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) selects the
row containing the reverse inner-cuff dart. Incidence is then a finite
membership test: a vertex occurs as a dart's origin, and an edge
occurs as the edge label of a dart. This file defines those lists
and tables. Its RAM marking procedure computes a membership table
from a label list, allowing repeated labels such as repeated visits
to a vertex on a face boundary.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Dense membership bits, including a slot for every permanent label. -/
def gm06IncidenceBits (n : ℕ) (labels : List ℕ) : List ℕ :=
  List.ofFn (fun v : Fin n => if v.val ∈ labels then 1 else 0)

/-- Origins encountered in an oriented face row. -/
def gm06FaceVertices (origins row : List ℕ) : List ℕ :=
  row.map (fun d => origins[d]?.getD 0)

/-- The edge labels encountered in an oriented face row. -/
def gm06FaceEdges (row : List ℕ) : List ℕ := row.map (fun d => d / 2)

/-- The vertex-incidence table of a face row: one bit for each of the `n` vertices, set when the
vertex is the origin of a dart of the row. -/
def gm06IncV (n : ℕ) (origins row : List ℕ) : List ℕ :=
  gm06IncidenceBits n (gm06FaceVertices origins row)

/-- The edge-incidence table of a face row: one bit for each of the `m` edges, set when a dart of
the row lies on the edge. -/
def gm06IncE (m : ℕ) (row : List ℕ) : List ℕ :=
  gm06IncidenceBits m (gm06FaceEdges row)

/-- Vertex incidence is exactly occurrence in the selected boundary row. -/
theorem gm06IncV_eq_one_iff (n : ℕ) (origins row : List ℕ) (v : Fin n) :
    (gm06IncV n origins row)[v.val]'(by simp [gm06IncV, gm06IncidenceBits]) = 1 ↔
      ∃ d ∈ row, origins[d]?.getD 0 = v.val := by
  simp [gm06IncV, gm06IncidenceBits, gm06FaceVertices]

/-- Edge incidence means that at least one of its two darts occurs. -/
theorem gm06IncE_eq_one_iff (m : ℕ) (row : List ℕ) (e : Fin m) :
    (gm06IncE m row)[e.val]'(by simp [gm06IncE, gm06IncidenceBits]) = 1 ↔
      2 * e.val ∈ row ∨ 2 * e.val + 1 ∈ row := by
  simp only [gm06IncE, gm06IncidenceBits, List.getElem_ofFn, ite_eq_left_iff,
    zero_ne_one, imp_false, not_not, gm06FaceEdges, List.mem_map]
  constructor
  · rintro ⟨d, hd, he⟩
    have hmod := Nat.mod_lt d (by decide : 0 < 2)
    have hdiv := Nat.mod_add_div d 2
    have hor : d = 2 * e.val ∨ d = 2 * e.val + 1 := by omega
    exact hor.elim (fun h => Or.inl (h ▸ hd)) (fun h => Or.inr (h ▸ hd))
  · intro h
    rcases h with h | h
    · exact ⟨_, h, by omega⟩
    · exact ⟨_, h, by omega⟩

/-- The dense list table agrees with the existing finite-bitset encoding. -/
theorem gm06IncidenceBits_eq_bitSetList {n : ℕ} (labels : List (Fin n)) :
    gm06IncidenceBits n (labels.map Fin.val) = bitSetList labels.toFinset := by
  unfold gm06IncidenceBits bitSetList
  congr 1
  funext v
  have hm : v.val ∈ labels.map Fin.val ↔ v ∈ labels.toFinset := by
    simp only [List.mem_map, List.mem_toFinset]
    constructor
    · rintro ⟨a, ha, heq⟩
      exact (Fin.ext heq) ▸ ha
    · intro h
      exact ⟨v, h, rfl⟩
  simp only [hm]

/-- Allocate a dense bit table of register-held size and mark its
source labels. Only registers 610--612 and the destination change. -/
def gm06IncidenceBitsProg (src dst : Arr) (size : Reg) : Cmd :=
  .seq (.alloc dst (.reg size))
    (.seq (.assign 610 (.const 0))
      (.seq (.assign 611 (.len src)) (markSliceGenProg src dst 610 611 612)))

/-- Exact linear RAM construction of a dense membership table.
The labels are input data, not a supplied incidence table. -/
theorem gm06IncidenceBitsProg_exec {w n : ℕ} (src dst size : ℕ) (hne : src ≠ dst)
    (labels : List (Fin n)) (s : State) (hw : 1 < 2 ^ w)
    (hn : n < 2 ^ w) (hl : labels.length < 2 ^ w)
    (hsize : s.regs size = n) (hsrc : s.arrs src = labels.map Fin.val) :
    ∃ s' t, Exec w (gm06IncidenceBitsProg src dst size) s s' t ∧
      t ≤ n + 10 + 14 * labels.length ∧
      Keeps [610, 611, 612] [dst] s s' ∧
      s'.arrs dst = gm06IncidenceBits n (labels.map Fin.val) := by
  let s₁ := s.setArr dst (List.replicate n 0)
  let s₂ := s₁.setReg 610 0
  let s₃ := s₂.setReg 611 labels.length
  have he₁ : Exec w (.alloc dst (.reg size)) s s₁ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg hsize hn)
  have he₂ : Exec w (.assign 610 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hs₂ : s₂.arrs src = labels.map Fin.val := by
    simpa only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ hne] using hsrc
  have he₃ : Exec w (.assign 611 (.len src)) s₂ s₃ 2 :=
    .assign (by simpa only [List.length_map] using
      GraphMinor.Compute.Crossing.eval_len hs₂ (by simpa only [List.length_map] using hl))
  obtain ⟨s₄, t₄, he₄, ht₄, hd₄, ha₄, hr₄⟩ := markSliceGenProg_exec
    src dst (r_start := 610) (r_len := 611) (r_idx := 612) hne (by decide) (by decide)
    [] labels [] ∅ (s := s₃) hw hn (by simpa using hl)
    (by simpa [s₃] using hs₂) (by simp [s₃, s₂]) (by simp [s₃])
    (by rw [Alg91.bitSetList_empty]; simp [s₃, s₂, s₁])
  refine ⟨s₄, (1 + n) + (2 + (2 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by omega, ⟨?_, ?_⟩, ?_⟩
  · intro r hr
    have hh : r ≠ 610 ∧ r ≠ 611 ∧ r ≠ 612 := by simpa using hr
    rw [hr₄ r hh.2.2]
    simp only [s₃, s₂, s₁, State.setReg_regs_ne _ _ hh.2.1,
      State.setReg_regs_ne _ _ hh.1, State.setArr_regs]
  · intro a ha
    have ha' : a ≠ dst := by simpa using ha
    rw [ha₄ a ha']
    exact State.setArr_arrs_ne _ _ ha'
  · rw [gm06IncidenceBits_eq_bitSetList]
    simpa only [Finset.empty_union] using hd₄

end GraphMinor.Compute
