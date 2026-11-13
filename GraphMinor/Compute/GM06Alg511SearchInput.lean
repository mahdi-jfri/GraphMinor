module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511Flow
public import GraphMinor.Compute.GM06UnpackRows
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# A plain graph layout for the initial search in VI (5.11)

The supplied finite drawing can also be written in the ordinary
simple-graph layout used by the verified Menger program. Store that
layout alongside the full drawing fields. It repeats only graph
incidence, the two cuff sets and the path count. It contains no
linkage, separator, winding answer or reduction sequence. The layout
is computed from finite labels by enumeration, without geometric
choice. The RAM loader retains the full drawing and copies the
simple-graph row to the Menger input array.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Full drawing data and its plain graph/cuff encoding for maximum
flow, written as two separate length-prefixed rows. -/
def gm06Alg511SearchRows (x : GM06Alg511WindingInput) : List (List ℕ) :=
  [gm06Alg511WindingWords x, encDisjointPathsIn x.drawing.flowInput]

/-- The finite input layout containing both ordinary graph encodings. -/
def gm06Alg511SearchWords (x : GM06Alg511WindingInput) : List ℕ :=
  gm06EncodeRows (gm06Alg511SearchRows x)

/-- The added graph layout retains all original geometric input fields. -/
theorem gm06Alg511SearchWords_injective : Function.Injective gm06Alg511SearchWords := by
  intro x y h
  have hr := gm06EncodeRows_injective h
  exact gm06Alg511WindingWords_injective (List.cons.inj hr).1

/-- Keep the full drawing in array 1000 and its finite flow encoding
in array 1001, then copy the latter to the Menger input array 0. -/
def gm06Alg511LoadSearchProg : Cmd :=
  .seq (.assign 8 (.const 1))
    (.seq (gm06UnpackRowsProg 0 1000 2)
      (.seq (.assign 8 (.const 0))
        (.seq (.assign 9 (.len 1001)) (copySliceToArrCmd 1001 0))))

private theorem mem_encoded_row {rows : List (List ℕ)} {row : List ℕ} {v : ℕ}
    (hrow : row ∈ rows) (hv : v ∈ row) : v ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨row, hrow, List.mem_cons_of_mem _ hv⟩

/-- The loader supplies exactly the ordinary Menger input while
retaining the full drawing in a separate array, in linear time. -/
theorem gm06Alg511LoadSearchProg_exec {w : ℕ} (x : GM06Alg511WindingInput) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 0 = gm06Alg511SearchWords x)
    (hn : (gm06Alg511SearchWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511LoadSearchProg s s' t ∧
      t ≤ 13 + 44 * (gm06Alg511SearchWords x).length ∧
      s'.arrs 0 = encDisjointPathsIn x.drawing.flowInput ∧
      s'.arrs 1000 = gm06Alg511WindingWords x := by
  let flow := encDisjointPathsIn x.drawing.flowInput
  have hrows : (gm06Alg511SearchRows x).length = 2 := rfl
  have hcode : gm06Alg511SearchWords x =
      [2] ++ gm06EncodeRowsPayload (gm06Alg511SearchRows x) ++ [] := by
    simp only [gm06Alg511SearchWords, gm06EncodeRows, hrows,
      List.singleton_append, List.append_nil]
  have hlen : (gm06Alg511SearchWords x).length =
      3 + (gm06Alg511WindingWords x).length + flow.length := by
    simp [gm06Alg511SearchWords, gm06Alg511SearchRows, gm06EncodeRows,
      gm06EncodeRowsPayload, gm06EncodeNatList, flow]
    omega
  let s₁ := s.setReg 8 1
  obtain ⟨s₂, t₂, he₂, ht₂, hfields, _, _, _⟩ :=
    gm06UnpackRowsProg_exec 0 1000 (by decide) (gm06Alg511SearchRows x) [2] [] s₁ hw
      (by simpa only [s₁, State.setReg_arrs, ha] using hcode)
      (by simpa only [s₁, State.setReg_arrs, ha] using hn)
      (by simpa only [s₁, State.setReg_arrs, ha] using hwords)
      (by simp [s₁])
  have hfull : s₂.arrs 1000 = gm06Alg511WindingWords x := hfields 0 (by simp [gm06Alg511SearchRows])
  have hflow : s₂.arrs 1001 = flow := hfields 1 (by simp [gm06Alg511SearchRows])
  have hflowfit : flow.length < 2 ^ w := by omega
  let s₃ := s₂.setReg 8 0
  let s₄ := s₃.setReg 9 flow.length
  have he₄ : Exec w (.assign 9 (.len 1001)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_len (by simpa only [s₃, State.setReg_arrs] using hflow) hflowfit)
  obtain ⟨s₅, t₅, he₅, ht₅, hinput, _, _, harr⟩ :=
    copySliceToArrCmd_exec 1001 0 (by decide) flow 0 (s := s₄) hw
      (by simpa only [s₄, s₃, State.setReg_arrs, hflow] using hflowfit)
      (by simp [s₄, s₃, hflow])
      (by intro j hj; simp [s₄, s₃, hflow, List.getElem?_eq_getElem hj])
      (by
        intro v hv
        exact hwords v (mem_encoded_row (by simp [gm06Alg511SearchRows, flow]) hv))
      (by simp [s₄, s₃]) (by simp [s₄])
  refine ⟨s₅, 2 + (t₂ + (2 + (2 + t₅))),
    .seq (.assign (GraphMinor.Compute.Crossing.eval_const hw)) (.seq he₂
      (.seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) (.seq he₄ he₅))),
    ?_, hinput, ?_⟩
  · have hpayload : (gm06EncodeRowsPayload (gm06Alg511SearchRows x)).length <
        (gm06Alg511SearchWords x).length := by
      rw [hcode]
      simp
    omega
  · rw [harr 1000 (by decide)]
    simpa only [s₄, s₃, State.setReg_arrs] using hfull

/-- Load the ordinary graph layout and run the verified initial
maximum-flow search. -/
def gm06Alg511InitialSearchProg : Cmd :=
  .seq gm06Alg511LoadSearchProg disjointPathsEndToEndProg

/-- The initial search with its machine-readable linkage-existence
flag copied to output register 0. -/
def gm06Alg511InitialSearchBitProg : Cmd :=
  .seq gm06Alg511InitialSearchProg (.assign 0 (.read outArr (.const 0)))

end GraphMinor.Compute
