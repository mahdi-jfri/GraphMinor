module

public import GraphMinor.Compute.GM06Alg34GapUpdateEntry
public import GraphMinor.Compute.GM06Alg34GapUpdateBuffer
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning all supplied cuff gaps after deletion

The live gap buffer is the consecutive selection writes for the cuff
positions already scanned. The entry theorem appends exactly the next
retained region number. This invariant proves the exact output list
and a cubic bound for the complete cuff scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Visit every supplied cuff gap, retaining and reindexing its region. -/
def gm06GapUpdateLoopProg : Cmd := forUp 6403 (.len 47) gm06GapUpdateEntryProg

/-- The cuff scan emits exactly the finite retained-gap update and
preserves the drawing, supplied gap labels, and prepared complement tables. -/
theorem gm06GapUpdateLoopProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hK : L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.cellCount) (hn : s.regs 100 = x.n)
    (hm : s.regs 101 = x.ends.length) (hi : s.regs 6403 = 0) (hcount : s.regs 6404 = 0)
    (hcap : L.length ≤ (s.arrs 48).length) (hL : s.arrs 2 = L.map Fin.val)
    (hR : s.arrs 47 = List.ofFn (fun j => (g j).val)) (hv : s.arrs 4 = gm06VertexMask vs)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hmask : s.arrs 36 = gm06RootMask x vs)
    (hranks : s.arrs 37 = List.ofFn (fun b : Fin x.cellCount => ((gm06RootMask x vs).take b.val).sum)) :
    ∃ s' t, Exec w gm06GapUpdateLoopProg s s' t ∧
      t ≤ 3 + L.length * (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 57) ∧
      (s'.arrs 48).take (s'.regs 6404) = gm06GapUpdatedWords x vs L g ∧
      s'.regs 6404 = (gm06GapUpdatedWords x vs L g).length ∧
      (s'.arrs 48).length = (s.arrs 48).length ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → A ≠ 48 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 187 → q ≠ 6400 → q ≠ 6401 →
        q ≠ 6402 → q ≠ 6403 → q ≠ 6404 → s'.regs q = s.regs q) := by
  let pos := List.finRange L.length
  let selected := fun i : Fin L.length => decide (L.get i ∈ vs)
  let labels := fun i : Fin L.length => (x.regionAfterDeletion vs (g i)).val
  let out := fun i => gm06BoundaryWords selected labels (pos.take i)
  let buf := fun i => gm06BoundaryWrites selected labels (pos.take i) 0 (s.arrs 48)
  let I : ℕ → State → Prop := fun i st =>
    st.regs 6403 = i ∧ st.regs 6404 = (out i).length ∧ st.arrs 48 = buf i ∧
    (∀ A : ℕ, A ≠ 33 → A ≠ 34 → A ≠ 48 → st.arrs A = s.arrs A) ∧
    (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 187 → q ≠ 6400 → q ≠ 6401 →
      q ≠ 6402 → q ≠ 6403 → q ≠ 6404 → st.regs q = s.regs q)
  have hhi : ∀ i ≤ L.length, ∀ st, I i st →
      st.regs 6403 = i ∧ (Expr.len 47).eval w st = some L.length := by
    intro i _ st hs
    exact ⟨hs.1, by simp [Expr.eval, checkWord,
      hs.2.2.2.1 47 (by decide) (by decide) (by decide), hR, hK]⟩
  have hbody : ∀ i < L.length, ∀ st, I i st → ∃ st' t,
      Exec w gm06GapUpdateEntryProg st st' t ∧
      t ≤ 26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 50 ∧
      I (i + 1) (st'.setReg 6403 (i + 1)) ∧ st'.regs 6403 = i := by
    intro i hip st hs
    obtain ⟨hir, hcnt, hbuf, harr, hreg⟩ := hs
    have hlenbuf : (st.arrs 48).length = (s.arrs 48).length := by
      rw [hbuf, gm06BoundaryWrites_length]
    have hcountle : (out i).length ≤ i :=
      (gm06BoundaryWords_length_le selected labels _).trans (List.length_take_le _ _)
    have hk : (out i).length + 1 < 2 ^ w := (by omega : (out i).length + 1 ≤ L.length).trans_lt hK
    have hcap' : (out i).length < (st.arrs 48).length := by rw [hlenbuf]; omega
    have hlists' : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) st :=
      hlists.of_arrs_eq (harr _ (by decide) (by decide) (by decide))
        (harr _ (by decide) (by decide) (by decide)) (harr _ (by decide) (by decide) (by decide))
    obtain ⟨st', t, hex, ht, hb', hc', ha', hr'⟩ :=
      gm06GapUpdateEntryProg_exec x vs L g ⟨i, hip⟩ hw hN hsquare hK hk
        ((hreg _ (Or.inl (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsize)
        ((hreg _ (Or.inl (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
        ((hreg _ (Or.inl (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm)
        hir hcnt hcap'
        ((harr _ (by decide) (by decide) (by decide)).trans hL)
        ((harr _ (by decide) (by decide) (by decide)).trans hR)
        ((harr _ (by decide) (by decide) (by decide)).trans hv)
        hlists' ((congrArg List.length (harr _ (by decide) (by decide) (by decide))).trans hlen)
        ((harr _ (by decide) (by decide) (by decide)).trans hmask)
        ((harr _ (by decide) (by decide) (by decide)).trans hranks)
    have htake : pos.take (i + 1) = pos.take i ++ [⟨i, hip⟩] := by
      have hh := List.take_succ_eq_append_getElem (l := pos) (by simpa only [pos, List.length_finRange] using hip)
      have hg : pos[i]'(by simpa only [pos, List.length_finRange] using hip) = ⟨i, hip⟩ := by
        simp only [pos, List.getElem_finRange]
        exact Fin.ext rfl
      simpa only [hg] using hh
    refine ⟨st', t, hex, ht, ⟨by simp, ?_, ?_, ?_, ?_⟩,
      (hr' _ (Or.inr (by decide)) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hir⟩
    · change st'.regs 6404 = _
      have hsingle : (gm06BoundaryWords selected labels [⟨i, hip⟩]).length =
          (if L.get ⟨i, hip⟩ ∈ vs then 1 else 0) := by
        simp only [gm06BoundaryWords, List.filter_cons, List.filter_nil, selected,
          decide_eq_true_eq]
        split <;> rfl
      have ho : out (i + 1) = out i ++ gm06BoundaryWords selected labels [⟨i, hip⟩] := by
        dsimp only [out]
        rw [htake, gm06BoundaryWords_append_lists]
      rw [hc', ho, List.length_append, hsingle]
    · change st'.arrs 48 = _
      rw [hb', hbuf]
      simp only [buf, htake, gm06BoundaryWrites_append_lists, Nat.zero_add,
        gm06BoundaryWrites, List.length_nil, selected, decide_eq_true_eq]
      rfl
    · intro A hA hA' hA''
      exact (ha' A hA hA' hA'').trans (harr A hA hA' hA'')
    · intro q hq hq' hq₀ hq₁ hq₂ hq₃ hq₄
      exact (State.setReg_regs_ne _ _ hq₃).trans
        ((hr' q hq hq' hq₀ hq₁ hq₂ hq₄).trans (hreg q hq hq' hq₀ hq₁ hq₂ hq₃ hq₄))
  have hinit : I 0 s := ⟨hi, by simpa only [out, List.take_zero, gm06BoundaryWords,
    List.filter_nil, List.map_nil, List.length_nil] using hcount, rfl,
    fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨s', t, hex, ht, _, hcnt, hbuf, harr, hreg⟩ :=
    Crossing.forUp_exec' I L.length (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 50)
      hw hK hhi hbody s hinit
  have hfull : pos.take L.length = pos := List.take_of_length_le (by simp only [pos, List.length_finRange]; exact le_rfl)
  have hout : out L.length = gm06GapUpdatedWords x vs L g := by
    simp only [out, hfull, gm06GapUpdatedWords]
    rfl
  have hbuf' : s'.arrs 48 = gm06BoundaryWrites selected labels pos 0 (s.arrs 48) := by
    simpa only [buf, hfull] using hbuf
  have hcost : 1 + 6 + (26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 50) =
      26 * (x.cellCount * x.cellCount) + 37 * x.cellCount + 57 := by omega
  simp only [Expr.cost, hcost] at ht
  refine ⟨s', t, hex, ht, ?_, hcnt.trans (congrArg List.length hout), ?_, harr, hreg⟩
  · rw [hcnt, hout, hbuf']
    exact gm06BoundaryWrites_take selected labels pos (s.arrs 48)
      (by simpa only [pos, List.length_finRange] using hcap)
  · rw [hbuf', gm06BoundaryWrites_length]

end GraphMinor.Compute
