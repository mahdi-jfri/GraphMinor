module

public import GraphMinor.Compute.GM06FaceEnumeration

/-!
# Initializing and returning the complete face enumeration

FACE_ROWS in Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
starts with all darts unseen and no completed rows. This file
allocates the owner table and row buffer, runs the verified scan,
and copies exactly the resulting encoded prefix to the output.
The execution theorem has only the successor table and active
labels as inputs; completed rows and an output certificate are not
supplied. The full rotation program computes the successor input.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Capacity of the completed-row buffer, computed from the dart count. -/
def gm06FaceCapacityExpr : Expr := .op .add (.const 1) (.op .mul (.const 2) (.len 603))

/-- Initialize owners 605 and buffer 606, enumerate active labels 604,
then return exactly the encoded rows in array 607. -/
def gm06FaceEnumerationProg : Cmd :=
  .seq (.alloc 605 (.len 603))
    (.seq (.alloc 606 gm06FaceCapacityExpr)
      (.seq (.assign 650 (.const 0))
        (.seq (.assign 655 (.const 0))
          (.seq (.assign 656 (.const 1))
            (.seq gm06FaceEnumerationLoop
              (gm13TabulateProg 658 (.reg 656) (.read 606 (.reg 658)) 607))))))

private theorem code_words_lt {b : ℕ} (rows : List (List ℕ))
    (hc : rows.length < b) (hl : ∀ row ∈ rows, row.length < b)
    (hd : ∀ d ∈ rows.flatten, d < b) : ∀ x ∈ gm06EncodeRows rows, x < b := by
  intro x hx
  simp only [gm06EncodeRows, List.mem_cons, gm06EncodeRowsPayload, List.mem_flatMap,
    gm06EncodeNatList, List.mem_cons] at hx
  rcases hx with rfl | ⟨row, hr, rfl | hx⟩
  · exact hc
  · exact hl row hr
  · exact hd x (List.mem_flatten.mpr ⟨row, hr, hx⟩)

/-- Exact enumeration from an ordinary successor table and active
label list. The explicit bound is quadratic in their total size. -/
theorem gm06FaceEnumerationProg_exec {w n : ℕ} (next : Equiv.Perm (Fin n))
    (labels : List (Fin n)) (s : State) (hw : 2 < 2 ^ w)
    (hcap : 1 + 2 * n < 2 ^ w) (hl : labels.length < 2 ^ w)
    (h603 : s.arrs 603 = List.ofFn (fun d => (next d).val))
    (h604 : s.arrs 604 = labels.map Fin.val) :
    let result := gm06FaceRows next n labels
    ∃ sf t, Exec w gm06FaceEnumerationProg s sf t ∧
      t ≤ 36 + 31 * n + labels.length * (40 + 18 * n) ∧
      Keeps (gm06FaceEnumerationRegs ++ [658]) [605, 606, 607] s sf ∧
      sf.arrs 605 = gm06FaceOwners n (result.map (List.map Fin.val)) ∧
      sf.arrs 607 = gm06EncodeRows (result.map (List.map Fin.val)) := by
  let cap := 1 + 2 * n
  have hn : n < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let s₁ := s.setArr 605 (List.replicate n 0)
  let s₂ := s₁.setArr 606 (List.replicate cap 0)
  let s₃ := s₂.setReg 650 0
  let s₄ := s₃.setReg 655 0
  let s₅ := s₄.setReg 656 1
  have he₁ : Exec w (.alloc 605 (.len 603)) s s₁ (1 + n) :=
    .alloc (by simpa only [List.length_ofFn] using GraphMinor.Compute.Crossing.eval_len h603 (by simpa using hn))
  have h603₁ : s₁.arrs 603 = List.ofFn (fun d => (next d).val) := by simp [s₁, h603]
  have hcapacity : gm06FaceCapacityExpr.eval w s₁ = some cap := by
    exact GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_const hw1)
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
        (by simpa only [List.length_ofFn] using GraphMinor.Compute.Crossing.eval_len h603₁ (by simpa using hn))
        (by omega)) hcap
  have he₂ : Exec w (.alloc 606 gm06FaceCapacityExpr) s₁ s₂ (5 + cap) := .alloc hcapacity
  have he₃ : Exec w (.assign 650 (.const 0)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₄ : Exec w (.assign 655 (.const 0)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₅ : Exec w (.assign 656 (.const 1)) s₄ s₅ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const hw1)
  have hk₅ : Keeps gm06FaceEnumerationRegs [605, 606] s s₅ :=
    (((((Keeps.refl _ _ s).setArr (by simp) _).setArr (by simp) _).setReg
      (by simp [gm06FaceEnumerationRegs]) _).setReg (by simp [gm06FaceEnumerationRegs]) _).setReg
        (by simp [gm06FaceEnumerationRegs]) _
  have hbuffer : s₅.arrs 606 = gm06FaceBuffer cap [] := by
    change List.replicate cap 0 = _
    have hlen : cap = 2 * n + 1 := by dsimp only [cap]; omega
    simp only [gm06FaceBuffer, gm06EncodeRows, gm06EncodeRowsPayload, List.length_nil,
      List.flatMap_nil, List.length_cons, List.singleton_append]
    rw [hlen]
    simp only [Nat.add_sub_cancel, List.replicate_succ]
  obtain ⟨sm, tm, hem, htm, hkm, hdm, hbm, _, hcm, hpm⟩ := gm06FaceEnumerationLoop_exec
    next [] labels [] s₅ hw1 hcap (by simpa using hl) (by simp) (by simp)
    ((hk₅.2 603 (by decide)).trans h603) ((hk₅.2 604 (by decide)).trans h604)
    (by simp [s₅, s₄, s₃, s₂, s₁, gm06FaceOwners, gm06FaceOwnerPairs, gm06Scatter])
    hbuffer (by simp [s₅, s₄, s₃]) (by simp [s₅, s₄]) (by simp [s₅, gm06EncodeRows, gm06EncodeRowsPayload])
  let result := gm06FaceRows next n labels
  have hr := gm06FaceRowsAux_invariant next n (by simp) labels [] (by simp) (by simp)
  have hresultnd : result.flatten.Nodup := hr.1
  have hresultorbits : ∀ row ∈ result, ∃ d, row = gm06OrbitTrace next d n := hr.2.1
  have hnonempty : ∀ row ∈ result, row ≠ [] := by
    intro row hrow
    obtain ⟨d, rfl⟩ := hresultorbits row hrow
    exact gm06OrbitTrace_ne_nil next d n (by simp)
  let code := gm06EncodeRows (result.map (List.map Fin.val))
  have hcodecap : code.length ≤ cap := gm06FaceCode_capacity result hresultnd hnonempty
  have hcodew : code.length < 2 ^ w := hcodecap.trans_lt hcap
  have hcodewords : ∀ x ∈ code, x < 2 ^ w := by
    apply code_words_lt
    · have hh := hcodecap
      rw [gm06FaceCode_length] at hh
      omega
    · intro row hrow
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
      have hnrow := (List.nodup_flatten.mp hresultnd).1 r hr
      have hh : r.length ≤ n := by simpa using hnrow.length_le_card
      simp only [List.length_map]
      omega
    · intro d hd
      rw [← List.map_flatten] at hd
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hd
      exact a.isLt.trans hn
  have hprefix : sm.arrs 606 = code ++ List.replicate (cap - code.length) 0 := hbm
  have hpos : sm.regs 656 = code.length := hpm
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec 658 (.reg 656) (.read 606 (.reg 658))
    607 code sm hw1 hcodew
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 656 (by decide)).trans hpos) hcodew)
    (fun st i hi hk hidx => by
      have harr : st.arrs 606 = code ++ List.replicate (cap - code.length) 0 :=
        (hk.2 606 (by decide)).trans hprefix
      have hib : i < (st.arrs 606).length := by rw [harr]; simp only [List.length_append, List.length_replicate]; omega
      have hget : (st.arrs 606)[i] = code[i] := by rw [List.getElem_of_eq harr, List.getElem_append_left hi]
      have he := GraphMinor.Compute.Crossing.eval_read (a := 606)
        (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hcodew)) hib (by rw [hget]; exact hcodewords _ (List.getElem_mem hi))
      simpa only [hget] using he)
  have hkinit := hk₅.trans hkm (fun _ h => h) (fun _ h => h)
  refine ⟨sf, (1 + n) + ((5 + cap) + (2 + (2 + (2 + (tm + tf))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq hem hef))))), ?_,
    (hkinit.mono (fun r hr => List.mem_append.mpr (Or.inl hr)) (by simp)).trans hkf (by simp) (by simp), ?_, hdf⟩
  · simp only [Expr.cost] at htf
    dsimp only [cap] at hcodecap ⊢
    omega
  · exact (hkf.2 605 (by decide)).trans hdm

end GraphMinor.Compute
