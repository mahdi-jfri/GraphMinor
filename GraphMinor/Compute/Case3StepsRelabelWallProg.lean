module

public import GraphMinor.Compute.Case3StepsMapWallSectionsProg
public import GraphMinor.Compute.Case3StepsBranchSliceProg

/-!
# Returning a wall encoding to original labels

The tagged wall returned by (7.2) is copied to a wall buffer. Its branch
labels and then its counted internal-vertex lists are mapped through the
member inverse list. The header, path lengths, and order stay unchanged.
The result is exactly the encoding of the moved wall.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy and rename the wall result of the supplied member algorithm. -/
def case3RelabelWallProg (h : ℕ) : Cmd :=
  .seq (.assign 112 (.op .sub (.len 129) (.const 1)))
    (.seq (.assign 114 (.const 1))
      (.seq (case3BranchSliceProg 46)
        (.seq (.assign 119 (.const 3))
          (.seq (.assign 112 (.const (elemWallNumVerts h)))
            (.seq case3MapWallSliceProg
              (.seq (.assign 119 (.const (3 + elemWallNumVerts h)))
                (case3MapWallSectionsProg (elemWallEdges h).length)))))))

/-- The returned wall is renamed exactly through the member inverse list,
with linear work in its encoding length and retained member data. -/
theorem case3RelabelWallProg_exec {w h n N : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (B : MultiDigraph N) (orig : Fin n → Fin N)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hlen : (1 :: W.encList).length < 2 ^ w)
    (hwords : ∀ x ∈ W.encList, x < 2 ^ w) {s : State}
    (hsrc : s.arrs 129 = 1 :: W.encList)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) :
    ∃ s' t, Exec w (case3RelabelWallProg h) s s' t ∧ t ≤ 60 * W.encList.length + 40 ∧
      s'.arrs 46 = (W.moveOrig B orig).encList ∧
      (∀ a, a ≠ 46 → s'.arrs a = s.arrs a) ∧
      (∀ r < 112, s'.regs r = s.regs r) := by
  let header := [h, elemWallNumVerts h, (elemWallEdges h).length]
  let branches := (List.finRange (elemWallNumVerts h)).map W.branchVert
  let lists := (List.finRange (elemWallEdges h).length).map W.internalVerts
  have hbrlen : branches.length = elemWallNumVerts h := by simp only [branches, List.length_map, List.length_finRange]
  have hlistlen : lists.length = (elemWallEdges h).length := by simp only [lists, List.length_map, List.length_finRange]
  have hheader : header.length = 3 := rfl
  have henc : W.encList = header ++ branches.map Fin.val ++ case3CountedLists Fin.val lists := by
    simpa only [header, branches, lists, List.map_map, Function.comp_def] using case3Wall_encList_counted W
  have hwallLen : W.encList.length = 3 + elemWallNumVerts h + (case3CountedLists Fin.val lists).length := by
    rw [henc]
    simp only [List.length_append, List.length_map, hheader, hbrlen]
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have htagLen : W.encList.length + 1 < 2 ^ w := hlen
  have hWlenw : W.encList.length < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  have hNV : elemWallNumVerts h < 2 ^ w := by omega
  have hcursor : 3 + elemWallNumVerts h < 2 ^ w := by omega
  let s₁ := s.setReg 112 W.encList.length
  let s₂ := s₁.setReg 114 1
  have hex₁ : Exec w (.assign 112 (.op .sub (.len 129) (.const 1))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsrc, List.length_cons, htagLen, h1, hWlenw])
  have hex₂ : Exec w (.assign 114 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, harr₃, hreg₃⟩ := case3BranchSliceProg_exec 46 (by decide)
    [1] W.encList [] h1 (by simp only [List.length_cons, List.length_nil] at hlen ⊢; omega) hwords
    (s := s₂) (by simpa only [s₂, s₁, State.setReg_arrs, List.singleton_append, List.append_nil] using hsrc)
    (by rw [State.setReg_regs_ne _ _ (show (112 : ℕ) ≠ 114 by decide), State.setReg_regs_self])
    (by simp only [s₂, State.setReg_regs_self, List.length_singleton])
  let s₄ := s₃.setReg 119 3
  let s₅ := s₄.setReg 112 (elemWallNumVerts h)
  have hex₄ : Exec w (.assign 119 (.const 3)) s₃ s₄ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hex₅ : Exec w (.assign 112 (.const (elemWallNumVerts h))) s₄ s₅ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hNV, ↓reduceIte])
  obtain ⟨s₆, t₆, hex₆, ht₆, hbuf₆, harr₆, hreg₆⟩ := case3MapWallSliceProg_exec orig header
    (case3CountedLists Fin.val lists) branches h1 hn hN
    (by rw [hheader, hbrlen]; simp only [List.length_cons] at hlen; omega)
    (s := s₅) ((harr₃ 47 (by decide)).trans hlabels) (hbuf₃.trans henc)
    (by rw [State.setReg_regs_ne _ _ (show (119 : ℕ) ≠ 112 by decide), State.setReg_regs_self]; exact hheader.symm)
    (by rw [State.setReg_regs_self]; exact hbrlen.symm)
  let s₇ := s₆.setReg 119 (3 + elemWallNumVerts h)
  have hex₇ : Exec w (.assign 119 (.const (3 + elemWallNumVerts h))) s₆ s₇ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hcursor, ↓reduceIte])
  obtain ⟨s₈, t₈, hex₈, ht₈, hbuf₈, harr₈, _⟩ := case3MapWallSectionsProg_exec orig
    (header ++ branches.map (fun u => (orig u).1)) [] lists (elemWallEdges h).length hlistlen h1 hn hN
    (by simp only [List.length_append, List.length_map, hheader, hbrlen]; simp only [List.length_cons] at hlen; omega)
    (s := s₇) ((harr₆ 47 (by decide)).trans ((harr₃ 47 (by decide)).trans hlabels))
    (by simpa only [s₇, State.setReg_arrs, List.append_nil] using hbuf₆)
    (by simp only [s₇, State.setReg_regs_self, List.length_append, List.length_map, hheader, hbrlen])
  have hex : Exec w (case3RelabelWallProg h) s s₈ (4 + (2 + (t₃ + (2 + (2 + (t₆ + (2 + t₈))))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))))))
  refine ⟨s₈, 4 + (2 + (t₃ + (2 + (2 + (t₆ + (2 + t₈)))))), hex, ?_, ?_, ?_, ?_⟩
  · rw [hbrlen] at ht₆
    omega
  · rw [case3Wall_moveOrig_encList_counted]
    simpa only [header, branches, lists, List.map_map, Function.comp_def, List.append_nil, List.append_assoc] using hbuf₈
  · intro a ha
    exact (harr₈ a ha).trans ((harr₆ a ha).trans (harr₃ a ha))
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3RelabelWallProg, case3BranchSliceProg, writeSliceProg, writeSliceBody, case3MapWallSliceProg,
        case3MapWallSectionsProg, case3MapWallSectionProg, forUp, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
