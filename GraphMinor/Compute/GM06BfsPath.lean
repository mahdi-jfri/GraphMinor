module

public import GraphMinor.Compute.TwoPathsBfs
public import GraphMinor.Compute.TwoPathsRename
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Breadth-first source paths for Reduction 4

Section 12 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) searches the
candidate graph by ordinary BFS. Reuse the verified queue and
predecessor-chain search, moving it to the finite-program workspace.
All candidate vertices are allowed. The program builds its own
initial labels. A successful output is a simple source-to-target
path, and failure is equivalent to non-reachability. Its list output
is encoded by a success bit, the vertex array and the target register.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths SimpleGraph

/-- Relocate the existing BFS into arrays 620--634 and registers
620--647. The renaming is an involution on all memory addresses. -/
def gm06BfsRename (x : ℕ) : ℕ :=
  if 40 ≤ x ∧ x < 43 then x + 580
  else if 620 ≤ x ∧ x < 623 then x - 580
  else if 60 ≤ x ∧ x < 77 then x + 570
  else if 630 ≤ x ∧ x < 647 then x - 570
  else x

/-- The relocation can be undone by the same map. -/
theorem gm06BfsRename_involutive : Function.Involutive gm06BfsRename := by
  intro x
  unfold gm06BfsRename
  split_ifs <;> omega

/-- BFS with its initial target/free labels computed in array 630. -/
def gm06BfsPathProg : Cmd :=
  .seq (gm13TabulateProg 647 (.reg 620)
    (.op .mul (.const 3) (.op .eq (.reg 647) (.reg 645))) 630)
    (renameCmd gm06BfsRename TwoPaths.bfsProg)

/-- The exact pure BFS result on adjacency lists, with every vertex
of the candidate graph allowed. The graph supplies the meaning of
the adjacency words and does not supply a path. -/
def gm06BfsPath {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (s t : Fin N) : Option (G.Walk s t) :=
  bfsFind G (encodeLists lists).1 (encodeLists lists).2.1 (encodeLists lists).2.2
    (List.finRange N) s t

/-- The pure vertex-list output of BFS_PATH. -/
def gm06BfsPathWords {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (s t : Fin N) : Option (List ℕ) :=
  (gm06BfsPath G lists s t).map (fun p => p.support.map Fin.val)

/-- Decode a BFS result. The stored array omits its final vertex,
which is held in target register 645. -/
def gm06BfsPathResult (s : State) : Option (List ℕ) :=
  if s.regs 646 = 0 then none else some (s.arrs 634 ++ [s.regs 645])

/-- A successful BFS returns a simple path of the candidate graph. -/
theorem gm06BfsPath_isPath {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (hG : IsAdjListFamily G lists) (s t : Fin N)
    (p : G.Walk s t) (hp : gm06BfsPath G lists s t = some p) : p.IsPath :=
  bfsFind_isPath (encodeLists_adjArrays hG) hp

/-- BFS_PATH returns NONE exactly when its target is unreachable. -/
theorem gm06BfsPath_none_iff {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (hG : IsAdjListFamily G lists) (s t : Fin N) :
    gm06BfsPath G lists s t = none ↔ ¬ G.Reachable s t := by
  constructor
  · intro hnone hreach
    obtain ⟨p⟩ := hreach
    have hh := bfsFind_isSome (encodeLists_adjArrays hG) p
      (fun x _ _ _ => List.mem_finRange x)
    rw [show bfsFind G (encodeLists lists).1 (encodeLists lists).2.1
      (encodeLists lists).2.2 (List.finRange N) s t = none from hnone] at hh
    cases hh
  · intro hno
    cases heq : gm06BfsPath G lists s t with
    | none => rfl
    | some p => exact False.elim (hno p.reachable)

/-- Exact execution and linear adjacency-size time bound for the
relocated BFS. No target/free label array is supplied as input. -/
theorem gm06BfsPathProg_exec {w N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (lists : Fin N → List ℕ) (hG : IsAdjListFamily G lists) (u v : Fin N)
    (s : State) (hN : s.regs 620 = N) (hu : s.regs 644 = u.val) (hv : s.regs 645 = v.val)
    (hgs : s.arrs 620 = (encodeLists lists).1)
    (hge : s.arrs 621 = (encodeLists lists).2.1)
    (hent : s.arrs 622 = (encodeLists lists).2.2)
    (hw : N + 4 < 2 ^ w) (hwords : (encodeLists lists).2.2.length < 2 ^ w) :
    ∃ s' t, Exec w gm06BfsPathProg s s' t ∧
      t ≤ 156 + 67 * N + 29 * totalAdjEntries lists ∧
      Keeps ((List.range' 630 14) ++ [646, 647]) (List.range' 630 5) s s' ∧
      gm06BfsPathResult s' = gm06BfsPathWords G lists u v ∧
      (s'.regs 646 = 0 ∨ s'.regs 646 = 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hn : N < 2 ^ w := by omega
  let labels := List.ofFn (bfsLabel (List.finRange N) u v)
  obtain ⟨s₀, t₀, he₀, ht₀, hk₀, hd₀⟩ := gm13TabulateProg_exec 647 (.reg 620)
    (.op .mul (.const 3) (.op .eq (.reg 647) (.reg 645))) 630 labels s hw1
    (by simpa [labels] using hn)
    (fun st hk => by simpa [labels] using (GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 620 (by decide)).trans hN) hn))
    (fun st i hi hk hidx => by
      have hin : i < N := by simpa [labels] using hi
      let x : Fin N := ⟨i, hin⟩
      have he := GraphMinor.Compute.Crossing.eval_mul
        (GraphMinor.Compute.Crossing.eval_const (show 3 < 2 ^ w by omega))
        (GraphMinor.Compute.Crossing.eval_eq (GraphMinor.Compute.Crossing.eval_reg hidx (hin.trans hn))
          (GraphMinor.Compute.Crossing.eval_reg ((hk.1 645 (by decide)).trans hv) (v.isLt.trans hn)) hw1)
        (show 3 * (if i = v.val then 1 else 0) < 2 ^ w by split_ifs <;> omega)
      have hiff : i = v.val ↔ x = v := by
        constructor
        · intro heq; exact Fin.ext heq
        · intro heq; exact congrArg Fin.val heq
      simpa [labels, bfsLabel, List.mem_finRange, x, hiff] using he)
  let sr := renameState gm06BfsRename s₀
  obtain ⟨sm, tm, hem, htm, hrm, ham, hres⟩ := bfsProg_find (encodeLists_adjArrays hG)
    (s := sr) ((hk₀.1 620 (by decide)).trans hN)
    ((hk₀.1 644 (by decide)).trans hu) ((hk₀.1 645 (by decide)).trans hv)
    ((hk₀.2 620 (by decide)).trans hgs) ((hk₀.2 621 (by decide)).trans hge)
    ((hk₀.2 622 (by decide)).trans hent) hd₀ hw hwords
  have hinv : renameState gm06BfsRename sr = s₀ := by
    ext x <;> simp [sr, renameState, gm06BfsRename_involutive x]
  let sf := renameState gm06BfsRename sm
  have hef : Exec w (renameCmd gm06BfsRename TwoPaths.bfsProg) s₀ sf tm := by
    rw [← hinv]
    exact exec_renameCmd gm06BfsRename_involutive hem
  have hkf : Keeps ((List.range' 630 14) ++ [646]) (List.range' 630 5) s₀ sf := by
    constructor
    · intro r hr
      have hnot : gm06BfsRename r ∉ bfsScratchRegs := by
        simp only [List.mem_append, List.mem_range'_1, List.mem_cons] at hr
        simp only [bfsScratchRegs, List.mem_append, List.mem_range'_1, List.mem_singleton,
          rWFound, gm06BfsRename]
        split_ifs <;> omega
      change sm.regs (gm06BfsRename r) = s₀.regs r
      rw [hrm _ hnot]
      exact congrArg s₀.regs (gm06BfsRename_involutive r)
    · intro a ha
      have hnot : gm06BfsRename a ∉ bfsScratchArrs ∧ gm06BfsRename a ≠ aLab := by
        simp only [List.mem_range'_1] at ha
        simp only [bfsScratchArrs, List.mem_cons, List.not_mem_nil, or_false, aPar,
          aQue, aSrc, aWalk, aLab, gm06BfsRename]
        split_ifs <;> omega
      change sm.arrs (gm06BfsRename a) = s₀.arrs a
      rw [ham _ hnot.1 hnot.2]
      exact congrArg s₀.arrs (gm06BfsRename_involutive a)
  have hkall : Keeps ((List.range' 630 14) ++ [646, 647]) (List.range' 630 5) s sf :=
    (hk₀.mono (by simp [List.mem_range'_1]) (by simp [List.mem_range'_1])).trans hkf
      (by simp only [List.mem_append, List.mem_range'_1, List.mem_cons]; tauto)
      (fun _ h => h)
  refine ⟨sf, t₀ + tm, .seq he₀ hef, ?_, hkall, ?_, ?_⟩
  · simp only [Expr.cost, labels, List.length_ofFn] at ht₀
    omega
  · have htarget : sf.regs 645 = v.val := (hkall.1 645 (by simp [List.mem_range'_1])).trans hv
    rcases hres with ⟨p, hp, hflag, harr⟩ | ⟨hnone, hflag⟩
    · change sm.regs 76 = 1 at hflag
      change sm.arrs 64 ++ [v.val] = p.support.map Fin.val at harr
      have hflag' : sf.regs 646 = 1 := hflag
      have harr' : sf.arrs 634 ++ [v.val] = p.support.map Fin.val := harr
      simp only [gm06BfsPathResult, hflag', one_ne_zero, ↓reduceIte, htarget,
        gm06BfsPathWords, gm06BfsPath, hp, Option.map_some, harr']
    · have hflag' : sf.regs 646 = 0 := hflag
      simp only [gm06BfsPathResult, hflag', ↓reduceIte, gm06BfsPathWords,
        gm06BfsPath, hnone, Option.map_none]
  · rcases hres with ⟨_, _, hflag, _⟩ | ⟨_, hflag⟩
    · exact Or.inr hflag
    · exact Or.inl hflag

end GraphMinor.Compute
