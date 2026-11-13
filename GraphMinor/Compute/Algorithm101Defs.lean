module

public import GraphMinor.Compute.Case3Block

/-!
# Supporting Combinators, Pure Folio/Model Decoders, and Bridges for GM XIII Algorithm (10.1)

This file provides the foundational definitions and bridge lemmas used by the Word RAM
formalizations of **Graph Minors XIII, Algorithms (10.1) and (10.4)** (Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, pages 106–108):

1. **Memory-Shifting Combinators (`Expr.shiftMem`, `Cmd.shiftMem`, `State.shiftDown`,
   `State.shiftUp`, `Exec.shiftMem`):**
   Shifts every register index by `R_off` and every array index by `A_off` in an arbitrary Word RAM
   command `c : Cmd`, proving that any execution on `s.shiftDown R_off A_off` lifts to an execution
   of `c.shiftMem R_off A_off` on `s` that automatically preserves all registers `< R_off` and all
   arrays `< A_off`.
2. **Pure Reading Decoders for `FolioSetRep`, `RootedDigraphModel`, and Algorithm (4.1) Output
   (`parseFolioSetRep`, `parseModelFull`, `parseFolioAndModels`, `Alg41Spec101`):**
   Decodes `encFolioSetRep F` followed by the serialized `RootedDigraphModel`s purely by reading
   words and checking decidable validity conditions, with round-trip theorems and explicit word and
   length bounds.
3. **Canonical Folio Class Codes and Constant-Time Word RAM Decision Tree (`folioRepCode`,
   `prefixTrieProg`):**
   Maps any `F : FolioSetRep k δ` (with `k ≤ q + 3`) to a canonical integer code `folioRepCode q F`
   such that two folios have equal `folioRepCode` if and only if they contain the same rooted
   digraphs of detail `≤ δ` up to isomorphism, and constructs a constant-time Word RAM decision tree
   `prefixTrieProg` that reads the self-delimiting `encFolioSetRep F` prefix of an array and outputs
   `folioRepCode q F`.
4. **Explicit Rooted Digraph Bridge for $\tilde{A}$ (`tildeAMultiDigraph`,
   `isoTildeAMultiDigraph`, `isDeltaFolioModelling_of_parsedFolioAndModels`):**
   Constructs the `MultiDigraph` representation `G_A` of $\tilde{A}$ on vertex ordering
   `vList = π(A) ++ remVerts`, proves an explicit `GM13.RootedDigraph.Iso` between
   `G_A.toGMRootedDigraph Z_A` and `GM13.rootedDigraphOfList D (π(A)) hroots`, and connects
   `ParsedFolioAndModels G_A Z_A δ` and `folioRepCode` to `GM13.IsDeltaFolioModelling` and
   `GM13.Vision.HasSameMemberDeltaFolio`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph GraphMinor.Surface GraphMinor.GM09

/-! ### Section 1: Memory-Shifting Combinators for Word RAM Programs -/

/-- Shift every register reference in `e : Expr` by `R_off` and every array reference by `A_off`. -/
def Expr.shiftMem (R_off A_off : ℕ) : Expr → Expr
  | .const n => .const n
  | .reg r => .reg (R_off + r)
  | .read a idx => .read (A_off + a) (idx.shiftMem R_off A_off)
  | .readMin a idx cap =>
    .readMin (A_off + a) (idx.shiftMem R_off A_off) (cap.shiftMem R_off A_off)
  | .len a => .len (A_off + a)
  | .op bop e₁ e₂ => .op bop (e₁.shiftMem R_off A_off) (e₂.shiftMem R_off A_off)

/-- Shift every register reference in `c : Cmd` by `R_off` and every array reference by `A_off`. -/
def Cmd.shiftMem (R_off A_off : ℕ) : Cmd → Cmd
  | .skip => .skip
  | .assign r e => .assign (R_off + r) (e.shiftMem R_off A_off)
  | .write a idx val =>
    .write (A_off + a) (idx.shiftMem R_off A_off) (val.shiftMem R_off A_off)
  | .alloc a len => .alloc (A_off + a) (len.shiftMem R_off A_off)
  | .seq c₁ c₂ => .seq (c₁.shiftMem R_off A_off) (c₂.shiftMem R_off A_off)
  | .ite cond c₁ c₂ =>
    .ite (cond.shiftMem R_off A_off) (c₁.shiftMem R_off A_off) (c₂.shiftMem R_off A_off)
  | .while cond body =>
    .while (cond.shiftMem R_off A_off) (body.shiftMem R_off A_off)

/-- View of state `s` shifted down by register offset `R_off` and array offset `A_off`. -/
def State.shiftDown (R_off A_off : ℕ) (s : State) : State where
  regs r := s.regs (R_off + r)
  arrs a := s.arrs (A_off + a)

/-- Merge a local post-state `s₀'` at offset `(R_off, A_off)` back into base state `s`,
preserving all registers `< R_off` and all arrays `< A_off` from `s`. -/
def State.shiftUp (R_off A_off : ℕ) (s s₀' : State) : State where
  regs r := if r < R_off then s.regs r else s₀'.regs (r - R_off)
  arrs a := if a < A_off then s.arrs a else s₀'.arrs (a - A_off)

@[simp]
theorem State.regs_shiftDown (R_off A_off : ℕ) (s : State) (r : Reg) :
    (s.shiftDown R_off A_off).regs r = s.regs (R_off + r) := rfl

@[simp]
theorem State.arrs_shiftDown (R_off A_off : ℕ) (s : State) (a : Arr) :
    (s.shiftDown R_off A_off).arrs a = s.arrs (A_off + a) := rfl

@[simp]
theorem State.regs_shiftUp_lt (R_off A_off : ℕ) (s s₀' : State) {r : Reg} (hr : r < R_off) :
    (s.shiftUp R_off A_off s₀').regs r = s.regs r := by
  simp [State.shiftUp, hr]

@[simp]
theorem State.arrs_shiftUp_lt (R_off A_off : ℕ) (s s₀' : State) {a : Arr} (ha : a < A_off) :
    (s.shiftUp R_off A_off s₀').arrs a = s.arrs a := by
  simp [State.shiftUp, ha]

@[simp]
theorem State.regs_shiftUp_add (R_off A_off : ℕ) (s s₀' : State) (r : Reg) :
    (s.shiftUp R_off A_off s₀').regs (R_off + r) = s₀'.regs r := by
  have hnot : ¬ (R_off + r < R_off) := by omega
  simp [State.shiftUp, hnot]

@[simp]
theorem State.arrs_shiftUp_add (R_off A_off : ℕ) (s s₀' : State) (a : Arr) :
    (s.shiftUp R_off A_off s₀').arrs (A_off + a) = s₀'.arrs a := by
  have hnot : ¬ (A_off + a < A_off) := by omega
  simp [State.shiftUp, hnot]

@[simp]
theorem State.shiftDown_shiftUp (R_off A_off : ℕ) (s s₀' : State) :
    (s.shiftUp R_off A_off s₀').shiftDown R_off A_off = s₀' := by
  ext r a <;> simp

@[simp]
theorem State.shiftUp_shiftDown (R_off A_off : ℕ) (s : State) :
    s.shiftUp R_off A_off (s.shiftDown R_off A_off) = s := by
  refine State.ext (funext fun r => ?_) (funext fun a => ?_)
  · dsimp [State.shiftUp, State.shiftDown]
    split_ifs with hr
    · rfl
    · rw [Nat.add_sub_of_le (Nat.not_lt.mp hr)]
  · dsimp [State.shiftUp, State.shiftDown]
    split_ifs with ha
    · rfl
    · rw [Nat.add_sub_of_le (Nat.not_lt.mp ha)]

@[simp]
theorem State.shiftUp_shiftUp (R_off A_off : ℕ) (s s₁ s₂ : State) :
    (s.shiftUp R_off A_off s₁).shiftUp R_off A_off s₂ = s.shiftUp R_off A_off s₂ := by
  refine State.ext (funext fun r => ?_) (funext fun a => ?_)
  · dsimp [State.shiftUp]
    split_ifs <;> rfl
  · dsimp [State.shiftUp]
    split_ifs <;> rfl

theorem State.setReg_shiftUp (R_off A_off : ℕ) (s : State) (r : ℕ) (v : ℕ) :
    s.setReg (R_off + r) v =
      s.shiftUp R_off A_off ((s.shiftDown R_off A_off).setReg r v) := by
  refine State.ext (funext fun r' => ?_) (funext fun a' => ?_)
  · by_cases h1 : r' = R_off + r
    · subst h1
      have hnot : ¬ (R_off + r < R_off) := by omega
      simp [State.setReg, State.shiftUp, State.shiftDown, Function.update_apply, hnot]
    · by_cases h2 : r' < R_off
      · simp [State.setReg, State.shiftUp, State.shiftDown, Function.update_apply, h1, h2]
      · have hadd : R_off + (r' - R_off) = r' := Nat.add_sub_of_le (Nat.not_lt.mp h2)
        have h3 : r' - R_off ≠ r := fun h => h1 (by rw [← hadd, h])
        simp [State.setReg, State.shiftUp, State.shiftDown, Function.update_apply, h1, h2, h3, hadd]
  · dsimp [State.setReg, State.shiftUp, State.shiftDown]
    split_ifs with ha
    · rfl
    · rw [Nat.add_sub_of_le (Nat.not_lt.mp ha)]

theorem State.setArr_shiftUp (R_off A_off : ℕ) (s : State) (a : ℕ) (l : List ℕ) :
    s.setArr (A_off + a) l =
      s.shiftUp R_off A_off ((s.shiftDown R_off A_off).setArr a l) := by
  refine State.ext (funext fun r' => ?_) (funext fun a' => ?_)
  · dsimp [State.setArr, State.shiftUp, State.shiftDown]
    split_ifs with hr
    · rfl
    · rw [Nat.add_sub_of_le (Nat.not_lt.mp hr)]
  · by_cases h1 : a' = A_off + a
    · subst h1
      have hnot : ¬ (A_off + a < A_off) := by omega
      simp [State.setArr, State.shiftUp, State.shiftDown, Function.update_apply, hnot]
    · by_cases h2 : a' < A_off
      · simp [State.setArr, State.shiftUp, State.shiftDown, Function.update_apply, h1, h2]
      · have hadd : A_off + (a' - A_off) = a' := Nat.add_sub_of_le (Nat.not_lt.mp h2)
        have h3 : a' - A_off ≠ a := fun h => h1 (by rw [← hadd, h])
        simp [State.setArr, State.shiftUp, State.shiftDown, Function.update_apply, h1, h2, h3, hadd]

theorem State.writeArr_shiftUp (R_off A_off : ℕ) (s : State) (a : Arr) (i v : ℕ) :
    s.writeArr (A_off + a) i v =
      s.shiftUp R_off A_off ((s.shiftDown R_off A_off).writeArr a i v) := by
  unfold State.writeArr
  rw [State.setArr_shiftUp]
  rfl

@[simp]
theorem Expr.cost_shiftMem (R_off A_off : ℕ) (e : Expr) :
    (e.shiftMem R_off A_off).cost = e.cost := by
  induction e <;> simp [Expr.shiftMem, Expr.cost, *]

@[simp]
theorem Expr.eval_shiftMem (w R_off A_off : ℕ) (s : State) (e : Expr) :
    (e.shiftMem R_off A_off).eval w s = e.eval w (s.shiftDown R_off A_off) := by
  induction e with
  | const n => rfl
  | reg r => rfl
  | read a idx ih =>
    unfold Expr.shiftMem Expr.eval
    rw [ih]
    rfl
  | readMin a idx cap ih₁ ih₂ =>
    unfold Expr.shiftMem Expr.eval
    rw [ih₁, ih₂]
    rfl
  | len a => rfl
  | op bop e₁ e₂ ih₁ ih₂ =>
    unfold Expr.shiftMem Expr.eval
    rw [ih₁, ih₂]

/-- Auxiliary lifting theorem for `Cmd.shiftMem` along `State.shiftDown` and `State.shiftUp`. -/
theorem Exec.shiftMem_aux {w R_off A_off : ℕ} {c : Cmd} {s₀ s₀' : State} {t : ℕ}
    (h : Exec w c s₀ s₀' t) :
    ∀ {s : State}, s.shiftDown R_off A_off = s₀ →
      Exec w (c.shiftMem R_off A_off) s (s.shiftUp R_off A_off s₀') t := by
  induction h with
  | skip s₀ =>
    intro s hs
    subst hs
    rw [State.shiftUp_shiftDown]
    exact .skip s
  | @assign r e s₀ v he =>
    intro s hs
    subst hs
    rw [← State.setReg_shiftUp, ← Expr.cost_shiftMem R_off A_off e]
    exact .assign (by rw [Expr.eval_shiftMem]; exact he)
  | @write a idx val s₀ i v hi hv hbound =>
    intro s hs
    subst hs
    rw [← State.writeArr_shiftUp, ← Expr.cost_shiftMem R_off A_off idx,
      ← Expr.cost_shiftMem R_off A_off val]
    exact .write (by rw [Expr.eval_shiftMem]; exact hi)
      (by rw [Expr.eval_shiftMem]; exact hv) hbound
  | @alloc a len s₀ m hm =>
    intro s hs
    subst hs
    rw [← State.setArr_shiftUp, ← Expr.cost_shiftMem R_off A_off len]
    exact .alloc (by rw [Expr.eval_shiftMem]; exact hm)
  | seq h₁ h₂ ih₁ ih₂ =>
    intro s hs
    have hex₁ := ih₁ hs
    have hex₂ := ih₂ (State.shiftDown_shiftUp R_off A_off s _)
    rw [State.shiftUp_shiftUp] at hex₂
    exact .seq hex₁ hex₂
  | ite_true hcond hv h₁ ih =>
    intro s hs
    subst hs
    rw [← Expr.cost_shiftMem R_off A_off _]
    refine .ite_true ?_ hv (ih rfl)
    rw [Expr.eval_shiftMem]
    exact hcond
  | ite_false hcond h₂ ih =>
    intro s hs
    subst hs
    rw [← Expr.cost_shiftMem R_off A_off _]
    refine .ite_false ?_ (ih rfl)
    rw [Expr.eval_shiftMem]
    exact hcond
  | while_false hcond =>
    intro s hs
    subst hs
    rw [State.shiftUp_shiftDown, ← Expr.cost_shiftMem R_off A_off _]
    refine .while_false ?_
    rw [Expr.eval_shiftMem]
    exact hcond
  | while_true hcond hv hbody hrest ih_body ih_rest =>
    intro s hs
    have hex_body := ih_body hs
    have hex_rest := ih_rest (State.shiftDown_shiftUp R_off A_off s _)
    rw [State.shiftUp_shiftUp] at hex_rest
    rw [← Expr.cost_shiftMem R_off A_off _]
    refine .while_true ?_ hv hex_body hex_rest
    rw [Expr.eval_shiftMem, hs]
    exact hcond

/-- Any execution `Exec w c (s.shiftDown R_off A_off) s₀' t` lifts to an execution of
`c.shiftMem R_off A_off` from `s` to `s.shiftUp R_off A_off s₀'` in the same number of steps `t`,
preserving all registers `< R_off` and all arrays `< A_off`. -/
theorem Exec.shiftMem {w R_off A_off : ℕ} {c : Cmd} {s s₀' : State} {t : ℕ}
    (h : Exec w c (s.shiftDown R_off A_off) s₀' t) :
    Exec w (c.shiftMem R_off A_off) s (s.shiftUp R_off A_off s₀') t :=
  h.shiftMem_aux rfl

/-! ### Section 2: Pure Reading Decoders for `FolioSetRep`, `RootedDigraphModel`, and (4.1) Output -/

/-- Serialize a list of word lists by prefixing each list with its length:
`lists.flatMap (fun l => l.length :: l)`. -/
def encLengthPrefixedLists (lists : List (List ℕ)) : List ℕ :=
  lists.flatMap (fun l => l.length :: l)

/-- Pure reading parser for `k` length-prefixed word lists from a flat word stream `words`. -/
def parseLengthPrefixedLists : ℕ → List ℕ → Option (List (List ℕ) × List ℕ)
  | 0, words => some ([], words)
  | _ + 1, [] => none
  | k + 1, len :: rest =>
    if rest.length < len then
      none
    else
      match parseLengthPrefixedLists k (rest.drop len) with
      | some (tailLists, rem) => some (rest.take len :: tailLists, rem)
      | none => none

@[simp]
theorem parseLengthPrefixedLists_encLengthPrefixedLists (lists : List (List ℕ)) (rem : List ℕ) :
    parseLengthPrefixedLists lists.length (encLengthPrefixedLists lists ++ rem) =
      some (lists, rem) := by
  induction lists with
  | nil => rfl
  | cons l ls ih =>
    have henc : encLengthPrefixedLists (l :: ls) ++ rem =
        l.length :: (l ++ (encLengthPrefixedLists ls ++ rem)) := by
      simp [encLengthPrefixedLists, List.append_assoc]
    rw [henc, List.length_cons, parseLengthPrefixedLists]
    have hnot : ¬ ((l ++ (encLengthPrefixedLists ls ++ rem)).length < l.length) := by
      simp
    simp only [hnot, ↓reduceIte, List.take_left, List.drop_left, ih]

theorem eq_encLengthPrefixedLists_of_parseLengthPrefixedLists :
    ∀ {k : ℕ} {words : List ℕ} {lists : List (List ℕ)} {rem : List ℕ},
      parseLengthPrefixedLists k words = some (lists, rem) →
      lists.length = k ∧ words = encLengthPrefixedLists lists ++ rem
  | 0, words, lists, rem, h => by
    simp only [parseLengthPrefixedLists, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  | k + 1, [], _, _, h => by nomatch h
  | k + 1, len :: rest, lists, rem, h => by
    unfold parseLengthPrefixedLists at h
    split_ifs at h with hlt
    cases hrec : parseLengthPrefixedLists k (rest.drop len) with
    | none => rw [hrec] at h; nomatch h
    | some pair =>
      rcases pair with ⟨tailLists, rem'⟩
      rw [hrec] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rcases eq_encLengthPrefixedLists_of_parseLengthPrefixedLists hrec with ⟨hlen, heq⟩
      have htake_len : (rest.take len).length = len := List.length_take_of_le (by omega)
      refine ⟨by simp [hlen], ?_⟩
      have hcons : encLengthPrefixedLists (rest.take len :: tailLists) ++ rem' =
          len :: (rest.take len ++ (encLengthPrefixedLists tailLists ++ rem')) := by
        simp [encLengthPrefixedLists, htake_len, List.append_assoc]
      rw [hcons, ← heq, List.take_append_drop]

/-- No proper prefix of `encLengthPrefixedLists lists` can be parsed by `parseLengthPrefixedLists
lists.length`. -/
theorem parseLengthPrefixedLists_take_lt (lists : List (List ℕ)) {m : ℕ}
    (hm : m < (encLengthPrefixedLists lists).length) :
    parseLengthPrefixedLists lists.length ((encLengthPrefixedLists lists).take m) = none := by
  cases h : parseLengthPrefixedLists lists.length ((encLengthPrefixedLists lists).take m) with
  | none => rfl
  | some pair =>
    rcases pair with ⟨lists', rem⟩
    have hfull := parseLengthPrefixedLists_encLengthPrefixedLists lists []
    rw [List.append_nil] at hfull
    rcases eq_encLengthPrefixedLists_of_parseLengthPrefixedLists h with ⟨_, heq⟩
    have htake :
        ((encLengthPrefixedLists lists).take m).take
          (encLengthPrefixedLists lists').length = encLengthPrefixedLists lists' := by
      rw [heq, List.take_left]
    have hlen_le : (encLengthPrefixedLists lists').length ≤ m := by
      have h1 := congrArg List.length heq
      rw [List.length_take, List.length_append] at h1
      omega
    have hpref :
        (encLengthPrefixedLists lists).take (encLengthPrefixedLists lists').length =
          encLengthPrefixedLists lists' := by
      have hmin :
          Nat.min (encLengthPrefixedLists lists').length m =
            (encLengthPrefixedLists lists').length := Nat.min_eq_left hlen_le
      rw [← hmin, ← List.take_take, htake]
    let tailDrop := (encLengthPrefixedLists lists).drop (encLengthPrefixedLists lists').length
    have hdrop :
        encLengthPrefixedLists lists = encLengthPrefixedLists lists' ++ tailDrop := by
      have htd := (List.take_append_drop (encLengthPrefixedLists lists').length
        (encLengthPrefixedLists lists)).symm
      rwa [hpref] at htd
    have hlen'_eq : lists'.length = lists.length :=
      (eq_encLengthPrefixedLists_of_parseLengthPrefixedLists h).1
    have hparse2 :
        parseLengthPrefixedLists lists.length (encLengthPrefixedLists lists) =
          some (lists', tailDrop) := by
      rw [hdrop, ← hlen'_eq]
      exact parseLengthPrefixedLists_encLengthPrefixedLists lists' tailDrop
    rw [hfull] at hparse2
    simp only [Option.some.injEq, Prod.mk.injEq] at hparse2
    rcases hparse2 with ⟨rfl, _⟩
    omega

/-- Pure reading parser for `encFolioSetRep F` (`FolioTable.lean`). -/
def parseFolioSetRep (k δ : ℕ) (words : List ℕ) : Option (FolioSetRep k δ × List ℕ) :=
  match words with
  | [] => none
  | numCodes :: rest =>
    match parseLengthPrefixedLists numCodes rest with
    | none => none
    | some (codes, rem) =>
      if h : (∀ c ∈ codes, IsDetailLeCode k δ c) ∧
          codes.Pairwise (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode k c₁ c₂) then
        some (⟨codes, h.1, h.2⟩, rem)
      else
        none

@[simp]
theorem parseFolioSetRep_encFolioSetRep {k δ : ℕ} (F : FolioSetRep k δ) (rem : List ℕ) :
    parseFolioSetRep k δ (encFolioSetRep F ++ rem) = some (F, rem) := by
  have henc : encFolioSetRep F ++ rem =
      F.codes.length :: (encLengthPrefixedLists F.codes ++ rem) := by
    rfl
  rw [henc]
  unfold parseFolioSetRep
  dsimp only
  rw [parseLengthPrefixedLists_encLengthPrefixedLists]
  dsimp only
  have hcond : (∀ c ∈ F.codes, IsDetailLeCode k δ c) ∧
      F.codes.Pairwise (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode k c₁ c₂) :=
    ⟨F.all_detail, F.pairwise_nonIso⟩
  split_ifs
  rcases F with ⟨_, _, _⟩
  rfl

theorem eq_encFolioSetRep_of_parseFolioSetRep {k δ : ℕ} {words : List ℕ}
    {F : FolioSetRep k δ} {rem : List ℕ}
    (h : parseFolioSetRep k δ words = some (F, rem)) :
    words = encFolioSetRep F ++ rem := by
  unfold parseFolioSetRep at h
  cases words with
  | nil => nomatch h
  | cons numCodes rest =>
    cases hpl : parseLengthPrefixedLists numCodes rest with
    | none => simp [hpl] at h
    | some pair =>
      rcases pair with ⟨codes, rem'⟩
      simp only [hpl] at h
      split_ifs at h with hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rcases eq_encLengthPrefixedLists_of_parseLengthPrefixedLists hpl with ⟨rfl, rfl⟩
      rfl

/-- Decode the `i`-th representative `k`-rooted digraph from `F : FolioSetRep k δ`. -/
def FolioSetRep.decodeCodeAt {k δ : ℕ} (F : FolioSetRep k δ) (i : Fin F.codes.length) :
    ComputeRootedDigraph k :=
  have hc : IsDetailLeCode k δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  match h : decRootedDigraph k (F.codes[i.1]'i.2) with
  | some H => H
  | none => False.elim (by unfold IsDetailLeCode at hc; rw [h] at hc; exact hc)

@[simp]
theorem FolioSetRep.encRootedDigraph_decodeCodeAt {k δ : ℕ} (F : FolioSetRep k δ)
    (i : Fin F.codes.length) :
    encRootedDigraph (F.decodeCodeAt i) = F.codes[i.1]'i.2 := by
  have hc : IsDetailLeCode k δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  unfold FolioSetRep.decodeCodeAt
  split
  next H h =>
    unfold IsDetailLeCode at hc
    rw [h] at hc
    exact hc.1.symm
  next h =>
    unfold IsDetailLeCode at hc
    rw [h] at hc
    exact False.elim hc

theorem FolioSetRep.hasDetailLe_decodeCodeAt {k δ : ℕ} (F : FolioSetRep k δ)
    (i : Fin F.codes.length) :
    (F.decodeCodeAt i).HasDetailLe δ := by
  have hc : IsDetailLeCode k δ (F.codes[i.1]'i.2) := F.all_detail _ (List.getElem_mem _)
  unfold FolioSetRep.decodeCodeAt
  split
  next H h =>
    unfold IsDetailLeCode at hc
    rw [h] at hc
    exact hc.2
  next h =>
    unfold IsDetailLeCode at hc
    rw [h] at hc
    exact False.elim hc

theorem FolioSetRep.decodeCodeAt_eq_of_eq_encRootedDigraph {k δ : ℕ} (F : FolioSetRep k δ)
    (i : Fin F.codes.length) (H : ComputeRootedDigraph k)
    (heq : F.codes[i.1]'i.2 = encRootedDigraph H) :
    F.decodeCodeAt i = H := by
  unfold FolioSetRep.decodeCodeAt
  split
  next H' h =>
    rw [heq, decRootedDigraph_encRootedDigraph] at h
    exact Option.some.inj h.symm
  next h =>
    rw [heq, decRootedDigraph_encRootedDigraph] at h
    nomatch h

/-- Construct a `Finset (Fin m)` from a list of natural numbers `l : List ℕ`. -/
def finsetFinOfNatList (m : ℕ) (l : List ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun x : Fin m => x.1 ∈ l)

@[simp]
theorem mem_finsetFinOfNatList (m : ℕ) (l : List ℕ) (x : Fin m) :
    x ∈ finsetFinOfNatList m l ↔ x.1 ∈ l := by
  simp [finsetFinOfNatList]

@[simp]
theorem finsetFinOfNatList_finsetToList {m : ℕ} (S : Finset (Fin m)) :
    finsetFinOfNatList m (finsetToList S) = S := by
  ext x
  simp [mem_finsetToList_iff, ← Fin.ext_iff]

@[simp]
theorem finsetToList_finsetFinOfNatList {m : ℕ} {l : List ℕ}
    (hpw : l.Pairwise (· < ·)) (hlt : ∀ x ∈ l, x < m) :
    finsetToList (finsetFinOfNatList m l) = l := by
  have hnd₁ : (finsetToList (finsetFinOfNatList m l)).Nodup :=
    nodup_finsetToList _
  have hnd₂ : l.Nodup := hpw.imp ne_of_lt
  have hpw₁ : (finsetToList (finsetFinOfNatList m l)).Pairwise (· < ·) := by
    unfold finsetToList
    exact List.pairwise_map.mpr (pairwise_lt_sortedFinsetList _)
  have hperm : List.Perm (finsetToList (finsetFinOfNatList m l)) l := by
    rw [List.perm_ext_iff_of_nodup hnd₁ hnd₂]
    intro x
    rw [mem_finsetToList_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (mem_finsetFinOfNatList m l u).mp hu
    · intro hx
      exact ⟨⟨x, hlt x hx⟩, (mem_finsetFinOfNatList m l ⟨x, hlt x hx⟩).mpr hx, rfl⟩
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (lt_asymm h1 h2)) hpw₁ hpw

/-- Complete word-list encoding of a `RootedDigraphModel H G`:
first the `H.digraph.numEdges` mapped edge indices `(M.edgeMap e).1`, followed by `2 * H.digraph.numVerts`
length-prefixed lists `[vList_0, eList_0, ..., vList_{v_H - 1}, eList_{v_H - 1}]` giving the
sorted vertex and edge finsets of each branch set `M.vertMap u`. -/
def encModelFull {k : ℕ} {H G : ComputeRootedDigraph k} (M : RootedDigraphModel H G) : List ℕ :=
  List.ofFn (fun e : Fin H.digraph.numEdges => (M.edgeMap e).1) ++
    encLengthPrefixedLists
      ((List.finRange H.digraph.numVerts).flatMap (fun u =>
        [finsetToList (M.vertMap u).verts, finsetToList (M.vertMap u).edges]))

/-- Pure reading parser for `encModelFull M`. -/
def parseModelFull {k : ℕ} (H G : ComputeRootedDigraph k) (words : List ℕ) :
    Option (RootedDigraphModel H G × List ℕ) :=
  let m_H := H.digraph.numEdges
  let v_H := H.digraph.numVerts
  if words.length < m_H then
    none
  else
    let edgeWords := words.take m_H
    let rest₁ := words.drop m_H
    match parseLengthPrefixedLists (2 * v_H) rest₁ with
    | none => none
    | some (veLists, rem) =>
      if hvalid :
          (∀ e : Fin m_H, edgeWords.getD e.1 0 < G.digraph.numEdges) ∧
          (∀ u : Fin v_H,
            let vL := veLists.getD (2 * u.1) []
            let eL := veLists.getD (2 * u.1 + 1) []
            vL.Pairwise (· < ·) ∧ (∀ x ∈ vL, x < G.digraph.numVerts) ∧
            eL.Pairwise (· < ·) ∧ (∀ e ∈ eL, e < G.digraph.numEdges) ∧
            (∀ ⦃e : Fin G.digraph.numEdges⦄,
              e ∈ finsetFinOfNatList G.digraph.numEdges eL →
                G.digraph.head e ∈ finsetFinOfNatList G.digraph.numVerts vL ∧
                G.digraph.tail e ∈ finsetFinOfNatList G.digraph.numVerts vL)) then
        let vertMap : Fin v_H → DigraphSubgraph G.digraph := fun u =>
          let vL := veLists.getD (2 * u.1) []
          let eL := veLists.getD (2 * u.1 + 1) []
          { verts := finsetFinOfNatList G.digraph.numVerts vL
            edges := finsetFinOfNatList G.digraph.numEdges eL
            head_mem := fun _ he => ((hvalid.2 u).2.2.2.2 he).1
            tail_mem := fun _ he => ((hvalid.2 u).2.2.2.2 he).2 }
        let edgeMap : Fin m_H → Fin G.digraph.numEdges := fun e =>
          ⟨edgeWords.getD e.1 0, hvalid.1 e⟩
        if hmodel :
            (∀ v : Fin v_H, (vertMap v).IsNonNullConnected) ∧
            (∀ u v : Fin v_H, u ≠ v → Disjoint (vertMap u).verts (vertMap v).verts) ∧
            Function.Injective edgeMap ∧
            (∀ (v : Fin v_H) (e : Fin m_H), edgeMap e ∉ (vertMap v).edges) ∧
            (∀ e : Fin m_H, G.digraph.head (edgeMap e) ∈ (vertMap (H.digraph.head e)).verts) ∧
            (∀ e : Fin m_H, G.digraph.tail (edgeMap e) ∈ (vertMap (H.digraph.tail e)).verts) ∧
            (∀ i : Fin k, G.roots i ∈ (vertMap (H.roots i)).verts) then
          some ({
            vertMap := vertMap
            edgeMap := edgeMap
            connected := hmodel.1
            vert_disjoint := hmodel.2.1
            edge_injective := hmodel.2.2.1
            edge_notMem_vert := hmodel.2.2.2.1
            head_mem_vertMap := hmodel.2.2.2.2.1
            tail_mem_vertMap := hmodel.2.2.2.2.2.1
            root_mem_vertMap := hmodel.2.2.2.2.2.2
          }, rem)
        else
          none
      else
        none

private theorem getD_flatMap_pair {α β : Type*} (l : List α) (f g : α → β) (d : β)
    (i : ℕ) (hi : i < l.length) :
    (l.flatMap (fun x => [f x, g x])).getD (2 * i) d = f (l[i]'hi) ∧
    (l.flatMap (fun x => [f x, g x])).getD (2 * i + 1) d = g (l[i]'hi) := by
  induction l generalizing i with
  | nil => nomatch hi
  | cons a tl ih =>
    cases i with
    | zero => simp
    | succ j =>
      have hj : j < tl.length := by simpa using hi
      have h1 : 2 * (j + 1) = (2 * j) + 1 + 1 := by omega
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, h1,
        List.getD_cons_succ, List.getElem_cons_succ]
      exact ih j hj

private theorem digraphSubgraph_ext {D : ComputeDigraph} (S₁ S₂ : DigraphSubgraph D)
    (hv : S₁.verts = S₂.verts) (he : S₁.edges = S₂.edges) : S₁ = S₂ := by
  rcases S₁ with ⟨_, _, _, _⟩
  rcases S₂ with ⟨_, _, _, _⟩
  dsimp only at hv he
  subst hv he
  rfl

private theorem rootedDigraphModel_ext {k : ℕ} {H G : ComputeRootedDigraph k}
    (M₁ M₂ : RootedDigraphModel H G)
    (hv : ∀ u, (M₁.vertMap u).verts = (M₂.vertMap u).verts ∧
      (M₁.vertMap u).edges = (M₂.vertMap u).edges)
    (he : ∀ e, (M₁.edgeMap e).1 = (M₂.edgeMap e).1) :
    M₁ = M₂ := by
  have hvm : M₁.vertMap = M₂.vertMap :=
    funext fun u => digraphSubgraph_ext _ _ (hv u).1 (hv u).2
  have hem : M₁.edgeMap = M₂.edgeMap :=
    funext fun e => Fin.ext (he e)
  rcases M₁ with ⟨⟨_, _, _, _, _, _, _, _⟩, _⟩
  rcases M₂ with ⟨⟨_, _, _, _, _, _, _, _⟩, _⟩
  dsimp only at hvm hem
  subst hvm hem
  rfl

@[simp]
theorem parseModelFull_encModelFull {k : ℕ} {H G : ComputeRootedDigraph k}
    (M : RootedDigraphModel H G) (rem : List ℕ) :
    parseModelFull H G (encModelFull M ++ rem) = some (M, rem) := by
  let m_H := H.digraph.numEdges
  let v_H := H.digraph.numVerts
  let veLists := (List.finRange v_H).flatMap (fun u =>
    [finsetToList (M.vertMap u).verts, finsetToList (M.vertMap u).edges])
  have hve_len : veLists.length = 2 * v_H := by
    dsimp [veLists]
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, Nat.mul_comm]
  have hve_pair : ∀ u : Fin v_H,
      veLists.getD (2 * u.1) [] = finsetToList (M.vertMap u).verts ∧
      veLists.getD (2 * u.1 + 1) [] = finsetToList (M.vertMap u).edges := by
    intro u
    have h := getD_flatMap_pair (List.finRange v_H)
      (fun x => finsetToList (M.vertMap x).verts)
      (fun x => finsetToList (M.vertMap x).edges) [] u.1 (by simp [u.2])
    simpa using h
  have hverts_eq : ∀ u : Fin v_H,
      finsetFinOfNatList G.digraph.numVerts (veLists.getD (2 * u.1) []) = (M.vertMap u).verts := by
    intro u
    rw [(hve_pair u).1, finsetFinOfNatList_finsetToList]
  have hedges_eq : ∀ u : Fin v_H,
      finsetFinOfNatList G.digraph.numEdges (veLists.getD (2 * u.1 + 1) []) = (M.vertMap u).edges := by
    intro u
    rw [(hve_pair u).2, finsetFinOfNatList_finsetToList]
  have hedge_val : ∀ e : Fin m_H,
      (List.ofFn (fun e' : Fin m_H => (M.edgeMap e').1)).getD e.1 0 = (M.edgeMap e).1 := by
    intro e
    rw [List.getD_eq_getElem _ _ (by simp [e.2]), List.getElem_ofFn]
  have henc : encModelFull M ++ rem =
      List.ofFn (fun e : Fin m_H => (M.edgeMap e).1) ++
        (encLengthPrefixedLists veLists ++ rem) := by
    simp [encModelFull, veLists, m_H, v_H, List.append_assoc]
  rw [henc]
  unfold parseModelFull
  have hnot_lt : ¬ ((List.ofFn (fun e : Fin m_H => (M.edgeMap e).1) ++
      (encLengthPrefixedLists veLists ++ rem)).length < m_H) := by
    simp [m_H]
  simp only [m_H, hnot_lt, ↓reduceIte, List.take_left', List.length_ofFn, List.drop_left']
  rw [← hve_len, parseLengthPrefixedLists_encLengthPrefixedLists]
  dsimp only
  have hvalid :
      (∀ e : Fin H.digraph.numEdges,
        (List.ofFn (fun e' : Fin H.digraph.numEdges => (M.edgeMap e').1)).getD e.1 0 < G.digraph.numEdges) ∧
      (∀ u : Fin H.digraph.numVerts,
        (veLists.getD (2 * u.1) []).Pairwise (· < ·) ∧
        (∀ x ∈ veLists.getD (2 * u.1) [], x < G.digraph.numVerts) ∧
        (veLists.getD (2 * u.1 + 1) []).Pairwise (· < ·) ∧
        (∀ e ∈ veLists.getD (2 * u.1 + 1) [], e < G.digraph.numEdges) ∧
        (∀ ⦃e : Fin G.digraph.numEdges⦄,
          e ∈ finsetFinOfNatList G.digraph.numEdges (veLists.getD (2 * u.1 + 1) []) →
            G.digraph.head e ∈ finsetFinOfNatList G.digraph.numVerts (veLists.getD (2 * u.1) []) ∧
            G.digraph.tail e ∈ finsetFinOfNatList G.digraph.numVerts (veLists.getD (2 * u.1) []))) := by
    refine ⟨fun e => by rw [hedge_val e]; exact (M.edgeMap e).2, fun u => ?_⟩
    rw [(hve_pair u).1, (hve_pair u).2]
    refine ⟨List.pairwise_map.mpr (pairwise_lt_sortedFinsetList _),
      fun x hx => by
        rw [mem_finsetToList_iff] at hx
        rcases hx with ⟨w, _, rfl⟩
        exact w.2,
      List.pairwise_map.mpr (pairwise_lt_sortedFinsetList _),
      fun e he => by
        rw [mem_finsetToList_iff] at he
        rcases he with ⟨f, _, rfl⟩
        exact f.2,
      fun e he => ?_⟩
    rw [finsetFinOfNatList_finsetToList] at he ⊢
    exact ⟨M.vertMap u |>.head_mem he, M.vertMap u |>.tail_mem he⟩
  split_ifs with h2
  · congr 1
    congr 1
    exact rootedDigraphModel_ext _ M (fun u => ⟨hverts_eq u, hedges_eq u⟩) hedge_val
  · exfalso
    apply h2
    refine ⟨fun v => ?_, fun u v huv => ?_, ?_, fun v e => ?_, fun e => ?_, fun e => ?_, fun i => ?_⟩
    · have hv_eq :
          ({ verts := finsetFinOfNatList G.digraph.numVerts (veLists.getD (2 * v.1) [])
             edges := finsetFinOfNatList G.digraph.numEdges (veLists.getD (2 * v.1 + 1) [])
             head_mem := fun _ he => ((hvalid.2 v).2.2.2.2 he).1
             tail_mem := fun _ he => ((hvalid.2 v).2.2.2.2 he).2 } : DigraphSubgraph G.digraph) =
          M.vertMap v :=
        digraphSubgraph_ext _ (M.vertMap v) (hverts_eq v) (hedges_eq v)
      rw [hv_eq]
      exact M.connected v
    · rw [hverts_eq u, hverts_eq v]
      exact M.vert_disjoint u v huv
    · intro e₁ e₂ heq
      have hval := congrArg Fin.val heq
      dsimp only at hval
      rw [hedge_val e₁, hedge_val e₂] at hval
      exact M.edge_injective (Fin.ext hval)
    · rw [hedges_eq v]
      have he_eq : (⟨(List.ofFn (fun e' : Fin m_H => (M.edgeMap e').1)).getD e.1 0, hvalid.1 e⟩ :
          Fin G.digraph.numEdges) = M.edgeMap e := Fin.ext (hedge_val e)
      rw [he_eq]
      exact M.edge_notMem_vert v e
    · rw [hverts_eq (H.digraph.head e)]
      have he_eq : (⟨(List.ofFn (fun e' : Fin m_H => (M.edgeMap e').1)).getD e.1 0, hvalid.1 e⟩ :
          Fin G.digraph.numEdges) = M.edgeMap e := Fin.ext (hedge_val e)
      rw [he_eq]
      exact M.head_mem_vertMap e
    · rw [hverts_eq (H.digraph.tail e)]
      have he_eq : (⟨(List.ofFn (fun e' : Fin m_H => (M.edgeMap e').1)).getD e.1 0, hvalid.1 e⟩ :
          Fin G.digraph.numEdges) = M.edgeMap e := Fin.ext (hedge_val e)
      rw [he_eq]
      exact M.tail_mem_vertMap e
    · rw [hverts_eq (H.roots i)]
      exact M.root_mem_vertMap i

/-- Serialize a sequence of models for a list of rooted digraphs `Hs : List (ComputeRootedDigraph k)`. -/
def encModelList {k : ℕ} {G : ComputeRootedDigraph k} :
    ∀ (Hs : List (ComputeRootedDigraph k)), (∀ i : Fin Hs.length, RootedDigraphModel (Hs[i.1]'i.2) G) →
      List ℕ
  | [], _ => []
  | H :: Hs, models =>
    encModelFull (models ⟨0, by simp⟩) ++
      encModelList Hs (fun i => models ⟨i.1 + 1, by simp [i.2]⟩)

/-- Parse a sequence of models for a list of rooted digraphs `Hs : List (ComputeRootedDigraph k)`. -/
def parseModelList {k : ℕ} (G : ComputeRootedDigraph k) :
    ∀ (Hs : List (ComputeRootedDigraph k)), List ℕ →
      Option ((∀ i : Fin Hs.length, RootedDigraphModel (Hs[i.1]'i.2) G) × List ℕ)
  | [], words => some ((fun i => nomatch i), words)
  | H :: Hs, words =>
    match parseModelFull H G words with
    | none => none
    | some (M₀, rest) =>
      match parseModelList G Hs rest with
      | none => none
      | some (tailModels, rem) =>
        some ((fun i =>
          match i with
          | ⟨0, _⟩ => M₀
          | ⟨j + 1, hj⟩ => tailModels ⟨j, Nat.lt_of_succ_lt_succ hj⟩), rem)

@[simp]
theorem parseModelList_encModelList {k : ℕ} {G : ComputeRootedDigraph k}
    (Hs : List (ComputeRootedDigraph k))
    (models : ∀ i : Fin Hs.length, RootedDigraphModel (Hs[i.1]'i.2) G)
    (rem : List ℕ) :
    parseModelList G Hs (encModelList Hs models ++ rem) = some (models, rem) := by
  induction Hs with
  | nil =>
    simp only [encModelList, List.nil_append, parseModelList, Option.some.injEq, Prod.mk.injEq,
      and_true]
    funext i
    nomatch i
  | cons H Hs ih =>
    simp only [encModelList, List.append_assoc, parseModelList, parseModelFull_encModelFull,
      ih, Option.some.injEq, Prod.mk.injEq, and_true]
    funext ⟨j, hj⟩
    cases j <;> rfl

/-- Decoded output of Algorithm (4.1) on `(G, Z)` with detail `δ`:
a `FolioSetRep Z.card δ` together with a concrete `RootedDigraphModel` for each of its decoded
representative codes. -/
structure ParsedFolioAndModels {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (δ : ℕ) where
  /-- The `δ`-folio representation `F : FolioSetRep Z.card δ`. -/
  folio : FolioSetRep Z.card δ
  /-- Concrete model in `rootedDigraphOfZ G Z` for each representative `folio.decodeCodeAt i`. -/
  models : ∀ i : Fin folio.codes.length,
    RootedDigraphModel (folio.decodeCodeAt i) (rootedDigraphOfZ G Z)

/-- The list of decoded `ComputeRootedDigraph k` representatives of `F : FolioSetRep k δ`. -/
def FolioSetRep.decodedList {k δ : ℕ} (F : FolioSetRep k δ) : List (ComputeRootedDigraph k) :=
  List.ofFn F.decodeCodeAt

@[simp]
theorem FolioSetRep.length_decodedList {k δ : ℕ} (F : FolioSetRep k δ) :
    F.decodedList.length = F.codes.length := by
  simp [FolioSetRep.decodedList]

@[simp]
theorem FolioSetRep.getElem_decodedList {k δ : ℕ} (F : FolioSetRep k δ)
    (i : ℕ) (hi : i < F.decodedList.length) :
    F.decodedList[i]'hi = F.decodeCodeAt ⟨i, by simpa using hi⟩ := by
  simp [FolioSetRep.decodedList]

/-- Flat word-list serialization of `out : ParsedFolioAndModels G Z δ`:
`encFolioSetRep out.folio` followed by the serialized models `encModelList` for
`out.folio.decodedList`. -/
def encFolioAndModels {n : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)} {δ : ℕ}
    (out : ParsedFolioAndModels G Z δ) : List ℕ :=
  encFolioSetRep out.folio ++
    encModelList out.folio.decodedList
      (fun i => out.folio.getElem_decodedList i.1 i.2 ▸
        out.models ⟨i.1, by simpa using i.2⟩)

/-- Pure reading parser for `encFolioAndModels out` from a flat word stream `words`. -/
def parseFolioAndModels {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (δ : ℕ)
    (words : List ℕ) : Option (ParsedFolioAndModels G Z δ × List ℕ) :=
  match parseFolioSetRep Z.card δ words with
  | none => none
  | some (F, rest) =>
    match parseModelList (rootedDigraphOfZ G Z) F.decodedList rest with
    | none => none
    | some (rawModels, rem) =>
      some ({
        folio := F
        models := fun i =>
          have hi : i.1 < F.decodedList.length := by simp [i.2]
          F.getElem_decodedList i.1 hi ▸ rawModels ⟨i.1, hi⟩
      }, rem)

/-- Full-stream parser for `ParsedFolioAndModels G Z δ`. -/
def parseFolioAndModelsFull {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (δ : ℕ)
    (words : List ℕ) : Option (ParsedFolioAndModels G Z δ) :=
  match parseFolioAndModels G Z δ words with
  | some (out, []) => some out
  | _ => none

@[simp]
theorem parseFolioAndModels_encFolioAndModels {n : ℕ} {G : MultiDigraph n}
    {Z : Finset (Fin n)} {δ : ℕ} (out : ParsedFolioAndModels G Z δ) (rem : List ℕ) :
    parseFolioAndModels G Z δ (encFolioAndModels out ++ rem) = some (out, rem) := by
  unfold encFolioAndModels parseFolioAndModels
  rw [List.append_assoc]
  simp only [parseFolioSetRep_encFolioSetRep, parseModelList_encModelList,
    Option.some.injEq, Prod.mk.injEq, and_true]
  rcases out with ⟨F, models⟩
  congr 1
  funext i
  have hcast :
      ∀ {α : Type} {x y : α} (h : x = y) (P : α → Type) (v : P y),
        h ▸ (h.symm ▸ v : P x) = v := by
    intro _ _ _ h _ v
    subst h
    rfl
  exact hcast (F.getElem_decodedList i.1 (by simp [i.2]))
    (fun H => RootedDigraphModel H (rootedDigraphOfZ G Z)) (models i)

@[simp]
theorem parseFolioAndModelsFull_encFolioAndModels {n : ℕ} {G : MultiDigraph n}
    {Z : Finset (Fin n)} {δ : ℕ} (out : ParsedFolioAndModels G Z δ) :
    parseFolioAndModelsFull G Z δ (encFolioAndModels out) = some out := by
  unfold parseFolioAndModelsFull
  have h := parseFolioAndModels_encFolioAndModels out []
  rw [List.append_nil] at h
  rw [h]

theorem parseFolioSetRep_of_parseFolioAndModelsFull {n : ℕ} {G : MultiDigraph n}
    {Z : Finset (Fin n)} {δ : ℕ} {words : List ℕ} {out : ParsedFolioAndModels G Z δ}
    (h : parseFolioAndModelsFull G Z δ words = some out) :
    ∃ rest : List ℕ,
      words = encFolioSetRep out.folio ++ rest ∧
      parseFolioSetRep Z.card δ words = some (out.folio, rest) := by
  unfold parseFolioAndModelsFull parseFolioAndModels at h
  cases h1 : parseFolioSetRep Z.card δ words with
  | none => simp [h1] at h
  | some pair₁ =>
    rcases pair₁ with ⟨F, rest⟩
    cases h2 : parseModelList (rootedDigraphOfZ G Z) F.decodedList rest with
    | none => simp [h1, h2] at h
    | some pair₂ =>
      rcases pair₂ with ⟨rawModels, rem⟩
      cases rem with
      | nil =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        exact ⟨rest, eq_encFolioSetRep_of_parseFolioSetRep h1, by simp⟩
      | cons _ _ => simp [h1, h2] at h

/-- Word RAM specification of **Graph Minors XIII, Algorithm (4.1)** (page 75) with the pure
reading output decoder `parseFolioAndModelsFull`, modeled directly on `Alg105.Alg41Spec` in
`GraphMinor/Compute/Specs105.lean`:

*Input:* `G_i` in array `alg105ArrBase p` (`G_i.enc`) with `n_i` in `s.regs 26`, `G_i.numEdges` in
`s.regs 28`, and expanded edge endpoints `tail` in array `alg105ArrBase p + 5` and `head` in array
`alg105ArrBase p + 6`; `Z_i` in array `alg105ArrBase p + 1` (`bitSetList Z_i`) with `|Z_i| ≤ ξ`;
and a written-out branch-decomposition `(t, par, f_tau)` of `G_i` of width `≤ B` (`t` in
`s.regs 52`, `par` in array `alg105ArrBase p + 2`, `f_tau` in array `alg105ArrBase p + 3`).
*Output:* In `outArr`, a word list `s'.arrs outArr` decoded by `parseFolioAndModelsFull G_i Z_i δ`
to `out : ParsedFolioAndModels G_i Z_i δ` with `IsDeltaFolioRep δ G_i Z_i out.folio`.
*Running time:* `O(v + ε)` (`C * (n_i + G_i.numEdges + 1)`). -/
def Alg41Spec101 (p ξ δ B : ℕ) : Prop :=
  let b := alg105ArrBase p
  ∃ (prog : Cmd) (C c : ℕ), 0 < c ∧ 0 < C ∧
    ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let N := n_i + G_i.numEdges + 1
      wordSize c N ≤ w →
      Z_i.card ≤ ξ →
      IsWrittenDigraphBD B G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ) (out : ParsedFolioAndModels G_i Z_i δ),
        Exec w prog s s' time ∧
        time ≤ C * N ∧
        (s'.arrs outArr).length ≤ C * N ∧
        (∀ x ∈ s'.arrs outArr, x < 2 ^ w) ∧
        parseFolioAndModelsFull G_i Z_i δ (s'.arrs outArr) = some out ∧
        IsDeltaFolioRep δ G_i Z_i out.folio

/-! ### Section 3: Canonical Folio Class Codes and Constant-Time Word RAM Decision Tree -/

/-- Characteristic bit-vector of a `FolioSetRep k δ` over `allDetailLeCodes k δ`. -/
def folioBitVec {k δ : ℕ} (F : FolioSetRep k δ) : List Bool :=
  (allDetailLeCodes k δ).map (fun c =>
    F.codes.any (fun c' => decide (IsIsoRootedDigraphCode k c c')))

@[simp]
theorem length_folioBitVec {k δ : ℕ} (F : FolioSetRep k δ) :
    (folioBitVec F).length = (allDetailLeCodes k δ).length := by
  simp [folioBitVec]

theorem folioBitVec_eq_iff {k δ : ℕ} (F₁ F₂ : FolioSetRep k δ) :
    folioBitVec F₁ = folioBitVec F₂ ↔
      ∀ H : ComputeRootedDigraph k, H.HasDetailLe δ → (F₁.MemIso H ↔ F₂.MemIso H) := by
  constructor
  · intro heq H hdet
    have hc : encRootedDigraph H ∈ allDetailLeCodes k δ :=
      (mem_allDetailLeCodes_iff k δ _).mpr (isDetailLeCode_encRootedDigraph hdet)
    rcases List.mem_iff_getElem.mp hc with ⟨idx, hidx, hget⟩
    have hmap := congrArg (fun L : List Bool => L[idx]?) heq
    simp only [folioBitVec, List.getElem?_map, List.getElem?_eq_getElem hidx, hget,
      Option.map_some, Option.some.injEq] at hmap
    have hiff := Bool.eq_iff_iff.mp hmap
    simpa [FolioSetRep.MemIso] using hiff
  · intro hall
    unfold folioBitVec
    apply List.map_congr_left
    intro c hc
    have hdet_code : IsDetailLeCode k δ c := (mem_allDetailLeCodes_iff k δ c).mp hc
    unfold IsDetailLeCode at hdet_code
    cases hdec : decRootedDigraph k c with
    | none => rw [hdec] at hdet_code; exact False.elim hdet_code
    | some H =>
      rw [hdec] at hdet_code
      rcases hdet_code with ⟨rfl, hdet⟩
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      simp only [decide_eq_true_eq]
      exact hall H hdet

/-- Binary encoding of a `List Bool` as a natural number. -/
def boolListToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * boolListToNat bs

theorem boolListToNat_lt_two_pow (bs : List Bool) :
    boolListToNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [boolListToNat]
  | cons b bs ih =>
    simp only [boolListToNat, List.length_cons, Nat.pow_succ]
    split_ifs <;> omega

theorem boolListToNat_inj_of_length_eq :
    ∀ {bs₁ bs₂ : List Bool}, bs₁.length = bs₂.length →
      boolListToNat bs₁ = boolListToNat bs₂ → bs₁ = bs₂
  | [], [], _, _ => rfl
  | b₁ :: bs₁, b₂ :: bs₂, hlen, heq => by
    rcases b₁ with _ | _ <;> rcases b₂ with _ | _ <;>
      simp only [boolListToNat, Bool.false_eq_true, ↓reduceIte] at heq
    · rw [boolListToNat_inj_of_length_eq (Nat.succ.inj hlen) (by omega)]
    · omega
    · omega
    · rw [boolListToNat_inj_of_length_eq (Nat.succ.inj hlen) (by omega)]

/-- Canonical positive integer code for `F : FolioSetRep k δ` when `k ≤ q + 3`. -/
def folioRepCode (q : ℕ) {k δ : ℕ} (F : FolioSetRep k δ) : ℕ :=
  (k + 1) + (q + 5) * boolListToNat (folioBitVec F)

theorem folioRepCode_pos (q : ℕ) {k δ : ℕ} (F : FolioSetRep k δ) :
    0 < folioRepCode q F := by
  unfold folioRepCode
  omega

theorem folioRepCode_eq_iff (q : ℕ) {k₁ k₂ δ : ℕ}
    (hk₁ : k₁ ≤ q + 3) (hk₂ : k₂ ≤ q + 3)
    (F₁ : FolioSetRep k₁ δ) (F₂ : FolioSetRep k₂ δ) :
    folioRepCode q F₁ = folioRepCode q F₂ ↔
      ∃ hk : k₁ = k₂,
        ∀ H : ComputeRootedDigraph k₁, H.HasDetailLe δ →
          (F₁.MemIso H ↔ (hk ▸ F₂).MemIso H) := by
  constructor
  · intro heq
    have hmod : folioRepCode q F₁ % (q + 5) = folioRepCode q F₂ % (q + 5) :=
      congrArg (· % (q + 5)) heq
    have hdiv : folioRepCode q F₁ / (q + 5) = folioRepCode q F₂ / (q + 5) :=
      congrArg (· / (q + 5)) heq
    unfold folioRepCode at hmod hdiv
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    have hk : k₁ = k₂ := by omega
    subst hk
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega)] at hdiv
    have hdiv' : boolListToNat (folioBitVec F₁) = boolListToNat (folioBitVec F₂) := by
      have h0 : (k₁ + 1) / (q + 5) = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have hbv : folioBitVec F₁ = folioBitVec F₂ :=
      boolListToNat_inj_of_length_eq (by simp) hdiv'
    exact ⟨rfl, (folioBitVec_eq_iff F₁ F₂).mp hbv⟩
  · rintro ⟨rfl, hall⟩
    have hbv : folioBitVec F₁ = folioBitVec F₂ := (folioBitVec_eq_iff F₁ F₂).mpr hall
    unfold folioRepCode
    rw [hbv]

/-- Maximum number of codes in any `FolioSetRep k δ` for `k ≤ q + 3`. -/
def maxFolioCodesCount (q δ : ℕ) : ℕ :=
  ((List.range (q + 4)).map (fun k => (allDetailLeCodes k δ).length)).foldr max 0

private theorem le_foldr_max_of_mem (l : List ℕ) {x : ℕ} (h : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => nomatch h
  | cons a tl ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | htl
    · exact Nat.le_max_left x _
    · exact (ih htl).trans (Nat.le_max_right a _)

theorem length_allDetailLeCodes_le_maxFolioCodesCount {q δ k : ℕ} (hk : k ≤ q + 3) :
    (allDetailLeCodes k δ).length ≤ maxFolioCodesCount q δ := by
  apply le_foldr_max_of_mem
  rw [List.mem_map]
  exact ⟨k, List.mem_range.mpr (by omega), rfl⟩

/-- Upper bound on `folioRepCode q F` for any `F : FolioSetRep k δ` with `k ≤ q + 3`. -/
def maxFolioRepCode (q δ : ℕ) : ℕ :=
  (q + 5) * 2 ^ maxFolioCodesCount q δ

theorem folioRepCode_le_maxFolioRepCode {q k δ : ℕ} (hk : k ≤ q + 3) (F : FolioSetRep k δ) :
    folioRepCode q F ≤ maxFolioRepCode q δ := by
  unfold folioRepCode maxFolioRepCode
  have hlt : boolListToNat (folioBitVec F) < 2 ^ (allDetailLeCodes k δ).length := by
    rw [← length_folioBitVec F]
    exact boolListToNat_lt_two_pow _
  have hpow : 2 ^ (allDetailLeCodes k δ).length ≤ 2 ^ maxFolioCodesCount q δ :=
    Nat.pow_le_pow_right (by omega) (length_allDetailLeCodes_le_maxFolioCodesCount hk)
  have hmul :
      (q + 5) * (boolListToNat (folioBitVec F) + 1) ≤ (q + 5) * 2 ^ maxFolioCodesCount q δ :=
    Nat.mul_le_mul_left (q + 5) (by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

/-- Upper bound on the length of `encFolioSetRep F` for any `F : FolioSetRep k δ` with
`k ≤ q + 3`. -/
def maxFolioEncLen101 (q δ : ℕ) : ℕ :=
  1 + maxFolioCodesCount q δ * (3 + (q + 3) + 2 * δ)

/-- Upper bound on every word in `encFolioSetRep F` for any `F : FolioSetRep k δ` with
`k ≤ q + 3`. -/
def maxFolioEncWord (q δ : ℕ) : ℕ :=
  max (maxFolioCodesCount q δ) (2 + (q + 3) + 2 * δ)

private theorem length_flatMap_le_mul {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (hf : ∀ x ∈ l, (f x).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := hf a List.mem_cons_self
    have htl := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem length_and_words_encFolioSetRep_le {q k δ : ℕ} (hk : k ≤ q + 3)
    (F : FolioSetRep k δ) :
    (encFolioSetRep F).length ≤ maxFolioEncLen101 q δ ∧
    ∀ w ∈ encFolioSetRep F, w ≤ maxFolioEncWord q δ := by
  have hcodes_len : F.codes.length ≤ maxFolioCodesCount q δ :=
    (length_codes_le_allDetailLeCodes F).trans (length_allDetailLeCodes_le_maxFolioCodesCount hk)
  refine ⟨?_, ?_⟩
  · unfold encFolioSetRep maxFolioEncLen101
    rw [List.length_append, List.length_singleton]
    have hflat : (F.codes.flatMap (fun c => c.length :: c)).length ≤
        F.codes.length * (3 + (q + 3) + 2 * δ) := by
      apply length_flatMap_le_mul
      intro c hc
      have hlen := (length_and_words_le_of_isDetailLeCode (F.all_detail c hc)).1
      simp only [List.length_cons]
      omega
    have hmul : F.codes.length * (3 + (q + 3) + 2 * δ) ≤
        maxFolioCodesCount q δ * (3 + (q + 3) + 2 * δ) :=
      Nat.mul_le_mul_right _ hcodes_len
    omega
  · intro w hw
    unfold encFolioSetRep at hw
    unfold maxFolioEncWord
    simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | ⟨c, hc, rfl | hwc⟩
    · exact le_max_of_le_left hcodes_len
    · have hlen := (length_and_words_le_of_isDetailLeCode (F.all_detail c hc)).1
      exact le_max_of_le_right (by omega)
    · have hw_le := (length_and_words_le_of_isDetailLeCode (F.all_detail c hc)).2 w hwc
      exact le_max_of_le_right (by omega)

/-- Check whether `pref : List ℕ` is a complete length-prefixed sequence `numCodes :: flat`
where `parseLengthPrefixedLists numCodes flat = some (_, [])`. -/
def isCompleteFolioPrefix (pref : List ℕ) : Bool :=
  match pref with
  | [] => false
  | numCodes :: rest =>
    match parseLengthPrefixedLists numCodes rest with
    | some (_, []) => true
    | _ => false

theorem isCompleteFolioPrefix_encFolioSetRep {k δ : ℕ} (F : FolioSetRep k δ) :
    isCompleteFolioPrefix (encFolioSetRep F) = true := by
  have henc : encFolioSetRep F = F.codes.length :: encLengthPrefixedLists F.codes := rfl
  have h := parseLengthPrefixedLists_encLengthPrefixedLists F.codes []
  rw [List.append_nil] at h
  simp only [henc, isCompleteFolioPrefix, h]

theorem isCompleteFolioPrefix_take_lt {k δ : ℕ} (F : FolioSetRep k δ) {m : ℕ}
    (hm : m < (encFolioSetRep F).length) :
    isCompleteFolioPrefix ((encFolioSetRep F).take m) = false := by
  have henc : encFolioSetRep F = F.codes.length :: encLengthPrefixedLists F.codes := rfl
  rw [henc] at hm ⊢
  cases m with
  | zero => rfl
  | succ m' =>
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hm
    simp only [List.take_succ_cons, isCompleteFolioPrefix,
      parseLengthPrefixedLists_take_lt F.codes hm]

/-- Compute `folioRepCode q F` from a word list `words` and root count `k`. -/
def folioPrefixCode (q δ k : ℕ) (words : List ℕ) : ℕ :=
  if k ≤ q + 3 then
    match parseFolioSetRep k δ words with
    | some (F, _) => folioRepCode q F
    | none => 0
  else
    0

@[simp]
theorem folioPrefixCode_encFolioSetRep {q δ k : ℕ} (hk : k ≤ q + 3) (F : FolioSetRep k δ) :
    folioPrefixCode q δ k (encFolioSetRep F) = folioRepCode q F := by
  unfold folioPrefixCode
  have h := parseFolioSetRep_encFolioSetRep F []
  rw [List.append_nil] at h
  simp [hk, h]

theorem folioPrefixCode_le_maxFolioRepCode (q δ k : ℕ) (words : List ℕ) :
    folioPrefixCode q δ k words ≤ maxFolioRepCode q δ := by
  unfold folioPrefixCode
  split_ifs with hk
  · cases parseFolioSetRep k δ words with
    | none => exact Nat.zero_le _
    | some pair => exact folioRepCode_le_maxFolioRepCode hk pair.1
  · exact Nat.zero_le _

/-- Branching helper over `0 ≤ v ≤ maxVal`: if `s.regs r_val = v`, run `branch v`. -/
def branchValProg (r_val : Reg) (branch : ℕ → Cmd) : ℕ → Cmd
  | 0 =>
    .ite (.op .eq (.reg r_val) (.const 0)) (branch 0) .skip
  | v + 1 =>
    .ite (.op .eq (.reg r_val) (.const (v + 1))) (branch (v + 1)) (branchValProg r_val branch v)

theorem branchValProg_exec {w : ℕ} (r_val : Reg) (branch : ℕ → Cmd) (maxVal : ℕ)
    {s : State} (hv : s.regs r_val ≤ maxVal) (hw_max : maxVal + 1 < 2 ^ w)
    {s' : State} {t : ℕ}
    (hbranch : Exec w (branch (s.regs r_val)) s s' t) :
    ∃ t_total : ℕ,
      Exec w (branchValProg r_val branch maxVal) s s' t_total ∧
      t_total ≤ t + 4 * (maxVal + 1) := by
  induction maxVal with
  | zero =>
    have hv0 : s.regs r_val = 0 := by omega
    refine ⟨(Expr.op .eq (.reg r_val) (.const 0)).cost + t, ?_, by simp [Expr.cost]; omega⟩
    refine Exec.ite_true (v := 1) ?_ (by decide) ?_
    · simp [Expr.eval, BinOp.eval, BinOp.raw, hv0, checkWord_of_lt (by omega : 0 < 2 ^ w),
        checkWord_of_lt (by omega : 1 < 2 ^ w)]
    · rw [← hv0]; exact hbranch
  | succ m ih =>
    by_cases heq : s.regs r_val = m + 1
    · refine ⟨(Expr.op .eq (.reg r_val) (.const (m + 1))).cost + t, ?_, by simp [Expr.cost]; omega⟩
      refine Exec.ite_true (v := 1) ?_ (by decide) ?_
      · simp [Expr.eval, BinOp.eval, BinOp.raw, heq,
          checkWord_of_lt (by omega : m + 1 < 2 ^ w),
          checkWord_of_lt (by omega : 1 < 2 ^ w)]
      · rw [← heq]; exact hbranch
    · rcases ih (by omega) (by omega) with ⟨t_sub, hex_sub, ht_sub⟩
      refine ⟨(Expr.op .eq (.reg r_val) (.const (m + 1))).cost + t_sub, ?_,
        by simp [Expr.cost]; omega⟩
      refine Exec.ite_false ?_ hex_sub
      have hval_lt : s.regs r_val < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, heq, checkWord_of_lt hval_lt,
        checkWord_of_lt (by omega : m + 1 < 2 ^ w),
        checkWord_of_lt (by omega : 0 < 2 ^ w)]

/-- Prefix-tree Word RAM program that reads a self-delimiting `encFolioSetRep F` prefix from
array `arr` and writes `f (encFolioSetRep F)` into `r_out` using scratch register `r_tmp`. -/
def folioTrieAuxProg (arr : Arr) (r_out r_tmp : Reg) (maxWord : ℕ) (f : List ℕ → ℕ) :
    ℕ → List ℕ → Cmd
  | 0, pref => .assign r_out (.const (f pref))
  | rem + 1, pref =>
    if isCompleteFolioPrefix pref then
      .assign r_out (.const (f pref))
    else
      .seq (.assign r_tmp (.read arr (.const pref.length)))
        (branchValProg r_tmp
          (fun v => folioTrieAuxProg arr r_out r_tmp maxWord f rem (pref ++ [v]))
          maxWord)

theorem folioTrieAuxProg_exec {w : ℕ} (arr : Arr) (r_out r_tmp : Reg) (maxWord : ℕ)
    (f : List ℕ → ℕ) (hf_lt : ∀ pref, f pref < 2 ^ w)
    {k δ : ℕ} (F : FolioSetRep k δ) (rest : List ℕ)
    (hwords : ∀ x ∈ encFolioSetRep F, x ≤ maxWord)
    (hw_max : maxWord + 1 < 2 ^ w)
    (hlen_w : (encFolioSetRep F).length < 2 ^ w) :
    ∀ (rem : ℕ) (m : ℕ),
      m ≤ (encFolioSetRep F).length →
      (encFolioSetRep F).length - m ≤ rem →
      rem < 2 ^ w →
      ∀ (s : State),
        s.arrs arr = encFolioSetRep F ++ rest →
        ∃ (s' : State) (t : ℕ),
          Exec w (folioTrieAuxProg arr r_out r_tmp maxWord f rem ((encFolioSetRep F).take m))
            s s' t ∧
          t ≤ (rem + 1) * (4 * maxWord + 10) ∧
          s'.regs r_out = f (encFolioSetRep F) ∧
          (∀ r, r ≠ r_out → r ≠ r_tmp → s'.regs r = s.regs r) ∧
          s'.arrs = s.arrs
  | 0, m, hm_le, hrem, _, s, harr => by
    have hm_eq : m = (encFolioSetRep F).length := by omega
    subst hm_eq
    rw [List.take_length]
    refine ⟨s.setReg r_out (f (encFolioSetRep F)), 2, ?_,
      by rw [Nat.one_mul]; omega, by simp, fun r hr₁ _ => by simp [hr₁], rfl⟩
    exact .assign (checkWord_of_lt (hf_lt _))
  | rem + 1, m, hm_le, hrem, hrem_w, s, harr => by
    unfold folioTrieAuxProg
    by_cases hm_eq : m = (encFolioSetRep F).length
    · subst hm_eq
      simp only [List.take_length, isCompleteFolioPrefix_encFolioSetRep, ↓reduceIte]
      refine ⟨s.setReg r_out (f (encFolioSetRep F)), 2, ?_,
        by rw [Nat.succ_mul]; omega, by simp, fun r hr₁ _ => by simp [hr₁], rfl⟩
      exact .assign (checkWord_of_lt (hf_lt _))
    · have hm_lt : m < (encFolioSetRep F).length := by omega
      have hm_w : m < 2 ^ w := by omega
      simp only [isCompleteFolioPrefix_take_lt F hm_lt, Bool.false_eq_true, ↓reduceIte]
      let v := (encFolioSetRep F)[m]'hm_lt
      have hv_mem : v ∈ encFolioSetRep F := List.getElem_mem hm_lt
      have hv_le : v ≤ maxWord := hwords v hv_mem
      have hv_w : v < 2 ^ w := by omega
      have hlen_take : ((encFolioSetRep F).take m).length = m := List.length_take_of_le hm_le
      have hidx_arr : m < (s.arrs arr).length := by
        rw [harr, List.length_append]
        omega
      have hget_arr : (s.arrs arr)[m]'hidx_arr = v := by
        simp [harr, List.getElem_append_left hm_lt, v]
      have hex_read :
          Exec w (.assign r_tmp (.read arr (.const ((encFolioSetRep F).take m).length)))
            s (s.setReg r_tmp v) 3 := by
        rw [hlen_take]
        refine .assign ?_
        simp [Expr.eval, checkWord_of_lt hm_w, hidx_arr, hget_arr, checkWord_of_lt hv_w]
      have htake_succ : (encFolioSetRep F).take m ++ [v] = (encFolioSetRep F).take (m + 1) := by
        simp [v]
      let s₁ := s.setReg r_tmp v
      have hs₁_arr : s₁.arrs arr = encFolioSetRep F ++ rest := harr
      rcases folioTrieAuxProg_exec arr r_out r_tmp maxWord f hf_lt F rest hwords hw_max hlen_w
          rem (m + 1) (by omega) (by omega) (by omega) s₁ hs₁_arr with
        ⟨s', t_rec, hex_rec, ht_rec, hrout, hregs, harrs⟩
      rw [← htake_succ] at hex_rec
      have hs₁_r_tmp : s₁.regs r_tmp = v := by simp [s₁]
      rcases branchValProg_exec r_tmp
          (fun val => folioTrieAuxProg arr r_out r_tmp maxWord f rem
            ((encFolioSetRep F).take m ++ [val]))
          maxWord (s := s₁) (by rw [hs₁_r_tmp]; exact hv_le) hw_max
          (by rw [hs₁_r_tmp]; exact hex_rec) with
        ⟨t_br, hex_br, ht_br⟩
      refine ⟨s', 3 + t_br, .seq hex_read hex_br, ?_, hrout, ?_, harrs⟩
      · rw [Nat.succ_mul (rem + 1)]
        omega
      · intro r hr₁ hr₂
        rw [hregs r hr₁ hr₂]
        simp [s₁, hr₂]

/-- Word RAM program that reads `k = s.regs r_k` (`k ≤ q + 3`) and the self-delimiting
`encFolioSetRep F` prefix of `s.arrs arr`, and writes `folioRepCode q F` into `r_out`. -/
def computeFolioRepCodeProg (q δ : ℕ) (arr : Arr) (r_k r_out r_tmp : Reg) : Cmd :=
  branchValProg r_k
    (fun k =>
      folioTrieAuxProg arr r_out r_tmp (maxFolioEncWord q δ)
        (folioPrefixCode q δ k) (maxFolioEncLen101 q δ) [])
    (q + 3)

theorem computeFolioRepCodeProg_exec {w q δ : ℕ} (arr : Arr) (r_k r_out r_tmp : Reg)
    {k : ℕ} (hk : k ≤ q + 3) (F : FolioSetRep k δ) (rest : List ℕ)
    (hw_code : maxFolioRepCode q δ < 2 ^ w)
    (hw_len : maxFolioEncLen101 q δ < 2 ^ w)
    (hw_word : maxFolioEncWord q δ + 1 < 2 ^ w)
    (hw_q : q + 4 < 2 ^ w)
    (s : State) (hr_k : s.regs r_k = k) (harr : s.arrs arr = encFolioSetRep F ++ rest) :
    ∃ (s' : State) (t : ℕ),
      Exec w (computeFolioRepCodeProg q δ arr r_k r_out r_tmp) s s' t ∧
      t ≤ (maxFolioEncLen101 q δ + 1) * (4 * maxFolioEncWord q δ + 10) + 4 * (q + 4) ∧
      s'.regs r_out = folioRepCode q F ∧
      (∀ r, r ≠ r_out → r ≠ r_tmp → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs := by
  rcases length_and_words_encFolioSetRep_le hk F with ⟨hlen_F, hwords_F⟩
  have hf_lt : ∀ pref, folioPrefixCode q δ k pref < 2 ^ w := fun pref =>
    lt_of_le_of_lt (folioPrefixCode_le_maxFolioRepCode q δ k pref) hw_code
  rcases folioTrieAuxProg_exec arr r_out r_tmp (maxFolioEncWord q δ)
      (folioPrefixCode q δ k) hf_lt F rest hwords_F hw_word (by omega)
      (maxFolioEncLen101 q δ) 0 (Nat.zero_le _) (by omega) hw_len s harr with
    ⟨s', t_trie, hex_trie, ht_trie, hrout, hregs, harrs⟩
  simp only [List.take_zero, folioPrefixCode_encFolioSetRep hk] at hex_trie hrout
  rcases branchValProg_exec r_k
      (fun k' =>
        folioTrieAuxProg arr r_out r_tmp (maxFolioEncWord q δ)
          (folioPrefixCode q δ k') (maxFolioEncLen101 q δ) [])
      (q + 3) (s := s) (by rw [hr_k]; exact hk) hw_q
      (by rw [hr_k]; exact hex_trie) with
    ⟨t_total, hex_total, ht_total⟩
  refine ⟨s', t_total, hex_total, by omega, hrout, hregs, harrs⟩

/-! ### Section 4: Explicit Rooted Digraph Bridge for $\tilde{A}$ (`tildeAMultiDigraph`) -/

/-- Filter `eList : List (ℕ × ℕ × ℕ)` for edges with tail `u` and head `v`. -/
def edgesBetween (eList : List (ℕ × ℕ × ℕ)) (u v : ℕ) : List (ℕ × ℕ × ℕ) :=
  eList.filter (fun e => decide (e.1 = u ∧ e.2.1 = v))

@[simp]
theorem mem_edgesBetween_iff (eList : List (ℕ × ℕ × ℕ)) (u v : ℕ) (e : ℕ × ℕ × ℕ) :
    e ∈ edgesBetween eList u v ↔ e ∈ eList ∧ e.1 = u ∧ e.2.1 = v := by
  simp [edgesBetween]

theorem nodup_edgesBetween {eList : List (ℕ × ℕ × ℕ)} (hnd : eList.Nodup) (u v : ℕ) :
    (edgesBetween eList u v).Nodup :=
  hnd.filter _

/-- Build the `MultiDigraph vList.length` representation of a subdigraph with vertex list `vList`
and edge list `eList`. -/
def tildeAMultiDigraph (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    MultiDigraph vList.length where
  edgeMult x y := (edgesBetween eList (vList[x.1]'x.2) (vList[y.1]'y.2)).length

/-- Root finset `{0, ..., k_A - 1} ⊆ Fin n_A` of the first `k_A` vertices in `vList`. -/
def prefixRootFinset (n_A k_A : ℕ) : Finset (Fin n_A) :=
  Finset.univ.filter (fun x : Fin n_A => x.1 < k_A)

@[simp]
theorem mem_prefixRootFinset (n_A k_A : ℕ) (x : Fin n_A) :
    x ∈ prefixRootFinset n_A k_A ↔ x.1 < k_A := by
  simp [prefixRootFinset]

theorem sortedFinsetList_prefixRootFinset {n_A k_A : ℕ} (hk : k_A ≤ n_A) :
    sortedFinsetList (prefixRootFinset n_A k_A) = (List.finRange n_A).take k_A := by
  have hnd₁ : (sortedFinsetList (prefixRootFinset n_A k_A)).Nodup :=
    nodup_sortedFinsetList _
  have hnd₂ : ((List.finRange n_A).take k_A).Nodup :=
    (List.nodup_finRange n_A).take
  have hpw₁ : (sortedFinsetList (prefixRootFinset n_A k_A)).Pairwise (· < ·) :=
    pairwise_lt_sortedFinsetList _
  have hpw₂ : ((List.finRange n_A).take k_A).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange n_A).take
  have hperm :
      List.Perm (sortedFinsetList (prefixRootFinset n_A k_A)) ((List.finRange n_A).take k_A) := by
    rw [List.perm_ext_iff_of_nodup hnd₁ hnd₂]
    intro x
    rw [mem_sortedFinsetList, mem_prefixRootFinset, List.mem_take_iff_getElem]
    constructor
    · intro hx
      exact ⟨x.1, by simp; omega, by simp⟩
    · rintro ⟨i, hi, heq⟩
      simp only [List.length_finRange, List.getElem_finRange] at hi heq
      subst heq
      dsimp
      omega
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (lt_asymm h1 h2)) hpw₁ hpw₂

@[simp]
theorem card_prefixRootFinset {n_A k_A : ℕ} (hk : k_A ≤ n_A) :
    (prefixRootFinset n_A k_A).card = k_A := by
  rw [← length_sortedFinsetList, sortedFinsetList_prefixRootFinset hk,
    List.length_take, List.length_finRange, Nat.min_eq_left hk]

@[simp]
theorem rootsZ_prefixRootFinset {n_A k_A : ℕ} (hk : k_A ≤ n_A)
    (i : Fin (prefixRootFinset n_A k_A).card) :
    (rootsZ (prefixRootFinset n_A k_A) i).1 = i.1 := by
  unfold rootsZ
  have h := congrArg (fun L : List (Fin n_A) => L[i.1]?) (sortedFinsetList_prefixRootFinset hk)
  have hi₁ : i.1 < (sortedFinsetList (prefixRootFinset n_A k_A)).length := by
    rw [length_sortedFinsetList]; exact i.2
  have hi₂ : i.1 < ((List.finRange n_A).take k_A).length := by
    rw [← sortedFinsetList_prefixRootFinset hk]; exact hi₁
  rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂] at h
  have hval := congrArg Fin.val (Option.some.inj h)
  simpa using hval

/-- Explicit `GM13.Digraph.Iso` from `(tildeAMultiDigraph vList eList).toGMDigraph` to a digraph `D`
whose vertex set is `{v | v ∈ vList}` and whose edge set is `{e | e ∈ eList}`. -/
def isoTildeAMultiDigraph (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ))
    (hv_nd : vList.Nodup)
    (hv_set : {v : ℕ | v ∈ vList} = D.vertexSet)
    (he_nd : eList.Nodup)
    (he_set : {e : ℕ × ℕ × ℕ | e ∈ eList} = D.edgeSet)
    (he_ends : ∀ e ∈ eList, D.tail e = e.1 ∧ D.head e = e.2.1 ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    GM13.Digraph.Iso (tildeAMultiDigraph vList eList).toGMDigraph D where
  vMap i := vList.getD i 0
  eMap p :=
    (edgesBetween eList (vList.getD p.1 0) (vList.getD p.2.1 0)).getD p.2.2 (0, 0, 0)
  bijOn_v :=
    ⟨fun i hi => by
      change i < vList.length at hi
      rw [← hv_set]
      change vList.getD i 0 ∈ vList
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi,
     fun i₁ hi₁ i₂ hi₂ heq => by
      change i₁ < vList.length at hi₁
      change i₂ < vList.length at hi₂
      simp only [List.getD_eq_getElem _ _ hi₁, List.getD_eq_getElem _ _ hi₂] at heq
      exact (hv_nd.getElem_inj_iff (hi := hi₁) (hj := hi₂)).mp heq,
     fun v hv => by
      rw [← hv_set] at hv
      rcases List.mem_iff_getElem.mp hv with ⟨idx, hidx, rfl⟩
      exact ⟨idx, hidx, List.getD_eq_getElem _ _ hidx⟩⟩
  bijOn_e :=
    ⟨fun p ⟨hu, hv, hk⟩ => by
      rw [← he_set]
      simp only [List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv]
      have hmem :
          (edgesBetween eList (vList[p.1]'hu) (vList[p.2.1]'hv))[p.2.2]'hk ∈
            edgesBetween eList (vList[p.1]'hu) (vList[p.2.1]'hv) :=
        List.getElem_mem hk
      rw [List.getD_eq_getElem _ _ hk]
      exact ((mem_edgesBetween_iff _ _ _ _).mp hmem).1,
     fun p₁ ⟨hu₁, hv₁, hk₁⟩ p₂ ⟨hu₂, hv₂, hk₂⟩ heq => by
      simp only [List.getD_eq_getElem _ _ hu₁, List.getD_eq_getElem _ _ hv₁,
        List.getD_eq_getElem _ _ hu₂, List.getD_eq_getElem _ _ hv₂,
        List.getD_eq_getElem _ _ hk₁, List.getD_eq_getElem _ _ hk₂] at heq
      have hm₁ := (mem_edgesBetween_iff _ _ _ _).mp (List.getElem_mem hk₁)
      have hm₂ := (mem_edgesBetween_iff _ _ _ _).mp (List.getElem_mem hk₂)
      have h_u : vList[p₁.1]'hu₁ = vList[p₂.1]'hu₂ := by
        rw [← hm₁.2.1, heq, hm₂.2.1]
      have h_v : vList[p₁.2.1]'hv₁ = vList[p₂.2.1]'hv₂ := by
        rw [← hm₁.2.2, heq, hm₂.2.2]
      have hp₁_1 : p₁.1 = p₂.1 := (hv_nd.getElem_inj_iff (hi := hu₁) (hj := hu₂)).mp h_u
      have hp₁_21 : p₁.2.1 = p₂.2.1 := (hv_nd.getElem_inj_iff (hi := hv₁) (hj := hv₂)).mp h_v
      rcases p₁ with ⟨u₁, v₁, k₁⟩
      rcases p₂ with ⟨u₂, v₂, k₂⟩
      dsimp only at hp₁_1 hp₁_21
      subst hp₁_1 hp₁_21
      have hk_eq : k₁ = k₂ :=
        ((nodup_edgesBetween he_nd _ _).getElem_inj_iff (hi := hk₁) (hj := hk₂)).mp heq
      rw [hk_eq],
     fun e he => by
      rw [← he_set] at he
      rcases he_ends e he with ⟨_, _, hu_mem, hv_mem⟩
      rcases List.mem_iff_getElem.mp hu_mem with ⟨u, hu, hu_eq⟩
      rcases List.mem_iff_getElem.mp hv_mem with ⟨v, hv, hv_eq⟩
      have he_eb : e ∈ edgesBetween eList (vList[u]'hu) (vList[v]'hv) :=
        (mem_edgesBetween_iff _ _ _ _).mpr ⟨he, hu_eq.symm, hv_eq.symm⟩
      rcases List.mem_iff_getElem.mp he_eb with ⟨k, hk, hk_eq⟩
      refine ⟨(u, v, k), ⟨hu, hv, hk⟩, ?_⟩
      dsimp only
      rw [List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv,
        List.getD_eq_getElem _ _ hk, hk_eq]⟩
  head_eq p := by
    rintro ⟨hu, hv, hk⟩
    change D.head ((edgesBetween eList (vList.getD p.1 0) (vList.getD p.2.1 0)).getD p.2.2 (0, 0, 0)) =
      vList.getD p.2.1 0
    simp only [List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv,
      List.getD_eq_getElem _ _ hk]
    have hm := (mem_edgesBetween_iff _ _ _ _).mp (List.getElem_mem hk)
    rw [(he_ends _ hm.1).2.1, hm.2.2]
  tail_eq p := by
    rintro ⟨hu, hv, hk⟩
    change D.tail ((edgesBetween eList (vList.getD p.1 0) (vList.getD p.2.1 0)).getD p.2.2 (0, 0, 0)) =
      vList.getD p.1 0
    simp only [List.getD_eq_getElem _ _ hu, List.getD_eq_getElem _ _ hv,
      List.getD_eq_getElem _ _ hk]
    have hm := (mem_edgesBetween_iff _ _ _ _).mp (List.getElem_mem hk)
    rw [(he_ends _ hm.1).1, hm.2.1]

@[simp]
theorem numEdges_tildeAMultiDigraph (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ))
    (hv_nd : vList.Nodup)
    (hv_set : {v : ℕ | v ∈ vList} = D.vertexSet)
    (he_nd : eList.Nodup)
    (he_set : {e : ℕ × ℕ × ℕ | e ∈ eList} = D.edgeSet)
    (he_ends : ∀ e ∈ eList, D.tail e = e.1 ∧ D.head e = e.2.1 ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    (tildeAMultiDigraph vList eList).numEdges = eList.length := by
  have iso := isoTildeAMultiDigraph D vList eList hv_nd hv_set he_nd he_set he_ends
  have hcard : D.edgeSet.ncard = (tildeAMultiDigraph vList eList).toGMDigraph.edgeSet.ncard := by
    rw [← iso.bijOn_e.image_eq, iso.bijOn_e.injOn.ncard_image]
  have hD_card : D.edgeSet.ncard = eList.length := by
    have heq : D.edgeSet = ↑eList.toFinset := by
      ext e
      rw [← he_set]
      simp
    rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup he_nd]
  rw [← (tildeAMultiDigraph vList eList).ncard_edgeSet_toGMDigraph, ← hcard, hD_card]

/-- Explicit `GM13.RootedDigraph.Iso` from
`((tildeAMultiDigraph vList eList).toGMRootedDigraph (prefixRootFinset vList.length rList.length)).castRoots (card_prefixRootFinset hk)`
to `GM13.rootedDigraphOfList D rList hroots` when `vList.take rList.length = rList`. -/
def isoRootedTildeAMultiDigraph (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) (rList : List ℕ)
    (hv_nd : vList.Nodup)
    (hv_set : {v : ℕ | v ∈ vList} = D.vertexSet)
    (he_nd : eList.Nodup)
    (he_set : {e : ℕ × ℕ × ℕ | e ∈ eList} = D.edgeSet)
    (he_ends : ∀ e ∈ eList, D.tail e = e.1 ∧ D.head e = e.2.1 ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (hk : rList.length ≤ vList.length)
    (htake : vList.take rList.length = rList)
    (hroots : ∀ x ∈ rList, x ∈ D.vertexSet) :
    GM13.RootedDigraph.Iso
      (((tildeAMultiDigraph vList eList).toGMRootedDigraph
        (prefixRootFinset vList.length rList.length)).castRoots (card_prefixRootFinset hk))
      (GM13.rootedDigraphOfList D rList hroots) :=
  { toIso := isoTildeAMultiDigraph D vList eList hv_nd hv_set he_nd he_set he_ends
    map_roots := fun i => by
      dsimp [GM13.RootedDigraph.castRoots, MultiDigraph.toGMRootedDigraph,
        isoTildeAMultiDigraph, GM13.rootedDigraphOfList]
      rw [rootsZ_prefixRootFinset hk]
      simp only [Fin.val_cast]
      have hi_v : i.1 < vList.length := lt_of_lt_of_le i.2 hk
      rw [List.getD_eq_getElem _ _ hi_v]
      have hget := congrArg (fun L : List ℕ => L[i.1]?) htake
      have hi_t : i.1 < (vList.take rList.length).length := by
        rw [List.length_take, Nat.min_eq_left hk]; exact i.2
      rw [List.getElem?_eq_getElem hi_t, List.getElem?_eq_getElem i.2,
        List.getElem_take] at hget
      exact Option.some.inj hget }

private theorem isRootedDigraphMinor_castRoots_right {α β : Type*} {k₁ k₂ : ℕ}
    (h : k₁ = k₂) (H : ComputeRootedDigraph k₁) (G : GM13.RootedDigraph α β k₁) :
    GM13.IsRootedDigraphMinor (h ▸ H).toGMRootedDigraph (G.castRoots h) ↔
      GM13.IsRootedDigraphMinor H.toGMRootedDigraph G := by
  subst h
  rfl

private theorem hasDetailLe_cast_symm {k₁ k₂ δ : ℕ}
    (h : k₁ = k₂) (H : ComputeRootedDigraph k₂) :
    (h.symm ▸ H).HasDetailLe δ ↔ H.HasDetailLe δ := by
  subst h
  rfl

private theorem memIso_cast_iff {k₁ k₂ δ : ℕ}
    (h : k₁ = k₂) (F : FolioSetRep k₁ δ) (H : ComputeRootedDigraph k₂) :
    (h ▸ F).MemIso H ↔ F.MemIso (h.symm ▸ H) := by
  subst h
  rfl

private theorem inFolio_castRoots_iff {α β : Type*} {k₁ k₂ : ℕ}
    (h : k₁ = k₂) (R : GM13.RootedDigraph α β k₁) (H : ComputeRootedDigraph k₂) :
    (R.castRoots h).InFolio H.toGMRootedDigraph ↔
      R.InFolio (h.symm ▸ H).toGMRootedDigraph := by
  subst h
  rfl

private theorem folioRepCode_eq_iff_inFolio_cast {k₁ k₂ δ : ℕ}
    (h : k₁ = k₂)
    (F₁ : FolioSetRep k₁ δ) (F₂ : FolioSetRep k₂ δ)
    (R₁ : GM13.RootedDigraph ℕ (ℕ × ℕ × ℕ) k₁)
    (R₂ : GM13.RootedDigraph ℕ (ℕ × ℕ × ℕ) k₂)
    (h₁ : ∀ H : ComputeRootedDigraph k₁, H.HasDetailLe δ →
      (F₁.MemIso H ↔ R₁.InFolio H.toGMRootedDigraph))
    (h₂ : ∀ H : ComputeRootedDigraph k₂, H.HasDetailLe δ →
      (F₂.MemIso H ↔ R₂.InFolio H.toGMRootedDigraph)) :
    (∀ H : ComputeRootedDigraph k₁, H.HasDetailLe δ →
      (F₁.MemIso H ↔ (h ▸ F₂).MemIso H)) ↔
    GM13.HasSameDeltaFolio R₁ (h ▸ R₂) δ := by
  subst h
  rw [hasSameDeltaFolio_iff_forall_computeRootedDigraph]
  exact forall_congr' fun H => imp_congr_right fun hdet => by rw [h₁ H hdet, h₂ H hdet]

/-- Bridge from `ParsedFolioAndModels` and `IsDeltaFolioRep` on `(tildeAMultiDigraph vList eList,
prefixRootFinset vList.length rList.length)` to `GM13.IsDeltaFolioModelling` on
`GM13.rootedDigraphOfList D rList hroots`, together with explicit transport of each concrete model
`out.models i` to a `GM13.IsRootedDigraphMinor` in `GM13.rootedDigraphOfList D rList hroots`. -/
theorem isDeltaFolioModelling_of_parsedFolioAndModels
    (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) (rList : List ℕ)
    (hv_nd : vList.Nodup)
    (hv_set : {v : ℕ | v ∈ vList} = D.vertexSet)
    (he_nd : eList.Nodup)
    (he_set : {e : ℕ × ℕ × ℕ | e ∈ eList} = D.edgeSet)
    (he_ends : ∀ e ∈ eList, D.tail e = e.1 ∧ D.head e = e.2.1 ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (hk : rList.length ≤ vList.length)
    (htake : vList.take rList.length = rList)
    (hroots : ∀ x ∈ rList, x ∈ D.vertexSet)
    {δ : ℕ}
    (out : ParsedFolioAndModels (tildeAMultiDigraph vList eList)
      (prefixRootFinset vList.length rList.length) δ)
    (_hrep : IsDeltaFolioRep δ (tildeAMultiDigraph vList eList)
      (prefixRootFinset vList.length rList.length) out.folio) :
    (∀ i : Fin out.folio.codes.length,
      GM13.IsRootedDigraphMinor
        (card_prefixRootFinset hk ▸ out.folio.decodeCodeAt i).toGMRootedDigraph
        (GM13.rootedDigraphOfList D rList hroots)) ∧
    ∃ (vMod : GM13.RootedDigraph ℕ ℕ rList.length → ℕ → GM13.Digraph ℕ (ℕ × ℕ × ℕ))
      (eMod : GM13.RootedDigraph ℕ ℕ rList.length → ℕ → (ℕ × ℕ × ℕ)),
      GM13.IsDeltaFolioModelling (GM13.rootedDigraphOfList D rList hroots) δ vMod eMod := by
  have : Nonempty ℕ := ⟨0⟩
  have : Nonempty (ℕ × ℕ × ℕ) := ⟨(0, 0, 0)⟩
  refine ⟨fun i => ?_, GM13.exists_isDeltaFolioModelling _ δ⟩
  let isoRD := isoRootedTildeAMultiDigraph D vList eList rList hv_nd hv_set he_nd he_set
    he_ends hk htake hroots
  have hmin₀ :
      GM13.IsRootedDigraphMinor (out.folio.decodeCodeAt i).toGMRootedDigraph
        ((tildeAMultiDigraph vList eList).toGMRootedDigraph
          (prefixRootFinset vList.length rList.length)) :=
    (hasRootedDigraphModel_iff_isRootedDigraphMinor_toGMRootedDigraph _ _ _).mp ⟨out.models i⟩
  have hmin₁ :
      GM13.IsRootedDigraphMinor
        (card_prefixRootFinset hk ▸ out.folio.decodeCodeAt i).toGMRootedDigraph
        (((tildeAMultiDigraph vList eList).toGMRootedDigraph
          (prefixRootFinset vList.length rList.length)).castRoots (card_prefixRootFinset hk)) :=
    (isRootedDigraphMinor_castRoots_right (card_prefixRootFinset hk) _ _).mpr hmin₀
  exact isRootedDigraphMinor_of_iso_right isoRD hmin₁

@[simp]
theorem folioRepCode_cast {q k₁ k₂ δ : ℕ} (h : k₁ = k₂) (F : FolioSetRep k₁ δ) :
    folioRepCode q (h ▸ F) = folioRepCode q F := by
  subst h
  rfl

/-- Single-member equivalence between `(card_prefixRootFinset hk ▸ F).MemIso H` and
`(GM13.rootedDigraphOfList D rList hroots).InFolio H.toGMRootedDigraph`. -/
theorem memIso_iff_inFolio_rootedDigraphOfList
    (D : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) (rList : List ℕ)
    (hv_nd : vList.Nodup) (hv_set : {v : ℕ | v ∈ vList} = D.vertexSet)
    (he_nd : eList.Nodup) (he_set : {e : ℕ × ℕ × ℕ | e ∈ eList} = D.edgeSet)
    (he_ends : ∀ e ∈ eList, D.tail e = e.1 ∧ D.head e = e.2.1 ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (hk : rList.length ≤ vList.length) (htake : vList.take rList.length = rList)
    (hroots : ∀ x ∈ rList, x ∈ D.vertexSet)
    {δ : ℕ}
    (F : FolioSetRep (prefixRootFinset vList.length rList.length).card δ)
    (hrep : IsDeltaFolioRep δ (tildeAMultiDigraph vList eList)
      (prefixRootFinset vList.length rList.length) F)
    (H : ComputeRootedDigraph rList.length) (hdet : H.HasDetailLe δ) :
    (card_prefixRootFinset hk ▸ F).MemIso H ↔
      (GM13.rootedDigraphOfList D rList hroots).InFolio H.toGMRootedDigraph := by
  let hc : (prefixRootFinset vList.length rList.length).card = rList.length :=
    card_prefixRootFinset hk
  let iso := isoRootedTildeAMultiDigraph D vList eList rList
    hv_nd hv_set he_nd he_set he_ends hk htake hroots
  have hdet' : (hc.symm ▸ H).HasDetailLe δ := (hasDetailLe_cast_symm hc H).mpr hdet
  rw [memIso_cast_iff hc F H, hrep (hc.symm ▸ H) hdet', hasRootedDigraphModel_iff_inFolio,
    ← inFolio_castRoots_iff hc _ H]
  exact ⟨fun ⟨hfin, hmin⟩ => ⟨hfin, isRootedDigraphMinor_of_iso_right iso hmin⟩,
    fun ⟨hfin, hmin⟩ => ⟨hfin, isRootedDigraphMinor_of_iso_right iso.symm hmin⟩⟩

/-- Two interior members `(D₁, vList₁, eList₁, rList₁)` and `(D₂, vList₂, eList₂, rList₂)` have equal
`folioRepCode q` if and only if they have the same `rList` length and the same `δ`-folio in
`GM13` (`GM13.HasSameDeltaFolio`). -/
theorem folioRepCode_eq_iff_hasSameDeltaFolio
    {q δ : ℕ}
    (D₁ : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList₁ : List ℕ) (eList₁ : List (ℕ × ℕ × ℕ)) (rList₁ : List ℕ)
    (hv_nd₁ : vList₁.Nodup) (hv_set₁ : {v : ℕ | v ∈ vList₁} = D₁.vertexSet)
    (he_nd₁ : eList₁.Nodup) (he_set₁ : {e : ℕ × ℕ × ℕ | e ∈ eList₁} = D₁.edgeSet)
    (he_ends₁ : ∀ e ∈ eList₁, D₁.tail e = e.1 ∧ D₁.head e = e.2.1 ∧ e.1 ∈ vList₁ ∧ e.2.1 ∈ vList₁)
    (hk₁ : rList₁.length ≤ vList₁.length) (htake₁ : vList₁.take rList₁.length = rList₁)
    (hroots₁ : ∀ x ∈ rList₁, x ∈ D₁.vertexSet) (hr₁_le : rList₁.length ≤ q + 3)
    (F₁ : FolioSetRep (prefixRootFinset vList₁.length rList₁.length).card δ)
    (hrep₁ : IsDeltaFolioRep δ (tildeAMultiDigraph vList₁ eList₁)
      (prefixRootFinset vList₁.length rList₁.length) F₁)
    (D₂ : GM13.Digraph ℕ (ℕ × ℕ × ℕ))
    (vList₂ : List ℕ) (eList₂ : List (ℕ × ℕ × ℕ)) (rList₂ : List ℕ)
    (hv_nd₂ : vList₂.Nodup) (hv_set₂ : {v : ℕ | v ∈ vList₂} = D₂.vertexSet)
    (he_nd₂ : eList₂.Nodup) (he_set₂ : {e : ℕ × ℕ × ℕ | e ∈ eList₂} = D₂.edgeSet)
    (he_ends₂ : ∀ e ∈ eList₂, D₂.tail e = e.1 ∧ D₂.head e = e.2.1 ∧ e.1 ∈ vList₂ ∧ e.2.1 ∈ vList₂)
    (hk₂ : rList₂.length ≤ vList₂.length) (htake₂ : vList₂.take rList₂.length = rList₂)
    (hroots₂ : ∀ x ∈ rList₂, x ∈ D₂.vertexSet) (hr₂_le : rList₂.length ≤ q + 3)
    (F₂ : FolioSetRep (prefixRootFinset vList₂.length rList₂.length).card δ)
    (hrep₂ : IsDeltaFolioRep δ (tildeAMultiDigraph vList₂ eList₂)
      (prefixRootFinset vList₂.length rList₂.length) F₂) :
    folioRepCode q F₁ = folioRepCode q F₂ ↔
      ∃ hlen : rList₁.length = rList₂.length,
        GM13.HasSameDeltaFolio
          (GM13.rootedDigraphOfList D₁ rList₁ hroots₁)
          (hlen ▸ GM13.rootedDigraphOfList D₂ rList₂ hroots₂) δ := by
  let F₁' : FolioSetRep rList₁.length δ := card_prefixRootFinset hk₁ ▸ F₁
  let F₂' : FolioSetRep rList₂.length δ := card_prefixRootFinset hk₂ ▸ F₂
  have hcode₁ : folioRepCode q F₁ = folioRepCode q F₁' :=
    (folioRepCode_cast (card_prefixRootFinset hk₁) F₁).symm
  have hcode₂ : folioRepCode q F₂ = folioRepCode q F₂' :=
    (folioRepCode_cast (card_prefixRootFinset hk₂) F₂).symm
  rw [hcode₁, hcode₂, folioRepCode_eq_iff q hr₁_le hr₂_le F₁' F₂']
  refine exists_congr fun hlen =>
    folioRepCode_eq_iff_inFolio_cast hlen F₁' F₂' _ _
      (memIso_iff_inFolio_rootedDigraphOfList D₁ vList₁ eList₁ rList₁
        hv_nd₁ hv_set₁ he_nd₁ he_set₁ he_ends₁ hk₁ htake₁ hroots₁ F₁ hrep₁)
      (memIso_iff_inFolio_rootedDigraphOfList D₂ vList₂ eList₂ rList₂
        hv_nd₂ hv_set₂ he_nd₂ he_set₂ he_ends₂ hk₂ htake₂ hroots₂ F₂ hrep₂)

end GraphMinor.Compute
