module

public import GraphMinor.Compute.TwoPathsReduction
public import GraphMinor.Compute.TwoPathsUnion
public import GraphMinor.Compute.TwoPathsSweepLoop
public import GraphMinor.Compute.TwoPathsChild

/-!
# The edges of the frame that the input graph lacks

Section 1.2 of Humeau and Pous reduces the two disjoint paths problem on `G` with terminals
`s₁, t₁, s₂, t₂` to the question whether the cycle `s₁ s₂ t₁ t₂` is crossed in `G` plus the four
edges of that cycle (`isCrossed_frame_iff`, `TwoPathsReduction.lean`). To build the adjacency lists
of this graph with `unionProg` (`TwoPathsUnion.lean`), the program needs the list `F₀` of the
edges of the frame that `G` lacks, with no edge twice (`IsNewEdgeList`).

`frameEdgesProg` tests each of the four pairs with `adjTest` (a scan of one adjacency list), counts
the pairs that are not edges, allocates `aF` with twice that many entries, and writes these pairs
into it (`frameEdgesProg_exec`). The math is in the first part: a list of pairs `ps` written flat
(`pairsList ps`) is a list of new edges when its pairs are new and distinct
(`isNewEdgeList_pairsList`), and `G ⊔ pairGraph N F₀` is `G ⊔ frameGraph s₁ s₂ t₁ t₂`
(`sup_pairGraph_frame`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {N : ℕ}

/-! ### Lists of pairs -/

/-- A list of pairs, written flat. -/
def pairsList (ps : List (Fin N × Fin N)) : List ℕ := ps.flatMap fun p => [p.1.1, p.2.1]

theorem length_pairsList (ps : List (Fin N × Fin N)) : (pairsList ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairsList, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem pairsList_cons (p : Fin N × Fin N) (ps : List (Fin N × Fin N)) :
    pairsList (p :: ps) = p.1.1 :: p.2.1 :: pairsList ps := rfl

theorem pairsList_getElem? (ps : List (Fin N × Fin N)) (i : ℕ) :
    (pairsList ps)[2 * i]? = ps[i]?.map (fun p => p.1.1) ∧
      (pairsList ps)[2 * i + 1]? = ps[i]?.map (fun p => p.2.1) := by
  induction ps generalizing i with
  | nil => simp [pairsList]
  | cons p ps ih =>
    rcases i with _ | i
    · simp [pairsList_cons]
    · rw [pairsList_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
        show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl]
      simp only [List.getElem?_cons_succ]
      exact ih i

/-- A list of pairs that are new edges, no two of them the same edge, written flat, is a list of
new edges. -/
theorem isNewEdgeList_pairsList {G : SimpleGraph (Fin N)} {Pv : List (Fin N)}
    {ps : List (Fin N × Fin N)}
    (h₁ : ∀ p ∈ ps, p.1 ≠ p.2 ∧ p.1 ∈ Pv ∧ p.2 ∈ Pv ∧ ¬ G.Adj p.1 p.2)
    (h₂ : ps.Pairwise fun p q => ¬ ((p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1))) :
    IsNewEdgeList G Pv (pairsList ps) := by
  refine ⟨⟨ps.length, by rw [length_pairsList]; ring⟩, fun i hi => ?_, fun i j hij hj => ?_⟩
  · rw [length_pairsList] at hi
    have hi' : i < ps.length := by omega
    obtain ⟨e1, e2⟩ := pairsList_getElem? ps i
    obtain ⟨hne, hu, hv, hadj⟩ := h₁ ps[i] (List.getElem_mem hi')
    refine ⟨ps[i].1, ps[i].2, ?_, ?_, hne, hu, hv, hadj⟩
    · rw [e1, List.getElem?_eq_getElem hi']; rfl
    · rw [e2, List.getElem?_eq_getElem hi']; rfl
  · rw [length_pairsList] at hj
    have hj' : j < ps.length := by omega
    have hi' : i < ps.length := by omega
    obtain ⟨a1, a2⟩ := pairsList_getElem? ps i
    obtain ⟨b1, b2⟩ := pairsList_getElem? ps j
    rw [a1, a2, b1, b2, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj']
    have hp := List.pairwise_iff_getElem.mp h₂ i j hi' hj' hij
    simp only [Option.map_some, Option.some.injEq]
    intro h
    apply hp
    rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨Fin.ext e1, Fin.ext e2⟩
    · exact Or.inr ⟨Fin.ext e1, Fin.ext e2⟩

/-- The edges of the graph of a list of pairs written flat. -/
theorem pairGraph_pairsList_adj {ps : List (Fin N × Fin N)} {u v : Fin N} :
    (pairGraph N (pairsList ps)).Adj u v ↔
      u ≠ v ∧ ∃ p ∈ ps, (p.1 = u ∧ p.2 = v) ∨ (p.1 = v ∧ p.2 = u) := by
  simp only [pairGraph]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨i, h⟩
    obtain ⟨e1, e2⟩ := pairsList_getElem? ps i
    rw [e1, e2] at h
    rcases hp : ps[i]? with _ | p
    · rw [hp] at h; simp at h
    · rw [hp] at h
      refine ⟨p, List.mem_of_getElem? hp, ?_⟩
      simp only [Option.map_some, Option.some.injEq] at h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
      · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
  · rintro ⟨p, hp, h⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    refine ⟨i, ?_⟩
    obtain ⟨e1, e2⟩ := pairsList_getElem? ps i
    rw [e1, e2, List.getElem?_eq_getElem hi]
    simp only [Option.map_some, Option.some.injEq]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

/-! ### The frame -/

/-- The four pairs of the frame `s₁ s₂ t₁ t₂`. -/
def framePairs (s₁ s₂ t₁ t₂ : Fin N) : List (Fin N × Fin N) :=
  [(s₁, s₂), (s₂, t₁), (t₁, t₂), (t₂, s₁)]

/-- The pairs of the frame that are not edges of `G`. -/
def newFramePairs (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (s₁ s₂ t₁ t₂ : Fin N) :
    List (Fin N × Fin N) :=
  (framePairs s₁ s₂ t₁ t₂).filter fun p => ¬ G.Adj p.1 p.2

variable {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {s₁ s₂ t₁ t₂ : Fin N}

/-- The new pairs of the frame are a list of new edges on `s₁ s₂ t₁ t₂`. -/
theorem isNewEdgeList_frame (h₁ : s₁ ≠ t₁) (h₂ : s₁ ≠ s₂) (h₃ : s₁ ≠ t₂) (h₄ : t₁ ≠ s₂)
    (h₅ : t₁ ≠ t₂) (h₆ : s₂ ≠ t₂) :
    IsNewEdgeList G [s₁, s₂, t₁, t₂] (pairsList (newFramePairs G s₁ s₂ t₁ t₂)) := by
  apply isNewEdgeList_pairsList
  · intro p hp
    simp only [newFramePairs, framePairs, List.mem_filter, List.mem_cons, List.not_mem_nil,
      or_false, decide_eq_true_eq] at hp
    obtain ⟨hp, hadj⟩ := hp
    refine ⟨?_, ?_, ?_, hadj⟩ <;> rcases hp with rfl | rfl | rfl | rfl <;>
      simp [*, Ne.symm h₃, Ne.symm h₄]
  · apply List.Pairwise.filter
    simp only [framePairs, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
      simp [h₁, h₂, h₃, h₄, h₅, h₆, Ne.symm h₁, Ne.symm h₂, Ne.symm h₃, Ne.symm h₄,
        Ne.symm h₅, Ne.symm h₆]

/-- The edges of the frame are its four pairs. -/
theorem frameGraph_adj_iff {u v : Fin N} : (frameGraph s₁ s₂ t₁ t₂).Adj u v ↔
    u ≠ v ∧ ∃ p ∈ framePairs s₁ s₂ t₁ t₂, (p.1 = u ∧ p.2 = v) ∨ (p.1 = v ∧ p.2 = u) := by
  simp only [frameGraph, sup_adj, edge_adj, framePairs, List.exists_mem_cons,
    List.not_mem_nil, false_and, exists_false, or_false]
  constructor
  · intro h; aesop
  · intro h; aesop

/-- **The graph of Section 1.2.** `G` with the new pairs of the frame is `G` with the frame. -/
theorem sup_pairGraph_frame :
    G ⊔ pairGraph N (pairsList (newFramePairs G s₁ s₂ t₁ t₂)) = G ⊔ frameGraph s₁ s₂ t₁ t₂ := by
  ext u v
  rw [sup_adj, sup_adj, pairGraph_pairsList_adj, frameGraph_adj_iff]
  by_cases hG : G.Adj u v
  · simp [hG]
  have hG' : ¬ G.Adj v u := fun h => hG h.symm
  have key : ∀ p ∈ framePairs s₁ s₂ t₁ t₂, ((p.1 = u ∧ p.2 = v) ∨ (p.1 = v ∧ p.2 = u)) →
      p ∈ newFramePairs G s₁ s₂ t₁ t₂ := by
    intro p hp h
    simp only [newFramePairs, List.mem_filter, decide_eq_true_eq]
    refine ⟨hp, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> assumption
  simp only [hG, false_or]
  constructor
  · rintro ⟨hne, p, hp, h⟩; exact ⟨hne, p, (List.mem_filter.mp hp).1, h⟩
  · rintro ⟨hne, p, hp, h⟩; exact ⟨hne, p, key p hp h, h⟩

/-- The new pairs of the frame, written flat, pair by pair. -/
theorem pairsList_newFramePairs :
    pairsList (newFramePairs G s₁ s₂ t₁ t₂) =
      (if G.Adj s₁ s₂ then [] else [s₁.1, s₂.1]) ++ (if G.Adj s₂ t₁ then [] else [s₂.1, t₁.1]) ++
        (if G.Adj t₁ t₂ then [] else [t₁.1, t₂.1]) ++ (if G.Adj t₂ s₁ then [] else [t₂.1, s₁.1]) := by
  simp only [newFramePairs, framePairs]
  by_cases a : G.Adj s₁ s₂ <;> by_cases b : G.Adj s₂ t₁ <;> by_cases c : G.Adj t₁ t₂ <;>
    by_cases d : G.Adj t₂ s₁ <;> simp [a, b, c, d, List.filter, pairsList]

/-! ### The adjacency test -/

/-- The answer of the adjacency test. -/
abbrev rAdj : Reg := 150
/-- The cursor of the adjacency test. -/
abbrev rAk : Reg := 151
/-- The end of the list of the adjacency test. -/
abbrev rAhi : Reg := 152
/-- The first vertex of the adjacency test. -/
abbrev rAu : Reg := 153
/-- The second vertex of the adjacency test. -/
abbrev rAv : Reg := 154
/-- The cursor of `aF`. -/
abbrev rIdx : Reg := 159
/-- The length of `aF`. -/
abbrev rFCnt : Reg := 160

/-- One step of the scan: compare one neighbour of `rAu` with `rAv`. -/
def adjStep : Cmd :=
  .ite (.op .eq (.read aEnt (.reg rAk)) (.reg rAv)) (.assign rAdj (.const 1)) .skip

/-- **The adjacency test**: `rAdj := 1` if `rAv` is in the list of `rAu`, else `0`. -/
def adjTest : Cmd :=
  .seq (.assign rAdj (.const 0)) (.seq (.assign rAk (.read aStart (.reg rAu)))
    (.seq (.assign rAhi (.read aEnd (.reg rAu))) (forUp rAk (.reg rAhi) adjStep)))

theorem adjTest_exec {w : ℕ} (hw : 1 < 2 ^ w) (hNw : N < 2 ^ w) {G : SimpleGraph (Fin N)}
    [DecidableRel G.Adj] {lists : Fin N → List ℕ} {s : State} (hadj : IsAdjList G aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w) (u v : Fin N) (hu : s.regs rAu = u.1)
    (hv : s.regs rAv = v.1) :
    ∃ s' t, Exec w adjTest s s' t ∧ t ≤ 20 + 13 * N ∧ Keeps [rAdj, rAk, rAhi] [] s s' ∧
      s'.regs rAdj = if G.Adj u v then 1 else 0 := by
  classical
  obtain ⟨st0, en0, hu_st, hu_en, hen_ent, hdiff, hst, hen, hle, helem⟩ := hadj.1.2.2 u
  obtain ⟨hlt, -, hlenN, hiff⟩ := hadj.2 u
  set l := lists u with hl
  have huw : u.1 < 2 ^ w := by have := u.2; omega
  have hst_w : st0 < 2 ^ w := by omega
  have hen_w : en0 < 2 ^ w := by omega
  set s₁ := s.setReg rAdj 0 with hs₁
  set s₂ := s₁.setReg rAk st0 with hs₂
  set s₃ := s₂.setReg rAhi en0 with hs₃
  have hex₁ : Exec w (.assign rAdj (.const 0)) s s₁ (1 + 1) := .assign (const_eval' (by omega))
  have hex₂ : Exec w (.assign rAk (.read aStart (.reg rAu))) s₁ s₂ (1 + 1 + 1) := by
    have := read_eval (s := s₁) (a := aStart) (reg_eval (r := rAu) (by simp [s₁, hu]) huw)
      (by simpa [s₁] using hu_st) (by simp only [s₁, State.setReg_arrs]; rw [hst]; exact hst_w)
    simp only [s₁, State.setReg_arrs] at this
    rw [hst] at this
    exact .assign this
  have hex₃ : Exec w (.assign rAhi (.read aEnd (.reg rAu))) s₂ s₃ (1 + 1 + 1) := by
    have := read_eval (s := s₂) (a := aEnd) (reg_eval (r := rAu) (by simp [s₂, s₁, hu]) huw)
      (by simpa [s₂, s₁] using hu_en) (by simp only [s₂, s₁, State.setReg_arrs]; rw [hen]; exact hen_w)
    simp only [s₂, s₁, State.setReg_arrs] at this
    rw [hen] at this
    exact .assign this
  let I : ℕ → State → Prop := fun i st => Keeps [rAdj, rAk, rAhi] [] s st ∧ st.regs rAk = i ∧
    st.regs rAhi = en0 ∧ st0 ≤ i ∧ st.regs rAdj = if v.1 ∈ l.take (i - st0) then 1 else 0
  have hI₃ : I st0 s₃ := ⟨(((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg
    (by simp) _, by simp [s₃, s₂], by simp [s₃], le_rfl, by simp [s₃, s₂, s₁]⟩
  have hloop := forUp_pot I (fun _ => 0) en0 6 (r_i := rAk) (hi := .reg rAhi) (body := adjStep)
    hw hen_w (fun i _ st hst => ⟨hst.2.1, reg_eval hst.2.2.1 hen_w⟩)
    (fun i hi st hst => by
      obtain ⟨hk, hri, hrh, hsti, hra⟩ := hst
      have hEnt : st.arrs aEnt = s.arrs aEnt := hk.2 aEnt (by simp)
      have hkl : i - st0 < l.length := by omega
      have hx : (st.arrs aEnt)[i]'(by rw [hEnt]; omega) = l[i - st0] := by
        simp only [hEnt]
        have := helem (i - st0) hkl
        simp only [show st0 + (i - st0) = i by omega] at this
        exact this
      have hxw : l[i - st0] < N := hlt _ (List.getElem_mem hkl)
      have hrd : (Expr.read aEnt (.reg rAk)).eval w st = some l[i - st0] := by
        rw [read_eval (reg_eval hri (by omega)) (by rw [hEnt]; omega) (by rw [hx]; omega), hx]
      have hvv : (Expr.reg rAv).eval w st = some v.1 :=
        reg_eval (by rw [hk.1 rAv (by simp)]; exact hv) (by have := v.2; omega)
      have htake : l.take (i + 1 - st0) = l.take (i - st0) ++ [l[i - st0]] := by
        rw [show i + 1 - st0 = i - st0 + 1 by omega, List.take_add_one, List.getElem?_eq_getElem hkl]
        rfl
      by_cases heq : l[i - st0] = v.1
      · refine ⟨st.setReg rAdj 1, _, .ite_true (eq_eval hrd hvv hw) (by simp [heq])
          (.assign (const_eval' (by omega))), by simp only [Expr.cost]; omega,
          ⟨(hk.setReg (by simp) _).setReg (by simp) _, by simp, by simp [hrh], by omega, ?_⟩,
          by simp [hri]⟩
        simp only [State.setReg_regs_ne _ _ (show rAdj ≠ rAk by decide), State.setReg_regs_self]
        rw [htake, if_pos (List.mem_append_right _ (by simp [heq]))]
      · refine ⟨st, _, .ite_false (by rw [eq_eval hrd hvv hw]; simp [heq]) (.skip st),
          by simp only [Expr.cost]; omega,
          ⟨hk.setReg (by simp) _, by simp, by simp [hrh], by omega, ?_⟩, hri⟩
        simp only [State.setReg_regs_ne _ _ (show rAdj ≠ rAk by decide)]
        rw [hra, htake]
        simp only [List.mem_append, List.mem_singleton]
        simp [Ne.symm heq])
    st0 hle s₃ hI₃
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, -, -, -, hra₄⟩ := hloop
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hk₄, ?_⟩
  · simp only [Expr.cost] at ht₄ ⊢
    have : en0 - st0 ≤ N := by omega
    have : (en0 - st0) * 13 ≤ 13 * N := by omega
    nlinarith
  · rw [hra₄, show en0 - st0 = l.length by omega, List.take_length]
    by_cases h : G.Adj u v
    · simp [h, (hiff v).mpr h]
    · rw [if_neg h, if_neg (fun h' => h ((hiff v).mp h'))]

/-! ### The list of new edges of the frame -/

/-- Test whether the vertices in `x` and `y` are adjacent; `rb := 0` if so, else `1`. -/
def testPair (x y rb : Reg) : Cmd :=
  .seq (.assign rAu (.reg x)) (.seq (.assign rAv (.reg y)) (.seq adjTest
    (.assign rb (.op .sub (.const 1) (.reg rAdj)))))

theorem testPair_exec {w : ℕ} (hw : 1 < 2 ^ w) (hNw : N < 2 ^ w) {G : SimpleGraph (Fin N)}
    [DecidableRel G.Adj] {lists : Fin N → List ℕ} {s : State}
    (hadj : IsAdjList G aStart aEnd aEnt lists s) (hent : (s.arrs aEnt).length < 2 ^ w)
    (x y rb : ℕ) (a b : Fin N) (hx : s.regs x = a.1) (hy : s.regs y = b.1) (hxy : x < 100)
    (hyx : y < 100) :
    ∃ s' t, Exec w (testPair x y rb) s s' t ∧ t ≤ 30 + 13 * N ∧
      Keeps [rAu, rAv, rAdj, rAk, rAhi, rb] [] s s' ∧ s'.regs rb = if G.Adj a b then 0 else 1 := by
  have haw : a.1 < 2 ^ w := by have := a.2; omega
  have hbw : b.1 < 2 ^ w := by have := b.2; omega
  set s₁ := s.setReg rAu a.1 with hs₁
  set s₂ := s₁.setReg rAv b.1 with hs₂
  have hex₁ : Exec w (.assign rAu (.reg x)) s s₁ (1 + 1) := .assign (reg_eval hx haw)
  have hex₂ : Exec w (.assign rAv (.reg y)) s₁ s₂ (1 + 1) :=
    .assign (reg_eval (by rw [hs₁, State.setReg_regs_ne _ _ (show y ≠ 153 by omega)]; exact hy) hbw)
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hr₃⟩ := adjTest_exec (s := s₂) hw hNw
    (hadj.of_arrs_eq rfl rfl rfl) hent a b
    (by rw [hs₂, State.setReg_regs_ne _ _ (show rAu ≠ rAv by decide), hs₁, State.setReg_regs_self])
    (by rw [hs₂, State.setReg_regs_self])
  have hex₄ : Exec w (.assign rb (.op .sub (.const 1) (.reg rAdj))) s₃
      (s₃.setReg rb (1 - (if G.Adj a b then 1 else 0))) (1 + 1 + 1 + 1) :=
    .assign (sub_eval (const_eval' (by omega)) (reg_eval hr₃ (by split_ifs <;> omega)))
  refine ⟨_, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega, ?_,
    by simp only [State.setReg_regs_self]; split_ifs <;> rfl⟩
  have hk₂ : Keeps [rAu, rAv, rAdj, rAk, rAhi, rb] [] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _
  exact (hk₂.trans hk₃ (by simp) (by simp)).setReg (by simp) _

/-- If `rb = 1`, append the vertices in `x` and `y` to `aF` at the cursor `rIdx`. -/
def writePair (x y rb : Reg) : Cmd :=
  .ite (.op .eq (.reg rb) (.const 1))
    (.seq (.write aF (.reg rIdx) (.reg x)) (.seq (.write aF (.op .add (.reg rIdx) (.const 1))
      (.reg y)) (.assign rIdx (.op .add (.reg rIdx) (.const 2))))) .skip

theorem set_append_cons' (L R : List ℕ) (x v : ℕ) : (L ++ x :: R).set L.length v = L ++ v :: R := by
  induction L with
  | nil => simp
  | cons y L ih => simp [ih]

theorem writePair_exec {w : ℕ} (hw : 1 < 2 ^ w) (hNw : N < 2 ^ w) (x y rb : ℕ) (p : Prop)
    [Decidable p] (a b : Fin N) (L : List ℕ) (K : ℕ) (hKw : K < 2 ^ w) {s : State}
    (hb : s.regs rb = if p then 0 else 1) (hx : s.regs x = a.1) (hy : s.regs y = b.1)
    (hF : s.arrs aF = L ++ List.replicate (K - L.length) 0) (hi : s.regs rIdx = L.length)
    (hfit : L.length + (if p then 0 else 2) ≤ K) :
    ∃ s' t, Exec w (writePair x y rb) s s' t ∧ t ≤ 20 ∧ Keeps [rIdx] [aF] s s' ∧
      s'.arrs aF = (L ++ if p then [] else [a.1, b.1]) ++
        List.replicate (K - (L ++ if p then [] else [a.1, b.1]).length) 0 ∧
      s'.regs rIdx = (L ++ if p then [] else [a.1, b.1]).length := by
  have haw : a.1 < 2 ^ w := by have := a.2; omega
  have hbw : b.1 < 2 ^ w := by have := b.2; omega
  by_cases hp : p
  · simp only [hp, if_true] at hb ⊢
    refine ⟨s, _, .ite_false (by rw [eq_eval (reg_eval hb (by omega)) (const_eval' (by omega)) hw]; rfl)
      (.skip s), by simp only [Expr.cost]; omega, Keeps.refl _ _ s, by simpa using hF,
      by simpa using hi⟩
  · simp only [hp, if_false] at hb hfit ⊢
    have hrep : List.replicate (K - L.length) 0 =
        0 :: 0 :: List.replicate (K - (L.length + 2)) 0 := by
      rw [show K - L.length = K - (L.length + 2) + 1 + 1 by omega]; rfl
    set s₁ := s.writeArr aF L.length a.1 with hs₁
    have hex₁ : Exec w (.write aF (.reg rIdx) (.reg x)) s s₁ (1 + 1 + 1) :=
      .write (reg_eval hi (by omega)) (reg_eval hx haw) (by rw [hF]; simp; omega)
    have hF₁ : s₁.arrs aF = (L ++ [a.1]) ++ 0 :: List.replicate (K - (L.length + 2)) 0 := by
      simp only [s₁, State.writeArr_arrs_self, hF, hrep, set_append_cons']; simp
    set s₂ := s₁.writeArr aF (L.length + 1) b.1 with hs₂
    have hex₂ : Exec w (.write aF (.op .add (.reg rIdx) (.const 1)) (.reg y)) s₁ s₂
        (1 + 1 + 1 + 1 + 1) :=
      .write (add_eval (reg_eval (by simp [s₁, hi]) (by omega)) (const_eval' (by omega))
        (by omega)) (reg_eval (by simp [s₁, hy]) hbw) (by rw [hF₁]; simp; try omega)
    have hF₂ : s₂.arrs aF = (L ++ [a.1, b.1]) ++ List.replicate (K - (L.length + 2)) 0 := by
      simp only [s₂, State.writeArr_arrs_self, hF₁]
      rw [show L.length + 1 = (L ++ [a.1]).length by simp, set_append_cons']; simp
    set s₃ := s₂.setReg rIdx (L.length + 2) with hs₃
    have hex₃ : Exec w (.assign rIdx (.op .add (.reg rIdx) (.const 2))) s₂ s₃ (1 + 1 + 1 + 1) :=
      .assign (add_eval (reg_eval (by simp [s₂, s₁, hi]) (by omega)) (const_eval' (by omega))
        (by omega))
    refine ⟨s₃, _, .ite_true (eq_eval (reg_eval hb (by omega)) (const_eval' (by omega)) hw)
      (by simp) (.seq hex₁ (.seq hex₂ hex₃)), by simp only [Expr.cost]; omega,
      ((((Keeps.refl _ _ s).writeArr (by simp) _ _).writeArr (by simp) _ _).setReg (by simp) _),
      ?_, by simp [s₃]⟩
    simp only [s₃, State.setReg_arrs, hF₂, List.length_append, List.length_cons, List.length_nil]

/-- **The new edges of the frame**: test the four pairs, count the new ones, allocate `aF` and
write them. The terminals are in registers `31` (`s₁`), `32` (`t₁`), `33` (`s₂`), `34` (`t₂`). -/
def frameEdgesProg : Cmd :=
  .seq (testPair 31 33 155) (.seq (testPair 33 32 156) (.seq (testPair 32 34 157)
    (.seq (testPair 34 31 158)
    (.seq (.assign rFCnt (.op .mul (.const 2) (.op .add (.op .add (.reg 155) (.reg 156))
      (.op .add (.reg 157) (.reg 158)))))
    (.seq (.alloc aF (.reg rFCnt)) (.seq (.assign rIdx (.const 0))
    (.seq (writePair 31 33 155) (.seq (writePair 33 32 156) (.seq (writePair 32 34 157)
      (writePair 34 31 158))))))))))

/-- The registers that `frameEdgesProg` writes. -/
def frameEdgesRegs : List ℕ := [rAu, rAv, rAdj, rAk, rAhi, 155, 156, 157, 158, rFCnt, rIdx]

theorem length_ite_pair (p : Prop) [Decidable p] (x y : ℕ) :
    (if p then ([] : List ℕ) else [x, y]).length = 2 * (if p then 0 else 1) := by
  split_ifs <;> rfl

theorem ite_zero_two (p : Prop) [Decidable p] :
    (if p then 0 else 2) = 2 * (if p then 0 else 1) := by
  split_ifs <;> rfl

theorem frameEdgesProg_exec {w : ℕ} (hw : 1 < 2 ^ w) (hNw : 4 * N + 4 < 2 ^ w)
    {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {lists : Fin N → List ℕ} {s : State}
    (hadj : IsAdjList G aStart aEnd aEnt lists s) (hent : (s.arrs aEnt).length < 2 ^ w)
    (s₁ t₁ s₂ t₂ : Fin N) (h31 : s.regs 31 = s₁.1) (h32 : s.regs 32 = t₁.1)
    (h33 : s.regs 33 = s₂.1) (h34 : s.regs 34 = t₂.1) :
    ∃ s' t, Exec w frameEdgesProg s s' t ∧ t ≤ 250 + 52 * N ∧ Keeps frameEdgesRegs [aF] s s' ∧
      s'.arrs aF = pairsList (newFramePairs G s₁ s₂ t₁ t₂) := by
  have hN : N < 2 ^ w := by omega
  have k1 : ∀ {R : List ℕ} {s' : State}, Keeps R [] s s' → (∀ r ∈ R, 100 ≤ r) →
      IsAdjList G aStart aEnd aEnt lists s' ∧ (s'.arrs aEnt).length < 2 ^ w ∧
      s'.regs 31 = s₁.1 ∧ s'.regs 32 = t₁.1 ∧ s'.regs 33 = s₂.1 ∧ s'.regs 34 = t₂.1 :=
    fun {R s'} hk hR => by
      have hr : ∀ r : ℕ, r < 100 → s'.regs r = s.regs r := fun r hr =>
        hk.1 r (fun h => by have := hR r h; omega)
      refine ⟨hadj.of_arrs_eq (hk.2 _ (by simp)) (hk.2 _ (by simp)) (hk.2 _ (by simp)),
        by rw [hk.2 _ (by simp)]; exact hent, by rw [hr 31 (by omega)]; exact h31,
        by rw [hr 32 (by omega)]; exact h32, by rw [hr 33 (by omega)]; exact h33,
        by rw [hr 34 (by omega)]; exact h34⟩
  have hR100 : ∀ r ∈ frameEdgesRegs, 100 ≤ r := by decide
  have km : ∀ {R : List ℕ} {s' s'' : State}, Keeps frameEdgesRegs [] s s' → Keeps R [] s' s'' →
      (∀ r ∈ R, r ∈ frameEdgesRegs) → Keeps frameEdgesRegs [] s s'' :=
    fun h₁ h₂ hR => h₁.trans h₂ hR (fun _ h => h)
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := k1 (Keeps.refl frameEdgesRegs [] s) hR100
  obtain ⟨u₁, t₁', hx₁, ht₁, hk₁, hb₁⟩ := testPair_exec hw hN a₁ b₁ 31 33 155 s₁ s₂ c₁ e₁
    (by omega) (by omega)
  have K₁ := km (Keeps.refl _ _ s) hk₁ (by decide)
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := k1 K₁ hR100
  obtain ⟨u₂, t₂', hx₂, ht₂, hk₂, hb₂⟩ := testPair_exec hw hN a₂ b₂ 33 32 156 s₂ t₁ e₂ d₂
    (by omega) (by omega)
  have K₂ := km K₁ hk₂ (by decide)
  obtain ⟨a₃, b₃, c₃, d₃, e₃, f₃⟩ := k1 K₂ hR100
  obtain ⟨u₃, t₃', hx₃, ht₃, hk₃, hb₃⟩ := testPair_exec hw hN a₃ b₃ 32 34 157 t₁ t₂ d₃ f₃
    (by omega) (by omega)
  have K₃ := km K₂ hk₃ (by decide)
  obtain ⟨a₄, b₄, c₄, d₄, e₄, f₄⟩ := k1 K₃ hR100
  obtain ⟨u₄, t₄', hx₄, ht₄, hk₄, hb₄⟩ := testPair_exec hw hN a₄ b₄ 34 31 158 t₂ s₁ f₄ c₄
    (by omega) (by omega)
  have K₄ := km K₃ hk₄ (by decide)
  obtain ⟨-, -, c₅, d₅, e₅, f₅⟩ := k1 K₄ hR100
  -- The four answers.
  set q₁ := if G.Adj s₁ s₂ then 0 else 1 with hq₁
  set q₂ := if G.Adj s₂ t₁ then 0 else 1 with hq₂
  set q₃ := if G.Adj t₁ t₂ then 0 else 1 with hq₃
  set q₄ := if G.Adj t₂ s₁ then 0 else 1 with hq₄
  have hq₁' : q₁ ≤ 1 := by rw [hq₁]; split_ifs <;> omega
  have hq₂' : q₂ ≤ 1 := by rw [hq₂]; split_ifs <;> omega
  have hq₃' : q₃ ≤ 1 := by rw [hq₃]; split_ifs <;> omega
  have hq₄' : q₄ ≤ 1 := by rw [hq₄]; split_ifs <;> omega
  have r₁ : u₄.regs 155 = q₁ := by
    rw [hk₄.1 155 (by decide), hk₃.1 155 (by decide), hk₂.1 155 (by decide)]; exact hb₁
  have r₂ : u₄.regs 156 = q₂ := by
    rw [hk₄.1 156 (by decide), hk₃.1 156 (by decide)]; exact hb₂
  have r₃ : u₄.regs 157 = q₃ := by rw [hk₄.1 157 (by decide)]; exact hb₃
  have r₄ : u₄.regs 158 = q₄ := hb₄
  set K := 2 * ((q₁ + q₂) + (q₃ + q₄)) with hK
  have hKw : K < 2 ^ w := by omega
  set u₅ := u₄.setReg rFCnt K with hu₅
  have hx₅ : Exec w (.assign rFCnt (.op .mul (.const 2) (.op .add (.op .add (.reg 155) (.reg 156))
      (.op .add (.reg 157) (.reg 158))))) u₄ u₅ (1 + (1 + 1 + 1 + (1 + 1 + 1)) + 1 + 1 + 1) :=
    .assign (op_eval (const_eval' (by omega))
      (add_eval (add_eval (reg_eval r₁ (by omega)) (reg_eval r₂ (by omega)) (by omega))
        (add_eval (reg_eval r₃ (by omega)) (reg_eval r₄ (by omega)) (by omega)) (by omega))
      (by simp [BinOp.eval, BinOp.raw, checkWord]; omega))
  set u₆ := u₅.setArr aF (List.replicate K 0) with hu₆
  have hx₆ : Exec w (.alloc aF (.reg rFCnt)) u₅ u₆ (1 + K) :=
    .alloc (reg_eval (by simp [u₅]) hKw)
  set u₇ := u₆.setReg rIdx 0 with hu₇
  have hx₇ : Exec w (.assign rIdx (.const 0)) u₆ u₇ (1 + 1) := .assign (const_eval' (by omega))
  have K₇ : Keeps frameEdgesRegs [aF] s u₇ :=
    (((K₄.mono (fun _ h => h) (by simp)).setReg (by decide) _).setArr (by simp) _).setReg
      (by decide) _
  have hr7 : ∀ r : ℕ, r < 100 → u₇.regs r = s.regs r := fun r hr =>
    K₇.1 r (fun h => by have := hR100 r h; omega)
  have hb7 : ∀ r : ℕ, 155 ≤ r → r ≤ 158 → u₇.regs r = u₄.regs r := fun r h1 h2 => by
    simp only [u₇, u₆, u₅]
    rw [State.setReg_regs_ne _ _ (show r ≠ 159 by omega), State.setArr_regs,
      State.setReg_regs_ne _ _ (show r ≠ 160 by omega)]
  -- The writes.
  obtain ⟨v₁, w₁, hy₁, hw₁, hl₁, hF₁, hi₁⟩ := writePair_exec hw hN 31 33 155 (G.Adj s₁ s₂) s₁ s₂ []
    K hKw (by rw [hb7 155 le_rfl (by omega), r₁]) (by rw [hr7 31 (by omega)]; exact h31)
    (by rw [hr7 33 (by omega)]; exact h33) (by simp [u₇, u₆]) (by simp [u₇])
    (by simp only [List.length_nil, ite_zero_two, ← hq₁]; omega)
  have hv₁ : ∀ r : ℕ, r ≠ rIdx → v₁.regs r = u₇.regs r := fun r hr => hl₁.1 r (by simp [hr])
  obtain ⟨v₂, w₂, hy₂, hw₂, hl₂, hF₂, hi₂⟩ := writePair_exec hw hN 33 32 156 (G.Adj s₂ t₁) s₂ t₁
    _ K hKw (by rw [hv₁ 156 (by decide), hb7 156 (by omega) (by omega), r₂])
    (by rw [hv₁ 33 (by decide), hr7 33 (by omega)]; exact h33)
    (by rw [hv₁ 32 (by decide), hr7 32 (by omega)]; exact h32) hF₁ hi₁
    (by simp only [List.length_append, List.length_nil, length_ite_pair, ite_zero_two, ← hq₁, ← hq₂, ← hq₃,
      ← hq₄]; omega)
  have hv₂ : ∀ r : ℕ, r ≠ rIdx → v₂.regs r = u₇.regs r := fun r hr => by
    rw [hl₂.1 r (by simp [hr])]; exact hv₁ r hr
  obtain ⟨v₃, w₃, hy₃, hw₃, hl₃, hF₃, hi₃⟩ := writePair_exec hw hN 32 34 157 (G.Adj t₁ t₂) t₁ t₂
    _ K hKw (by rw [hv₂ 157 (by decide), hb7 157 (by omega) (by omega), r₃])
    (by rw [hv₂ 32 (by decide), hr7 32 (by omega)]; exact h32)
    (by rw [hv₂ 34 (by decide), hr7 34 (by omega)]; exact h34) hF₂ hi₂
    (by simp only [List.length_append, List.length_nil, length_ite_pair, ite_zero_two, ← hq₁, ← hq₂, ← hq₃,
      ← hq₄]; omega)
  have hv₃ : ∀ r : ℕ, r ≠ rIdx → v₃.regs r = u₇.regs r := fun r hr => by
    rw [hl₃.1 r (by simp [hr])]; exact hv₂ r hr
  obtain ⟨v₄, w₄, hy₄, hw₄, hl₄, hF₄, hi₄⟩ := writePair_exec hw hN 34 31 158 (G.Adj t₂ s₁) t₂ s₁
    _ K hKw (by rw [hv₃ 158 (by decide), hb7 158 (by omega) (by omega), r₄])
    (by rw [hv₃ 34 (by decide), hr7 34 (by omega)]; exact h34)
    (by rw [hv₃ 31 (by decide), hr7 31 (by omega)]; exact h31) hF₃ hi₃
    (by simp only [List.length_append, List.length_nil, length_ite_pair, ite_zero_two, ← hq₁, ← hq₂, ← hq₃,
      ← hq₄]; omega)
  refine ⟨v₄, _, .seq hx₁ (.seq hx₂ (.seq hx₃ (.seq hx₄ (.seq hx₅ (.seq hx₆ (.seq hx₇
    (.seq hy₁ (.seq hy₂ (.seq hy₃ hy₄))))))))), ?_, ?_, ?_⟩
  · omega
  · exact ((K₇.trans hl₁ (by decide) (by simp)).trans hl₂ (by decide) (by simp)).trans hl₃
      (by decide) (by simp) |>.trans hl₄ (by decide) (by simp)
  · rw [hF₄, pairsList_newFramePairs]
    simp only [List.length_append, List.length_nil, length_ite_pair, List.nil_append, ← hq₁,
      ← hq₂, ← hq₃, ← hq₄]
    rw [show K - (2 * q₁ + 2 * q₂ + 2 * q₃ + 2 * q₄) = 0 by omega, List.replicate_zero,
      List.append_nil]

end GraphMinor.Compute.TwoPaths
