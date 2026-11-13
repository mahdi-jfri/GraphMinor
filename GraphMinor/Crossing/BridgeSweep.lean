module

public import GraphMinor.Crossing.BridgeDefs

/-!
# Linear-time candidate sweep for cycle bridges (Section 5.2 of the note)

This file formalizes Section 5.2 of `docs/crossing/crossing_extractor.tex` ("Finding differently
colored alternating candidates in linear time"):

1. **Two stable counting sorts (`countingSort`, `sortCandidates`)**:
   "Sort the candidates by increasing \(l\), breaking ties by decreasing \(r\). Two stable
   counting sorts do this in linear time."
   We prove that `sortCandidates` returns a permutation of the input candidates that is pairwise
   ordered by increasing `l` and tie-broken by decreasing `r`, and runs in `2 * (c + cs.length)`
   bucket-pass steps.

2. **The stack of one-color blocks and sweep (`Block`, `cleanStack`, `firstDiffBlock`,
   `minRightCandidate`, `insertCandidate`, `sweepStep`, `sweepLoop`, `sweepCandidates`)**:
   We formalize invariants 1, 2 and 3 and steps 1–4 of Section 5.2 and prove soundness and
   completeness:
   `sweepCandidates` on a sorted candidate list returns `some (I', I)` with
   `I'.γ ≠ I.γ ∧ I'.l < I.l ∧ I.l < I'.r ∧ I'.r < I.r` if and only if the list contains two
   candidates of different colors with interleaving endpoints.

3. **The linear bound (block size at most six and single insertion/removal)**:
   "At any sweep position, one bridge has at most six active candidates. A cut of the cyclic
   attachment list at the sweep position separates it into two consecutive blocks. At most two
   pairs at cyclic distance one and four pairs at cyclic distance two cross this cut, counting
   duplicates. Therefore every stack block has size at most six. Each candidate is inserted once
   and removed at most once."
-/

@[expose] public section

namespace GraphMinor.Crossing

variable {α : Type*} {β : Type*}

/-! ### 1. Two stable counting sorts -/

/-- One pass of stable counting sort with `c` buckets `0, ..., c - 1` and key `key : α → ℕ`. -/
def countingSort (c : ℕ) (key : α → ℕ) (xs : List α) : List α :=
  (List.range c).flatMap (fun k => xs.filter (fun x => key x == k))

/-- Explicit step count of one counting-sort pass (`c` buckets plus `xs.length` elements). -/
def countingSortSteps (c : ℕ) (key : α → ℕ) (xs : List α) : ℕ :=
  let _ := key
  c + xs.length

/-- "Sort the candidates by increasing \(l\), breaking ties by decreasing \(r\). Two stable counting
sorts do this in linear time." (`docs/crossing/crossing_extractor.tex`, Section 5.2). -/
def sortCandidates (c : ℕ) (cs : List Candidate) : List Candidate :=
  let pass1 := countingSort c (fun I => c - 1 - I.r) cs
  countingSort c (fun I => I.l) pass1

/-- Total step count of the two stable counting-sort passes. -/
def sortCandidatesSteps (c : ℕ) (cs : List Candidate) : ℕ :=
  let pass1 := countingSort c (fun I => c - 1 - I.r) cs
  countingSortSteps c (fun I => c - 1 - I.r) cs + countingSortSteps c (fun I => I.l) pass1

/-- The target order of Section 5.2: increasing `l`, breaking ties by decreasing `r`. -/
def CandidateOrder (I₁ I₂ : Candidate) : Prop :=
  I₁.l < I₂.l ∨ (I₁.l = I₂.l ∧ I₂.r ≤ I₁.r)

theorem filter_key_eq_filter_not_key (key : α → ℕ) (xs : List α) {k j : ℕ} (hne : j ≠ k) :
    xs.filter (fun x => key x == j) =
      (xs.filter (fun x => !(key x == k))).filter (fun x => key x == j) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x _
  by_cases hxj : key x = j
  · simp [hxj, hne]
  · simp [hxj]

/-- Flat-mapping disjoint buckets over a nodup key list never exceeds `xs.length`. -/
theorem length_flatMap_filter_le (key : α → ℕ) {ks : List ℕ} (hnd : ks.Nodup) (xs : List α) :
    (ks.flatMap (fun k => xs.filter (fun x => key x == k))).length ≤ xs.length := by
  induction ks generalizing xs with
  | nil => simp
  | cons k ks' ih =>
    rw [List.flatMap_cons, List.length_append]
    have hnd_cons := List.nodup_cons.mp hnd
    have hcongr : ks'.flatMap (fun j => xs.filter (fun x => key x == j)) =
        ks'.flatMap (fun j => (xs.filter (fun x => !(key x == k))).filter (fun x => key x == j)) := by
      apply List.flatMap_congr
      intro j hj
      have hjk : j ≠ k := fun h => hnd_cons.1 (h ▸ hj)
      exact filter_key_eq_filter_not_key key xs hjk
    rw [hcongr]
    have hle := ih hnd_cons.2 (xs.filter (fun x => !(key x == k)))
    have hsum : (xs.filter (fun x => key x == k)).length +
        (xs.filter (fun x => !(key x == k))).length = xs.length := by
      rw [← List.length_append, (List.filter_append_perm (fun x => key x == k) xs).length_eq]
    omega

/-- When every element's key belongs to the nodup bucket list `ks`, flat-mapping the bucket filters
yields a permutation of `xs`. -/
theorem flatMap_filter_perm (key : α → ℕ) {ks : List ℕ} (hnd : ks.Nodup) (xs : List α)
    (hkeys : ∀ x ∈ xs, key x ∈ ks) :
    (ks.flatMap (fun k => xs.filter (fun x => key x == k))).Perm xs := by
  induction ks generalizing xs with
  | nil =>
    cases xs with
    | nil => simp
    | cons x _ => exact absurd (hkeys x List.mem_cons_self) List.not_mem_nil
  | cons k ks' ih =>
    rw [List.flatMap_cons]
    have hnd_cons := List.nodup_cons.mp hnd
    have hcongr : ks'.flatMap (fun j => xs.filter (fun x => key x == j)) =
        ks'.flatMap (fun j => (xs.filter (fun x => !(key x == k))).filter (fun x => key x == j)) := by
      apply List.flatMap_congr
      intro j hj
      have hjk : j ≠ k := fun h => hnd_cons.1 (h ▸ hj)
      exact filter_key_eq_filter_not_key key xs hjk
    rw [hcongr]
    have hkeys' : ∀ x ∈ xs.filter (fun x => !(key x == k)), key x ∈ ks' := by
      intro x hx
      rw [List.mem_filter] at hx
      rcases List.mem_cons.mp (hkeys x hx.1) with hxk | hmem
      · simp [hxk] at hx
      · exact hmem
    have hperm' := ih hnd_cons.2 (xs.filter (fun x => !(key x == k))) hkeys'
    exact (hperm'.append_left (xs.filter (fun x => key x == k))).trans
      (List.filter_append_perm (fun x => key x == k) xs)

/-- `countingSort` never increases the length of `xs`. -/
theorem length_countingSort_le (c : ℕ) (key : α → ℕ) (xs : List α) :
    (countingSort c key xs).length ≤ xs.length :=
  length_flatMap_filter_le key List.nodup_range xs

/-- When all keys are `< c`, `countingSort c key xs` is a permutation of `xs`. -/
theorem countingSort_perm (c : ℕ) (key : α → ℕ) (xs : List α) (hkeys : ∀ x ∈ xs, key x < c) :
    (countingSort c key xs).Perm xs := by
  apply flatMap_filter_perm key List.nodup_range xs
  intro x hx
  exact List.mem_range.mpr (hkeys x hx)

/-- Pairwise ordering of a `flatMap` over an ordered key list. -/
theorem pairwise_flatMap_of_pairwise {ks : List β} {f : β → List α} {R : α → α → Prop}
    {S : β → β → Prop} (hks : ks.Pairwise S)
    (h_in : ∀ k ∈ ks, (f k).Pairwise R)
    (h_between : ∀ k₁ ∈ ks, ∀ k₂ ∈ ks, S k₁ k₂ → ∀ x₁ ∈ f k₁, ∀ x₂ ∈ f k₂, R x₁ x₂) :
    (ks.flatMap f).Pairwise R := by
  induction ks with
  | nil => simp
  | cons k ks' ih =>
    rw [List.flatMap_cons, List.pairwise_append]
    have hks_cons := List.pairwise_cons.mp hks
    refine ⟨h_in k List.mem_cons_self, ?_, ?_⟩
    · exact ih hks_cons.2
        (fun k' hk' => h_in k' (List.mem_cons_of_mem k hk'))
        (fun k₁ hk₁ k₂ hk₂ hS => h_between k₁ (List.mem_cons_of_mem k hk₁)
          k₂ (List.mem_cons_of_mem k hk₂) hS)
    · intro x₁ hx₁ x₂ hx₂
      rw [List.mem_flatMap] at hx₂
      obtain ⟨k₂, hk₂, hx₂k⟩ := hx₂
      exact h_between k List.mem_cons_self k₂ (List.mem_cons_of_mem k hk₂)
        (hks_cons.1 k₂ hk₂) x₁ hx₁ x₂ hx₂k

/-- Stability and ordering of `countingSort`: if `xs` is pairwise ordered by `R₀`, then
`countingSort c key xs` is pairwise ordered by `R` whenever equal-key elements inherit `R` from `R₀`
and strictly increasing keys imply `R`. -/
theorem countingSort_pairwise (c : ℕ) (key : α → ℕ) (xs : List α)
    {R₀ R : α → α → Prop} (hR₀ : xs.Pairwise R₀)
    (h_eq : ∀ x₁ ∈ xs, ∀ x₂ ∈ xs, key x₁ = key x₂ → R₀ x₁ x₂ → R x₁ x₂)
    (h_lt : ∀ x₁ ∈ xs, ∀ x₂ ∈ xs, key x₁ < key x₂ → R x₁ x₂) :
    (countingSort c key xs).Pairwise R := by
  unfold countingSort
  apply pairwise_flatMap_of_pairwise List.pairwise_lt_range
  · intro k _
    have hfilt : (xs.filter (fun x => key x == k)).Pairwise R₀ := hR₀.filter _
    rw [List.pairwise_iff_getElem] at hfilt ⊢
    intro i j hi hj hij
    have hmem_i := List.mem_filter.mp (List.getElem_mem hi)
    have hmem_j := List.mem_filter.mp (List.getElem_mem hj)
    have hki : key (xs.filter (fun x => key x == k))[i] = k := by simpa using hmem_i.2
    have hkj : key (xs.filter (fun x => key x == k))[j] = k := by simpa using hmem_j.2
    exact h_eq _ hmem_i.1 _ hmem_j.1 (hki.trans hkj.symm) (hfilt i j hi hj hij)
  · intro k₁ _ k₂ _ hk x₁ hx₁ x₂ hx₂
    rw [List.mem_filter] at hx₁ hx₂
    have hk₁ : key x₁ = k₁ := by simpa using hx₁.2
    have hk₂ : key x₂ = k₂ := by simpa using hx₂.2
    exact h_lt x₁ hx₁.1 x₂ hx₂.1 (by omega)

/-- `sortCandidates` returns a permutation of `cs` when all endpoints are `< c`. -/
theorem sortCandidates_perm {c : ℕ} {cs : List Candidate}
    (hcs : ∀ I ∈ cs, I.l < c ∧ I.r < c) :
    (sortCandidates c cs).Perm cs := by
  unfold sortCandidates
  set pass1 := countingSort c (fun I => c - 1 - I.r) cs
  have hperm1 : pass1.Perm cs := by
    apply countingSort_perm
    intro I hI
    have hr := (hcs I hI).2
    omega
  have hperm2 : (countingSort c (fun I => I.l) pass1).Perm pass1 := by
    apply countingSort_perm
    intro I hI
    exact (hcs I (hperm1.subset hI)).1
  exact hperm2.trans hperm1

theorem pairwise_true (xs : List α) : xs.Pairwise (fun _ _ => True) := by
  induction xs with
  | nil => simp
  | cons _ _ ih => exact List.pairwise_cons.mpr ⟨fun _ _ => trivial, ih⟩

/-- `sortCandidates` orders the candidates by `CandidateOrder` (increasing `l`, tie-breaking by
decreasing `r`). -/
theorem sortCandidates_pairwise {c : ℕ} {cs : List Candidate}
    (hcs : ∀ I ∈ cs, I.l < c ∧ I.r < c) :
    (sortCandidates c cs).Pairwise CandidateOrder := by
  unfold sortCandidates
  set pass1 := countingSort c (fun I => c - 1 - I.r) cs
  have hpw1 : pass1.Pairwise (fun I₁ I₂ => I₂.r ≤ I₁.r) := by
    apply countingSort_pairwise c (fun I => c - 1 - I.r) cs (pairwise_true cs)
    · intro I₁ hI₁ I₂ hI₂ heq _
      have hr₁ := (hcs I₁ hI₁).2
      have hr₂ := (hcs I₂ hI₂).2
      omega
    · intro I₁ hI₁ I₂ hI₂ hlt
      have hr₁ := (hcs I₁ hI₁).2
      have hr₂ := (hcs I₂ hI₂).2
      omega
  apply countingSort_pairwise c (fun I => I.l) pass1 hpw1
  · intro I₁ _ I₂ _ heq hr
    exact Or.inr ⟨heq, hr⟩
  · intro I₁ _ I₂ _ hlt
    exact Or.inl hlt

/-- The step count of `sortCandidates` is at most `2 * (c + cs.length)`. -/
theorem sortCandidatesSteps_le (c : ℕ) (cs : List Candidate) :
    sortCandidatesSteps c cs ≤ 2 * (c + cs.length) := by
  dsimp only [sortCandidatesSteps, countingSortSteps]
  have hlen := length_countingSort_le c (fun I => c - 1 - I.r) cs
  omega

/-! ### 2. The sweep stack and algorithm (Section 5.2) -/

/-- A one-color block on the sweep stack (`docs/crossing/crossing_extractor.tex`, Section 5.2):
"We maintain a stack of blocks, each block containing candidates of one color". -/
structure Block where
  γ : ℕ
  items : List Candidate
  deriving DecidableEq, Repr

/-- All candidates currently stored in the stack `st`, from top block to bottom block. -/
def storedCandidates (st : List Block) : List Candidate :=
  st.flatMap Block.items

/-- Step 1 of the sweep (`docs/crossing/crossing_extractor.tex`, Section 5.2):
"Delete the candidates with right endpoint at most \(l\) from the top block. Pop the top block if
it becomes empty, and repeat with the new top block." -/
def cleanStack (l : ℕ) : List Block → List Block
  | [] => []
  | B :: rest =>
    let items' := B.items.filter (fun J => decide (l < J.r))
    if items'.isEmpty then
      cleanStack l rest
    else
      { γ := B.γ, items := items' } :: rest

/-- Step 2 of the sweep (`docs/crossing/crossing_extractor.tex`, Section 5.2):
"Let \(B\) be the first block from the top whose color differs from \(\gamma\). By invariant 1,
this is the top block or the second block." -/
def firstDiffBlock (γ : ℕ) : List Block → Option Block
  | [] => none
  | B₁ :: rest =>
    if B₁.γ != γ then some B₁
    else match rest with
      | [] => none
      | B₂ :: _ => if B₂.γ != γ then some B₂ else none

/-- Find the candidate in a list attaining the minimum right endpoint `r`. -/
def minRightCandidate : List Candidate → Option Candidate
  | [] => none
  | [J] => some J
  | J :: J₂ :: Js =>
    match minRightCandidate (J₂ :: Js) with
    | none => some J
    | some J' => if J.r ≤ J'.r then some J else some J'

/-- Step 4 of the sweep (`docs/crossing/crossing_extractor.tex`, Section 5.2):
"Otherwise, append \(I\) to the top block if its color is \(\gamma\), and push a new block
containing \(I\) if not." -/
def insertCandidate (I : Candidate) : List Block → List Block
  | [] => [{ γ := I.γ, items := [I] }]
  | B :: rest =>
    if B.γ == I.γ then
      { γ := B.γ, items := B.items ++ [I] } :: rest
    else
      { γ := I.γ, items := [I] } :: B :: rest

/-- Process a new candidate `I = (l, r, γ)` in the sweep (`docs/crossing/crossing_extractor.tex`,
Section 5.2). Returns `Sum.inr (J, I)` if Step 3 finds a crossing candidate `J` of a different
color, or `Sum.inl st'` with the updated stack after Step 4. -/
def sweepStep (st : List Block) (I : Candidate) : List Block ⊕ (Candidate × Candidate) :=
  let st₁ := cleanStack I.l st
  match firstDiffBlock I.γ st₁ with
  | some B =>
    match minRightCandidate B.items with
    | some J =>
      if J.r < I.r then Sum.inr (J, I)
      else Sum.inl (insertCandidate I st₁)
    | none => Sum.inl (insertCandidate I st₁)
  | none => Sum.inl (insertCandidate I st₁)

/-- Run the sweep over a list of candidates starting from stack `st`. -/
def sweepLoop : List Block → List Candidate → Option (Candidate × Candidate)
  | _, [] => none
  | st, I :: Is =>
    match sweepStep st I with
    | Sum.inr pair => some pair
    | Sum.inl st' => sweepLoop st' Is

/-- Complete sweep over a sorted list of candidates starting from the empty stack. -/
def sweepCandidates (cs : List Candidate) : Option (Candidate × Candidate) :=
  sweepLoop [] cs

/-! ### 3. Properties of `minRightCandidate` -/

theorem minRightCandidate_isSome {items : List Candidate} (h : items ≠ []) :
    (minRightCandidate items).isSome := by
  induction items with
  | nil => contradiction
  | cons J Js ih =>
    cases Js with
    | nil => rfl
    | cons J₂ Js' =>
      simp only [minRightCandidate]
      have hsub : (minRightCandidate (J₂ :: Js')).isSome := ih (List.cons_ne_nil J₂ Js')
      rcases Option.isSome_iff_exists.mp hsub with ⟨J', hJ'⟩
      rw [hJ']
      dsimp only
      split_ifs <;> rfl

theorem minRightCandidate_mem {items : List Candidate} {J' : Candidate}
    (h : minRightCandidate items = some J') : J' ∈ items := by
  induction items generalizing J' with
  | nil => simp [minRightCandidate] at h
  | cons J Js ih =>
    cases Js with
    | nil =>
      simp only [minRightCandidate, Option.some.injEq] at h
      subst h
      exact List.mem_singleton.mpr rfl
    | cons J₂ Js' =>
      simp only [minRightCandidate] at h
      cases hrec : minRightCandidate (J₂ :: Js') with
      | none =>
        rw [hrec] at h
        simp only [Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      | some K =>
        rw [hrec] at h
        dsimp only at h
        split_ifs at h with hle
        · simp only [Option.some.injEq] at h
          subst h
          exact List.mem_cons_self
        · simp only [Option.some.injEq] at h
          subst h
          exact List.mem_cons_of_mem J (ih hrec)

theorem minRightCandidate_le {items : List Candidate} {J' : Candidate}
    (h : minRightCandidate items = some J') : ∀ K ∈ items, J'.r ≤ K.r := by
  induction items generalizing J' with
  | nil => simp [minRightCandidate] at h
  | cons J Js ih =>
    cases Js with
    | nil =>
      simp only [minRightCandidate, Option.some.injEq] at h
      subst h
      intro K hK
      rcases List.mem_singleton.mp hK with rfl
      exact le_rfl
    | cons J₂ Js' =>
      simp only [minRightCandidate] at h
      have hne : J₂ :: Js' ≠ [] := List.cons_ne_nil J₂ Js'
      rcases Option.isSome_iff_exists.mp (minRightCandidate_isSome hne) with ⟨M, hM⟩
      rw [hM] at h
      dsimp only at h
      have hM_le := ih hM
      intro K hK
      split_ifs at h with hle
      · simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hK with rfl | hK'
        · exact le_rfl
        · exact le_trans hle (hM_le K hK')
      · simp only [Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hK with rfl | hK'
        · omega
        · exact hM_le K hK'

/-! ### 4. Stack invariants and correctness of the sweep -/

/-- Well-formedness of a single block: nonempty and monochromatic. -/
def BlockWellFormed (B : Block) : Prop :=
  B.items ≠ [] ∧ ∀ J ∈ B.items, J.γ = B.γ

/-- Invariant 1 of Section 5.2:
"Adjacent blocks have different colors." -/
def AdjDiffColor : List Block → Prop
  | [] => True
  | [_] => True
  | B₁ :: B₂ :: rest => B₁.γ ≠ B₂.γ ∧ AdjDiffColor (B₂ :: rest)

/-- Invariant 2 of Section 5.2:
"Every right endpoint in a block is at most every right endpoint in the block immediately below
it." -/
def BlockEndpointOrder : List Block → Prop
  | [] => True
  | [_] => True
  | B₁ :: B₂ :: rest =>
    (∀ J₁ ∈ B₁.items, ∀ J₂ ∈ B₂.items, J₁.r ≤ J₂.r) ∧ BlockEndpointOrder (B₂ :: rest)

/-- Invariant 3 of Section 5.2:
"Before a candidate with left endpoint \(l\) is processed, every stored candidate has right
endpoint greater than \(l\)." -/
def ActiveAbove (l : ℕ) (st : List Block) : Prop :=
  ∀ J ∈ storedCandidates st, l < J.r

/-- Bundled structural invariant of the stack `st`. -/
structure StackInv (st : List Block) : Prop where
  wf : ∀ B ∈ st, BlockWellFormed B
  adjDiff : AdjDiffColor st
  endpointOrder : BlockEndpointOrder st

theorem StackInv.nil : StackInv [] where
  wf := by simp
  adjDiff := trivial
  endpointOrder := trivial

theorem AdjDiffColor.tail {B : Block} {rest : List Block} (h : AdjDiffColor (B :: rest)) :
    AdjDiffColor rest := by
  cases rest with
  | nil => trivial
  | cons B₂ rest' => exact h.2

theorem BlockEndpointOrder.tail {B : Block} {rest : List Block}
    (h : BlockEndpointOrder (B :: rest)) : BlockEndpointOrder rest := by
  cases rest with
  | nil => trivial
  | cons B₂ rest' => exact h.2

theorem StackInv.tail {B : Block} {rest : List Block} (h : StackInv (B :: rest)) :
    StackInv rest where
  wf := fun B' hB' => h.wf B' (List.mem_cons_of_mem B hB')
  adjDiff := h.adjDiff.tail
  endpointOrder := h.endpointOrder.tail

/-- Because every block is nonempty, Invariant 2 (`BlockEndpointOrder`) is transitive across all
blocks in the stack. -/
theorem StackInv.pairwise_endpointOrder {st : List Block} (h : StackInv st) :
    st.Pairwise (fun B₁ B₂ => ∀ J₁ ∈ B₁.items, ∀ J₂ ∈ B₂.items, J₁.r ≤ J₂.r) := by
  induction st with
  | nil => simp
  | cons B₁ rest ih =>
    rw [List.pairwise_cons]
    refine ⟨?_, ih h.tail⟩
    intro B₂ hB₂
    cases rest with
    | nil => cases hB₂
    | cons B_mid rest' =>
      have hhead : ∀ J₁ ∈ B₁.items, ∀ Jm ∈ B_mid.items, J₁.r ≤ Jm.r := h.endpointOrder.1
      rcases List.mem_cons.mp hB₂ with rfl | hB₂_rest'
      · exact hhead
      · have hpw_tail := ih h.tail
        have hmid_B₂ : ∀ Jm ∈ B_mid.items, ∀ J₂ ∈ B₂.items, Jm.r ≤ J₂.r :=
          (List.pairwise_cons.mp hpw_tail).1 B₂ hB₂_rest'
        have hmid_ne : B_mid.items ≠ [] := (h.wf B_mid (by simp)).1
        obtain ⟨Jm, hJm⟩ := List.exists_mem_of_ne_nil B_mid.items hmid_ne
        intro J₁ hJ₁ J₂ hJ₂
        exact le_trans (hhead J₁ hJ₁ Jm hJm) (hmid_B₂ Jm hJm J₂ hJ₂)

/-- `cleanStack l st` preserves `StackInv`. -/
theorem cleanStack_stackInv (l : ℕ) {st : List Block} (h : StackInv st) :
    StackInv (cleanStack l st) := by
  induction st with
  | nil => exact StackInv.nil
  | cons B rest ih =>
    simp only [cleanStack]
    split_ifs with hemp
    · exact ih h.tail
    · have hne : B.items.filter (fun J => decide (l < J.r)) ≠ [] :=
        List.isEmpty_eq_false_iff.mp (Bool.eq_false_iff.mpr hemp)
      refine ⟨?_, ?_, ?_⟩
      · intro B' hB'
        rcases List.mem_cons.mp hB' with rfl | hB'_rest
        · refine ⟨hne, ?_⟩
          intro J hJ
          exact (h.wf B List.mem_cons_self).2 J (List.mem_filter.mp hJ).1
        · exact h.wf B' (List.mem_cons_of_mem B hB'_rest)
      · cases rest with
        | nil => trivial
        | cons B₂ rest' => exact ⟨h.adjDiff.1, h.adjDiff.2⟩
      · cases rest with
        | nil => trivial
        | cons B₂ rest' =>
          refine ⟨?_, h.endpointOrder.2⟩
          intro J₁ hJ₁ J₂ hJ₂
          exact h.endpointOrder.1 J₁ (List.mem_filter.mp hJ₁).1 J₂ hJ₂

/-- "Cleanup needs to inspect only the top block. If that block keeps an active candidate, then by
invariant 2 every right endpoint in every lower block is at least its right endpoint, so these
candidates are active too." (`docs/crossing/crossing_extractor.tex`, Section 5.2). Thus
`cleanStack l st` establishes invariant 3 (`ActiveAbove l`). -/
theorem cleanStack_activeAbove (l : ℕ) {st : List Block} (h : StackInv st) :
    ActiveAbove l (cleanStack l st) := by
  induction st with
  | nil => intro J hJ; cases hJ
  | cons B rest ih =>
    simp only [cleanStack]
    split_ifs with hemp
    · exact ih h.tail
    · have hne : B.items.filter (fun J => decide (l < J.r)) ≠ [] :=
        List.isEmpty_eq_false_iff.mp (Bool.eq_false_iff.mpr hemp)
      obtain ⟨J₀, hJ₀⟩ := List.exists_mem_of_ne_nil _ hne
      have hJ₀_mem : J₀ ∈ B.items := (List.mem_filter.mp hJ₀).1
      have hJ₀_lt : l < J₀.r := of_decide_eq_true (List.mem_filter.mp hJ₀).2
      intro J hJ
      simp only [storedCandidates, List.flatMap_cons, List.mem_append] at hJ
      rcases hJ with hJ_top | hJ_rest
      · exact of_decide_eq_true (List.mem_filter.mp hJ_top).2
      · rw [List.mem_flatMap] at hJ_rest
        obtain ⟨B₂, hB₂, hJB₂⟩ := hJ_rest
        have hpw := (List.pairwise_cons.mp h.pairwise_endpointOrder).1 B₂ hB₂
        have hle := hpw J₀ hJ₀_mem J hJB₂
        omega

/-- `cleanStack l st` retains exactly the stored candidates of `st` whose right endpoint is `> l`. -/
theorem mem_storedCandidates_cleanStack_iff (l : ℕ) {st : List Block} (h : StackInv st)
    (J : Candidate) :
    J ∈ storedCandidates (cleanStack l st) ↔ J ∈ storedCandidates st ∧ l < J.r := by
  constructor
  · intro hmem
    refine ⟨?_, cleanStack_activeAbove l h J hmem⟩
    induction st with
    | nil => exact hmem
    | cons B rest ih =>
      simp only [cleanStack] at hmem
      split_ifs at hmem with hemp
      · exact List.mem_append_right _ (ih h.tail hmem)
      · simp only [storedCandidates, List.flatMap_cons, List.mem_append] at hmem ⊢
        rcases hmem with htop | hrest
        · exact Or.inl (List.mem_filter.mp htop).1
        · exact Or.inr hrest
  · rintro ⟨hmem, hlt⟩
    induction st with
    | nil => cases hmem
    | cons B rest ih =>
      simp only [storedCandidates, List.flatMap_cons, List.mem_append] at hmem
      simp only [cleanStack]
      split_ifs with hemp
      · rcases hmem with hB | hrest
        · exfalso
          have hfilt : J ∈ B.items.filter (fun K => decide (l < K.r)) :=
            List.mem_filter.mpr ⟨hB, decide_eq_true hlt⟩
          rw [List.isEmpty_iff.mp hemp] at hfilt
          cases hfilt
        · exact ih h.tail hrest
      · simp only [storedCandidates, List.flatMap_cons, List.mem_append]
        rcases hmem with hB | hrest
        · exact Or.inl (List.mem_filter.mpr ⟨hB, decide_eq_true hlt⟩)
        · exact Or.inr hrest

/-- Stored candidates after `insertCandidate I st` are `I` together with `storedCandidates st`. -/
theorem mem_storedCandidates_insertCandidate_iff (I : Candidate) (st : List Block) (J : Candidate) :
    J ∈ storedCandidates (insertCandidate I st) ↔ J = I ∨ J ∈ storedCandidates st := by
  cases st with
  | nil =>
    simp [insertCandidate, storedCandidates]
  | cons B rest =>
    simp only [insertCandidate]
    split_ifs <;> simp [storedCandidates, or_left_comm]

/-- `firstDiffBlock γ st` returns a block `B ∈ st` with `B.γ ≠ γ`. -/
theorem firstDiffBlock_mem_and_ne {γ : ℕ} {st : List Block} {B : Block}
    (h : firstDiffBlock γ st = some B) : B ∈ st ∧ B.γ ≠ γ := by
  cases st with
  | nil => simp [firstDiffBlock] at h
  | cons B₁ rest =>
    simp only [firstDiffBlock] at h
    split_ifs at h with h₁
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨List.mem_cons_self, by simpa using h₁⟩
    · cases rest with
      | nil => simp at h
      | cons B₂ rest' =>
        dsimp only at h
        split_ifs at h with h₂
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨List.mem_cons_of_mem B₁ List.mem_cons_self, by simpa using h₂⟩

/-- Under `StackInv st`, if `st` contains any block `B' ∈ st` with `B'.γ ≠ γ`, then
`firstDiffBlock γ st` succeeds and returns a block `B` that is either `B'` itself or lies
strictly above `B'` (so every right endpoint in `B` is at most every right endpoint in `B'`). -/
theorem firstDiffBlock_le_of_mem {γ : ℕ} {st : List Block} (h : StackInv st)
    {B' : Block} (hB' : B' ∈ st) (hne : B'.γ ≠ γ) :
    ∃ B, firstDiffBlock γ st = some B ∧
      (B = B' ∨ ∀ J₁ ∈ B.items, ∀ J₂ ∈ B'.items, J₁.r ≤ J₂.r) := by
  cases st with
  | nil => cases hB'
  | cons B₁ rest =>
    simp only [firstDiffBlock]
    by_cases h₁ : (B₁.γ != γ) = true
    · simp only [h₁, ↓reduceIte]
      refine ⟨B₁, rfl, ?_⟩
      rcases List.mem_cons.mp hB' with rfl | hB'_rest
      · exact Or.inl rfl
      · exact Or.inr ((List.pairwise_cons.mp h.pairwise_endpointOrder).1 B' hB'_rest)
    · simp only [h₁, Bool.false_eq_true, ↓reduceIte]
      have hB₁_eq : B₁.γ = γ := by simpa using h₁
      rcases List.mem_cons.mp hB' with rfl | hB'_rest
      · exact absurd hB₁_eq hne
      · cases rest with
        | nil => cases hB'_rest
        | cons B₂ rest' =>
          dsimp only
          have hadj : B₁.γ ≠ B₂.γ := h.adjDiff.1
          have h₂ : (B₂.γ != γ) = true := by
            rw [bne_iff_ne]
            intro hB₂_eq
            exact hadj (hB₁_eq.trans hB₂_eq.symm)
          simp only [h₂, ↓reduceIte]
          refine ⟨B₂, rfl, ?_⟩
          rcases List.mem_cons.mp hB'_rest with rfl | hB'_rest'
          · exact Or.inl rfl
          · exact Or.inr ((List.pairwise_cons.mp h.tail.pairwise_endpointOrder).1 B' hB'_rest')

/-- "The endpoint-order invariant 2 makes the tested minimum no greater than the right endpoint of
any stored candidate of a different color." (`docs/crossing/crossing_extractor.tex`,
Section 5.2). -/
theorem firstDiffBlock_min_le_of_mem {γ : ℕ} {st : List Block} (h : StackInv st)
    {J' : Candidate} (hJ' : J' ∈ storedCandidates st) (hne : J'.γ ≠ γ) :
    ∃ B J_min, firstDiffBlock γ st = some B ∧
      minRightCandidate B.items = some J_min ∧ J_min.r ≤ J'.r := by
  simp only [storedCandidates, List.mem_flatMap] at hJ'
  obtain ⟨B', hB', hJ'B'⟩ := hJ'
  have hB'_γ : B'.γ ≠ γ := by
    have hJ'_eq : J'.γ = B'.γ := (h.wf B' hB').2 J' hJ'B'
    rwa [← hJ'_eq]
  obtain ⟨B, hfirst, hB_rel⟩ := firstDiffBlock_le_of_mem h hB' hB'_γ
  have hB_mem : B ∈ st := (firstDiffBlock_mem_and_ne hfirst).1
  have hB_ne : B.items ≠ [] := (h.wf B hB_mem).1
  obtain ⟨J_min, hmin⟩ := Option.isSome_iff_exists.mp (minRightCandidate_isSome hB_ne)
  refine ⟨B, J_min, hfirst, hmin, ?_⟩
  rcases hB_rel with rfl | hle
  · exact minRightCandidate_le hmin J' hJ'B'
  · exact hle J_min (minRightCandidate_mem hmin) J' hJ'B'

/-- "A failed test also gives exactly the inequality needed to preserve invariant 2 when appending
or pushing." (`docs/crossing/crossing_extractor.tex`, Section 5.2). -/
theorem insertCandidate_stackInv (I : Candidate) {st : List Block} (h : StackInv st)
    (h_no_cross : ∀ B J_min, firstDiffBlock I.γ st = some B →
      minRightCandidate B.items = some J_min → I.r ≤ J_min.r) :
    StackInv (insertCandidate I st) := by
  cases st with
  | nil =>
    simp only [insertCandidate]
    refine ⟨?_, trivial, trivial⟩
    intro B hB
    rcases List.mem_singleton.mp hB with rfl
    exact ⟨List.cons_ne_nil I [], fun J hJ => by rcases List.mem_singleton.mp hJ with rfl; rfl⟩
  | cons B₁ rest =>
    simp only [insertCandidate]
    by_cases hγ : (B₁.γ == I.γ) = true
    · simp only [hγ, ↓reduceIte]
      have hB₁_eq : B₁.γ = I.γ := by simpa using hγ
      refine ⟨?_, ?_, ?_⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB_rest
        · refine ⟨by simp, ?_⟩
          intro J hJ
          rcases List.mem_append.mp hJ with hJB₁ | hJI
          · exact (h.wf B₁ List.mem_cons_self).2 J hJB₁
          · rcases List.mem_singleton.mp hJI with rfl
            exact hB₁_eq.symm
        · exact h.wf B (List.mem_cons_of_mem B₁ hB_rest)
      · cases rest with
        | nil => trivial
        | cons B₂ rest' => exact ⟨h.adjDiff.1, h.adjDiff.2⟩
      · cases rest with
        | nil => trivial
        | cons B₂ rest' =>
          refine ⟨?_, h.endpointOrder.2⟩
          intro J₁ hJ₁ J₂ hJ₂
          rcases List.mem_append.mp hJ₁ with hJ₁B₁ | hJ₁I
          · exact h.endpointOrder.1 J₁ hJ₁B₁ J₂ hJ₂
          · have hJ₁_eq : J₁ = I := List.mem_singleton.mp hJ₁I
            rw [hJ₁_eq]
            have hadj : B₁.γ ≠ B₂.γ := h.adjDiff.1
            have hB₂_ne : B₂.γ ≠ I.γ := by omega
            have hfirst : firstDiffBlock I.γ (B₁ :: B₂ :: rest') = some B₂ := by
              simp [firstDiffBlock, hB₁_eq, hB₂_ne]
            have hB₂_items_ne : B₂.items ≠ [] := (h.wf B₂ (by simp)).1
            obtain ⟨J_min, hmin⟩ :=
              Option.isSome_iff_exists.mp (minRightCandidate_isSome hB₂_items_ne)
            have hI_le := h_no_cross B₂ J_min hfirst hmin
            have hmin_le := minRightCandidate_le hmin J₂ hJ₂
            exact le_trans hI_le hmin_le
    · simp only [hγ, Bool.false_eq_true, ↓reduceIte]
      have hB₁_ne : B₁.γ ≠ I.γ := by simpa using hγ
      have hfirst : firstDiffBlock I.γ (B₁ :: rest) = some B₁ := by
        simp [firstDiffBlock, hB₁_ne]
      have hB₁_items_ne : B₁.items ≠ [] := (h.wf B₁ List.mem_cons_self).1
      obtain ⟨J_min, hmin⟩ :=
        Option.isSome_iff_exists.mp (minRightCandidate_isSome hB₁_items_ne)
      have hI_le := h_no_cross B₁ J_min hfirst hmin
      refine ⟨?_, ⟨hB₁_ne.symm, h.adjDiff⟩, ?_⟩
      · intro B hB
        rcases List.mem_cons.mp hB with rfl | hB_rest
        · exact ⟨List.cons_ne_nil I [], fun J hJ => by
            rcases List.mem_singleton.mp hJ with rfl; rfl⟩
        · exact h.wf B hB_rest
      · refine ⟨?_, h.endpointOrder⟩
        intro J₁ hJ₁ J₂ hJ₂
        rcases List.mem_singleton.mp hJ₁ with rfl
        exact le_trans hI_le (minRightCandidate_le hmin J₂ hJ₂)

/-- Two candidates `J` and `I` have different colors and strictly interleaving endpoints
`J.l < I.l < J.r < I.r`. -/
def InterleavingDiffColor (J I : Candidate) : Prop :=
  J.γ ≠ I.γ ∧ J.l < I.l ∧ I.l < J.r ∧ J.r < I.r

/-- Characterization of a single step `sweepStep st I`:
- If it returns `Sum.inr (J, I')`, then `I' = I`, `J ∈ storedCandidates st`, `I.l < J.r`,
  `J.r < I.r`, and `J.γ ≠ I.γ`.
- If it returns `Sum.inl st'`, then `StackInv st'`, `storedCandidates st'` consists of `I` and
  all `J ∈ storedCandidates st` with `I.l < J.r`, and no `J ∈ storedCandidates st` has
  `J.γ ≠ I.γ ∧ I.l < J.r ∧ J.r < I.r`. -/
theorem sweepStep_spec {st : List Block} (h : StackInv st) (I : Candidate) :
    match sweepStep st I with
    | Sum.inr (J, I') =>
      I' = I ∧ J ∈ storedCandidates st ∧ J.γ ≠ I.γ ∧ I.l < J.r ∧ J.r < I.r
    | Sum.inl st' =>
      StackInv st' ∧
      (∀ J, J ∈ storedCandidates st' ↔ J = I ∨ (J ∈ storedCandidates st ∧ I.l < J.r)) ∧
      (∀ J ∈ storedCandidates st, J.γ ≠ I.γ → I.l < J.r → I.r ≤ J.r) := by
  have hst₁ : StackInv (cleanStack I.l st) := cleanStack_stackInv I.l h
  have hmem₁ : ∀ J, J ∈ storedCandidates (cleanStack I.l st) ↔ J ∈ storedCandidates st ∧ I.l < J.r :=
    mem_storedCandidates_cleanStack_iff I.l h
  dsimp only [sweepStep]
  cases hfirst : firstDiffBlock I.γ (cleanStack I.l st) with
  | none =>
    dsimp only
    have hno_cross : ∀ B J_min, firstDiffBlock I.γ (cleanStack I.l st) = some B →
        minRightCandidate B.items = some J_min → I.r ≤ J_min.r := by
      intro B _ hB; rw [hfirst] at hB; cases hB
    refine ⟨insertCandidate_stackInv I hst₁ hno_cross, ?_, ?_⟩
    · intro J
      rw [mem_storedCandidates_insertCandidate_iff, hmem₁]
    · intro J hJ hγ hlt
      exfalso
      have hJ₁ : J ∈ storedCandidates (cleanStack I.l st) := (hmem₁ J).mpr ⟨hJ, hlt⟩
      obtain ⟨B, _, hB, _, _⟩ := firstDiffBlock_min_le_of_mem hst₁ hJ₁ hγ
      rw [hfirst] at hB
      cases hB
  | some B =>
    dsimp only
    have hB_info := firstDiffBlock_mem_and_ne hfirst
    cases hmin : minRightCandidate B.items with
    | none =>
      exfalso
      have hB_ne : B.items ≠ [] := (hst₁.wf B hB_info.1).1
      have hisSome := minRightCandidate_isSome hB_ne
      rw [hmin] at hisSome
      cases hisSome
    | some J_min =>
      dsimp only
      split_ifs with hlt_r
      · dsimp only
        have hJ_in_B : J_min ∈ B.items := minRightCandidate_mem hmin
        have hJ_in_st₁ : J_min ∈ storedCandidates (cleanStack I.l st) :=
          List.mem_flatMap.mpr ⟨B, hB_info.1, hJ_in_B⟩
        have hJ_γ : J_min.γ = B.γ := (hst₁.wf B hB_info.1).2 J_min hJ_in_B
        refine ⟨rfl, (hmem₁ J_min).mp hJ_in_st₁ |>.1, ?_, (hmem₁ J_min).mp hJ_in_st₁ |>.2, hlt_r⟩
        rw [hJ_γ]
        exact hB_info.2
      · dsimp only
        have hle_r : I.r ≤ J_min.r := Nat.le_of_not_lt hlt_r
        have hno_cross : ∀ B' J', firstDiffBlock I.γ (cleanStack I.l st) = some B' →
            minRightCandidate B'.items = some J' → I.r ≤ J'.r := by
          intro B' J' hB' hJ'
          rw [hfirst] at hB'
          cases hB'
          rw [hmin] at hJ'
          cases hJ'
          exact hle_r
        refine ⟨insertCandidate_stackInv I hst₁ hno_cross, ?_, ?_⟩
        · intro J
          rw [mem_storedCandidates_insertCandidate_iff, hmem₁]
        · intro J hJ hγ hlt
          have hJ₁ : J ∈ storedCandidates (cleanStack I.l st) := (hmem₁ J).mpr ⟨hJ, hlt⟩
          obtain ⟨B', J', hB', hJ', hJ'_le⟩ := firstDiffBlock_min_le_of_mem hst₁ hJ₁ hγ
          rw [hfirst] at hB'
          cases hB'
          rw [hmin] at hJ'
          cases hJ'
          exact le_trans hle_r hJ'_le

/-- Soundness of `sweepLoop`: if `sweepLoop st rem = some (J, I)` where `st` satisfies `StackInv`
and every candidate in `st` precedes every candidate in `rem` under `CandidateOrder`, then
`InterleavingDiffColor J I`. -/
theorem sweepLoop_sound {st : List Block} {rem : List Candidate} {J I : Candidate}
    (hst : StackInv st) (hpw : rem.Pairwise CandidateOrder)
    (h_prev : ∀ K ∈ storedCandidates st, ∀ M ∈ rem, CandidateOrder K M)
    (heq : sweepLoop st rem = some (J, I)) :
    (J ∈ storedCandidates st ∨ J ∈ rem) ∧ I ∈ rem ∧ InterleavingDiffColor J I := by
  induction rem generalizing st with
  | nil => simp [sweepLoop] at heq
  | cons M Ms ih =>
    simp only [sweepLoop] at heq
    have hspec := sweepStep_spec hst M
    have hpw_cons := List.pairwise_cons.mp hpw
    cases hstep : sweepStep st M with
    | inr pair =>
      rw [hstep] at heq hspec
      rcases pair with ⟨J₀, I₀⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨hJ₀, hI₀⟩
      subst hJ₀; subst hI₀
      rcases hspec with ⟨hI₀_eq, hJ_st, hγ, hl_lt, hr_lt⟩
      subst hI₀_eq
      have hord : CandidateOrder J₀ I₀ := h_prev J₀ hJ_st I₀ List.mem_cons_self
      have hl_strict : J₀.l < I₀.l := by
        rcases hord with hlt | ⟨_, hr_ge⟩
        · exact hlt
        · omega
      exact ⟨Or.inl hJ_st, List.mem_cons_self, hγ, hl_strict, hl_lt, hr_lt⟩
    | inl st' =>
      rw [hstep] at heq hspec
      rcases hspec with ⟨hst', hmem', _⟩
      have h_prev' : ∀ K ∈ storedCandidates st', ∀ M' ∈ Ms, CandidateOrder K M' := by
        intro K hK M' hM'
        rcases (hmem' K).mp hK with rfl | ⟨hK_st, _⟩
        · exact hpw_cons.1 M' hM'
        · exact h_prev K hK_st M' (List.mem_cons_of_mem M hM')
      obtain ⟨hJ_mem, hI_mem, hinter⟩ := ih hst' hpw_cons.2 h_prev' heq
      refine ⟨?_, List.mem_cons_of_mem M hI_mem, hinter⟩
      rcases hJ_mem with hJ_st' | hJ_Ms
      · rcases (hmem' J).mp hJ_st' with rfl | ⟨hJ_st, _⟩
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hJ_st
      · exact Or.inr (List.mem_cons_of_mem M hJ_Ms)

/-- Completeness of `sweepLoop`: if `sweepLoop st rem = none`, then no stored candidate `J` (or
candidate `J` in `rem` appearing before `I ∈ rem`) can interleave with `I` with different colors. -/
theorem sweepLoop_complete {st : List Block} {rem : List Candidate}
    (hst : StackInv st) (hpw : rem.Pairwise CandidateOrder)
    (hnone : sweepLoop st rem = none) :
    (∀ J ∈ storedCandidates st, ∀ I ∈ rem, ¬ InterleavingDiffColor J I) ∧
    ∀ i j (hi : i < rem.length) (hj : j < rem.length),
      i < j → ¬ InterleavingDiffColor rem[i] rem[j] := by
  induction rem generalizing st with
  | nil =>
    refine ⟨by simp, ?_⟩
    intro i _ hi
    simp at hi
  | cons M Ms ih =>
    simp only [sweepLoop] at hnone
    have hspec := sweepStep_spec hst M
    have hpw_cons := List.pairwise_cons.mp hpw
    cases hstep : sweepStep st M with
    | inr pair =>
      rw [hstep] at hnone
      cases hnone
    | inl st' =>
      rw [hstep] at hnone hspec
      rcases hspec with ⟨hst', hmem', hno_M⟩
      obtain ⟨hno_st', hno_Ms⟩ := ih hst' hpw_cons.2 hnone
      refine ⟨?_, ?_⟩
      · intro J hJ I hI hinter
        rcases List.mem_cons.mp hI with rfl | hI_Ms
        · have hle := hno_M J hJ hinter.1 hinter.2.2.1
          exact absurd hinter.2.2.2 (not_lt_of_ge hle)
        · have hord : CandidateOrder M I := hpw_cons.1 I hI_Ms
          have hM_le_I : M.l ≤ I.l := by
            rcases hord with hlt | ⟨heq, _⟩ <;> omega
          have hM_lt_Jr : M.l < J.r := lt_of_le_of_lt hM_le_I hinter.2.2.1
          have hJ_st' : J ∈ storedCandidates st' :=
            (hmem' J).mpr (Or.inr ⟨hJ, hM_lt_Jr⟩)
          exact hno_st' J hJ_st' I hI_Ms hinter
      · intro i j hi hj hij
        cases i with
        | zero =>
          cases j with
          | zero => omega
          | succ j' =>
            have hj' : j' < Ms.length := by simp at hj; omega
            have hM_st' : M ∈ storedCandidates st' := (hmem' M).mpr (Or.inl rfl)
            exact hno_st' M hM_st' Ms[j'] (List.getElem_mem hj')
        | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
            have hi' : i' < Ms.length := by simp at hi; omega
            have hj' : j' < Ms.length := by simp at hj; omega
            exact hno_Ms i' j' hi' hj' (by omega)

/-- Soundness of `sweepCandidates` (`docs/crossing/crossing_extractor.tex`, Section 5.2):
"In step 3, the returned earlier candidate \((l',r',\gamma')\) satisfies" \(l'<l<r'<r\). "The
strict inequality \(l'<l\) follows from the tie-breaking order: an earlier candidate with the same
left endpoint would have right endpoint at least \(r\)." -/
theorem sweepCandidates_sound {cs : List Candidate} {J I : Candidate}
    (hpw : cs.Pairwise CandidateOrder) (heq : sweepCandidates cs = some (J, I)) :
    J ∈ cs ∧ I ∈ cs ∧ InterleavingDiffColor J I := by
  have h := sweepLoop_sound StackInv.nil hpw (by simp [storedCandidates]) heq
  rcases h with ⟨hJ, hI, hinter⟩
  simp only [storedCandidates, List.flatMap_nil, List.not_mem_nil, false_or] at hJ
  exact ⟨hJ, hI, hinter⟩

/-- Completeness of `sweepCandidates` (`docs/crossing/crossing_extractor.tex`, Section 5.2):
"Thus a failed test excludes every differently colored crossing between the new candidate and a
stored one." -/
theorem sweepCandidates_complete {cs : List Candidate}
    (hpw : cs.Pairwise CandidateOrder)
    {J I : Candidate} (hJ : J ∈ cs) (hI : I ∈ cs) (hinter : InterleavingDiffColor J I) :
    (sweepCandidates cs).isSome := by
  by_contra hnot
  have hnone : sweepCandidates cs = none := Option.not_isSome_iff_eq_none.mp hnot
  have hcomp := (sweepLoop_complete StackInv.nil hpw hnone).2
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hJ
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hI
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hcomp i j hi hj hij hinter
  · exact Nat.lt_irrefl _ hinter.2.1
  · have hord : CandidateOrder cs[j] cs[i] := List.pairwise_iff_getElem.mp hpw j i hj hi hji
    have hle : cs[j].l ≤ cs[i].l := by
      rcases hord with hlt | ⟨heq, _⟩ <;> omega
    exact absurd hinter.2.1 (not_lt_of_ge hle)

/-- `sweepCandidates` on a sorted candidate list returns `some` pair of differently colored
interleaving candidates if and only if such a pair exists in `cs`. -/
theorem sweepCandidates_isSome_iff {cs : List Candidate} (hpw : cs.Pairwise CandidateOrder) :
    (sweepCandidates cs).isSome ↔ ∃ J ∈ cs, ∃ I ∈ cs, InterleavingDiffColor J I := by
  constructor
  · intro his
    obtain ⟨⟨J, I⟩, heq⟩ := Option.isSome_iff_exists.mp his
    obtain ⟨hJ, hI, hinter⟩ := sweepCandidates_sound hpw heq
    exact ⟨J, hJ, I, hI, hinter⟩
  · rintro ⟨J, hJ, I, hI, hinter⟩
    exact sweepCandidates_complete hpw hJ hI hinter

/-! ### 5. Linear bound: block size at most six and single insertion/removal -/

/-- In a nodup list `L`, filtering for equality with `s` leaves at most 1 element. -/
theorem length_filter_beq_le_one [DecidableEq α] {L : List α} (hnd : L.Nodup) (s : α) :
    (L.filter (fun x => x == s)).length ≤ 1 := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    have hnd_cons := List.nodup_cons.mp hnd
    rw [List.filter_cons]
    split_ifs with h
    · have hds : hd = s := by simpa using h
      subst hds
      have hempty : tl.filter (fun x => x == hd) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx heq
        have hxhd : x = hd := by simpa using heq
        exact hnd_cons.1 (hxhd ▸ hx)
      simp [hempty]
    · exact ih hnd_cons.2

/-- If `L` is nodup and every element of `L` belongs to `S`, then `L.length ≤ S.length`. -/
theorem nodup_length_le_of_subset [DecidableEq α] {L S : List α} (hnd : L.Nodup)
    (hsub : ∀ x ∈ L, x ∈ S) : L.length ≤ S.length := by
  induction S generalizing L with
  | nil =>
    cases L with
    | nil => simp
    | cons x _ => exact absurd (hsub x List.mem_cons_self) List.not_mem_nil
  | cons s S' ih =>
    have hperm := List.filter_append_perm (fun x => x == s) L
    have hlen : L.length =
        (L.filter (fun x => x == s)).length + (L.filter (fun x => !(x == s))).length := by
      rw [← List.length_append, hperm.length_eq]
    have hle1 : (L.filter (fun x => x == s)).length ≤ 1 := length_filter_beq_le_one hnd s
    have hnd' : (L.filter (fun x => !(x == s))).Nodup := hnd.filter _
    have hsub' : ∀ x ∈ L.filter (fun x => !(x == s)), x ∈ S' := by
      intro x hx
      rw [List.mem_filter] at hx
      rcases List.mem_cons.mp (hsub x hx.1) with rfl | hxS'
      · simp at hx
      · exact hxS'
    have hle2 := ih hnd' hsub'
    simp only [List.length_cons]
    omega

/-- In a strictly increasing list `t`, `t[j] ≤ l₀` holds if and only if `j` is less than the
number of elements of `t` that are `≤ l₀`. -/
theorem getElem_le_iff_lt_filter_length {t : List ℕ} (ht : t.Pairwise (· < ·)) (l₀ : ℕ)
    {j : ℕ} (hj : j < t.length) :
    t[j] ≤ l₀ ↔ j < (t.filter (fun x => decide (x ≤ l₀))).length := by
  induction t generalizing j with
  | nil => simp at hj
  | cons hd tl ih =>
    have ht_cons := List.pairwise_cons.mp ht
    rw [List.filter_cons]
    by_cases hhd : hd ≤ l₀
    · simp only [decide_eq_true hhd, ↓reduceIte, List.length_cons]
      cases j with
      | zero => simp [hhd]
      | succ j' =>
        have hj' : j' < tl.length := by simp at hj; omega
        simp only [List.getElem_cons_succ]
        rw [ih ht_cons.2 hj']
        omega
    · simp only [decide_eq_false hhd, Bool.false_eq_true, ↓reduceIte]
      have hempty : tl.filter (fun x => decide (x ≤ l₀)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have hlt : hd < x := ht_cons.1 x hx
        simp; omega
      rw [hempty, List.length_nil]
      have hgt : l₀ < (hd :: tl)[j] := by
        cases j with
        | zero => simp; omega
        | succ j' =>
          have hj' : j' < tl.length := by simp at hj; omega
          have hlt : hd < tl[j'] := ht_cons.1 tl[j'] (List.getElem_mem hj')
          simp; omega
      omega

/-- Lift a boolean predicate `P` to `Option β` (`false` on `none`). -/
def optionPred (P : β → Bool) : Option β → Bool
  | some y => P y
  | none => false

@[simp] theorem optionPred_none (P : β → Bool) : optionPred P none = false := rfl

@[simp] theorem optionPred_some (P : β → Bool) (y : β) : optionPred P (some y) = P y := rfl

/-- Length of a filtered `filterMap` is bounded by the length of the corresponding filtered input
list. -/
theorem length_filter_filterMap_le (P : β → Bool) (f : α → Option β) (xs : List α) :
    ((xs.filterMap f).filter P).length ≤
      (xs.filter (fun x => optionPred P (f x))).length := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    cases fx : f x with
    | none =>
      simp [fx, ih]
    | some y =>
      cases hPy : P y <;> simp [fx, hPy, ih]

/-- "At most two pairs at cyclic distance one" cross the cut at a sweep position
(`docs/crossing/crossing_extractor.tex`, Section 5.2, paragraph "Linear bound"). -/
theorem length_active_stepCandidates_one_le {t : List ℕ} (ht : t.Pairwise (· < ·)) (l₀ : ℕ) :
    ((stepCandidates 1 t).filter
      (fun p => decide (min p.1 p.2 ≤ l₀ ∧ l₀ < max p.1 p.2))).length ≤ 2 := by
  unfold stepCandidates
  set P : ℕ × ℕ → Bool := fun p => decide (min p.1 p.2 ≤ l₀ ∧ l₀ < max p.1 p.2)
  set f : ℕ → Option (ℕ × ℕ) := fun i =>
    if h : 0 < t.length then
      let a := t[i % t.length]'(Nat.mod_lt _ h)
      let b := t[(i + 1) % t.length]'(Nat.mod_lt _ h)
      if a = b then none else some (a, b)
    else none
  have hle1 := length_filter_filterMap_le P f (List.range t.length)
  set m := (t.filter (fun x => decide (x ≤ l₀))).length
  have hm_le : m ≤ t.length := List.length_filter_le _ _
  have hsub : ∀ i ∈ (List.range t.length).filter (fun x => optionPred P (f x)),
      i ∈ ([m - 1, t.length - 1] : List ℕ) := by
    intro i hi
    rw [List.mem_filter, List.mem_range] at hi
    rcases hi with ⟨hi_lt, hfi⟩
    have hpos : 0 < t.length := by omega
    simp only [f, hpos, ↓reduceDIte] at hfi
    split_ifs at hfi with heq
    · simp [optionPred] at hfi
    simp only [optionPred] at hfi
    set a := t[i % t.length]'(Nat.mod_lt _ hpos)
    set b := t[(i + 1) % t.length]'(Nat.mod_lt _ hpos)
    have hP : min a b ≤ l₀ ∧ l₀ < max a b := of_decide_eq_true hfi
    have himod : i % t.length = i := Nat.mod_eq_of_lt hi_lt
    have ha_iff : a ≤ l₀ ↔ i % t.length < m :=
      getElem_le_iff_lt_filter_length ht l₀ (Nat.mod_lt i hpos)
    have hb_iff : b ≤ l₀ ↔ (i + 1) % t.length < m :=
      getElem_le_iff_lt_filter_length ht l₀ (Nat.mod_lt (i + 1) hpos)
    have hcross : (i < m ∧ m ≤ (i + 1) % t.length) ∨ ((i + 1) % t.length < m ∧ m ≤ i) := by
      by_cases ha : a ≤ l₀
      · by_cases hb : b ≤ l₀
        · exfalso; have : max a b ≤ l₀ := max_le ha hb; omega
        · left
          exact ⟨himod ▸ ha_iff.mp ha, Nat.le_of_not_lt (mt hb_iff.mpr hb)⟩
      · by_cases hb : b ≤ l₀
        · right
          exact ⟨hb_iff.mp hb, himod ▸ Nat.le_of_not_lt (mt ha_iff.mpr ha)⟩
        · exfalso
          have : l₀ < min a b := lt_min (by omega) (by omega)
          omega
    have hj_cases : (i + 1 < t.length ∧ (i + 1) % t.length = i + 1) ∨
        (i = t.length - 1 ∧ (i + 1) % t.length = 0) := by
      by_cases hlt : i + 1 < t.length
      · left; exact ⟨hlt, Nat.mod_eq_of_lt hlt⟩
      · right
        have heq_len : i + 1 = t.length := by omega
        refine ⟨by omega, ?_⟩
        rw [heq_len, Nat.mod_self]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hj_cases with ⟨_, hj_eq⟩ | ⟨hi_eq, hj_eq⟩ <;> omega
  have hle2 := nodup_length_le_of_subset (List.nodup_range.filter _) hsub
  exact le_trans hle1 hle2

/-- At most "four pairs at cyclic distance two cross this cut, counting duplicates."
(`docs/crossing/crossing_extractor.tex`, Section 5.2, paragraph "Linear bound"). -/
theorem length_active_stepCandidates_two_le {t : List ℕ} (ht : t.Pairwise (· < ·)) (l₀ : ℕ) :
    ((stepCandidates 2 t).filter
      (fun p => decide (min p.1 p.2 ≤ l₀ ∧ l₀ < max p.1 p.2))).length ≤ 4 := by
  unfold stepCandidates
  set P : ℕ × ℕ → Bool := fun p => decide (min p.1 p.2 ≤ l₀ ∧ l₀ < max p.1 p.2)
  set f : ℕ → Option (ℕ × ℕ) := fun i =>
    if h : 0 < t.length then
      let a := t[i % t.length]'(Nat.mod_lt _ h)
      let b := t[(i + 2) % t.length]'(Nat.mod_lt _ h)
      if a = b then none else some (a, b)
    else none
  have hle1 := length_filter_filterMap_le P f (List.range t.length)
  set m := (t.filter (fun x => decide (x ≤ l₀))).length
  have hm_le : m ≤ t.length := List.length_filter_le _ _
  have hsub : ∀ i ∈ (List.range t.length).filter (fun x => optionPred P (f x)),
      i ∈ ([m - 2, m - 1, t.length - 2, t.length - 1] : List ℕ) := by
    intro i hi
    rw [List.mem_filter, List.mem_range] at hi
    rcases hi with ⟨hi_lt, hfi⟩
    have hpos : 0 < t.length := by omega
    simp only [f, hpos, ↓reduceDIte] at hfi
    split_ifs at hfi with heq
    · simp [optionPred] at hfi
    simp only [optionPred] at hfi
    set a := t[i % t.length]'(Nat.mod_lt _ hpos)
    set b := t[(i + 2) % t.length]'(Nat.mod_lt _ hpos)
    have hP : min a b ≤ l₀ ∧ l₀ < max a b := of_decide_eq_true hfi
    have himod : i % t.length = i := Nat.mod_eq_of_lt hi_lt
    have ha_iff : a ≤ l₀ ↔ i % t.length < m :=
      getElem_le_iff_lt_filter_length ht l₀ (Nat.mod_lt i hpos)
    have hb_iff : b ≤ l₀ ↔ (i + 2) % t.length < m :=
      getElem_le_iff_lt_filter_length ht l₀ (Nat.mod_lt (i + 2) hpos)
    have hcross : (i < m ∧ m ≤ (i + 2) % t.length) ∨ ((i + 2) % t.length < m ∧ m ≤ i) := by
      by_cases ha : a ≤ l₀
      · by_cases hb : b ≤ l₀
        · exfalso; have : max a b ≤ l₀ := max_le ha hb; omega
        · left
          exact ⟨himod ▸ ha_iff.mp ha, Nat.le_of_not_lt (mt hb_iff.mpr hb)⟩
      · by_cases hb : b ≤ l₀
        · right
          exact ⟨hb_iff.mp hb, himod ▸ Nat.le_of_not_lt (mt ha_iff.mpr ha)⟩
        · exfalso
          have : l₀ < min a b := lt_min (by omega) (by omega)
          omega
    have hj_cases : (i + 2 < t.length ∧ (i + 2) % t.length = i + 2) ∨
        i = t.length - 2 ∨ i = t.length - 1 := by
      by_cases hlt : i + 2 < t.length
      · left; exact ⟨hlt, Nat.mod_eq_of_lt hlt⟩
      · right; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hj_cases with ⟨_, hj_eq⟩ | hi_eq | hi_eq <;> omega
  have hle2 := nodup_length_le_of_subset (List.nodup_range.filter _) hsub
  exact le_trans hle1 hle2

/-- "At any sweep position, one bridge has at most six active candidates."
(`docs/crossing/crossing_extractor.tex`, Section 5.2). -/
theorem length_active_candidatesOfIndices_le (γ : ℕ) {t : List ℕ} (ht : t.Pairwise (· < ·))
    (l₀ : ℕ) :
    ((candidatesOfIndices γ t).filter (fun I => decide (I.l ≤ l₀ ∧ l₀ < I.r))).length ≤ 6 := by
  unfold candidatesOfIndices attachmentCandidates
  rw [List.filter_map, List.length_map, List.filter_append, List.length_append]
  have h1 := length_active_stepCandidates_one_le ht l₀
  have h2 := length_active_stepCandidates_two_le ht l₀
  exact Nat.add_le_add h1 h2

/-- Every block `B ∈ st` has `B.items` a sublist of the stored candidates of color `B.γ`. -/
theorem Block.items_sublist_storedCandidates_filter {st : List Block} (hst : StackInv st)
    {B : Block} (hB : B ∈ st) :
    B.items.Sublist ((storedCandidates st).filter (fun J => J.γ == B.γ)) := by
  have hsub : B.items.Sublist (storedCandidates st) := by
    unfold storedCandidates
    induction st with
    | nil => cases hB
    | cons B₁ rest ih =>
      rw [List.flatMap_cons]
      rcases List.mem_cons.mp hB with rfl | hB_rest
      · exact List.sublist_append_left B.items _
      · exact (ih hst.tail hB_rest).trans (List.sublist_append_right _ _)
  have hfilt := hsub.filter (fun J => J.γ == B.γ)
  have heq : B.items.filter (fun J => J.γ == B.γ) = B.items := by
    rw [List.filter_eq_self]
    intro J hJ
    simp [(hst.wf B hB).2 J hJ]
  rwa [heq] at hfilt

/-- `cleanStack l st` produces a sublist of `storedCandidates st`. -/
theorem storedCandidates_cleanStack_sublist (l : ℕ) (st : List Block) :
    (storedCandidates (cleanStack l st)).Sublist (storedCandidates st) := by
  induction st with
  | nil => simp [cleanStack, storedCandidates]
  | cons B rest ih =>
    simp only [cleanStack]
    split_ifs with hemp
    · exact ih.trans (List.sublist_append_right B.items (storedCandidates rest))
    · simp only [storedCandidates, List.flatMap_cons]
      exact (List.filter_sublist).append (List.Sublist.refl _)

/-- `insertCandidate I st` increases `(storedCandidates st).length` by 1. -/
theorem length_storedCandidates_insertCandidate (I : Candidate) (st : List Block) :
    (storedCandidates (insertCandidate I st)).length = (storedCandidates st).length + 1 := by
  cases st with
  | nil => simp [insertCandidate, storedCandidates]
  | cons B rest =>
    simp only [insertCandidate]
    split_ifs
    · simp [storedCandidates]; omega
    · simp [storedCandidates]

/-- "Therefore every stack block has size at most six." (`docs/crossing/crossing_extractor.tex`,
Section 5.2): Whenever the stored candidates of color `B.γ` in `st` have count at most the active
candidates of `candidatesOfIndices B.γ t` at sweep position `l₀` (where `t.Pairwise (· < ·)`), every
block `B` in `st` of color `B.γ` has `B.items.length ≤ 6`. -/
theorem Block.length_items_le_six {st : List Block} (hst : StackInv st)
    {B : Block} (hB : B ∈ st) {t : List ℕ} (ht : t.Pairwise (· < ·)) (l₀ : ℕ)
    (hle : ((storedCandidates st).filter (fun J => J.γ == B.γ)).length ≤
      ((candidatesOfIndices B.γ t).filter (fun I => decide (I.l ≤ l₀ ∧ l₀ < I.r))).length) :
    B.items.length ≤ 6 := by
  have h1 := (Block.items_sublist_storedCandidates_filter hst hB).length_le
  exact le_trans h1 (le_trans hle (length_active_candidatesOfIndices_le B.γ ht l₀))

/-- Total number of candidate insertions performed during `sweepLoop`. -/
def sweepInsertions : List Block → List Candidate → ℕ
  | _, [] => 0
  | st, I :: Is =>
    match sweepStep st I with
    | Sum.inr _ => 0
    | Sum.inl st' => 1 + sweepInsertions st' Is

/-- Total number of candidate removals performed by `cleanStack` during `sweepLoop`. -/
def sweepRemovals : List Block → List Candidate → ℕ
  | _, [] => 0
  | st, I :: Is =>
    let st₁ := cleanStack I.l st
    let removed := (storedCandidates st).length - (storedCandidates st₁).length
    match sweepStep st I with
    | Sum.inr _ => removed
    | Sum.inl st' => removed + sweepRemovals st' Is

/-- "Each candidate is inserted once and removed at most once."
(`docs/crossing/crossing_extractor.tex`, Section 5.2): In `sweepLoop st cs`, the total number of
insertions is at most `cs.length`. -/
theorem sweepInsertions_le (st : List Block) (cs : List Candidate) :
    sweepInsertions st cs ≤ cs.length := by
  induction cs generalizing st with
  | nil => simp [sweepInsertions]
  | cons I Is ih =>
    simp only [sweepInsertions, List.length_cons]
    rcases hstep : sweepStep st I with st' | _
    · dsimp only
      have := ih st'
      omega
    · dsimp only
      omega

/-- "Each candidate is inserted once and removed at most once."
(`docs/crossing/crossing_extractor.tex`, Section 5.2): In `sweepLoop st cs`, the total number of
candidate removals is at most `(storedCandidates st).length + cs.length` (so at most `cs.length`
when starting from `st = []`). -/
theorem sweepRemovals_le (st : List Block) (cs : List Candidate) :
    sweepRemovals st cs ≤ (storedCandidates st).length + cs.length := by
  induction cs generalizing st with
  | nil => simp [sweepRemovals]
  | cons I Is ih =>
    simp only [sweepRemovals, List.length_cons]
    have hsub : (storedCandidates (cleanStack I.l st)).length ≤ (storedCandidates st).length :=
      (storedCandidates_cleanStack_sublist I.l st).length_le
    rcases hstep : sweepStep st I with st' | _
    · dsimp only
      have hst' : st' = insertCandidate I (cleanStack I.l st) := by
        dsimp only [sweepStep] at hstep
        cases hfirst : firstDiffBlock I.γ (cleanStack I.l st) with
        | none =>
          rw [hfirst] at hstep
          exact Sum.inl.inj hstep.symm
        | some B =>
          rw [hfirst] at hstep
          dsimp only at hstep
          cases hmin : minRightCandidate B.items with
          | none =>
            rw [hmin] at hstep
            exact Sum.inl.inj hstep.symm
          | some J =>
            rw [hmin] at hstep
            dsimp only at hstep
            split_ifs at hstep
            exact Sum.inl.inj hstep.symm
      have hlen_st' :
          (storedCandidates st').length = (storedCandidates (cleanStack I.l st)).length + 1 := by
        rw [hst', length_storedCandidates_insertCandidate]
      have hrec := ih st'
      omega
    · dsimp only
      omega

end GraphMinor.Crossing
