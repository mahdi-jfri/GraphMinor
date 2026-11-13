module

public import GraphMinor.Compute.PlanarityRamLayout

/-!
# Frames for the linked lists and block stacks of the solver

The solver of Part I, Sections 3 to 6 of the planarity note changes memory by
a few word writes at a time. A list, a block stack or a summary is read only
at its own addresses, so it survives every write elsewhere. This file makes
that precise.

A `Frame s s' W` says that `s'` agrees with `s` at every cell `(a, q)` (array
`a`, index `q`) outside the set `W`, and that no array changes length. Frames
compose, and a single write is a frame for its one cell. Each representation
of `PlanarityRamLayout.lean` then survives a frame that avoids its cells
(`NodeChain.frame`, `ListAt.frame`, `BlockChain.frame`, `SummaryAt.frame`).

The file also proves the facts about linked lists that the list operations
use: the first and last depths, the tail of a list, the concatenation of two
lists by one pointer write (`ListAt.append`), and the push of a block
(`BlockChain.push`).
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- `s'` agrees with `s` outside the cells of `W`, and every array keeps its
length. -/
def Frame (s s' : State) (W : ℕ → ℕ → Prop) : Prop :=
  ∀ a, (s'.arrs a).length = (s.arrs a).length ∧
    ∀ q, ¬ W a q → (s'.arrs a)[q]? = (s.arrs a)[q]?

/-- The cells of the three node arrays at address `q`. -/
def NodeCell (W : ℕ → ℕ → Prop) (q : ℕ) : Prop :=
  W Field.nodeEdge.array q ∨ W Field.nodeDepth.array q ∨ W Field.nodeNext.array q

/-- The cells of the five block arrays at address `q`. -/
def BlockCell (W : ℕ → ℕ → Prop) (q : ℕ) : Prop :=
  W Field.blockLeftFirst.array q ∨ W Field.blockLeftLast.array q ∨
    W Field.blockRightFirst.array q ∨ W Field.blockRightLast.array q ∨
    W Field.blockBelow.array q

/-- The cells of the four summary arrays at address `q`. -/
def SummaryCell (W : ℕ → ℕ → Prop) (q : ℕ) : Prop :=
  W Field.summaryLeast.array q ∨ W Field.summaryFirst.array q ∨
    W Field.summaryLast.array q ∨ W Field.summaryTop.array q

theorem Frame.refl (s : State) (W : ℕ → ℕ → Prop) : Frame s s W :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem Frame.trans {s s₁ s₂ : State} {W₁ W₂ : ℕ → ℕ → Prop}
    (h₁ : Frame s s₁ W₁) (h₂ : Frame s₁ s₂ W₂) :
    Frame s s₂ (fun a q => W₁ a q ∨ W₂ a q) := by
  intro a
  refine ⟨(h₂ a).1.trans (h₁ a).1, fun q hq => ?_⟩
  rw [(h₂ a).2 q (fun h => hq (Or.inr h)), (h₁ a).2 q (fun h => hq (Or.inl h))]

theorem Frame.mono {s s' : State} {W W' : ℕ → ℕ → Prop} (h : Frame s s' W)
    (hW : ∀ a q, W a q → W' a q) : Frame s s' W' :=
  fun a => ⟨(h a).1, fun q hq => (h a).2 q (fun h' => hq (hW a q h'))⟩

theorem Frame.setReg (s : State) (r v : ℕ) (W : ℕ → ℕ → Prop) :
    Frame s (s.setReg r v) W :=
  fun _ => ⟨rfl, fun _ _ => rfl⟩

theorem Frame.of_arrs_eq {s s' : State} (h : s'.arrs = s.arrs) (W : ℕ → ℕ → Prop) :
    Frame s s' W := by
  intro a
  rw [h]
  exact ⟨rfl, fun _ _ => rfl⟩

/-- One write changes only its own cell. -/
theorem Frame.writeArr (s : State) (a i v : ℕ) :
    Frame s (s.writeArr a i v) (fun a' q => a' = a ∧ q = i) := by
  intro a'
  by_cases ha : a' = a
  · subst ha
    refine ⟨by simp, fun q hq => ?_⟩
    have hne : i ≠ q := fun h => hq ⟨rfl, h.symm⟩
    simp [List.getElem?_set_ne hne]
  · exact ⟨by simp [ha], fun q _ => by simp [ha]⟩

/-- A frame keeps the value of a cell outside its set. -/
theorem Frame.get {s s' : State} {W : ℕ → ℕ → Prop} (h : Frame s s' W) {a q : ℕ}
    (hq : ¬ W a q) : (s'.arrs a)[q]? = (s.arrs a)[q]? :=
  (h a).2 q hq

/-! ### Node chains and lists -/

/-- Every address of a chain is a positive index below the capacity. -/
theorem NodeChain.mem_bounds {s : State} {cap p : ℕ} {A : List ℕ} {l : List ReturnNode}
    (h : NodeChain s cap p A l) : ∀ q ∈ A, 0 < q ∧ q < cap := by
  induction h with
  | nil => simp
  | cons hpos hb _ _ _ _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hpos, hb⟩
    · exact ih q hq

/-- The first pointer of a chain is zero or an address below the capacity. -/
theorem NodeChain.first_lt {s : State} {cap p : ℕ} {A : List ℕ} {l : List ReturnNode}
    (h : NodeChain s cap p A l) (hcap : 0 < cap) : p < cap := by
  cases h with
  | nil => exact hcap
  | cons _ hb _ _ _ _ => exact hb

/-- The first address of a chain is its first pointer. -/
theorem NodeChain.head_eq {s : State} {cap p q : ℕ} {A : List ℕ} {l : List ReturnNode}
    (h : NodeChain s cap p (q :: A) l) : p = q := by
  cases h
  rfl

/-- A chain survives every frame that avoids its cells. -/
theorem NodeChain.frame {s s' : State} {cap p : ℕ} {A : List ℕ} {l : List ReturnNode}
    {W : ℕ → ℕ → Prop} (h : NodeChain s cap p A l) (hF : Frame s s' W)
    (hW : ∀ q ∈ A, ¬ NodeCell W q) : NodeChain s' cap p A l := by
  induction h with
  | nil => exact .nil
  | @cons p q ps b bs hpos hb he hd hn _ ih =>
    have hp := hW p (by simp)
    simp only [NodeCell, not_or] at hp
    refine .cons hpos hb ?_ ?_ ?_ (ih fun q hq => hW q (by simp [hq]))
    · rw [hF.get hp.1]
      exact he
    · rw [hF.get hp.2.1]
      exact hd
    · rw [hF.get hp.2.2]
      exact hn

/-- The depth of the last node is stored at the last address. -/
theorem NodeChain.getLast_depth {s : State} {cap p : ℕ} {A : List ℕ} {l : List ReturnNode}
    (h : NodeChain s cap p A l) (hA : A ≠ []) (hl : l ≠ []) :
    (s.arrs Field.nodeDepth.array)[A.getLast hA]? = some (l.getLast hl).depth := by
  induction h with
  | nil => exact absurd rfl hA
  | @cons p q ps b bs _ _ _ hd _ hrest ih =>
    cases hrest with
    | nil => simpa using hd
    | cons _ _ _ _ _ _ =>
      simp only [List.getLast_cons_cons]
      exact ih (by simp) (by simp)

/-- Writing the last node's next pointer concatenates two disjoint chains. -/
theorem NodeChain.append_write {s s' : State} {cap f₁ f₂ x : ℕ} {A B : List ℕ}
    {l₁ l₂ : List ReturnNode} (h₁ : NodeChain s cap f₁ A l₁) (h₂ : NodeChain s cap f₂ B l₂)
    (hx : A.getLast? = some x) (hnd : A.Nodup) (hdis : ∀ q ∈ A, q ∉ B)
    (hF : Frame s s' (fun a q => a = Field.nodeNext.array ∧ q = x))
    (hlast : (s'.arrs Field.nodeNext.array)[x]? = some f₂) :
    NodeChain s' cap f₁ (A ++ B) (l₁ ++ l₂) := by
  induction h₁ with
  | nil => simp at hx
  | @cons p q ps b bs hpos hb he hd hn hrest ih =>
    have hpx : p ∉ B := hdis p (by simp)
    have hcellB : ∀ q ∈ B, ¬ NodeCell (fun a q => a = Field.nodeNext.array ∧ q = x) q := by
      intro q hq
      simp only [NodeCell, Field.array, not_or]
      refine ⟨by omega, by omega, fun h => ?_⟩
      have hxA : x ∈ p :: ps := List.mem_of_getLast? hx
      exact hdis x hxA (h.2 ▸ hq)
    have hedge : (s'.arrs Field.nodeEdge.array)[p]? = some b.edge := by
      rw [hF.get (by simp [Field.array])]
      exact he
    have hdepth : (s'.arrs Field.nodeDepth.array)[p]? = some b.depth := by
      rw [hF.get (by simp [Field.array])]
      exact hd
    by_cases hps : ps = []
    · subst hps
      cases hrest
      simp only [List.getLast?_singleton, Option.some.injEq] at hx
      subst hx
      exact .cons hpos hb hedge hdepth hlast (h₂.frame hF hcellB)
    · have hx' : ps.getLast? = some x := by
        rw [List.getLast?_cons] at hx
        rcases List.getLast?_eq_some_getLast hps with h'
        rw [h'] at hx ⊢
        simpa using hx
      have hpne : p ≠ x := by
        intro hpx'
        subst hpx'
        exact (List.nodup_cons.mp hnd).1 (List.mem_of_getLast? hx')
      have hnext : (s'.arrs Field.nodeNext.array)[p]? = some q := by
        rw [hF.get (by simp [hpne])]
        exact hn
      exact .cons hpos hb hedge hdepth hnext
        (ih hx' (List.nodup_cons.mp hnd).2 (fun q hq => hdis q (by simp [hq])))

/-- A list survives every frame that avoids its node cells. -/
theorem ListAt.frame {s s' : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    {W : ℕ → ℕ → Prop} (h : ListAt s cap f l A x) (hF : Frame s s' W)
    (hW : ∀ q ∈ A, ¬ NodeCell W q) : ListAt s' cap f l A x :=
  ⟨h.1.frame hF hW, h.2.1, h.2.2⟩

/-- The first pointer is zero exactly for the empty address list. -/
theorem ListAt.first_eq_zero_iff {s : State} {cap f l : ℕ} {A : List ℕ}
    {x : List ReturnNode} (h : ListAt s cap f l A x) : f = 0 ↔ A = [] := by
  rw [h.1.first_eq_zero_iff, ← List.length_eq_zero_iff, ← h.1.length_eq,
    List.length_eq_zero_iff]

/-- The last pointer is zero exactly for the empty address list. -/
theorem ListAt.last_eq_zero_iff {s : State} {cap f l : ℕ} {A : List ℕ}
    {x : List ReturnNode} (h : ListAt s cap f l A x) : l = 0 ↔ A = [] := by
  rcases h with ⟨hc, hl, _⟩
  subst hl
  constructor
  · intro h0
    by_contra hA
    have hmem := List.getLast_mem hA
    have hpos := (hc.mem_bounds _ hmem).1
    rw [List.getLast?_eq_some_getLast hA] at h0
    simp at h0
    omega
  · intro hA
    simp [hA]

/-- The depth stored at the first pointer is the first depth. -/
theorem ListAt.first_depth {s : State} {cap f l : ℕ} {A : List ℕ} {b : ReturnNode}
    {x : List ReturnNode} (h : ListAt s cap f l A (b :: x)) :
    (s.arrs Field.nodeDepth.array)[f]? = some b.depth := by
  rcases h with ⟨hc, _, _⟩
  cases hc with
  | cons _ _ _ hd _ _ => exact hd

/-- The depth stored at the last pointer is the last depth. -/
theorem ListAt.last_depth {s : State} {cap f l : ℕ} {A : List ℕ} {x : List ReturnNode}
    (h : ListAt s cap f l A x) (hx : x ≠ []) :
    (s.arrs Field.nodeDepth.array)[l]? = some (x.getLast hx).depth := by
  rcases h with ⟨hc, hl, _⟩
  have hA : A ≠ [] := by
    intro hA
    subst hA
    have := hc.length_eq
    simp at this
    exact hx (List.length_eq_zero_iff.mp this.symm)
  rw [hl, List.getLast?_eq_some_getLast hA]
  exact hc.getLast_depth hA hx

/-- Dropping the first node of a list follows its next pointer. -/
theorem ListAt.tail {s : State} {cap f l q : ℕ} {A : List ℕ} {b : ReturnNode}
    {x : List ReturnNode} (h : ListAt s cap f l A (b :: x))
    (hq : (s.arrs Field.nodeNext.array)[f]? = some q) :
    ListAt s cap q (if q = 0 then 0 else l) A.tail x := by
  rcases h with ⟨hc, hl, hnd⟩
  cases hc with
  | cons hpos hb he hd hn hrest =>
    rename_i q' ps
    have hqq : q' = q := by
      rw [hn] at hq
      exact Option.some.inj hq
    subst hqq
    refine ⟨hrest, ?_, (List.nodup_cons.mp hnd).2⟩
    by_cases hq0 : q' = 0
    · have hps : ps = [] := by
        have h1 := hrest.first_eq_zero_iff.mp hq0
        have h2 := hrest.length_eq
        rw [h1] at h2
        exact List.length_eq_zero_iff.mp h2
      simp [hq0, hps]
    · have hps : ps ≠ [] := by
        intro hps
        subst hps
        cases hrest
        exact hq0 rfl
      simp only [hq0, ↓reduceIte, List.tail_cons, hl]
      rw [List.getLast?_cons, List.getLast?_eq_some_getLast hps]
      rfl

/-- The header after appending list `(f₂, l₂)` to list `(f₁, l₁)`. If the
second list is empty, nothing changes. Otherwise its last pointer becomes the
last pointer, and its first pointer becomes the first pointer when the first
list is empty. -/
def appendFirst (f₁ f₂ : ℕ) : ℕ := if f₂ = 0 then f₁ else if f₁ = 0 then f₂ else f₁

/-- See `appendFirst`. -/
def appendLast (l₁ f₂ l₂ : ℕ) : ℕ := if f₂ = 0 then l₁ else l₂

/-- Part I, Section 3: "Concatenation is destructive: we connect the old last
node to the new first node, update the last pointer, and empty the header of
the list that was appended." If both lists are
nonempty, the next pointer of the old last node is set to the new first node;
otherwise memory is unchanged. -/
theorem ListAt.append {s s' : State} {cap f₁ l₁ f₂ l₂ : ℕ} {A B : List ℕ}
    {x y : List ReturnNode} (h₁ : ListAt s cap f₁ l₁ A x) (h₂ : ListAt s cap f₂ l₂ B y)
    (hdis : ∀ q ∈ A, q ∉ B)
    (hF : Frame s s' (fun a q => a = Field.nodeNext.array ∧ q = l₁ ∧ f₁ ≠ 0 ∧ f₂ ≠ 0))
    (hlast : f₁ ≠ 0 → f₂ ≠ 0 → (s'.arrs Field.nodeNext.array)[l₁]? = some f₂) :
    ListAt s' cap (appendFirst f₁ f₂) (appendLast l₁ f₂ l₂) (A ++ B) (x ++ y) := by
  have hnd : (A ++ B).Nodup := List.nodup_append.mpr ⟨h₁.2.2, h₂.2.2,
    fun a ha b hb hab => hdis a ha (hab ▸ hb)⟩
  by_cases hf₂ : f₂ = 0
  · have hB := h₂.first_eq_zero_iff.mp hf₂
    have hy : y = [] := by
      have := h₂.1.length_eq
      rw [hB] at this
      exact List.length_eq_zero_iff.mp this.symm
    subst hB hy
    simp only [appendFirst, appendLast, hf₂, ↓reduceIte, List.append_nil]
    exact h₁.frame hF fun q _ => by simp [NodeCell, hf₂]
  · by_cases hf₁ : f₁ = 0
    · have hA := h₁.first_eq_zero_iff.mp hf₁
      have hx : x = [] := by
        have := h₁.1.length_eq
        rw [hA] at this
        exact List.length_eq_zero_iff.mp this.symm
      subst hA hx
      simp only [appendFirst, appendLast, hf₂, hf₁, ↓reduceIte, List.nil_append]
      exact h₂.frame hF fun q _ => by simp [NodeCell, hf₁]
    · have hA : A ≠ [] := fun h => hf₁ (h₁.first_eq_zero_iff.mpr h)
      have hB : B ≠ [] := fun h => hf₂ (h₂.first_eq_zero_iff.mpr h)
      have hx : A.getLast? = some l₁ := by
        rw [h₁.2.1, List.getLast?_eq_some_getLast hA]
        rfl
      simp only [appendFirst, appendLast, hf₂, hf₁, ↓reduceIte]
      have hF' := hF.mono (W' := fun a q => a = Field.nodeNext.array ∧ q = l₁)
        (fun _ _ h => ⟨h.1, h.2.1⟩)
      refine ⟨h₁.1.append_write h₂.1 hx h₁.2.2 hdis hF' (hlast hf₁ hf₂), ?_, hnd⟩
      rw [h₂.2.1, List.getLast?_append, List.getLast?_eq_some_getLast hB]
      rfl

/-! ### Block stacks and summaries -/

/-- A block stack survives every frame that avoids its block and node cells. -/
theorem BlockChain.frame {s s' : State} {cap p : ℕ} {bs ns : List ℕ} {stack : List Block}
    {W : ℕ → ℕ → Prop} (h : BlockChain s cap p bs ns stack) (hF : Frame s s' W)
    (hb : ∀ q ∈ bs, ¬ BlockCell W q) (hn : ∀ q ∈ ns, ¬ NodeCell W q) :
    BlockChain s' cap p bs ns stack := by
  induction h with
  | nil => exact .nil
  | @cons p below lf ll rf rl blocks nodes left right b bs' hpos hcap hlf hll hrf hrl hnext
      hleft hright _ ih =>
    have hp := hb p (by simp)
    simp only [BlockCell, not_or] at hp
    refine .cons hpos hcap ?_ ?_ ?_ ?_ ?_
      (hleft.frame hF fun q hq => hn q (by simp [hq]))
      (hright.frame hF fun q hq => hn q (by simp [hq]))
      (ih (fun q hq => hb q (by simp [hq])) (fun q hq => hn q (by simp [hq])))
    · rw [hF.get hp.1]; exact hlf
    · rw [hF.get hp.2.1]; exact hll
    · rw [hF.get hp.2.2.1]; exact hrf
    · rw [hF.get hp.2.2.2.1]; exact hrl
    · rw [hF.get hp.2.2.2.2]; exact hnext

/-- Every block address of a stack is a positive index below the capacity. -/
theorem BlockChain.mem_bounds {s : State} {cap p : ℕ} {bs ns : List ℕ} {stack : List Block}
    (h : BlockChain s cap p bs ns stack) : ∀ q ∈ bs, 0 < q ∧ q < cap := by
  induction h with
  | nil => simp
  | cons hpos hcap _ _ _ _ _ _ _ _ ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨hpos, hcap⟩
    · exact ih q hq

/-- Every node address of a stack is a positive index below the capacity. -/
theorem BlockChain.node_bounds {s : State} {cap p : ℕ} {bs ns : List ℕ} {stack : List Block}
    (h : BlockChain s cap p bs ns stack) : ∀ q ∈ ns, 0 < q ∧ q < cap := by
  induction h with
  | nil => simp
  | cons _ _ _ _ _ _ _ hleft hright _ ih =>
    intro q hq
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact hleft.1.mem_bounds q hq
    · exact hright.1.mem_bounds q hq
    · exact ih q hq

/-- The top pointer is zero exactly for the empty stack. -/
theorem BlockChain.top_eq_zero_iff {s : State} {cap p : ℕ} {bs ns : List ℕ}
    {stack : List Block} (h : BlockChain s cap p bs ns stack) : p = 0 ↔ stack = [] := by
  cases h with
  | nil => simp
  | cons hpos _ _ _ _ _ _ _ _ _ => simp [Nat.ne_of_gt hpos]

/-- The five block arrays. -/
def IsBlockArr (a : ℕ) : Prop :=
  a = Field.blockLeftFirst.array ∨ a = Field.blockLeftLast.array ∨
    a = Field.blockRightFirst.array ∨ a = Field.blockRightLast.array ∨
    a = Field.blockBelow.array

/-- Writing a fresh block record on top of a stack pushes a block. -/
theorem BlockChain.push {s s' : State} {cap top p lf ll rf rl : ℕ} {bs ns L R : List ℕ}
    {stack : List Block} {x y : List ReturnNode}
    (h : BlockChain s cap top bs ns stack) (hL : ListAt s cap lf ll L x)
    (hR : ListAt s cap rf rl R y) (hpos : 0 < p) (hcap : p < cap) (hfresh : p ∉ bs)
    (hF : Frame s s' (fun a q => q = p ∧ IsBlockArr a))
    (hlf : (s'.arrs Field.blockLeftFirst.array)[p]? = some lf)
    (hll : (s'.arrs Field.blockLeftLast.array)[p]? = some ll)
    (hrf : (s'.arrs Field.blockRightFirst.array)[p]? = some rf)
    (hrl : (s'.arrs Field.blockRightLast.array)[p]? = some rl)
    (hbelow : (s'.arrs Field.blockBelow.array)[p]? = some top) :
    BlockChain s' cap p (p :: bs) (L ++ R ++ ns) (⟨x, y⟩ :: stack) := by
  have hnode : ∀ q, ¬ NodeCell (fun a q => q = p ∧ IsBlockArr a) q := by
    intro q
    simp [NodeCell, IsBlockArr, Field.array]
  exact .cons hpos hcap hlf hll hrf hrl hbelow (hL.frame hF fun q _ => hnode q)
    (hR.frame hF fun q _ => hnode q)
    (h.frame hF (fun q hq => by
      simp only [BlockCell]
      intro hc
      rcases hc with h1 | h1 | h1 | h1 | h1 <;> exact hfresh (h1.1 ▸ hq))
      (fun q _ => hnode q))

/-- A summary survives every frame that avoids its record, block and node cells. -/
theorem SummaryAt.frame {s s' : State} {M p : ℕ} {S : Summary} {bs ns : List ℕ}
    {W : ℕ → ℕ → Prop} (h : SummaryAt s M p S bs ns) (hF : Frame s s' W)
    (hp : ¬ SummaryCell W p) (hb : ∀ q ∈ bs, ¬ BlockCell W q)
    (hn : ∀ q ∈ ns, ¬ NodeCell W q) : SummaryAt s' M p S bs ns := by
  obtain ⟨hpos, hcap, hleast, first, last, top, anchor, stackNodes, hfirst, hlast, htop,
    hanchor, hstack, hns, hnd, hbnd⟩ := h
  simp only [SummaryCell, not_or] at hp
  subst hns
  refine ⟨hpos, hcap, ?_, first, last, top, anchor, stackNodes, ?_, ?_, ?_,
    hanchor.frame hF (fun q hq => hn q (by simp [hq])),
    hstack.frame hF hb (fun q hq => hn q (by simp [hq])), rfl, hnd, hbnd⟩
  · rw [hF.get hp.1]; exact hleast
  · rw [hF.get hp.2.1]; exact hfirst
  · rw [hF.get hp.2.2.1]; exact hlast
  · rw [hF.get hp.2.2.2]; exact htop

end GraphMinor.Compute.PlanarityRam
