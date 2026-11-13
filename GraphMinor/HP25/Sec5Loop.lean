module

public import GraphMinor.HP25.Sec5Tight
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.SplitTools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Sec5Lemma54

/-!
# The loop of Algorithm 5.2 keeps `P` induced, separating and tight

Algorithm 5.2 of Humeau and Pous (page 23) replaces `P` by `P y u P` after adding the edge `yu`
(lines 7 and 8). With Lemma 5.4's choice `y = y_j`, `u = y_s`, no vertex strictly between `y_j` and
`y_s` is on the side of `y_s` that `y_r` lacks. This file proves that the new path `P y_j y_s P`
(written `P'`, with vertex list `L₁ ++ y :: s :: L₂` when `P` has `L₁ ++ y :: N ++ s :: L₂`) is again
induced, separating and tight in `G + y_j y_s`, as the corrected algorithm needs before the next
step (`loop_invariant`). We call the side that the vertices of `N` lack `B`.

* Induced: a chord of `P'` in `G` is a chord of `P`; two vertices that are consecutive on `P` and both
  on `P'` are consecutive on `P'`.
* Separating: a path from `A` to `B` that misses `P'` meets `P` only in `N`; the switching lemma
  `exists_connected_of_walk` then gives a vertex of `N` on side `B`, or a path from `A` to `B` that
  misses `P`.
* Tight: a component of `G + y_j y_s - (C ∪ P')` that contains a vertex of `N` and meets neither side
  has all its vertices on no side, so it lies in the zone of `Sec5Tight.lean`, whose only neighbours
  on `P'` are `y_j` and `y_s`. Any other component is a component of `G - (C ∪ P)`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lists -/

/-- An edge of a list `l₁ ++ m ++ l₂` whose ends are not in `m`, with `m` not empty, is an edge of
`l₁` or of `l₂`. -/
theorem IsListEdge.of_append_middle {l₁ m l₂ : List V} {u v : V} (hm : m ≠ [])
    (h : IsListEdge (l₁ ++ m ++ l₂) u v) (hu : u ∉ m) (hv : v ∉ m) :
    IsListEdge l₁ u v ∨ IsListEdge l₂ u v := by
  obtain ⟨p, hp, he⟩ := h
  obtain ⟨i, hi, h1, h2⟩ := mem_zip_tail_iff.mp (show (p.1, p.2) ∈ _ from hp)
  have hmlen : 0 < m.length := List.length_pos_of_ne_nil hm
  simp only [List.length_append] at hi
  have hpu : p.1 = u ∨ p.1 = v := by
    rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨-, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  have hpv : p.2 = u ∨ p.2 = v := by
    rcases Sym2.eq_iff.mp he with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  have hnot : ∀ {x}, (x = u ∨ x = v) → x ∉ m := fun {x} hx => by
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  by_cases hA : i + 1 < l₁.length
  · left
    refine ⟨p, mem_zip_tail_iff.mpr ⟨i, hA, ?_, ?_⟩, he⟩
    · rw [← h1, List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)]
    · rw [← h2, List.getElem_append_left (by simp; omega), List.getElem_append_left (by omega)]
  · by_cases hB : l₁.length + m.length ≤ i
    · right
      refine ⟨p, mem_zip_tail_iff.mpr ⟨i - (l₁.length + m.length), by omega, ?_, ?_⟩, he⟩
      · rw [← h1, List.getElem_append_right (by simp; omega)]
        congr 1
        simp
      · rw [← h2, List.getElem_append_right (by simp; omega)]
        congr 1
        simp
        omega
    · -- one end of the pair lies in `m`
      exfalso
      by_cases hc : i + 1 < l₁.length + m.length
      · have hmem : (l₁ ++ m ++ l₂)[i + 1] ∈ m := by
          rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
          exact List.getElem_mem _
        rw [h2] at hmem
        exact hnot hpv hmem
      · have hmem : (l₁ ++ m ++ l₂)[i] ∈ m := by
          rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
          exact List.getElem_mem _
        rw [h1] at hmem
        exact hnot hpu hmem

/-- Every entry of a list with at least two entries lies on an edge of the list. -/
theorem exists_isListEdge_of_mem {l : List V} (hl : 2 ≤ l.length) {x : V} (hx : x ∈ l) :
    ∃ x', IsListEdge l x x' := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  by_cases h : i + 1 < l.length
  · exact ⟨l[i + 1], ⟨(l[i], l[i + 1]), mem_zip_tail_iff.mpr ⟨i, h, rfl, rfl⟩, rfl⟩⟩
  · have h0 : 0 < i := by omega
    refine ⟨l[i - 1], ⟨(l[i - 1], l[i]), mem_zip_tail_iff.mpr ⟨i - 1, by omega, rfl, ?_⟩, ?_⟩⟩
    · congr 1; omega
    · exact Sym2.eq_swap

/-! ### Walks of `G + yu` -/

/-- A walk of `G + yu` that misses `y` or `u` is a walk of `G` with the same vertices. -/
theorem exists_walk_of_sup_edge {y u : V} :
    ∀ {x z : V} (p : (G ⊔ edge y u).Walk x z), (y ∉ p.support ∨ u ∉ p.support) →
      ∃ q : G.Walk x z, q.support = p.support
  | _, _, .nil, _ => ⟨.nil, rfl⟩
  | x, _, .cons (v := w) h p, hy => by
    have hy' : y ∉ p.support ∨ u ∉ p.support := by
      rcases hy with hy | hy
      · exact Or.inl fun h' => hy (by simp [h'])
      · exact Or.inr fun h' => hy (by simp [h'])
    obtain ⟨q, hq⟩ := exists_walk_of_sup_edge p hy'
    have hadj : G.Adj x w := by
      rcases (sup_adj _ _ _ _).mp h with h | h
      · exact h
      · exfalso
        have hw : w ∈ p.support := p.start_mem_support
        rcases ((edge_adj _ _ _ _).mp h).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          rcases hy with hy | hy <;> simp_all
    exact ⟨.cons hadj q, by simp [hq]⟩

/-- A path of `G + yu` with no inner vertex in `X` is such a path of `G` when `y` (or `u`) lies in
`X`, is not its start and is not in the target set `S`. -/
theorem IsConnectedAvoiding.of_sup_edge {y u : V} {X : Set V} {x : V} {S : Set V}
    (hyu : (y ∈ X ∧ x ≠ y ∧ y ∉ S) ∨ (u ∈ X ∧ x ≠ u ∧ u ∉ S))
    (h : IsConnectedAvoiding (G ⊔ edge y u) X x S) : IsConnectedAvoiding G X x S := by
  obtain ⟨t, ht, p, hp, hin⟩ := h
  have hmiss : ∀ {c}, c ∈ X → x ≠ c → c ∉ S → c ∉ p.support := fun {c} hcX hxc hcS h' => by
    by_cases h2 : c = t
    · exact hcS (h2 ▸ ht)
    · exact hin c h' (Ne.symm hxc) h2 hcX
  obtain ⟨q, hq⟩ := exists_walk_of_sup_edge p
    (hyu.imp (fun h => hmiss h.1 h.2.1 h.2.2) (fun h => hmiss h.1 h.2.1 h.2.2))
  exact ⟨t, ht, q, by rw [Walk.isPath_def, hq]; exact hp.support_nodup,
    fun v hv => hin v (hq ▸ hv)⟩

/-- Any two entries of a list whose consecutive entries are adjacent are joined by a walk inside the
list. -/
theorem exists_walk_of_isChain : ∀ {l : List V}, l.IsChain G.Adj → ∀ {x z : V}, x ∈ l → z ∈ l →
    ∃ p : G.Walk x z, ∀ v ∈ p.support, v ∈ l
  | [], _, _, _, hx, _ => by simp at hx
  | [c], _, x, z, hx, hz => by
    simp only [List.mem_singleton] at hx hz
    subst hx; subst hz
    exact ⟨.nil, by simp⟩
  | c :: d :: t, hl, x, z, hx, hz => by
    rw [List.isChain_cons_cons] at hl
    have hfrom : ∀ w ∈ c :: d :: t, ∃ p : G.Walk c w, ∀ v ∈ p.support, v ∈ c :: d :: t := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨.nil, by simp⟩
      · obtain ⟨p, hp⟩ := exists_walk_of_isChain hl.2 (List.mem_cons_self ..) hw
        refine ⟨.cons hl.1 p, fun v hv => ?_⟩
        rw [Walk.support_cons, List.mem_cons] at hv
        rcases hv with rfl | hv
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hp v hv)
    obtain ⟨p, hp⟩ := hfrom x hx
    obtain ⟨q, hq⟩ := hfrom z hz
    refine ⟨p.reverse.append q, fun v hv => ?_⟩
    rw [Walk.support_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hp v (by simpa using hv)
    · exact hq v (List.mem_of_mem_tail hv)

variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-- The vertices of `P` that are not on `P'` are the vertices of `N`. -/
theorem mem_N_of_not_mem (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) {v : V}
    (hv : v ∈ P.support) (hv' : v ∉ L₁ ++ y :: s :: L₂) : v ∈ N := by
  rw [hsupp] at hv
  simp only [List.mem_append, List.mem_cons] at hv hv'
  tauto

/-- The vertices of `N` are not on `P'`. -/
theorem not_mem_short_of_mem_N (hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup) {v : V} (hv : v ∈ N) :
    v ∉ L₁ ++ y :: s :: L₂ := by
  intro h
  have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ [y]) ++ (N ++ s :: L₂) := by simp
  rw [e, List.nodup_append] at hnd
  simp only [List.mem_append, List.mem_cons] at h
  rcases h with h | rfl | rfl | h
  · exact hnd.2.2 v (by simp [h]) v (by simp [hv]) rfl
  · exact hnd.2.2 v (by simp) v (by simp [hv]) rfl
  · have := hnd.2.1
    rw [List.nodup_append] at this
    exact this.2.2 v hv v (by simp) rfl
  · have := hnd.2.1
    rw [List.nodup_append] at this
    exact this.2.2 v hv v (by simp [h]) rfl

/-- **The loop of Algorithm 5.2 keeps `P` induced and separating.** Let `P` be an induced
`C`-path that separates `A` from `B`, with `P.support = L₁ ++ y :: N ++ s :: L₂`, and let no vertex
of `N` be on side `B`. Then the path `P'` of `G + ys` with vertex list `L₁ ++ y :: s :: L₂` is induced
and separates `A` from `B`. -/
theorem loop_induced_separates (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (hNB : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    {P' : (G ⊔ edge y s).Walk a b} (hP's : P'.support = L₁ ++ y :: s :: L₂) :
    (∀ u ∈ P'.support, ∀ v ∈ P'.support, (G ⊔ edge y s).Adj u v →
        IsListEdge P'.support u v) ∧
      Separates (G ⊔ edge y s) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} := by
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  set X' : Set V := {x | x ∈ C ∨ x ∈ P'.support} with hX'
  have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hsubP : ∀ {v}, v ∈ P'.support → v ∈ P.support := fun {v} hv => by
    rw [hsupp]; rw [hP's] at hv
    simp only [List.mem_append, List.mem_cons] at hv ⊢
    tauto
  have hX'X : X' ⊆ X := fun v hv => hv.imp id hsubP
  have hNC : ∀ {v}, v ∈ N → v ∉ C := fun hv => not_mem_C_of_mem_window hP hsupp hv
  have hNP' : ∀ {v}, v ∈ N → v ∉ P'.support := fun hv => hP's ▸ not_mem_short_of_mem_N hnd hv
  have hNX' : ∀ {v}, v ∈ N → v ∉ X' := fun hv h => h.elim (hNC hv) (hNP' hv)
  have hyP' : y ∈ P'.support := by rw [hP's]; simp
  have hsP' : s ∈ P'.support := by rw [hP's]; simp
  have hys : y ≠ s := (List.nodup_append.mp hnd).2.2 y (by simp) s (by simp)
  have hyse : IsListEdge P'.support y s := by
    rw [hP's]; exact IsListEdge.append_right (l₁ := L₁) ⟨(y, s), by simp, rfl⟩
  have hlen : 2 ≤ P'.support.length := by rw [hP's]; simp; omega
  -- an edge of `P` with no end in `N` is an edge of `P'`
  have htrans : ∀ {v w}, IsListEdge P.support v w → v ∉ N → w ∉ N →
      IsListEdge P'.support v w := fun {v w} he hv hw => by
    rw [hP's, show L₁ ++ y :: s :: L₂ = (L₁ ++ [y]) ++ (s :: L₂) by simp]
    rw [hsupp, show L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ [y]) ++ N ++ (s :: L₂) by simp] at he
    by_cases hN : N = []
    · subst hN
      rwa [List.append_nil] at he
    · rcases he.of_append_middle hN hv hw with h | h
      · exact h.append_left
      · exact h.append_right
  refine ⟨?_, ?_⟩
  · -- induced
    intro u hu v hv huv
    rcases (sup_adj _ _ _ _).mp huv with h | h
    · exact htrans (hind u (hsubP hu) v (hsubP hv) h) (fun h' => hNP' h' hu)
        (fun h' => hNP' h' hv)
    · rcases ((edge_adj _ _ _ _).mp h).1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyse
      · exact hyse.symm
  · -- separating
    intro u hu w hw p
    by_contra hcon
    have hoff : ∀ v ∈ p.support, v ∉ P'.support := fun v hv h => hcon ⟨v, hv, h⟩
    obtain ⟨q, hq⟩ := exists_walk_of_sup_edge p (Or.inl fun h => hoff y h hyP')
    have hoffq : ∀ v ∈ q.support, v ∉ P'.support := fun v hv => hoff v (hq ▸ hv)
    have hAC : ∀ {v}, v ∈ A → v ∈ C := fun {v} hv =>
      (List.mem_rotate (n := k)).mp (by rw [hrot]; simp [hv])
    have hBC : ∀ {v}, v ∈ B → v ∈ C := fun {v} hv =>
      (List.mem_rotate (n := k)).mp (by rw [hrot]; simp [hv])
    have hoffP : ∀ {v}, v ∈ C → v ∉ P'.support → v ∉ P.support := fun {v} hvC hv h =>
      hNC (mem_N_of_not_mem hsupp h (hP's ▸ hv)) hvC
    have hvX : ∀ v ∈ q.support, v ∈ X →
        v ∈ {x | (x ∈ A ∧ x ∉ P.support) ∨ x ∈ N} ∨ v ∈ {x | x ∈ B ∧ x ∉ P.support} := by
      intro v hv hvX
      have hv' := hoffq v hv
      by_cases hvP : v ∈ P.support
      · exact Or.inl (Or.inr (mem_N_of_not_mem hsupp hvP (hP's ▸ hv')))
      · rcases hvX with hvC | hvP'
        · rcases mem_of_rotate hrot hvC with rfl | h | rfl | h
          · exact absurd P.start_mem_support hvP
          · exact Or.inl (Or.inl ⟨h, hvP⟩)
          · exact absurd P.end_mem_support hvP
          · exact Or.inr ⟨h, hvP⟩
        · exact absurd hvP' hvP
    have huP : u ∉ P.support := hoffP (hAC hu) (hoffq u q.start_mem_support)
    have hwP : w ∉ P.support := hoffP (hBC hw) (hoffq w q.end_mem_support)
    obtain ⟨a', ha', b', hb', hc⟩ := exists_connected_of_walk (X := X)
      (A := {x | (x ∈ A ∧ x ∉ P.support) ∨ x ∈ N}) (B := {x | x ∈ B ∧ x ∉ P.support}) q
      ⟨hw, hwP⟩ hvX u (Or.inl ⟨hu, huP⟩) Walk.nil (fun v hv h => by simp at hv; exact absurd hv h)
    obtain ⟨t, rfl, r, hr, hrin⟩ := hc
    rcases ha' with ⟨ha'A, ha'P⟩ | ha'N
    · obtain ⟨v, hv, hvP⟩ := hsep a' ha'A t hb'.1 r
      by_cases h1 : v = a'
      · exact ha'P (h1 ▸ hvP)
      · by_cases h2 : v = t
        · exact hb'.2 (h2 ▸ hvP)
        · exact hrin v hv h1 h2 (Or.inr hvP)
    · exact hNB a' ha'N ⟨t, hb'.1, r, hr, hrin⟩

/-- **The loop of Algorithm 5.2 keeps `P` induced, separating and tight** (Humeau and Pous, page 23,
lines 7 and 8: "G ← G + yu" and "P ← PyuP", with Lemma 5.4's `y = y_j` and `u = y_s`). Let `P` be an
induced, tight `C`-path that separates `A` from `B`, with `P.support = L₁ ++ y :: N ++ s :: L₂`, and
let no vertex of `N` be on side `B`. Then the path `P'` of `G + ys` with vertex list
`L₁ ++ y :: s :: L₂` is induced, separates `A` from `B`, and is tight. The paper does not state this
invariant. Its proofs need `P` induced (Lemma 5.4) and separating (line 6 of Algorithm 5.1), and our
correction of Claim 5.5 needs `P` tight. -/
theorem loop_invariant (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hsep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B})
    (hNB : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    {P' : (G ⊔ edge y s).Walk a b} (hP's : P'.support = L₁ ++ y :: s :: L₂) :
    (∀ u ∈ P'.support, ∀ v ∈ P'.support, (G ⊔ edge y s).Adj u v →
        IsListEdge P'.support u v) ∧
      Separates (G ⊔ edge y s) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
      IsTight (G ⊔ edge y s) C A B P'.support := by
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  set X' : Set V := {x | x ∈ C ∨ x ∈ P'.support} with hX'
  have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hsubP : ∀ {v}, v ∈ P'.support → v ∈ P.support := fun {v} hv => by
    rw [hsupp]; rw [hP's] at hv
    simp only [List.mem_append, List.mem_cons] at hv ⊢
    tauto
  have hX'X : X' ⊆ X := fun v hv => hv.imp id hsubP
  have hNC : ∀ {v}, v ∈ N → v ∉ C := fun hv => not_mem_C_of_mem_window hP hsupp hv
  have hNP' : ∀ {v}, v ∈ N → v ∉ P'.support := fun hv => hP's ▸ not_mem_short_of_mem_N hnd hv
  have hNX' : ∀ {v}, v ∈ N → v ∉ X' := fun hv h => h.elim (hNC hv) (hNP' hv)
  have hyP' : y ∈ P'.support := by rw [hP's]; simp
  have hsP' : s ∈ P'.support := by rw [hP's]; simp
  have hys : y ≠ s := (List.nodup_append.mp hnd).2.2 y (by simp) s (by simp)
  have hyse : IsListEdge P'.support y s := by
    rw [hP's]; exact IsListEdge.append_right (l₁ := L₁) ⟨(y, s), by simp, rfl⟩
  have hlen : 2 ≤ P'.support.length := by rw [hP's]; simp; omega
  -- an edge of `P` with no end in `N` is an edge of `P'`
  have htrans : ∀ {v w}, IsListEdge P.support v w → v ∉ N → w ∉ N →
      IsListEdge P'.support v w := fun {v w} he hv hw => by
    rw [hP's, show L₁ ++ y :: s :: L₂ = (L₁ ++ [y]) ++ (s :: L₂) by simp]
    rw [hsupp, show L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ [y]) ++ N ++ (s :: L₂) by simp] at he
    by_cases hN : N = []
    · subst hN
      rwa [List.append_nil] at he
    · rcases he.of_append_middle hN hv hw with h | h
      · exact h.append_left
      · exact h.append_right
  refine ⟨?_, ?_, ?_⟩
  · exact (loop_induced_separates hrot hP hsupp hind hsep hNB hP's).1
  · exact (loop_induced_separates hrot hP hsupp hind hsep hNB hP's).2
  · -- tight
    intro u huC huP' hnAB
    by_cases hcase : ∃ m ∈ N, IsConnectedAvoiding (G ⊔ edge y s) X' u {m}
    · -- the component of `u` meets `N`: it lies in the zone of `N`
      obtain ⟨m, hm, hum⟩ := hcase
      obtain ⟨m', rfl, π, hπ, hπin⟩ := hum
      have hNch : N.IsChain G.Adj := by
        have := P.isChain_adj_support
        rw [hsupp] at this
        exact this.infix ⟨L₁ ++ [y], s :: L₂, by simp⟩
      -- no vertex of `N` is on side `A`, else `u` would reach `A`
      have hNA : ∀ n ∈ N, ¬ IsOnSide G X {x | x ∈ A} n := by
        rintro n hn ⟨t, htA, r, hr, hrin⟩
        obtain ⟨σ, hσ⟩ := exists_walk_of_isChain hNch hm hn
        apply hnAB
        refine isConnectedAvoiding_of_walk_mem (Or.inl htA)
          (π.append ((σ.append r).mapLe le_sup_left)) fun v hv hvX' => ?_
        rw [Walk.support_append, List.mem_append] at hv
        rcases hv with hv | hv
        · by_cases h1 : v = u
          · exact Or.inl h1
          · by_cases h2 : v = m'
            · exact absurd (h2 ▸ hvX') (hNX' hm)
            · exact absurd hvX' (hπin v hv h1 h2)
        · have hv := List.mem_of_mem_tail hv
          rw [support_mapLe, Walk.support_append, List.mem_append] at hv
          rcases hv with hv | hv
          · exact absurd hvX' (hNX' (hσ v hv))
          · have hv := List.mem_of_mem_tail hv
            by_cases h1 : v = n
            · exact absurd (h1 ▸ hvX') (hNX' hn)
            · by_cases h2 : v = t
              · exact Or.inr h2
              · exact absurd (hX'X hvX') (hrin v hv h1 h2)
      have hno : ∀ v ∈ N, ¬ IsOnSide G X {x | x ∈ A} v ∧ ¬ IsOnSide G X {x | x ∈ B} v :=
        fun v hv => ⟨hNA v hv, hNB v hv⟩
      have hcl : ∀ v ∈ tightZone G X N, ∀ w, G.Adj v w →
          w ∈ tightZone G X N ∨ w = y ∨ w = s := fun v hv w hvw =>
        tightZone_closed hrot hP hsupp hind htight hno hv hvw
      -- a path of `G + ys` avoiding `X'` inside, with ends other than `y` and `s`
      have hGwalk : ∀ {x z : V} (ρ : (G ⊔ edge y s).Walk x z),
          (∀ v ∈ ρ.support, v ≠ x → v ≠ z → v ∉ X') → x ≠ y ∧ x ≠ s → z ≠ y ∧ z ≠ s →
          ∃ ρ' : G.Walk x z, ∀ v ∈ ρ'.support, v ≠ y ∧ v ≠ s := by
        intro x z ρ hρ hx hz
        have hys' : ∀ v ∈ ρ.support, v ≠ y ∧ v ≠ s := by
          intro v hv
          by_cases h1 : v = x
          · exact h1 ▸ hx
          · by_cases h2 : v = z
            · exact h2 ▸ hz
            · have := hρ v hv h1 h2
              exact ⟨fun h => this (Or.inr (h ▸ hyP')), fun h => this (Or.inr (h ▸ hsP'))⟩
        obtain ⟨ρ', hρ'⟩ := exists_walk_of_sup_edge ρ (Or.inl fun h => (hys' y h).1 rfl)
        exact ⟨ρ', fun v hv => hys' v (hρ' ▸ hv)⟩
      have hune : u ≠ y ∧ u ≠ s := ⟨fun h => huP' (h ▸ hyP'), fun h => huP' (h ▸ hsP')⟩
      have hmne : m' ≠ y ∧ m' ≠ s :=
        ⟨fun h => hNP' hm (h ▸ hyP'), fun h => hNP' hm (h ▸ hsP')⟩
      obtain ⟨π', hπ'⟩ := hGwalk π hπin hune hmne
      have huZ : u ∈ tightZone G X N :=
        mem_of_walk_of_closed hcl π'.reverse (Or.inl hm) (fun v hv => hπ' v (by simpa using hv))
      refine ⟨y, s, hyse, fun p hp hup => ?_⟩
      by_contra hne
      push Not at hne
      obtain ⟨p', rfl, ρ, -, hρin⟩ := hup
      obtain ⟨ρ', hρ'⟩ := hGwalk ρ hρin hune hne
      rcases mem_of_walk_of_closed hcl ρ' huZ hρ' with h | ⟨h, -⟩
      · exact hNP' h hp
      · exact h (Or.inr (hsubP hp))
    · -- the component of `u` misses `N`: it is a component of `G - (C ∪ P)`
      have huN : u ∉ N := fun h =>
        hcase ⟨u, h, u, rfl, .nil, Walk.IsPath.nil, fun v hv h1 => by simp at hv; exact absurd hv h1⟩
      have huP : u ∉ P.support := fun h => huN (mem_N_of_not_mem hsupp h (hP's ▸ huP'))
      obtain ⟨v', w', he, hall⟩ :=
        htight u huC huP fun h => hnAB (h.mono le_sup_left hX'X)
      have hyX : y ∈ X := Or.inr (hsubP hyP')
      have hsX : s ∈ X := Or.inr (hsubP hsP')
      have hune : u ≠ y ∧ u ≠ s := ⟨fun h => huP' (h ▸ hyP'), fun h => huP' (h ▸ hsP')⟩
      -- every attachment of `u` on `P'` in `G + ys` is one in `G`
      have hatt : ∀ p ∈ P'.support, IsConnectedAvoiding (G ⊔ edge y s) X' u {p} →
          p = v' ∨ p = w' := by
        intro p hp hup
        obtain ⟨p', rfl, ρ, -, hρin⟩ := hup
        have hρX : ∀ v ∈ ρ.support, v ∈ X → v ∈ ({u} : Set V) ∨ v ∈ {x | x ∈ N ∨ x = p'} := by
          intro v hv hvX
          by_cases h1 : v = u
          · exact Or.inl h1
          · by_cases h2 : v = p'
            · exact Or.inr (Or.inr h2)
            · have hvX' := hρin v hv h1 h2
              rcases hvX with hvC | hvP
              · exact absurd (Or.inl hvC) hvX'
              · exact Or.inr (Or.inl (mem_N_of_not_mem hsupp hvP
                  (hP's ▸ fun h => hvX' (Or.inr h))))
        obtain ⟨b', hb', c', hc', hc⟩ := exists_connected_of_walk (X := X) ρ (Or.inr rfl) hρX u rfl
          Walk.nil (fun v hv h => by simp at hv; exact absurd hv h)
        rw [Set.mem_singleton_iff] at hb'
        subst hb'
        rcases hc' with hc'N | rfl
        · exact absurd ⟨c', hc'N, hc.mono le_rfl hX'X⟩ hcase
        · refine hall c' (hsubP hp) (hc.of_sup_edge ?_)
          by_cases hcy : c' = y
          · exact Or.inr ⟨hsX, hune.2, fun h => hys (hcy ▸ h).symm⟩
          · exact Or.inl ⟨hyX, hune.1, fun h => hcy h.symm⟩
      by_cases hv'P : v' ∈ P'.support
      · by_cases hw'P : w' ∈ P'.support
        · exact ⟨v', w', htrans he (fun h => hNP' h hv'P) (fun h => hNP' h hw'P), hatt⟩
        · obtain ⟨x', hx'⟩ := exists_isListEdge_of_mem hlen hv'P
          exact ⟨v', x', hx', fun p hp hup =>
            (hatt p hp hup).elim Or.inl fun h => absurd (h ▸ hp) hw'P⟩
      · by_cases hw'P : w' ∈ P'.support
        · obtain ⟨x', hx'⟩ := exists_isListEdge_of_mem hlen hw'P
          exact ⟨w', x', hx', fun p hp hup =>
            (hatt p hp hup).elim (fun h => absurd (h ▸ hp) hv'P) Or.inl⟩
        · exact ⟨y, s, hyse, fun p hp hup =>
            (hatt p hp hup).elim (fun h => absurd (h ▸ hp) hv'P) fun h => absurd (h ▸ hp) hw'P⟩

end GraphMinor.HP25
