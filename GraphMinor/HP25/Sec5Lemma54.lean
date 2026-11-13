module

public import GraphMinor.HP25.Sec5Tight
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.CycleEdges

/-!
# Lemma 5.4: the sides after adding `y_j y_s`, and the case `r = s` for tight paths

Lemma 5.4 of Humeau and Pous (page 19) concludes: "Then the edge $y_jy_s$ is safe, and in the graph
$G+y_jy_s$, all vertices of $Py_jy_s$ lie on both $Py_jy_sP$-sides." The second conclusion holds as
printed; the first fails (`Checks/HP25Examples.lean`). This file proves:

* `lemma_5_4_sides`: the second conclusion. The paper's proof: "we only need proving that $y_s$ is
  on both $Py_jy_sP$-sides. The remainder follows from the assumption that all vertices of $Py_j$ lie
  on both $P$-sides in $G$. ... The paths $R$ and $Qy_rPy_s$ prove that $y_s$ is on both
  $Py_jy_sP$-sides in $G+y_jy_s$." We take the path `P y_j y_s P` of `G + y_j y_s` explicitly, and,
  for each side, either a side path of `y_s` or a side path of some `y_r` strictly between `y_j` and
  `y_s` (followed by `P` from `y_r` to `y_s`);
* `lemma_5_4_tight_of_noSide`: Lemma 5.4 for an induced, tight `P` in the case `r = s`, where the
  vertices strictly between `y_j` and `y_s` are on no side. The safety is Claim 5.5
  (`claim_5_5_tight`).

As in `Sec5Tight.lean`, `P.support = L₁ ++ y :: N ++ s :: L₂`, with `y = y_j` and `s = y_s`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- A path with no inner vertex in `X` stays one in a larger graph and for a smaller `X`. -/
theorem IsConnectedAvoiding.mono {G' : SimpleGraph V} (hle : G ≤ G') {X X' : Set V} {u : V}
    {S : Set V} (h : IsConnectedAvoiding G X u S) (hX : X' ⊆ X) : IsConnectedAvoiding G' X' u S := by
  obtain ⟨t, ht, p, hp, hin⟩ := h
  refine ⟨t, ht, p.mapLe hle, hp.mapLe hle, fun x hx h1 h2 hxX => ?_⟩
  rw [support_mapLe] at hx
  exact hin x hx h1 h2 (hX hxX)

/-- A walk from `u` to `t ∈ S` whose only vertices in `X` are its ends joins `u` to `S` avoiding `X`. -/
theorem isConnectedAvoiding_of_walk_mem {X S : Set V} {u t : V} (ht : t ∈ S) (W : G.Walk u t)
    (hW : ∀ v ∈ W.support, v ∈ X → v = u ∨ v = t) : IsConnectedAvoiding G X u S := by
  obtain ⟨t', rfl, p, hp, hin⟩ := isConnectedAvoiding_of_walk W hW
  exact ⟨t', ht, p, hp, hin⟩

variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-- The head of the list of vertices of a walk is its start. -/
private theorem head_of_supp (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) :
    (L₁ ++ y :: s :: L₂).head? = some a := by
  have h0 : P.support.head? = some a := by rw [← Walk.cons_tail_support]; rfl
  rw [hsupp] at h0
  cases L₁ <;> simpa using h0

/-- The last entry of the list of vertices of a walk is its end. -/
private theorem last_of_supp (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) :
    (L₁ ++ y :: s :: L₂).getLast? = some b := by
  have h0 : P.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  rw [hsupp] at h0
  have e1 : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ y :: N) ++ (s :: L₂) := by simp
  have e2 : L₁ ++ y :: s :: L₂ = (L₁ ++ [y]) ++ (s :: L₂) := by simp
  rw [e1, List.getLast?_append_of_ne_nil _ (by simp)] at h0
  rw [e2, List.getLast?_append_of_ne_nil _ (by simp)]
  exact h0

/-- The list `L₁ ++ y :: s :: L₂` is a sublist of `L₁ ++ y :: N ++ s :: L₂`. -/
private theorem sublist_short : (L₁ ++ y :: s :: L₂).Sublist (L₁ ++ y :: N ++ s :: L₂) := by
  simp only [List.cons_append, List.append_assoc]
  exact List.Sublist.append_left (List.Sublist.cons_cons _
    (List.sublist_append_right N (s :: L₂))) L₁

/-- **The second conclusion of Lemma 5.4** (Humeau and Pous, page 19): "in the graph $G+y_jy_s$, all
vertices of $Py_jy_s$ lie on both $Py_jy_sP$-sides." Here `P` is a `C`-path from `a` to `b`, with
`C = a A b B` up to rotation, and `P.support = L₁ ++ y :: N ++ s :: L₂`. We assume what the paper
uses: every vertex of `L₁ ++ [y]` (the path `Py_j`) is on both `P`-sides, and for each side, `s` is on
it, or some vertex of `N` is (the paper's `y_r`, with `y_s` on the other side). The path
`P y_j y_s P` of `G + y_j y_s` is the `C`-path `P'` below. -/
theorem lemma_5_4_sides (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hpre : ∀ v ∈ L₁ ++ [y], IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hsA : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} s ∨
      ∃ r ∈ N, IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} r)
    (hsB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s ∨
      ∃ r ∈ N, IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} r) :
    ∃ P' : (G ⊔ edge y s).Walk a b, IsTPath (G ⊔ edge y s) C P' ∧
      P'.support = L₁ ++ y :: s :: L₂ ∧
      ∀ v ∈ L₁ ++ [y, s],
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v := by
  classical
  have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hle : G ≤ G ⊔ edge y s := le_sup_left
  have hch : (L₁ ++ y :: N ++ s :: L₂).IsChain G.Adj := hsupp ▸ P.isChain_adj_support
  -- the path `P y_j y_s P`
  have hys : y ≠ s := fun h => by
    subst h
    have e : L₁ ++ y :: N ++ y :: L₂ = L₁ ++ y :: (N ++ y :: L₂) := by simp
    rw [e, List.nodup_append, List.nodup_cons] at hnd
    exact hnd.2.1.1 (by simp)
  have hch' : (L₁ ++ y :: s :: L₂).IsChain (G ⊔ edge y s).Adj := by
    have h1 : (L₁ ++ [y]).IsChain G.Adj := by
      have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ [y]) ++ (N ++ s :: L₂) := by simp
      rw [e] at hch
      exact hch.left_of_append
    have h2 : (s :: L₂).IsChain G.Adj := by
      have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ y :: N) ++ (s :: L₂) := by simp
      rw [e] at hch
      exact hch.right_of_append
    have e : L₁ ++ y :: s :: L₂ = (L₁ ++ [y]) ++ (s :: L₂) := by simp
    rw [e, List.isChain_append]
    refine ⟨h1.imp fun _ _ h => Or.inl h, h2.imp fun _ _ h => Or.inl h, fun u hu v hv => ?_⟩
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.mem_def, Option.some.injEq, List.head?_cons] at hu hv
    subst hu hv
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hys⟩)
  have hsub := (sublist_short (L₁ := L₁) (y := y) (N := N) (s := s) (L₂ := L₂))
  have hndP' : (L₁ ++ y :: s :: L₂).Nodup := hnd.sublist hsub
  have hmemC : ∀ v, v ∈ a :: A ++ b :: B → v ∈ C := fun v hv =>
    List.mem_rotate.mp (hrot ▸ hv)
  obtain ⟨P', hP', hP's⟩ := exists_tPath_of_list hch' hndP' (head_of_supp hsupp)
    (last_of_supp hsupp) (hmemC a (by simp)) (hmemC b (by simp)) (fun w hw hwC => by
      have hwP : w ∈ P.support := hsupp ▸ hsub.subset hw
      by_contra hne
      push Not at hne
      exact (hP.2.2.2 w hwP hne.1 hne.2).1 hwC)
  -- the new path has fewer vertices
  have hX : {x | x ∈ C ∨ x ∈ P'.support} ⊆ {x | x ∈ C ∨ x ∈ P.support} := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr (by rw [hsupp]; rw [hP's] at hx; exact hsub.subset hx)
  -- a vertex of `N` is off `C` and off `P'`
  have hNoff : ∀ v ∈ N, v ∉ C ∧ v ∉ P'.support := fun v hv => by
    refine ⟨not_mem_C_of_mem_window hP hsupp hv, fun h => ?_⟩
    rw [hP's] at h
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
  have hNX : ∀ v ∈ N, v ∉ {x | x ∈ C ∨ x ∈ P'.support} := fun v hv h =>
    h.elim (hNoff v hv).1 (hNoff v hv).2
  -- `s` is on a side through some `y_r ∈ N`
  have hviaN : ∀ {S : Set V} (r : V), r ∈ N → IsOnSide G {x | x ∈ C ∨ x ∈ P.support} S r →
      IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} S s := by
    intro S r hr hside
    obtain ⟨N₁, N₂, rfl⟩ := List.append_of_mem hr
    have hseg : (r :: N₂ ++ [s]).IsChain G.Adj :=
      hch.infix ⟨L₁ ++ y :: N₁, L₂, by simp⟩
    obtain ⟨seg, hseg'⟩ := exists_walk_of_chain (u := r) (v := s) _ hseg (by simp) (List.getLast?_concat ..)
    obtain ⟨t, ht, q, -, hqin⟩ := hside
    refine isConnectedAvoiding_of_walk_mem ht ((seg.reverse.append q).mapLe hle) ?_
    intro v hv hvX
    rw [support_mapLe, Walk.support_append, Walk.support_reverse, hseg', List.mem_append,
      List.mem_reverse] at hv
    rcases hv with hv | hv
    · simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hv
      rcases hv with rfl | hv | rfl
      · exact absurd hvX (hNX v (by simp))
      · exact absurd hvX (hNX v (by simp [hv]))
      · exact Or.inl rfl
    · have hvq : v ∈ q.support := List.mem_of_mem_tail hv
      by_cases h1 : v = r
      · subst h1
        exact absurd hvX (hNX v (by simp))
      · by_cases h2 : v = t
        · exact Or.inr h2
        · exact absurd (hX hvX) (hqin v hvq h1 h2)
  refine ⟨P', hP', hP's, fun v hv => ?_⟩
  have hv' : v ∈ L₁ ++ [y] ∨ v = s := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    tauto
  rcases hv' with hv' | rfl
  · exact ⟨(hpre v hv').1.mono hle hX, (hpre v hv').2.mono hle hX⟩
  · refine ⟨?_, ?_⟩
    · rcases hsA with h | ⟨r, hr, h⟩
      · exact h.mono hle hX
      · exact hviaN r hr h
    · rcases hsB with h | ⟨r, hr, h⟩
      · exact h.mono hle hX
      · exact hviaN r hr h

/-- **Lemma 5.4 for tight paths, case `r = s`** (Humeau and Pous, page 19). Let `P` be an induced,
tight `C`-path, `P.support = L₁ ++ y :: N ++ s :: L₂`, with every vertex of `L₁ ++ [y]` (the path
`Py_j`) and `s` (the vertex `y_r = y_s`) on both `P`-sides, and the vertices of `N` on no side. Then
"the edge $y_jy_s$ is safe, and in the graph $G+y_jy_s$, all vertices of $Py_jy_s$ lie on both
$Py_jy_sP$-sides." -/
theorem lemma_5_4_tight_of_noSide (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hpre : ∀ v ∈ L₁ ++ [y], IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hno : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} v ∧
      ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hs : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ A} s ∧
      IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s) :
    IsSafe G (edge y s) C ∧ ∃ P' : (G ⊔ edge y s).Walk a b, IsTPath (G ⊔ edge y s) C P' ∧
      P'.support = L₁ ++ y :: s :: L₂ ∧
      ∀ v ∈ L₁ ++ [y, s],
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v ∧
        IsOnSide (G ⊔ edge y s) {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ B} v :=
  ⟨claim_5_5_tight hrot hP hsupp hind htight hno,
    lemma_5_4_sides hrot hP hsupp hpre (Or.inl hs.1) (Or.inl hs.2)⟩

/-- The path `P y s P`: for `P.support = L₁ ++ y :: N ++ s :: L₂`, the list `L₁ ++ y :: s :: L₂`
is the support of a `C`-path of `G + ys` from `a` to `b`. -/
theorem exists_short_path (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂) :
    ∃ P' : (G ⊔ edge y s).Walk a b, IsTPath (G ⊔ edge y s) C P' ∧
      P'.support = L₁ ++ y :: s :: L₂ := by
  classical
  have hnd : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
  have hch : (L₁ ++ y :: N ++ s :: L₂).IsChain G.Adj := hsupp ▸ P.isChain_adj_support
  have hys : y ≠ s := fun h => by
    subst h
    have e : L₁ ++ y :: N ++ y :: L₂ = L₁ ++ y :: (N ++ y :: L₂) := by simp
    rw [e, List.nodup_append, List.nodup_cons] at hnd
    exact hnd.2.1.1 (by simp)
  have hch' : (L₁ ++ y :: s :: L₂).IsChain (G ⊔ edge y s).Adj := by
    have h1 : (L₁ ++ [y]).IsChain G.Adj := by
      have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ [y]) ++ (N ++ s :: L₂) := by simp
      rw [e] at hch
      exact hch.left_of_append
    have h2 : (s :: L₂).IsChain G.Adj := by
      have e : L₁ ++ y :: N ++ s :: L₂ = (L₁ ++ y :: N) ++ (s :: L₂) := by simp
      rw [e] at hch
      exact hch.right_of_append
    have e : L₁ ++ y :: s :: L₂ = (L₁ ++ [y]) ++ (s :: L₂) := by simp
    rw [e, List.isChain_append]
    refine ⟨h1.imp fun _ _ h => Or.inl h, h2.imp fun _ _ h => Or.inl h, fun u hu v hv => ?_⟩
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.mem_def, Option.some.injEq, List.head?_cons] at hu hv
    subst hu hv
    exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, hys⟩)
  have hsub := (sublist_short (L₁ := L₁) (y := y) (N := N) (s := s) (L₂ := L₂))
  have hndP' : (L₁ ++ y :: s :: L₂).Nodup := hnd.sublist hsub
  have hmemC : ∀ v, v ∈ a :: A ++ b :: B → v ∈ C := fun v hv =>
    List.mem_rotate.mp (hrot ▸ hv)
  exact exists_tPath_of_list hch' hndP' (head_of_supp hsupp)
    (last_of_supp hsupp) (hmemC a (by simp)) (hmemC b (by simp)) (fun w hw hwC => by
      have hwP : w ∈ P.support := hsupp ▸ hsub.subset hw
      by_contra hne
      push Not at hne
      exact (hP.2.2.2 w hwP hne.1 hne.2).1 hwC)

end GraphMinor.HP25
