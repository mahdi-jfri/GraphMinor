module

public import GraphMinor.HP25.Prop34
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Corollary 3.5 and Proposition 3.6: web decompositions

Humeau and Pous, arXiv:2505.16431v2, page 11. "**Corollary 3.5.** In a web whose frame $C$ has
length at least four, there is a $C$-path whose endpoints are non-consecutive vertices of $C$."
We follow the paper's proof, from item 2 of Proposition 3.4 (`cor_3_5`).

"**Proposition 3.6.** Every web whose frame has length at least four is a web composition of two
webs." The paper's proof: "By Corollary 3.5 there is a $C$-path $P$ whose endpoints are
non-consecutive vertices of $C$. We may assume without loss of generality that $P$ is an induced
path, i.e., a path in $R$." We first move the path into the rib (`WebData.exists_rib_path`), then
remove chords one at a time (`exists_induced`); each step keeps the ends and uses only vertices of
the old path. The rest of the proof is the split of the rib along the path
(`WebData.split`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-- **Removing chords.** A path list `l` gives an induced path list with the same first and last
entries, on vertices of `l`. -/
theorem exists_induced {R : Set V} : ∀ (n : ℕ) (l : List V), l.length ≤ n → IsPathList G R l →
    ∃ l' : List V, IsPathList G R l' ∧ l'.head? = l.head? ∧ l'.getLast? = l.getLast? ∧
      (∀ v ∈ l', v ∈ l) ∧ ∀ u ∈ l', ∀ v ∈ l', G.Adj u v → IsListEdge l' u v := by
  intro n
  induction n with
  | zero =>
    intro l hl hP
    refine ⟨l, hP, rfl, rfl, fun v hv => hv, fun u hu => ?_⟩
    rw [List.eq_nil_of_length_eq_zero (by omega : l.length = 0)] at hu
    simp at hu
  | succ n ih =>
    intro l hl hP
    by_cases hind : ∀ u ∈ l, ∀ v ∈ l, G.Adj u v → IsListEdge l u v
    · exact ⟨l, hP, rfl, rfl, fun v hv => hv, hind⟩
    push Not at hind
    -- a chord `uv` with `u` before `v`
    obtain ⟨A, u, M, v, B, rfl, huv, hM⟩ : ∃ A u M v B, l = A ++ u :: M ++ v :: B ∧ G.Adj u v ∧
        M ≠ [] := by
      obtain ⟨u, hu, v, hv, huv, hne⟩ := hind
      have key : ∀ {u v : V}, G.Adj u v → ¬ IsListEdge l u v → ∀ A T, l = A ++ u :: T → v ∈ T →
          ∃ A u M v B, l = A ++ u :: M ++ v :: B ∧ G.Adj u v ∧ M ≠ [] := by
        intro u v huv hne A T hl hvT
        obtain ⟨M, B, rfl⟩ := List.append_of_mem hvT
        refine ⟨A, u, M, v, B, by rw [hl]; simp, huv, fun hM => hne ?_⟩
        subst hM
        rw [hl]
        exact IsListEdge.append_right ⟨(u, v), by simp, rfl⟩
      obtain ⟨A, T, hlAT⟩ := List.append_of_mem hu
      have hv' : v ∈ A ++ u :: T := hlAT ▸ hv
      rcases List.mem_append.mp hv' with hvA | hvT
      · obtain ⟨A₁, M', rfl⟩ := List.append_of_mem hvA
        exact key huv.symm (fun h => hne h.symm) A₁ (M' ++ u :: T) (by rw [hlAT]; simp)
          (by simp)
      · rcases List.mem_cons.mp hvT with rfl | hvT
        · exact absurd huv (G.loopless.irrefl _)
        · exact key huv hne A T hlAT hvT
    -- shortcut the chord
    set l₂ := A ++ u :: v :: B with hl₂
    have hsub : l₂.Sublist (A ++ u :: M ++ v :: B) := by
      rw [hl₂, List.append_assoc]
      refine List.Sublist.append_left ?_ A
      refine List.Sublist.cons_cons u ?_
      exact List.sublist_append_right M (v :: B)
    have hch : l₂.IsChain G.Adj := by
      have h₁ : (A ++ [u]).IsChain G.Adj := by
        have := hP.2.1
        rw [show A ++ u :: M ++ v :: B = (A ++ [u]) ++ (M ++ v :: B) by simp] at this
        exact this.left_of_append
      have h₂ : (v :: B).IsChain G.Adj := by
        have := hP.2.1
        rw [show A ++ u :: M ++ v :: B = (A ++ u :: M) ++ (v :: B) by simp] at this
        exact this.right_of_append
      have h₃ : ([u] ++ v :: B).IsChain G.Adj := List.isChain_cons_cons.mpr ⟨huv, h₂⟩
      have := List.IsChain.append_overlap h₁ h₃ (by simp)
      simpa [hl₂] using this
    have hP₂ : IsPathList G R l₂ :=
      ⟨hP.1.sublist hsub, hch, fun w hw => hP.2.2 w (hsub.subset hw)⟩
    have hlen : l₂.length ≤ n := by
      have := List.length_pos_of_ne_nil hM
      simp [hl₂] at hl ⊢
      omega
    obtain ⟨l', hP', hh, hlst, hsub', hind'⟩ := ih l₂ hlen hP₂
    refine ⟨l', hP', ?_, ?_, fun w hw => hsub.subset (hsub' w hw), hind'⟩
    · rw [hh, hl₂]
      cases A <;> simp
    · rw [hlst, hl₂, show A ++ u :: v :: B = (A ++ [u]) ++ (v :: B) by simp,
        show A ++ u :: M ++ v :: B = (A ++ u :: M) ++ (v :: B) by simp,
        List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_append_of_ne_nil _ (by simp)]

variable {S : Set V} {C : List V}

/-- **Corollary 3.5** (Humeau and Pous, page 11). "In a web whose frame $C$ has length at least
four, there is a $C$-path whose endpoints are non-consecutive vertices of $C$." -/
theorem cor_3_5 (h : IsWebOn G S C) (h4 : 4 ≤ C.length) :
    ∃ c c' : V, ∃ P : G.Walk c c', IsTPath G C P ∧ c ≠ c' ∧ ¬ IsCycleEdge C c c' := by
  classical
  have hC : IsCycleList G C := by
    obtain ⟨-, -, -, -, ⟨hC, -⟩, -⟩ := h
    exact hC
  have hnd := hC.2.1
  -- two non-consecutive vertices of `C`
  have h0 : 0 < C.length := by omega
  have h2 : 2 < C.length := by omega
  have hne : C[0] ≠ C[2] := fun he => by
    have := (List.Nodup.getElem_inj_iff hnd).mp he
    omega
  have hnot : ¬ IsCycleEdge C C[0] C[2] := by
    rw [isCycleEdge_iff_idxOf hnd, hnd.idxOf_getElem, hnd.idxOf_getElem]
    rintro ⟨-, -, h | h⟩
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h
      omega
  have hS : ∀ v ∈ C, v ∈ S := h.frame_subset
  -- "If $c$ is $C$-connected to $c'$ then this provides a $C$-path whose endpoints are
  -- non-consecutive vertices of $C$."
  rcases prop_3_4_ii h (hS _ (List.getElem_mem h0)) (hS _ (List.getElem_mem h2)) with
    ⟨z, hz, p, hp, hpC⟩ | ⟨u, u', hu, hu', -, -, -, -, -, hcomp⟩
  · rw [mem_singleton_iff] at hz
    subst hz
    refine ⟨C[0], C[2], p, ⟨hp, List.getElem_mem _, List.getElem_mem _, fun w hw h1 h2 => ?_⟩,
      hne, hnot⟩
    exact ⟨hpC w hw h1 h2, hpC w hw h1 h2⟩
  · -- "Otherwise, by Proposition 3.4, the web is given as an edge composition along some edge
    -- $uu'$ between nonconsecutive vertices of $C$. This edge is a $C$-path whose endpoints are
    -- non-consecutive vertices."
    obtain ⟨huu, hnot', -, -⟩ := hcomp.chord hnd
    exact ⟨u, u', huu.toWalk, isTPath_toWalk huu hu hu', huu.ne, hnot'⟩

/-- **Proposition 3.6** (Humeau and Pous, page 11). "Every web whose frame has length at least four
is a web composition of two webs." The path of the composition has non-consecutive ends on the
frame, so both webs are smaller. -/
theorem prop_3_6 (h : IsWebOn G S C) (h4 : 4 ≤ C.length) :
    ∃ (a b : V) (m : List V), ¬ IsCycleEdge C a b ∧ IsWebComposition G S C (a :: m ++ [b]) := by
  classical
  obtain ⟨R, tri, W⟩ := h.exists_webData
  have hC := W.rib.1
  have hCR := W.rib.2.1
  obtain ⟨c, c', P, ⟨hP, hc, hc', hin⟩, hcc, hnot⟩ := cor_3_5 h h4
  -- the path moved into the rib
  obtain ⟨q, hq, hqR⟩ := W.exists_rib_path P (hCR c hc) (hCR c' hc')
  -- and made induced
  obtain ⟨l, hl, hhead, hlast, hsub, hind⟩ :=
    exists_induced (G := G) (R := R) q.support.length q.support le_rfl
      (isPathList_support hq fun v hv => (hqR v hv).1)
  have hhead' : l.head? = some c := by rw [hhead, ← Walk.cons_tail_support q]; rfl
  have hlast' : l.getLast? = some c' := by
    rw [hlast, List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]
  -- `l = c m c'`
  obtain ⟨m, rfl⟩ : ∃ m, l = c :: m ++ [c'] := by
    match l, hhead', hlast' with
    | x :: t, hh, hl' =>
      have hxc : x = c := Option.some_injective _ hh
      obtain ⟨m, y, ht⟩ : ∃ m y, t = m ++ [y] := by
        cases t using List.reverseRecOn with
        | nil => simp at hl'; exact absurd (hxc.symm.trans hl') hcc
        | append_singleton m y => exact ⟨m, y, rfl⟩
      subst ht
      have hy : y = c' := by
        rw [show x :: (m ++ [y]) = (x :: m) ++ [y] by simp,
          List.getLast?_append_of_ne_nil _ (by simp)] at hl'
        exact Option.some_injective _ hl'
      exact ⟨m, by rw [hxc, hy]; simp⟩
  have hmC : ∀ v ∈ m, v ∉ C := by
    intro v hv hvC
    have hnd := hl.1
    rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
    have hvc : v ≠ c := fun he => hnd.1 (List.mem_append_left _ (he ▸ hv))
    have hvc' : v ≠ c' := fun he => hnd.2.2.2 v hv c' (by simp) he
    have hvP : v ∈ P.support := (hqR v (hsub v (by simp [hv]))).2
    exact (hin v hvP hvc hvc').1 hvC
  obtain ⟨k, A, B, hrot⟩ := exists_rotate_cons_cons hc hc' hcc
  exact ⟨c, c', m, hnot, W.split hrot hnot hl hmC hind⟩

end GraphMinor.HP25
