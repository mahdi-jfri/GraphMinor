module

public import GraphMinor.HP25.Prop51
public import GraphMinor.HP25.Lemma43
import GraphMinor.HP25.Completion
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case2
import GraphMinor.HP25.Prop32
import GraphMinor.HP25.Split

/-!
# Proposition 5.2: the two subinstances, when `C` is crossed

Humeau and Pous, Proposition 5.2 (page 17): "If $P$ separates $\mathring P_1$ from $\mathring P_2$ and
all vertices of $P$ are on both $P$-sides, then $C$ is crossed in $G$ if and only if $P_1P$ is crossed
in $G_1$ or $P_2P$ is crossed in $G_2$, where $G_1$ and $G_2$ are the subgraphs obtained by
Proposition 5.1."

The setting (`SplitSetting`) is that of Proposition 5.1: `C = a A b B` up to rotation, a `C`-path
`P = a m b` separating `A` from `B`, and `G` the path composition along `P` of `G₁ ⊇ a A b` and
`G₂ ⊇ b B a`. The cycles of the two subinstances are `C₁ = a A b m⁻¹` (the paper's `P₁P`) and
`C₂ = b B a m` (the paper's `P₂P`, read backwards).

This file proves the implication from a crossing of `C` (`SplitSetting.crossed_side`), by the
paper's argument for its contrapositive: "Assume that $P_iP$ is crossless in $G_i$ for every
$i\in\{1,2\}$. By Theorem 1.3, $G_i$ has a web completion $F_i$. In $G_i+F_i$, the path $P$ must be
induced." Then "By Proposition 3.1 the web composition of $G_1+F_1$ and $G_2+F_2$ along $P$ is a web".
We take for `G_i + F_i` a maximal crossless completion of `G_i` on its vertices, a web by
`lemma_4_3_on`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The setting of Propositions 5.1 and 5.2: `C = a A b B` up to rotation with `A`, `B` not empty,
`P = a m b` a `C`-path that separates `A` from `B`, and `G` the path composition along `P` of
`G₁` on `S₁`, which contains `a A b`, and `G₂` on `S₂`, which contains `b B a`. -/
structure SplitSetting (G : SimpleGraph V) (C : List V) (a b : V) (A B m : List V) (k : ℕ)
    (P : G.Walk a b) (G₁ G₂ : SimpleGraph V) (S₁ S₂ : Set V) : Prop where
  cyc : IsCycleList G C
  rot : C.rotate k = a :: A ++ b :: B
  neA : A ≠ []
  neB : B ≠ []
  path : IsTPath G C P
  supp : P.support = a :: m ++ [b]
  sep : Separates G {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}
  comp : IsPathComposition G G₁ G₂ S₁ S₂ P.support
  chain₁ : (a :: A ++ [b]).IsChain G₁.Adj
  sub₁ : ∀ v ∈ a :: A ++ [b], v ∈ S₁
  chain₂ : (b :: B ++ [a]).IsChain G₂.Adj
  sub₂ : ∀ v ∈ b :: B ++ [a], v ∈ S₂

/-- "we say that a vertex $y\in P$ *is on $P$-side $i$* when $y$ and $\mathring{P_i}$ are
$P$-connected" (page 17), read with `C ∪ P`-paths as in the proofs. Every vertex of `P` is on both
sides. -/
@[expose] def OnBothSides (G : SimpleGraph V) (C A B : List V) {a b : V} (P : G.Walk a b) : Prop :=
  ∀ v ∈ P.support, IsOnSide G {u | u ∈ C ∨ u ∈ P.support} {u | u ∈ A} v ∧
    IsOnSide G {u | u ∈ C ∨ u ∈ P.support} {u | u ∈ B} v

/-- Path composition is symmetric. -/
theorem IsPathComposition.symm {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V} {l : List V}
    (h : IsPathComposition G G₁ G₂ S₁ S₂ l) : IsPathComposition G G₂ G₁ S₂ S₁ l := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨by rw [h1, sup_comm], h3, h2, by rw [union_comm, h4], by rw [inter_comm, h5], h7, h6⟩

/-- A path that ends in `S₁ - l` and meets `l` at most at its start runs inside `G₁`. -/
theorem IsPathComposition.walk_side {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V} {l : List V}
    (h : IsPathComposition G G₁ G₂ S₁ S₂ l) : ∀ {u w : V} (p : G.Walk u w), p.IsPath →
      w ∈ S₁ → w ∉ l → (∀ x ∈ p.support, x ≠ u → x ∉ l) →
      (∀ x ∈ p.support, x ∈ S₁) ∧ ∀ e ∈ p.edges, e ∈ G₁.edgeSet
  | _, _, .nil, _, hw, _, _ => ⟨fun x hx => by simp at hx; exact hx ▸ hw, by simp⟩
  | u, w, .cons (v := v) huv p, hp, hw, hwl, hin => by
    have hup : u ∉ p.support := (Walk.cons_isPath_iff _ _).mp hp |>.2
    have hvl : v ∉ l := hin v (by simp) fun e => hup (e ▸ p.start_mem_support)
    obtain ⟨ih1, ih2⟩ := h.walk_side p ((Walk.cons_isPath_iff _ _).mp hp).1 hw hwl
      fun x hx _ => hin x (by simp [hx]) fun e => hup (e ▸ hx)
    have hvS := ih1 v p.start_mem_support
    have h1 : G₁.Adj u v := by
      have : (G₁ ⊔ G₂).Adj u v := h.1 ▸ huv
      rcases this with h' | h'
      · exact h'
      · have : v ∈ S₁ ∩ S₂ := ⟨hvS, h.2.2.1 h'.symm⟩
        rw [h.2.2.2.2.1] at this
        exact absurd this hvl
    refine ⟨fun x hx => ?_, fun e he => ?_⟩
    · rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h.2.1 h1
      · exact ih1 x hx
    · rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact h1
      · exact ih2 e he

/-- **A chord crosses a path to the rest of the cycle.** If `u v` is an edge of `W` between two
entries of `T`, and a `T`-path `Q` from `z` to `c` misses `u` and `v`, with `u, v` alternating with
`z, c` on `T`, then `T` is crossed in `W`. -/
theorem isCrossed_of_chord {W : SimpleGraph V} {T : List V} {u v z c : V}
    (halt : Alternate T u v z c) (hadj : W.Adj u v) (huT : u ∈ T) (hvT : v ∈ T)
    (Q : W.Walk z c) (hQ : IsTPath W T Q) (hu : u ∉ Q.support) (hv : v ∉ Q.support) :
    IsCrossed W T := by
  have hQ' : IsTPath W T (Walk.cons hadj Walk.nil) := by
    refine ⟨by simp [W.ne_of_adj hadj], huT, hvT, fun x hx h1 h2 => ?_⟩
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl h2
  refine isCrossed_of_alternate' halt _ Q hQ' hQ fun x hx hxQ => ?_
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · exact hu hxQ
  · exact hv hxQ

/-- Alternation is unchanged by rotating the list. -/
theorem Alternate.of_rotate {T : List V} {r : ℕ} {u v z c : V} (h : Alternate (T.rotate r) u v z c) :
    Alternate T u v z c := by
  obtain ⟨k, L₁, L₂, hrot, h1, h2⟩ := h
  exact ⟨r + k, L₁, L₂, by rw [← List.rotate_rotate]; exact hrot, h1, h2⟩

namespace SplitSetting

variable {C : List V} {a b : V} {A B m : List V} {k : ℕ} {P : G.Walk a b}
  {G₁ G₂ : SimpleGraph V} {S₁ S₂ : Set V}

theorem nodup (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) : (a :: A ++ b :: B).Nodup := by
  have := hs.cyc.2.1
  rwa [← List.nodup_rotate (n := k), hs.rot] at this

theorem mem_C (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} :
    v ∈ C ↔ v ∈ a :: A ++ b :: B := by
  rw [← List.mem_rotate (n := k), hs.rot]

/-- The inner vertices of `P` are off `C`. -/
theorem m_not_mem (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} (hv : v ∈ m) :
    v ∉ C := by
  have hnd := hs.path.1.support_nodup
  rw [hs.supp] at hnd
  have hP : v ∈ P.support := by rw [hs.supp]; simp [hv]
  have hva : v ≠ a := fun e => by
    subst e
    rw [List.cons_append, List.nodup_cons] at hnd
    exact hnd.1 (List.mem_append_left _ hv)
  have hvb : v ≠ b := fun e => by
    subst e
    rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
    exact hnd.2.2.2 v hv v (by simp) rfl
  exact (hs.path.2.2.2 v hP hva hvb).1

/-- The inner vertices of `P₁` and `P₂` are off `P`. -/
theorem AB_not_mem (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} (hv : v ∈ A ++ B) :
    v ∉ P.support := by
  have hnd := hs.nodup
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  intro hvP
  rw [hs.supp] at hvP
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hvP
  rcases hvP with rfl | hvm | rfl
  · exact hnd.1 (by rcases List.mem_append.mp hv with h | h <;> simp [h])
  · exact hs.m_not_mem hvm (hs.mem_C.mpr (by rcases List.mem_append.mp hv with h | h <;> simp [h]))
  · rcases List.mem_append.mp hv with h | h
    · exact hnd.2.2.2 v h v (by simp) rfl
    · exact (List.nodup_cons.mp hnd.2.2.1).1 h

/-- `P₁ P = a A b m⁻¹` is a cycle of `G₁`. -/
theorem cycle₁ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) :
    IsCycleList G₁ (a :: A ++ b :: m.reverse) := by
  have hnd := hs.nodup
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  have hPnd := hs.path.1.support_nodup
  have hPch := hs.comp.2.2.2.2.2.1
  rw [hs.supp] at hPnd hPch
  have h₁ : IsPathList G₁ univ (a :: A ++ [b]) :=
    ⟨by
      rw [List.cons_append, List.nodup_cons, List.nodup_append]
      refine ⟨by simpa using ⟨fun h => hnd.1 (List.mem_append_left _ h), fun e => hnd.1 (by simp [e])⟩,
        hnd.2.1,
        List.nodup_singleton _, fun x hx y hy e => ?_⟩
      rw [List.mem_singleton] at hy
      subst e; subst hy
      exact hnd.2.2.2 x hx x (by simp) rfl,
      hs.chain₁, fun _ _ => trivial⟩
  have h₂ : IsPathList G₁ univ (b :: m.reverse ++ [a]) := by
    have := (IsPathList.reverse (R := univ) (l := a :: m ++ [b]) ⟨hPnd, hPch, fun _ _ => trivial⟩)
    simpa using this
  refine isCycleList_of_two_paths h₁ h₂ (fun v hv hvm => ?_) ?_ (Or.inl hs.neA)
  · exact hs.AB_not_mem (List.mem_append_left _ hv) (by rw [hs.supp]; simp [List.mem_reverse.mp hvm])
  · intro e; subst e; exact hnd.1 (by simp)

/-- `P₂ P`, read backwards as `b B a m`, is a cycle of `G₂`. -/
theorem cycle₂ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) :
    IsCycleList G₂ (b :: B ++ a :: m) := by
  have hnd := hs.nodup
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  have hPnd := hs.path.1.support_nodup
  have hPch := hs.comp.2.2.2.2.2.2
  rw [hs.supp] at hPnd hPch
  have hbB := List.nodup_cons.mp hnd.2.2.1
  have h₁ : IsPathList G₂ univ (b :: B ++ [a]) :=
    ⟨by
      rw [List.cons_append, List.nodup_cons, List.nodup_append]
      refine ⟨by simpa using ⟨hbB.1, fun h => hnd.1 (by simp [h])⟩, hbB.2,
        List.nodup_singleton _, fun x hx y hy e => ?_⟩
      rw [List.mem_singleton] at hy
      subst e; subst hy
      exact hnd.1 (by simp [hx]),
      hs.chain₂, fun _ _ => trivial⟩
  have h₂ : IsPathList G₂ univ (a :: m ++ [b]) := ⟨hPnd, hPch, fun _ _ => trivial⟩
  refine isCycleList_of_two_paths h₁ h₂ (fun v hv hvm => ?_) ?_ (Or.inl hs.neB)
  · exact hs.AB_not_mem (List.mem_append_right _ hv) (by rw [hs.supp]; simp [hvm])
  · intro e; subst e; exact hnd.1 (by simp)

theorem P_sub₁ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} (hv : v ∈ P.support) :
    v ∈ S₁ := by
  have : v ∈ S₁ ∩ S₂ := by rw [hs.comp.2.2.2.2.1]; exact hv
  exact this.1

theorem P_sub₂ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V} (hv : v ∈ P.support) :
    v ∈ S₂ := by
  have : v ∈ S₁ ∩ S₂ := by rw [hs.comp.2.2.2.2.1]; exact hv
  exact this.2

/-- A path from a vertex of `P` to `A` given by "on side 1" is a path of `G₁`, and a
`P₁ P`-path. -/
theorem side_path₁ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V}
    (hv : v ∈ P.support) (hside : IsOnSide G {u | u ∈ C ∨ u ∈ P.support} {u | u ∈ A} v) :
    ∃ c ∈ A, ∃ Q : G₁.Walk v c, IsTPath G₁ (a :: A ++ b :: m.reverse) Q ∧
      ∀ x ∈ Q.support, x ≠ v → x ∉ P.support := by
  obtain ⟨c, hc, Q, hQ, hin⟩ := hside
  have hcP : c ∉ P.support := hs.AB_not_mem (List.mem_append_left _ hc)
  have hoff : ∀ x ∈ Q.support, x ≠ v → x ∉ P.support := fun x hx hxv => by
    by_cases hxc : x = c
    · exact hxc ▸ hcP
    · exact fun h' => hin x hx hxv hxc (Or.inr h')
  obtain ⟨-, hE⟩ := hs.comp.walk_side Q hQ (hs.sub₁ c (List.mem_append_left _ (List.mem_cons_of_mem _ hc))) hcP hoff
  refine ⟨c, hc, Q.transfer G₁ hE, ⟨hQ.transfer _, ?_, List.mem_append_left _ (List.mem_cons_of_mem _ hc),
    fun x hx h1 h2 => ?_⟩, ?_⟩
  · have : v ∈ a :: m ++ [b] := hs.supp ▸ hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at this
    rcases this with rfl | h | rfl
    · simp
    · simp [h]
    · simp
  · rw [Walk.support_transfer] at hx
    have hX := hin x hx h1 h2
    have hxC : x ∉ a :: A ++ b :: m.reverse := fun h' => by
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at h'
      apply hX
      rcases h' with rfl | h' | rfl | h'
      · exact Or.inr P.start_mem_support
      · exact Or.inl (hs.mem_C.mpr (by simp [h']))
      · exact Or.inr P.end_mem_support
      · exact Or.inr (by rw [hs.supp]; simp [h'])
    exact ⟨hxC, hxC⟩
  · rw [Walk.support_transfer]; exact hoff

/-- The same for side 2, as a `P₂ P`-path of `G₂`. -/
theorem side_path₂ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) {v : V}
    (hv : v ∈ P.support) (hside : IsOnSide G {u | u ∈ C ∨ u ∈ P.support} {u | u ∈ B} v) :
    ∃ c ∈ B, ∃ Q : G₂.Walk v c, IsTPath G₂ (b :: B ++ a :: m) Q ∧
      ∀ x ∈ Q.support, x ≠ v → x ∉ P.support := by
  obtain ⟨c, hc, Q, hQ, hin⟩ := hside
  have hcP : c ∉ P.support := hs.AB_not_mem (List.mem_append_right _ hc)
  have hoff : ∀ x ∈ Q.support, x ≠ v → x ∉ P.support := fun x hx hxv => by
    by_cases hxc : x = c
    · exact hxc ▸ hcP
    · exact fun h' => hin x hx hxv hxc (Or.inr h')
  obtain ⟨-, hE⟩ := hs.comp.symm.walk_side Q hQ (hs.sub₂ c (List.mem_append_left _ (List.mem_cons_of_mem _ hc))) hcP hoff
  refine ⟨c, hc, Q.transfer G₂ hE, ⟨hQ.transfer _, ?_, List.mem_append_left _ (List.mem_cons_of_mem _ hc),
    fun x hx h1 h2 => ?_⟩, ?_⟩
  · have : v ∈ a :: m ++ [b] := hs.supp ▸ hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at this
    rcases this with rfl | h | rfl
    · simp
    · simp [h]
    · simp
  · rw [Walk.support_transfer] at hx
    have hX := hin x hx h1 h2
    have hxC : x ∉ b :: B ++ a :: m := fun h' => by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at h'
      apply hX
      rcases h' with rfl | h' | rfl | h'
      · exact Or.inr P.end_mem_support
      · exact Or.inl (hs.mem_C.mpr (by simp [h']))
      · exact Or.inr P.start_mem_support
      · exact Or.inr (by rw [hs.supp]; simp [h'])
    exact ⟨hxC, hxC⟩
  · rw [Walk.support_transfer]; exact hoff

/-- A `T`-path of a subgraph is a `T`-path of a larger graph. -/
theorem IsTPath.mapLe' {H W : SimpleGraph V} {T : List V} {u v : V} {Q : H.Walk u v}
    (hQ : IsTPath H T Q) (hle : H ≤ W) : IsTPath W T (Q.mapLe hle) :=
  ⟨(Walk.isPath_mapLe _).mpr hQ.1, hQ.2.1, hQ.2.2.1, by
    rw [Walk.support_mapLe_eq_support]; exact hQ.2.2.2⟩

/-- **`P` is induced in a crossless extension of `G₁`** (page 17): "if $xy$ were an edge of
$G_i+F_i$ between non-consecutive vertices of $P$, then we could consider $z$ an inner vertex of
$xPy$. As $z$ is on both $P$-sides, there is in $G_i$ a $\mathring{P_i}$-$z$ path $Q$. The pair
$(Q,xy)$ is a crossing of $P_iP$ in the web $G_i+F_i$, a contradiction." -/
theorem induced₁ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) (hsides : OnBothSides G C A B P)
    {W : SimpleGraph V} (hle : G₁ ≤ W) (hnc : ¬ IsCrossed W (a :: A ++ b :: m.reverse)) :
    ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W.Adj u v → IsListEdge (a :: m ++ [b]) u v := by
  have hnd : P.support.Nodup := hs.path.1.support_nodup
  have hmemT : ∀ v ∈ P.support, v ∈ a :: A ++ b :: m.reverse := by
    rw [hs.supp]
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with h | h | h <;> simp [h]
  have hrot : (a :: A ++ b :: m.reverse).rotate (A.length + 1) = P.support.reverse ++ A := by
    rw [rotate_cons_append_cons, hs.supp]; simp
  have key : ∀ t t' (ht : t' < P.support.length) (_ : t + 2 ≤ t'),
      ¬ W.Adj (P.support[t]'(by omega)) P.support[t'] := by
    intro t t' ht htt hadj
    have hz : P.support[t' - 1]'(by omega) ∈ P.support := List.getElem_mem _
    obtain ⟨c, hc, Q, hQ, hoff⟩ := hs.side_path₁ hz (hsides _ hz).1
    have halt := alternate_chord (P := P.support.reverse) (L := A)
      (i := P.support.length - 1 - t') (j := P.support.length - 1 - t) (by omega)
      (by simp) hc
    simp only [List.getElem_reverse] at halt
    have e1 : P.support[P.support.length - 1 - (P.support.length - 1 - t')]'(by omega) =
        P.support[t'] := by congr 1; omega
    have e2 : P.support[P.support.length - 1 - (P.support.length - 1 - t)]'(by omega) =
        P.support[t]'(by omega) := by congr 1; omega
    have e3 : P.support[P.support.length - 1 - (P.support.length - 1 - t' + 1)]'(by omega) =
        P.support[t' - 1]'(by omega) := by congr 1; omega
    rw [e1, e2, e3] at halt
    have hne : ∀ {i} (hi : i < P.support.length), i ≠ t' - 1 →
        P.support[i] ∉ (Q.mapLe hle).support := by
      intro i hi hit hmem
      rw [Walk.support_mapLe_eq_support] at hmem
      by_cases e : P.support[i] = P.support[t' - 1]'(by omega)
      · exact hit (hnd.getElem_inj_iff.mp e)
      · exact hoff _ hmem e (List.getElem_mem hi)
    exact hnc (isCrossed_of_chord (Alternate.of_rotate (hrot ▸ halt)) hadj.symm
      (hmemT _ (List.getElem_mem _)) (hmemT _ (List.getElem_mem _)) (Q.mapLe hle)
      (IsTPath.mapLe' hQ hle) (hne _ (by omega)) (hne _ (by omega)))
  rw [← hs.supp]
  intro u hu v hv huv
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hv
  have hne : t ≠ t' := fun e => by subst e; exact W.ne_of_adj huv rfl
  rcases (show t' = t + 1 ∨ t = t' + 1 ∨ t + 2 ≤ t' ∨ t' + 2 ≤ t by omega)
    with rfl | rfl | h' | h'
  · exact isListEdge_getElem _ t ht'
  · exact (isListEdge_getElem _ t' ht).symm
  · exact absurd huv (key t t' ht' h')
  · exact absurd huv.symm (key t' t ht h')

/-- `P` is induced in a crossless extension of `G₂`, as for `G₁`. -/
theorem induced₂ (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) (hsides : OnBothSides G C A B P)
    {W : SimpleGraph V} (hle : G₂ ≤ W) (hnc : ¬ IsCrossed W (b :: B ++ a :: m)) :
    ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W.Adj u v → IsListEdge (a :: m ++ [b]) u v := by
  have hnd : P.support.Nodup := hs.path.1.support_nodup
  have hmemT : ∀ v ∈ P.support, v ∈ b :: B ++ a :: m := by
    rw [hs.supp]
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hv
    rcases hv with h | h | h <;> simp [h]
  have hrot : (b :: B ++ a :: m).rotate (B.length + 1) = P.support ++ B := by
    rw [rotate_cons_append_cons, hs.supp]; simp
  have key : ∀ t t' (ht : t' < P.support.length) (_ : t + 2 ≤ t'),
      ¬ W.Adj (P.support[t]'(by omega)) P.support[t'] := by
    intro t t' ht htt hadj
    have hz : P.support[t + 1]'(by omega) ∈ P.support := List.getElem_mem _
    obtain ⟨c, hc, Q, hQ, hoff⟩ := hs.side_path₂ hz (hsides _ hz).2
    have halt := alternate_chord (P := P.support) (L := B) htt ht hc
    have hne : ∀ {i} (hi : i < P.support.length), i ≠ t + 1 →
        P.support[i] ∉ (Q.mapLe hle).support := by
      intro i hi hit hmem
      rw [Walk.support_mapLe_eq_support] at hmem
      by_cases e : P.support[i] = P.support[t + 1]'(by omega)
      · exact hit (hnd.getElem_inj_iff.mp e)
      · exact hoff _ hmem e (List.getElem_mem hi)
    exact hnc (isCrossed_of_chord (Alternate.of_rotate (hrot ▸ halt)) hadj
      (hmemT _ (List.getElem_mem _)) (hmemT _ (List.getElem_mem _)) (Q.mapLe hle)
      (IsTPath.mapLe' hQ hle) (hne _ (by omega)) (hne _ (by omega)))
  rw [← hs.supp]
  intro u hu v hv huv
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hv
  have hne : t ≠ t' := fun e => by subst e; exact W.ne_of_adj huv rfl
  rcases (show t' = t + 1 ∨ t = t' + 1 ∨ t + 2 ≤ t' ∨ t' + 2 ≤ t by omega)
    with rfl | rfl | h' | h'
  · exact isListEdge_getElem _ t ht'
  · exact (isListEdge_getElem _ t' ht).symm
  · exact absurd huv (key t t' ht' h')
  · exact absurd huv.symm (key t' t ht h')

/-- **Proposition 5.2, the implication from a crossing of `C`** (page 17): if `C` is crossed in `G`, then `P₁ P` is crossed in `G₁` or `P₂ P` is
crossed in `G₂`. Otherwise both have web completions in which `P` is induced (`induced₁`,
`induced₂`), their union is a web with frame `C` (Proposition 3.1), and it contains `G`. -/
theorem crossed_side [Finite V]
    (hs : SplitSetting G C a b A B m k P G₁ G₂ S₁ S₂) (hsides : OnBothSides G C A B P)
    (hc : IsCrossed G C) :
    IsCrossed G₁ (a :: A ++ b :: m.reverse) ∨ IsCrossed G₂ (b :: B ++ a :: m) := by
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  obtain ⟨W₁, hle₁, hmax₁⟩ := exists_maxCrosslessOn hs.comp.2.1 h1
  obtain ⟨W₂, hle₂, hmax₂⟩ := exists_maxCrosslessOn hs.comp.2.2.1 h2
  have hPm : ∀ v ∈ m, v ∈ P.support := fun v hv => by rw [hs.supp]; simp [hv]
  have hweb₁ := lemma_4_3_on _ W₁ S₁ _ rfl (hs.cycle₁.mono hle₁) (fun v hv => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at hv
    rcases hv with rfl | hv | rfl | hv
    · exact hs.sub₁ _ (by simp)
    · exact hs.sub₁ _ (by simp [hv])
    · exact hs.sub₁ _ (by simp)
    · exact hs.P_sub₁ (hPm v hv)) hmax₁
  have hweb₂ := lemma_4_3_on _ W₂ S₂ _ rfl (hs.cycle₂.mono hle₂) (fun v hv => by
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hv
    rcases hv with rfl | hv | rfl | hv
    · exact hs.sub₂ _ (by simp)
    · exact hs.sub₂ _ (by simp [hv])
    · exact hs.sub₂ _ (by simp)
    · exact hs.P_sub₂ (hPm v hv)) hmax₂
  have hweb := isWebOn_sup_of_pieces hs.rot hs.comp.2.2.2.1
    (by rw [hs.comp.2.2.2.2.1, hs.supp]) hweb₁ hweb₂
    (hs.induced₁ hsides hle₁ hmax₁.2.1) (hs.induced₂ hsides hle₂ hmax₂.2.1)
  refine hweb.not_isCrossed (hc.mono ?_)
  rw [hs.comp.1]
  exact sup_le_sup hle₁ hle₂

end SplitSetting

end GraphMinor.HP25
