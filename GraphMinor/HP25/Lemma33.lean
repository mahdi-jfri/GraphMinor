module

public import GraphMinor.HP25.Prop23
public import GraphMinor.HP25.Defs
import GraphMinor.HP25.RibConnected
import GraphMinor.HP25.WebPath
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Lemma 3.3

Humeau and Pous, arXiv:2505.16431v2, Lemma 3.3 (page 9): "Let $x$ be a vertex in a web $G$ with
frame $C$ such that $|C|\ge 4$. There exists a $C$-path $P$ between non-consecutive vertices $c_x$
and $c_x'$ of $C$ such that $x$ is $C$-connected to all vertices of $P$."

"`x` is `C`-connected to `v`" is `IsConnectedAvoiding G {z | z ∈ C} x {v}`: a path from `x` to `v`
with no inner vertex on `C` (Section 2.1, page 5: "A third set of vertices $U$ is *$H$-connected
to $K$* when there is a $H$-path from $U$ to $K$").

We follow the paper's proof. It first treats a rib (`lemma_3_3_rib`), with all paths in the rib.
* `x ∈ C`: by Proposition 2.3 the neighbours of `x` form a path `F` from the predecessor to the
  successor of `x` on `C`. If `F` has no inner vertex on `C`, it is the path. Otherwise an inner
  vertex `y` of `F` on `C` is adjacent to `x` and not consecutive with it, and the path is `xy`.
* `x ∉ C`: ribs are connected (`IsRibEmbedding.reach_frame`). Take a path `P` from `x` to a vertex
  `c` of `C` with no inner vertex on `C`, and let `u` be its first vertex adjacent to `c`. The
  neighbours of `c` form a path from `d` to `d'` (Proposition 2.3) through `u`; it gives paths `Q`
  and `R` from `u` to `d` and to `d'`, disjoint except for `u`. Let `c_x` and `c_x'` be their first
  vertices on `C`. The paper shows that `c_x` and `c_x'` are not consecutive since otherwise the
  edge `c c_x` would bound three faces. We use the form of this fact given by Proposition 2.3: two
  neighbours of `c` are adjacent only when they are consecutive on the path of neighbours of `c`,
  and `u` lies between `c_x` and `c_x'` on it.

Then the web (`lemma_3_3`). The paper: "It is sufficient to prove the statement for ribs. ... two
clique vertices are $C$-connected in $G$ if and only if two of their rib neighbours are
$C$-connected in the rib of $G$." For a clique vertex `x` on the triangle `T`, we use a vertex of `T`
off `C` if there is one. If all of `T` is on `C`, two vertices of `T` are not consecutive on `C`
(since `|C| ≥ 4`), and the edge between them is the path.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-! ### Walks -/

/-- The part of a walk up to its first vertex in `S`. -/
theorem exists_first_hit {W : Type*} {H : SimpleGraph W} (S : Set W) :
    ∀ {u v : W} (w : H.Walk u v), v ∈ S → ∃ s ∈ S, ∃ w' : H.Walk u s,
      (∀ y ∈ w'.support, y ∈ w.support) ∧ (∀ y ∈ w'.support, y ≠ s → y ∉ S) ∧
      (w.IsPath → w'.IsPath)
  | _, _, .nil, hv => ⟨_, hv, .nil, fun _ hy => hy,
      fun _ hy hne => by simp at hy; exact absurd hy hne, fun _ => Walk.IsPath.nil⟩
  | u, _, .cons h p, hv => by
    by_cases hu : u ∈ S
    · exact ⟨u, hu, .nil, fun y hy => by simp at hy; simp [hy],
        fun y hy hne => by simp at hy; exact absurd hy hne, fun _ => Walk.IsPath.nil⟩
    · obtain ⟨s, hs, w', h1, h2, h3⟩ := exists_first_hit S p hv
      refine ⟨s, hs, .cons h w', fun y hy => ?_, fun y hy hne => ?_, fun hp => ?_⟩
      · rw [Walk.support_cons, List.mem_cons] at hy ⊢
        rcases hy with rfl | hy
        · exact Or.inl rfl
        · exact Or.inr (h1 y hy)
      · rw [Walk.support_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact hu
        · exact h2 y hy hne
      · rw [Walk.cons_isPath_iff] at hp ⊢
        exact ⟨h3 hp.1, fun hm => hp.2 (h1 u hm)⟩

/-- Two paths that meet only at the common end form a path. -/
theorem isPath_append_of {W : Type*} {H : SimpleGraph W} {a b c : W} {p : H.Walk a b}
    {q : H.Walk b c} (hp : p.IsPath) (hq : q.IsPath)
    (h : ∀ y ∈ p.support, y ∈ q.support → y = b) : (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  have hqn := (Walk.isPath_def q).mp hq
  rw [← Walk.cons_tail_support q] at hqn
  refine ⟨(Walk.isPath_def p).mp hp, (List.nodup_cons.mp hqn).2, ?_⟩
  rintro y hy z hz rfl
  have hyb := h y hy (List.mem_of_mem_tail hz)
  subst hyb
  exact (List.nodup_cons.mp hqn).1 hz

/-- On a path `p.append q`, a common vertex of `p` and `q` is the vertex where they meet. -/
theorem eq_of_mem_append_path {W : Type*} {H : SimpleGraph W} {a b c : W} {p : H.Walk a b}
    {q : H.Walk b c} (h : (p.append q).IsPath) {y : W} (hp : y ∈ p.support)
    (hq : y ∈ q.support) : y = b := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append] at h
  rw [← Walk.cons_tail_support q, List.mem_cons] at hq
  rcases hq with rfl | hq
  · rfl
  · exact absurd rfl (h.2.2 y hp y hq)

/-- A walk whose inner vertices avoid `X` gives a path whose inner vertices avoid `X`, on the
vertices of the walk. -/
theorem exists_path_of_walk {a b : V} (w : G.Walk a b) (X : Set V)
    (hw : ∀ y ∈ w.support, y ≠ a → y ≠ b → y ∉ X) :
    ∃ q : G.Walk a b, q.IsPath ∧ (∀ y ∈ q.support, y ∈ w.support) ∧
      ∀ y ∈ q.support, y ≠ a → y ≠ b → y ∉ X := by
  classical
  refine ⟨w.bypass, w.bypass_isPath, fun y hy => w.support_bypass_subset_support hy,
    fun y hy h1 h2 => hw y (w.support_bypass_subset_support hy) h1 h2⟩

/-! ### Lemma 3.3 for ribs -/

/-- `x` is joined to `v` by a path of `G` on `R` with no inner vertex on `C`. -/
def ConnectedIn (G : SimpleGraph V) (R : Set V) (C : List V) (x v : V) : Prop :=
  ∃ q : G.Walk x v, q.IsPath ∧ (∀ y ∈ q.support, y ∈ R) ∧
    ∀ y ∈ q.support, y ≠ x → y ≠ v → y ∉ {z | z ∈ C}

theorem connectedIn_of_adj {R : Set V} {C : List V} {x v : V} (hx : x ∈ R) (hv : v ∈ R)
    (h : G.Adj x v) : ConnectedIn G R C x v := by
  refine ⟨h.toWalk, Walk.IsPath.of_adj h, fun y hy => ?_, fun y hy h1 h2 => ?_⟩
  · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_nil_iff,
      or_false] at hy
    rcases hy with rfl | rfl
    · exact hx
    · exact hv
  · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons, List.mem_nil_iff,
      or_false] at hy
    rcases hy with rfl | rfl
    · exact absurd rfl h1
    · exact absurd rfl h2

theorem connectedIn_refl {R : Set V} {C : List V} {x : V} (hx : x ∈ R) : ConnectedIn G R C x x :=
  ⟨.nil, Walk.IsPath.nil, fun y hy => by simp at hy; exact hy ▸ hx,
    fun y hy h1 _ => by simp at hy; exact absurd hy h1⟩

/-- **Lemma 3.3, for ribs.** Let `x` be a vertex of a rib with frame `C`, `|C| ≥ 4`. There is a
`C`-path `P` of the rib between non-consecutive vertices `c` and `c'` of `C` such that `x` is
`C`-connected in the rib to every vertex of `P`. -/
theorem lemma_3_3_rib {R : Set V} {C : List V} (h : IsRibOn G R C) (h4 : 4 ≤ C.length) {x : V}
    (hx : x ∈ R) :
    ∃ c c' : V, ∃ P : G.Walk c c', IsTPath G C P ∧ c ≠ c' ∧ ¬ IsCycleEdge C c c' ∧
      (∀ v ∈ P.support, v ∈ R) ∧ ∀ v ∈ P.support, ConnectedIn G R C x v := by
  classical
  obtain ⟨hC, hR, φ, hφ⟩ := id h
  by_cases hxC : x ∈ C
  · -- `x` is on the frame: the path of its neighbours
    obtain ⟨d, d', hne, hd, hd', hall⟩ := hC.frame_neighbours hxC
    obtain ⟨F, hF, hFs, -⟩ := h.fan hne hd hd'
    have hdd : ¬ IsCycleEdge C d d' := hC.not_isCycleEdge_frame_neighbours h4 hne hd hd'
    by_cases hin : ∀ y ∈ F.support, y ≠ d → y ≠ d' → y ∉ C
    · refine ⟨d, d', F, ⟨hF, hd.symm.mem_left, hd'.symm.mem_left,
        fun y hy h1 h2 => ⟨hin y hy h1 h2, hin y hy h1 h2⟩⟩, hne, hdd,
        fun v hv => ((hFs v).mp hv).1, fun v hv => ?_⟩
      exact connectedIn_of_adj hx ((hFs v).mp hv).1 ((hFs v).mp hv).2
    · push Not at hin
      obtain ⟨y, hy, h1, h2, hyC⟩ := hin
      have hxy := ((hFs y).mp hy).2
      have hyR := ((hFs y).mp hy).1
      refine ⟨x, y, hxy.toWalk, ⟨Walk.IsPath.of_adj hxy, hxC, hyC, fun z hz hz1 hz2 => ?_⟩,
        hxy.ne, fun he => ?_, fun v hv => ?_, fun v hv => ?_⟩
      · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl
        · exact absurd rfl hz1
        · exact absurd rfl hz2
      · rcases hall y he with h | h
        · exact h1 h
        · exact h2 h
      · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl
        · exact hx
        · exact hyR
      · simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.mem_nil_iff, or_false] at hv
        rcases hv with rfl | rfl
        · exact connectedIn_refl hx
        · exact connectedIn_of_adj hx hyR hxy
  · -- `x` is off the frame: a path to the frame, then the neighbours of its last vertex
    obtain ⟨c₀, hc₀, hreach⟩ := hφ.reach_frame hC hR hx
    obtain ⟨w₀⟩ := hreach
    have hle : restrict G R ≤ G := fun _ _ h => h.1
    set w₁ := (w₀.toPath.1).mapLe hle
    have hw₁ : w₁.IsPath := w₀.toPath.2.mapLe hle
    have hw₁R : ∀ y ∈ w₁.support, y ∈ R := by
      intro y hy
      rw [support_mapLe] at hy
      exact mem_of_support_restrict _ hx y hy
    -- `P₁` from `x` to its first vertex `c` on `C`
    obtain ⟨c, hcC, P₁, hP₁s, hP₁C, hP₁p⟩ := exists_first_hit {z | z ∈ C} w₁ hc₀
    have hP₁ := hP₁p hw₁
    have hcR := hR c hcC
    -- `P₀` from `x` to its first vertex `u` adjacent to `c`
    obtain ⟨u, hu, P₀, hP₀s, hP₀N, hP₀p⟩ := exists_first_hit {z | G.Adj z c ∨ z = c} P₁ (Or.inr rfl)
    have hP₀ := hP₀p hP₁
    have huc : G.Adj u c := by
      rcases hu with hu | rfl
      · exact hu
      · exfalso
        have hxc : x ≠ u := fun h => hxC (h ▸ hcC)
        have hnil : ¬ P₀.Nil := Walk.not_nil_of_ne hxc
        have hpen := P₀.adj_penultimate hnil
        have hpm : P₀.penultimate ∈ P₀.support := P₀.getVert_mem_support _
        exact hP₀N _ hpm hpen.ne (Or.inl hpen)
    have hP₀R : ∀ y ∈ P₀.support, y ∈ R := fun y hy => hw₁R y (hP₁s y (hP₀s y hy))
    have hP₀C : ∀ y ∈ P₀.support, y ∉ C := by
      intro y hy hyC
      have hyc : y ≠ c := by
        by_cases hyu : y = u
        · rw [hyu]; exact huc.ne
        · exact fun h => hP₀N y hy hyu (Or.inr h)
      exact hP₁C y (hP₀s y hy) hyc hyC
    have hP₀adj : ∀ y ∈ P₀.support, y ≠ u → ¬ G.Adj y c := fun y hy hyu h =>
      hP₀N y hy hyu (Or.inl h)
    have huR : u ∈ R := hP₀R u P₀.end_mem_support
    have huC : u ∉ C := hP₀C u P₀.end_mem_support
    -- the path `F` of the neighbours of `c`, through `u`
    obtain ⟨d, d', hne, hd, hd', -⟩ := hC.frame_neighbours hcC
    obtain ⟨F, hF, hFs, hFe⟩ := h.fan hne hd hd'
    have huF : u ∈ F.support := (hFs u).mpr ⟨huR, huc.symm⟩
    set F₁ := F.takeUntil u huF
    set F₂ := F.dropUntil u huF
    have hFspec : F₁.append F₂ = F := F.take_spec huF
    have hFp : (F₁.append F₂).IsPath := hFspec ▸ hF
    have hF₁ : F₁.IsPath := hF.takeUntil huF
    have hF₂ : F₂.IsPath := hF.dropUntil huF
    have hF₁s : ∀ y ∈ F₁.support, y ∈ F.support := fun y hy =>
      F.support_takeUntil_subset_support huF hy
    have hF₂s : ∀ y ∈ F₂.support, y ∈ F.support := fun y hy =>
      F.support_dropUntil_subset_support huF hy
    -- first vertices of `F₁` reversed and of `F₂` on `C`
    obtain ⟨e, heC, Q, hQs, hQC, hQp⟩ := exists_first_hit {z | z ∈ C} F₁.reverse hd.symm.mem_left
    obtain ⟨e', he'C, Q', hQ's, hQ'C, hQ'p⟩ := exists_first_hit {z | z ∈ C} F₂ hd'.symm.mem_left
    have hQ := hQp hF₁.reverse
    have hQ' := hQ'p hF₂
    have hQF₁ : ∀ y ∈ Q.support, y ∈ F₁.support := fun y hy => by
      have := hQs y hy
      rwa [Walk.support_reverse, List.mem_reverse] at this
    have hFR : ∀ y ∈ F.support, y ∈ R := fun y hy => ((hFs y).mp hy).1
    have hFc : ∀ y ∈ F.support, G.Adj c y := fun y hy => ((hFs y).mp hy).2
    have hmeet : ∀ y ∈ Q.support, y ∈ Q'.support → y = u := fun y hy hy' =>
      eq_of_mem_append_path hFp (hQF₁ y hy) (hQ's y hy')
    have hee : e ≠ e' := fun h => huC (hmeet e Q.end_mem_support (h ▸ Q'.end_mem_support) ▸ heC)
    -- `e` and `e'` are not consecutive on `C`
    have hcons : ¬ IsCycleEdge C e e' := by
      intro hce
      have heF : e ∈ F.support := hF₁s e (hQF₁ e Q.end_mem_support)
      have he'F : e' ∈ F.support := hF₂s e' (hQ's e' Q'.end_mem_support)
      have hedge := (hFe e e' (hFR e heF) (hFc e heF) (hFR e' he'F) (hFc e' he'F)).mp (hce.adj hC)
      rw [← hFspec, Walk.edges_append, List.mem_append] at hedge
      rcases hedge with h1 | h2
      · have := eq_of_mem_append_path hFp (F₁.snd_mem_support_of_mem_edges h1)
          (hQ's e' Q'.end_mem_support)
        exact huC (this ▸ he'C)
      · have := eq_of_mem_append_path hFp (hQF₁ e Q.end_mem_support)
          (F₂.fst_mem_support_of_mem_edges h2)
        exact huC (this ▸ heC)
    -- the path from `e` to `e'` through `u`
    have hT : (Q.reverse.append Q').IsPath := isPath_append_of hQ.reverse hQ' (fun y hy hy' => by
      rw [Walk.support_reverse, List.mem_reverse] at hy
      exact hmeet y hy hy')
    have hTs : ∀ y ∈ (Q.reverse.append Q').support, y ∈ Q.support ∨ y ∈ Q'.support := by
      intro y hy
      rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hy
      exact hy
    refine ⟨e, e', Q.reverse.append Q', ⟨hT, heC, he'C, fun y hy h1 h2 => ?_⟩, hee, hcons,
      fun v hv => ?_, fun v hv => ?_⟩
    · rcases hTs y hy with hy | hy
      · exact ⟨hQC y hy h1, hQC y hy h1⟩
      · exact ⟨hQ'C y hy h2, hQ'C y hy h2⟩
    · rcases hTs v hv with hv | hv
      · exact hFR v (hF₁s v (hQF₁ v hv))
      · exact hFR v (hF₂s v (hQ's v hv))
    · -- `x` reaches `v` through `P₀` and the part of `Q` or `Q'` up to `v`
      have key : ∀ {e₀ : V} (Q₀ : G.Walk u e₀), Q₀.IsPath → (∀ y ∈ Q₀.support, y ∈ R) →
          (∀ y ∈ Q₀.support, y ≠ e₀ → y ∉ {z | z ∈ C}) → ∀ v ∈ Q₀.support,
          ConnectedIn G R C x v := by
        intro e₀ Q₀ hQ₀ hQ₀R hQ₀C v hv
        set W := P₀.append (Q₀.takeUntil v hv)
        have hWs : ∀ y ∈ W.support, y ∈ P₀.support ∨ y ∈ (Q₀.takeUntil v hv).support := by
          intro y hy
          exact (Walk.mem_support_append_iff _ _).mp hy
        obtain ⟨q, hq, hqs, hqC⟩ := exists_path_of_walk W {z | z ∈ C} (fun y hy _ h2 => by
          rcases hWs y hy with hy | hy
          · exact hP₀C y hy
          · have hyQ := Q₀.support_takeUntil_subset_support hv hy
            refine hQ₀C y hyQ fun he => ?_
            subst he
            exact Walk.endpoint_notMem_support_takeUntil hQ₀ hv h2 hy)
        refine ⟨q, hq, fun y hy => ?_, hqC⟩
        rcases hWs y (hqs y hy) with hy | hy
        · exact hP₀R y hy
        · exact hQ₀R y (Q₀.support_takeUntil_subset_support hv hy)
      rcases hTs v hv with hv | hv
      · exact key Q hQ (fun y hy => hFR y (hF₁s y (hQF₁ y hy))) hQC v hv
      · exact key Q' hQ' (fun y hy => hFR y (hF₂s y (hQ's y hy))) hQ'C v hv

/-! ### Lemma 3.3 for webs -/

theorem support_toWalk {a b : V} (h : G.Adj a b) : h.toWalk.support = [a, b] := by
  simp [Adj.toWalk]

/-- An edge between two vertices of `C` is a `C`-path. -/
theorem isTPath_toWalk {C : List V} {a b : V} (h : G.Adj a b) (ha : a ∈ C) (hb : b ∈ C) :
    IsTPath G C h.toWalk := by
  refine ⟨Walk.IsPath.of_adj h, ha, hb, fun z hz h1 h2 => ?_⟩
  rw [support_toWalk, List.mem_cons, List.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2

theorem ConnectedIn.isConnectedAvoiding {R : Set V} {C : List V} {x v : V}
    (h : ConnectedIn G R C x v) : IsConnectedAvoiding G {z | z ∈ C} x {v} := by
  obtain ⟨q, hq, -, hqC⟩ := h
  exact ⟨v, rfl, q, hq, hqC⟩

theorem isConnectedAvoiding_of_adj {C : List V} {x v : V} (h : G.Adj x v) :
    IsConnectedAvoiding G {z | z ∈ C} x {v} := by
  refine ⟨v, rfl, h.toWalk, Walk.IsPath.of_adj h, fun z hz h1 h2 => ?_⟩
  rw [support_toWalk, List.mem_cons, List.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2

/-- **Lemma 3.3** (Humeau and Pous, page 9). "Let $x$ be a vertex in a web $G$ with frame $C$ such
that $|C|\ge 4$. There exists a $C$-path $P$ between non-consecutive vertices $c_x$ and $c_x'$ of
$C$ such that $x$ is $C$-connected to all vertices of $P$." -/
theorem lemma_3_3 {S : Set V} {C : List V} (h : IsWebOn G S C) (h4 : 4 ≤ C.length) {x : V}
    (hx : x ∈ S) :
    ∃ c c' : V, ∃ P : G.Walk c c', IsTPath G C P ∧ c ≠ c' ∧ ¬ IsCycleEdge C c c' ∧
      ∀ v ∈ P.support, IsConnectedAvoiding G {z | z ∈ C} x {v} := by
  obtain ⟨R, tri, W⟩ := h.exists_webData
  have hC := W.rib.1
  by_cases hxR : x ∈ R
  · obtain ⟨c, c', P, hP, hne, hcons, -, hconn⟩ := lemma_3_3_rib W.rib h4 hxR
    exact ⟨c, c', P, hP, hne, hcons, fun v hv => (hconn v hv).isConnectedAvoiding⟩
  -- `x` is a clique vertex on the triangle `abc`
  have hxSR : x ∈ S \ R := ⟨hx, hxR⟩
  obtain ⟨a, b, c, hT, htri⟩ := W.tri_spec x hxSR
  have hadj : ∀ y ∈ tri x, G.Adj x y := fun y hy => (W.adj_iff x hxSR y).mpr (Or.inl hy)
  have hxa := hadj a (by rw [htri]; exact Or.inl rfl)
  have hxb := hadj b (by rw [htri]; exact Or.inr (Or.inl rfl))
  have hxc := hadj c (by rw [htri]; exact Or.inr (Or.inr rfl))
  obtain ⟨ha, hb, hc, hab, hbc, hac⟩ := hT
  -- through a vertex `y` of the triangle off `C`
  have hoff : ∀ y, y ∈ R → y ∉ C → G.Adj x y → ∃ c c' : V, ∃ P : G.Walk c c', IsTPath G C P ∧
      c ≠ c' ∧ ¬ IsCycleEdge C c c' ∧ ∀ v ∈ P.support, IsConnectedAvoiding G {z | z ∈ C} x {v} := by
    intro y hyR hyC hxy
    obtain ⟨e, e', P, hP, hne, hcons, -, hconn⟩ := lemma_3_3_rib W.rib h4 hyR
    refine ⟨e, e', P, hP, hne, hcons, fun v hv => ?_⟩
    obtain ⟨q, hq, hqR, hqC⟩ := hconn v hv
    have hxq : x ∉ q.support := fun h => hxR (hqR x h)
    refine ⟨v, rfl, .cons hxy q, (Walk.cons_isPath_iff _ _).mpr ⟨hq, hxq⟩, fun z hz h1 h2 => ?_⟩
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact absurd rfl h1
    · by_cases hzy : z = y
      · rw [hzy]; exact hyC
      · exact hqC z hz hzy h2
  by_cases haC : a ∈ C
  swap
  · exact hoff a ha haC hxa
  by_cases hbC : b ∈ C
  swap
  · exact hoff b hb hbC hxb
  by_cases hcC : c ∈ C
  swap
  · exact hoff c hc hcC hxc
  -- all of the triangle is on `C`: two of its vertices are not consecutive
  have hedge : ∀ {y z : V}, G.Adj y z → y ∈ C → z ∈ C → G.Adj x y → G.Adj x z →
      ¬ IsCycleEdge C y z → ∃ c c' : V, ∃ P : G.Walk c c', IsTPath G C P ∧
        c ≠ c' ∧ ¬ IsCycleEdge C c c' ∧
        ∀ v ∈ P.support, IsConnectedAvoiding G {z | z ∈ C} x {v} := by
    intro y z hyz hy hz hxy hxz hcons
    refine ⟨y, z, hyz.toWalk, isTPath_toWalk hyz hy hz, hyz.ne, hcons, fun v hv => ?_⟩
    rw [support_toWalk, List.mem_cons, List.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact isConnectedAvoiding_of_adj hxy
    · exact isConnectedAvoiding_of_adj hxz
  by_cases h1 : IsCycleEdge C a b
  · by_cases h2 : IsCycleEdge C a c
    · exact hedge hbc hbC hcC hxb hxc
        (hC.not_isCycleEdge_frame_neighbours h4 hbc.ne h1 h2)
    · exact hedge hac haC hcC hxa hxc h2
  · exact hedge hab haC hbC hxa hxb h1

end GraphMinor.HP25
