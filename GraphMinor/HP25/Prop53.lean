module

public import GraphMinor.HP25.Prop52Converse
import GraphMinor.HP25.WebPath
import GraphMinor.HP25.WebSplit
import GraphMinor.HP25.Prop34
import GraphMinor.HP25.Prop36
import GraphMinor.HP25.Alternate
import GraphMinor.HP25.Completion
import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Lemma41
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma43Case2

/-!
# Proposition 5.3: `P`-completions exist

Humeau and Pous, Section 5.1 (page 17): "Given a $C$-path $P$ of $G$ we call *$P$-completion* a
safe set $F$ of edges such that $P+F$ contains a $C$-path $P'$ whose vertices are all on both
$P'$-sides in $G+F$." Proposition 5.3: "Let $G$ be a graph with a cycle $C$. For every $C$-path $P$
between non-consecutive vertices of $C$, there exists a $P$-completion."

The proof follows the paper (pages 17–18). "If $C$ is crossed in $G$ then $y_1y_l$ is a
$P$-completion": the single edge `ab` is a `C`-path whose two ends are next to both sides on `C`.
"If instead $C$ is crossless, then by Theorem 1.3 there is a set $F$ of edges such that $G+F$ ... is
a web. Any $C$-path $P'$ of $G+F$ which is induced and contained in $P+F$ can then be used to prove
that $F$ is a $P$-completion (see Claim 4.2 for details on proving that vertices of $P'$ lie on both
$P'$-sides)." We take for `G + F` a maximal crossless completion `W` of `G`, a web by
`lemma_4_3_on`. We remove chords from `P` in `W`
(`exists_induced`) to get `P'`. Since `P'` is induced, `W` splits along `P'` into two webs
(`WebData.split`), and Claim 4.2 in each of them puts every vertex of `P'` on both sides
(`WebData.onBothSides`).

The `C`-path `P'` we give has the same ends as `P`, so that its sides are those of `P`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- A set of edges `F` (here a graph) is *safe* for `T` (page 15): "A set of edges $F$ is called
*safe* for $T$ if, when $T$ is crossed in $G+F$, then $T$ is crossed in $G$." -/
@[expose] def IsSafe (G F : SimpleGraph V) (T : List V) : Prop :=
  IsCrossed (G ⊔ F) T → IsCrossed G T

/-- A *`P`-completion* (page 17): "a safe set $F$ of edges such that $P+F$ contains a $C$-path $P'$
whose vertices are all on both $P'$-sides in $G+F$". Here `C = a A b B` up to rotation, `P` runs
from `a` to `b`, and we ask that `P'` runs from `a` to `b` as well, so that its sides are `A` and
`B`. -/
@[expose] def IsPCompletion (G : SimpleGraph V) (C A B : List V) {a b : V} (P : G.Walk a b)
    (F : SimpleGraph V) : Prop :=
  IsSafe G F C ∧ ∃ P' : (G ⊔ F).Walk a b, IsTPath (G ⊔ F) C P' ∧
    (∀ e ∈ P'.edges, e ∈ P.edges ∨ e ∈ F.edgeSet) ∧ OnBothSides (G ⊔ F) C A B P'

/-- A vertex next to a vertex of `A` is connected to `A`, avoiding anything. -/
theorem isConnectedAvoiding_of_adj_mem {X : Set V} {A : List V} {x c : V} (h : G.Adj x c)
    (hc : c ∈ A) : IsConnectedAvoiding G X x {z | z ∈ A} := by
  refine ⟨c, hc, h.toWalk, Walk.IsPath.of_adj h, fun z hz h1 h2 => ?_⟩
  rw [support_toWalk, List.mem_cons, List.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2

/-- The two ends of a chain `x L y` with `L` not empty each have a neighbour in `L`. -/
theorem exists_adj_ends {x y : V} {L : List V} (hL : L ≠ []) (h : (x :: L ++ [y]).IsChain G.Adj) :
    (∃ c ∈ L, G.Adj x c) ∧ ∃ c ∈ L, G.Adj y c := by
  obtain ⟨c, L', rfl⟩ := List.exists_cons_of_ne_nil hL
  refine ⟨⟨c, List.mem_cons_self .., (List.isChain_cons_cons.mp (by simpa using h)).1⟩, ?_⟩
  have hrev := List.isChain_reverse.mpr (h.imp fun _ _ h => h.symm)
  simp only [List.cons_append, List.reverse_cons, List.reverse_append, List.reverse_nil,
    List.nil_append] at hrev
  obtain ⟨d, L'', hd⟩ := List.exists_cons_of_ne_nil (show (L'.reverse ++ [c]) ≠ [] by simp)
  rw [hd] at hrev
  have hdL : d ∈ c :: L' := by
    have : d ∈ L'.reverse ++ [c] := by rw [hd]; simp
    simpa [or_comm] using this
  exact ⟨d, hdL, (List.isChain_cons_cons.mp (by simpa using hrev)).1⟩

/-- **Claim 4.2, moved to the whole web.** Let `W` restricted to `T` be a web with frame
`a A b m⁻¹` in which `a m b` is induced. Then a vertex `x` of `T` is joined to `A` by a path of `W`
whose inner vertices avoid `Y`, for every set `Y` that meets `T` only in the frame. -/
theorem isConnectedAvoiding_of_web {W : SimpleGraph V} {T Y : Set V} {a b : V} {A m : List V}
    (hH : IsWebOn (restrict W T) T (a :: A ++ b :: m.reverse))
    (hind : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W.Adj u v → IsListEdge (a :: m ++ [b]) u v)
    (hA : A ≠ []) {x : V} (hx : x ∈ T) (hY : ∀ z ∈ T, z ∈ Y → z ∈ a :: A ++ b :: m.reverse) :
    IsConnectedAvoiding W Y x {z | z ∈ A} := by
  obtain ⟨c, hc, p, hp, hin⟩ := claim_4_2 hH (fun u hu v hv h => hind u hu v hv h.1) hA hx
  refine ⟨c, hc, p.mapLe (restrict_le W T), (Walk.isPath_mapLe _).mpr hp,
    fun z hz h1 h2 hzY => ?_⟩
  rw [Walk.support_mapLe_eq_support] at hz
  exact hin z hz h1 h2 (hY z (mem_of_mem_support_restrict p hz h1) hzY)

/-- **Vertices of an induced `C`-path of a web are on both sides** (proof of Proposition 5.3, with
Claim 4.2). In a web `W` with frame `C = a A b B` (up to rotation, `A` and `B` not empty), every
vertex of an induced `C`-path from `a` to `b` is on both of its sides. -/
theorem WebData.onBothSides {W : SimpleGraph V} {C : List V} {R : Set V} {tri : V → Set V}
    (WD : WebData W univ C R tri) {a b : V} {A B : List V} {k : ℕ}
    (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ []) {P : W.Walk a b}
    (hP : IsTPath W C P)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, W.Adj u v → IsListEdge P.support u v) :
    OnBothSides W C A B P := by
  classical
  have hC := WD.rib.1
  have hCR := WD.rib.2.1
  have hnd' : (a :: A ++ b :: B).Nodup := hrot ▸ List.nodup_rotate.mpr hC.2.1
  have hab : a ≠ b := by
    rintro rfl
    rw [List.cons_append, List.nodup_cons] at hnd'
    exact hnd'.1 (by simp)
  obtain ⟨m, hm⟩ := IsXZPath.exists_middle (G := W) (C := []) (P := P.support)
    ⟨P.isChain_adj_support, hP.1.support_nodup, Walk.support_head? P,
      Walk.support_getLast? P, fun _ _ h => by simp at h⟩ (by
      rw [Walk.length_support]
      have : P.length ≠ 0 := fun h0 => hab (Walk.eq_of_length_eq_zero h0)
      omega)
  have hPnd : (a :: m ++ [b]).Nodup := hm ▸ hP.1.support_nodup
  have hPch : (a :: m ++ [b]).IsChain W.Adj := hm ▸ P.isChain_adj_support
  have hmC : ∀ v ∈ m, v ∉ C := fun v hv => by
    have hva : v ≠ a := by
      rintro rfl
      rw [List.cons_append, List.nodup_cons] at hPnd
      exact hPnd.1 (List.mem_append_left _ hv)
    have hvb : v ≠ b := by
      rintro rfl
      rw [List.cons_append, List.nodup_cons, List.nodup_append] at hPnd
      exact hPnd.2.2.2 v hv v (by simp) rfl
    exact (hP.2.2.2 v (by rw [hm]; simp [hv]) hva hvb).1
  have hind' : ∀ u ∈ a :: m ++ [b], ∀ v ∈ a :: m ++ [b], W.Adj u v →
      IsListEdge (a :: m ++ [b]) u v := by
    rw [← hm]; exact hind
  have haC : a ∈ C := hP.2.1
  have hbC : b ∈ C := hP.2.2.1
  -- `P` lies in the rib
  have hl : IsPathList W R (a :: m ++ [b]) := by
    refine ⟨hPnd, hPch, fun v hv => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv
    by_cases h0 : t = 0
    · subst h0; simpa using hCR a haC
    by_cases h1 : t + 1 = (a :: m ++ [b]).length
    · have e : (a :: m ++ [b])[t] = b := by
        simp only [List.length_append, List.length_cons, List.length_nil] at h1
        simp [show t = m.length + 1 by omega]
      rw [e]; exact hCR b hbC
    · exact WD.mem_rib_of_induced hPnd hPch (fun _ _ => trivial) hind' (by omega) (by omega)
  obtain ⟨a', b', m', A', B', k', S₁, S₂, hl', hrot', -, -, hI, -, -, hH, hK⟩ :=
    WD.split hrot (not_isCycleEdge_of_rotate hC.2.1 hrot hA hB) hl hmC hind'
  -- the split is along the same path, with the same sides of `C`
  obtain ⟨rfl, h2⟩ := List.cons_eq_cons.mp hl'
  obtain ⟨rfl, h3⟩ := List.append_inj' h2 rfl
  obtain rfl := List.singleton_inj.mp h3
  have hXY := rotate_eq_of_head hC.2.1 hrot hrot'
  obtain ⟨rfl, rfl⟩ := split_unique hXY (by
    rw [List.cons_append, List.nodup_cons] at hnd'
    exact hnd'.2)
  -- a vertex of `C ∪ P` that lies on both sides lies on `P`
  have hY : ∀ z, z ∈ C ∨ z ∈ P.support →
      z ∈ a :: A ++ b :: B ∧ (z ∈ B → z ∈ S₁ → z ∈ a :: m ++ [b]) ∧
        (z ∈ A → z ∈ S₂ → z ∈ a :: m ++ [b]) ∨ z ∈ a :: m ++ [b] := by
    rintro z (hz | hz)
    · refine Or.inl ⟨by rw [← hrot]; exact List.mem_rotate.mpr hz, fun hzB hz1 => ?_,
        fun hzA hz2 => ?_⟩
      · have : z ∈ S₁ ∩ S₂ := ⟨hz1, hK.frame_subset z (by simp [hzB])⟩
        rw [hI] at this
        exact this
      · have : z ∈ S₁ ∩ S₂ := ⟨hH.frame_subset z (by simp [hzA]), hz2⟩
        rw [hI] at this
        exact this
    · exact Or.inr (hm ▸ hz)
  have hm₁ : ∀ z ∈ a :: m ++ [b], z ∈ a :: A ++ b :: m.reverse := fun z hz => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse,
      List.not_mem_nil, or_false] at hz ⊢
    tauto
  have hm₂ : ∀ z ∈ a :: m ++ [b], z ∈ b :: B ++ a :: m.reverse.reverse := fun z hz => by
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.reverse_reverse,
      List.not_mem_nil, or_false] at hz ⊢
    tauto
  intro x hx
  have hx12 : x ∈ S₁ ∩ S₂ := by rw [hI, ← hm]; exact hx
  constructor
  · refine isConnectedAvoiding_of_web hH hind' hA hx12.1 fun z hz hzY => ?_
    rcases hY z hzY with ⟨hzC, hzB, -⟩ | h
    · simp only [List.cons_append, List.mem_cons, List.mem_append] at hzC
      rcases hzC with rfl | h | rfl | h
      · simp
      · simp [h]
      · simp
      · exact hm₁ z (hzB h hz)
    · exact hm₁ z h
  · have hK' : IsWebOn (restrict W S₂) S₂ (b :: B ++ a :: m.reverse.reverse) := by
      rwa [List.reverse_reverse]
    have hrev : (a :: m ++ [b]).reverse = b :: m.reverse ++ [a] := by simp
    refine isConnectedAvoiding_of_web hK' (fun u hu v hv huv => ?_) hB hx12.2
      fun z hz hzY => ?_
    · rw [← hrev] at hu hv ⊢
      rw [List.mem_reverse] at hu hv
      exact (hind' u hu v hv huv).reverse
    · rcases hY z hzY with ⟨hzC, -, hzA⟩ | h
      · simp only [List.cons_append, List.mem_cons, List.mem_append] at hzC
        rcases hzC with rfl | h | rfl | h
        · simp
        · exact hm₂ z (hzA h hz)
        · simp
        · simp [h]
      · exact hm₂ z h

/-- **Proposition 5.3** (page 17): "Let $G$ be a graph with a cycle $C$. For every $C$-path $P$
between non-consecutive vertices of $C$, there exists a $P$-completion." Here `C = a A b B` up to
rotation with `A` and `B` not empty, and `P` runs from `a` to `b`. The crossless case uses
Theorem 1.3, through `lemma_4_3_on`. -/
theorem prop_5_3 [Finite V] {C : List V} (hC : IsCycleList G C) {a b : V}
    {A B : List V} {k : ℕ} (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    {P : G.Walk a b} (hP : IsTPath G C P) : ∃ F : SimpleGraph V, IsPCompletion G C A B P F := by
  classical
  have haC : a ∈ C := hP.2.1
  have hbC : b ∈ C := hP.2.2.1
  by_cases hc : IsCrossed G C
  · -- the edge `ab` is a `P`-completion
    have hC' : IsCycleList G (a :: A ++ b :: B) := hrot ▸ hC.rotate k
    have hnd' := hC'.2.1
    have hab : a ≠ b := by
      rintro rfl
      rw [List.cons_append, List.nodup_cons] at hnd'
      exact hnd'.1 (by simp)
    have hP₁ := (hC'.isPathList (R := univ) fun _ _ => trivial)
    rw [show a :: A ++ b :: B = (a :: A ++ [b]) ++ B by simp] at hP₁
    have hP₂ := ((hC'.rotate (A.length + 1)).isPathList (R := univ) fun _ _ => trivial)
    rw [rotate_cons_append_cons, show b :: B ++ a :: A = (b :: B ++ [a]) ++ A by simp] at hP₂
    obtain ⟨⟨c₁, hc₁, ha₁⟩, ⟨c₂, hc₂, hb₁⟩⟩ := exists_adj_ends hA hP₁.prefix.2.1
    obtain ⟨⟨c₃, hc₃, hb₂⟩, ⟨c₄, hc₄, ha₂⟩⟩ := exists_adj_ends hB hP₂.prefix.2.1
    have hF : (fromEdgeSet {s(a, b)} : SimpleGraph V).Adj a b := by simp [hab]
    have hadj : (G ⊔ fromEdgeSet {s(a, b)}).Adj a b := Or.inr hF
    have hle : G ≤ G ⊔ fromEdgeSet {s(a, b)} := le_sup_left
    refine ⟨fromEdgeSet {s(a, b)}, fun _ => hc, hadj.toWalk, isTPath_toWalk hadj haC hbC,
      fun e he => Or.inr ?_, fun v hv => ?_⟩
    · simp only [Adj.toWalk, Walk.edges_cons, Walk.edges_nil, List.mem_cons, List.not_mem_nil,
        or_false] at he
      subst he
      exact hF
    · rw [support_toWalk, List.mem_cons, List.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨isConnectedAvoiding_of_adj_mem (hle ha₁) hc₁,
          isConnectedAvoiding_of_adj_mem (hle ha₂) hc₄⟩
      · exact ⟨isConnectedAvoiding_of_adj_mem (hle hb₁) hc₂,
          isConnectedAvoiding_of_adj_mem (hle hb₂) hc₃⟩
  · -- a web completion `W`, and an induced `C`-path of `W` on the vertices of `P`
    obtain ⟨W, hle, hmax⟩ := exists_maxCrosslessOn (G := G) (S := univ) (C := C)
      (fun _ _ _ => trivial) hc
    have hweb : IsWebOn W univ C :=
      lemma_4_3_on _ W univ C rfl (hC.mono hle) (fun _ _ => trivial) hmax
    obtain ⟨R, tri, WD⟩ := hweb.exists_webData
    have hPl : IsPathList W {v | v ∈ P.support} P.support :=
      ⟨hP.1.support_nodup, P.isChain_adj_support.imp fun _ _ h => hle h, fun _ h => h⟩
    obtain ⟨l, hl, hh, hlast, hsub, hind⟩ := exists_induced _ P.support le_rfl hPl
    rw [Walk.support_head?] at hh
    rw [Walk.support_getLast?] at hlast
    obtain ⟨P', hP', hsupp⟩ := exists_tPath_of_list hl.2.1 hl.1 hh hlast haC hbC
      fun w hw hwC => by
        by_contra hne
        push Not at hne
        exact (hP.2.2.2 w (hsub w hw) hne.1 hne.2).1 hwC
    have e : G ⊔ W = W := sup_eq_right.mpr hle
    refine ⟨W, ?_⟩
    unfold IsPCompletion IsSafe
    rw [e]
    exact ⟨fun h => absurd h hmax.2.1, P', hP', fun e he => Or.inr (P'.edges_subset_edgeSet he),
      WD.onBothSides hrot hA hB hP' (hsupp ▸ hind)⟩

end GraphMinor.HP25
