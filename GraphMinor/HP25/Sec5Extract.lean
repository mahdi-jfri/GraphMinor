module

public import GraphMinor.HP25.Sec5Tighten
public import GraphMinor.HP25.Lemma41
public import GraphMinor.HP25.Prop52
public import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma33
import GraphMinor.HP25.Sec5Lemma54
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Embedding
import GraphMinor.HP25.CrossTools
import GraphMinor.HP25.CycleEdges
import GraphMinor.HP25.Method
import GraphMinor.HP25.Prop52Converse
import GraphMinor.HP25.Completion

/-!
# Extracting a crossing of `C` in `G` from a subinstance crossing or an added-edge crossing

Section 5.3 of Humeau and Pous returns a crossing of `C` in `G + F` and never removes the added
edges `F` (see the correction to Section 5.3 in `corrections/HP25.md`). This file formalizes both
the direct lifting of a crossing from either subinstance of Proposition 5.1
(`Setting.cross_of_side`) and the per-edge undo searches that remove an added edge `yu` from a
crossing `(Q, R)` of `C` in `G + yu` with `yu` on `Q`:

* *rule 1*: keep `R`, and search `G - R` for a `C`-path between the two arcs of `C` cut by the ends
  of `R`;
* *rule 2*: replace the edge `yu` of `Q` by a `G`-walk between `y` and `u` (either the pocket
  `y P u`, or the side-`B` detour via `B` and the two side paths from `y` and `u`), and search `G`
  minus the resulting `C`-path for a crossing `C`-path;
* *rule 3*: when `R` meets both the pocket `N` and the lower world (`B` together with the side-`B`
  paths from `L₁` and `L₂`), let `t ∈ N` and `z` be the ends of a bridge of `R` between `N` and the
  lower world (`exists_bridge_of_meets_pocket_and_lower`); this gives a rerouted `C`-path `P_new` in
  `G` bypassing `y` or `u` (`exists_rerouted_path_of_bridge`), and when `P_new` fails to separate
  `A` from `B` (in particular when the bypassed vertex reaches `A` in `G - P_new`), searching
  `G - P_new` between `A` and `B` extracts a crossing of `C` in `G` (`undo_of_bridge_rule_three_left`,
  `undo_of_bridge_rule_three_right`).

We also formalize the three observations connecting the subinstances of Proposition 5.1 directly to
`G`:

* **Observation 1** (`Sec5Tighten.isConnectedAvoiding_iff_of_adj_or_mem` and
  `Sec5Tighten.onBothSides_iff_of_adj_or_mem`): once skipped collapse edges are left out of `F` so
  every added edge of `H \ G` has both ends on `P'`, every vertex of `P'` is on both sides in `G`
  itself (`OnBothSidesList G C A B P'.support`).
* **Observation 2** (`exists_tPath_of_not_isCycleEdge`, `exists_crossing_of_adj_or_isCycleEdge`):
  a subinstance crossing `(Q_in, R_in)` in `H` uses no edge of `P'`, hence transfers directly to `G`
  with the same supports.
* **Observation 3** (`setting_of_onBothSidesList`, `exists_tPath_sideSetOf_B_of_tight`,
  `isCrossed_of_sub_crossed`): `OnBothSidesList` and `Separates` in `G` give the `Setting` of
  Figure 11 directly without web completions or Theorem 1.3, and `IsTight` moves any crossing of the
  second subinstance (`sideComplOf`) into `sideSetOf`, so `Setting.cross_of_side` lifts any
  subinstance crossing in `H` to `IsCrossed H C`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **A walk between the two arcs of a `C`-path gives a crossing.** Let `R` be a `T`-path from `c` to
`d`, and `a, c, b, d` in this cyclic order on `T`. A walk of `G` from `a` to `b` that misses `R`
contains a `T`-path that crosses `R`: from its start to its first vertex `t` in the arc of `b`, then
back to the last vertex in the arc of `a`. -/
theorem isCrossed_of_walk_avoiding {T : List V} {a b c d : V} (halt : Alternate T a b c d)
    {R : G.Walk c d} (hR : IsTPath G T R) (W : G.Walk a b)
    (hW : ∀ x ∈ W.support, x ∉ R.support) : IsCrossed G T := by
  classical
  obtain ⟨k, L₁, L₂, hrot, hb, ha⟩ := halt.comm
  have hmemT : ∀ {x}, x ∈ c :: L₁ ++ d :: L₂ → x ∈ T := fun {x} hx =>
    (List.mem_rotate (n := k)).mp (hrot ▸ hx)
  -- the first vertex `t` of `W` in `L₁`
  obtain ⟨t, ht, w₁, hw₁, hw₁L, -⟩ := exists_first_hit {x | x ∈ L₁} W hb
  -- the last vertex `r` of `w₁` in `L₂`
  obtain ⟨r, hr, w₂, hw₂, hw₂L, -⟩ := exists_first_hit {x | x ∈ L₂} w₁.reverse ha
  have hsub : ∀ x ∈ w₂.support, x ∈ W.support := fun x hx =>
    hw₁ x (by simpa using hw₂ x hx)
  -- the inner vertices of `w₂` are off `T`
  have hin : ∀ x ∈ w₂.support, x ≠ t → x ≠ r → x ∉ T := by
    intro x hx hxt hxr hxT
    have hx₁ : x ∈ w₁.support := by simpa using hw₂ x hx
    have hc : x ≠ c := fun h => hW x (hsub x hx) (h ▸ R.start_mem_support)
    have hd : x ≠ d := fun h => hW x (hsub x hx) (h ▸ R.end_mem_support)
    have : x ∈ c :: L₁ ++ d :: L₂ := hrot ▸ List.mem_rotate.mpr hxT
    simp only [List.cons_append, List.mem_cons, List.mem_append] at this
    rcases this with h | h | h | h
    · exact hc h
    · exact hw₁L x hx₁ hxt h
    · exact hd h
    · exact hw₂L x hx hxr h
  have hZ : IsTPath G T w₂.bypass := by
    refine ⟨w₂.bypass_isPath, hmemT (List.mem_append_left _ (List.mem_cons_of_mem _ ht)),
      hmemT (List.mem_append_right _ (List.mem_cons_of_mem _ hr)), fun x hx h1 h2 => ?_⟩
    have := hin x (w₂.support_bypass_subset_support hx) h1 h2
    exact ⟨this, this⟩
  refine isCrossed_of_alternate hrot ht hr R w₂.bypass hR hZ ?_
  intro x hxR hxZ
  exact hW x (hsub x (w₂.support_bypass_subset_support hxZ)) hxR

/-- The head of the list of vertices of a walk is its start. -/
private theorem head_support {u v : V} (p : G.Walk u v) : p.support.head? = some u := by
  rw [← Walk.cons_tail_support]; rfl

/-- The last entry of the list of vertices of a walk is its end. -/
private theorem getLast_support {u v : V} (p : G.Walk u v) : p.support.getLast? = some v := by
  rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support]

/-- A path `X₁ u v X₂` of `G + uv` from `a` to `b`, and a walk `W` of `G` from `u` to `v`, give a walk
of `G` from `a` to `b` whose vertices are on the path or on `W`. -/
private theorem exists_walk_replace {u v a b : V} {X₁ X₂ : List V}
    (hX : (X₁ ++ u :: v :: X₂).IsChain (G ⊔ edge u v).Adj) (hnd : (X₁ ++ u :: v :: X₂).Nodup)
    (hh : (X₁ ++ u :: v :: X₂).head? = some a) (hl : (X₁ ++ u :: v :: X₂).getLast? = some b)
    (W : G.Walk u v) :
    ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ X₁ ++ u :: v :: X₂ ∨ x ∈ W.support := by
  have hnd' := hnd
  rw [List.nodup_append, List.nodup_cons, List.nodup_cons] at hnd'
  have huv : u ≠ v := fun h => hnd'.2.1.1 (by simp [h])
  have hvX₁ : v ∉ X₁ := fun h => hnd'.2.2 v h v (by simp) rfl
  have huX₂ : u ∉ v :: X₂ := hnd'.2.1.1
  have e1 : X₁ ++ u :: v :: X₂ = (X₁ ++ [u]) ++ (v :: X₂) := by simp
  rw [e1] at hX hh hl
  have c1 : (X₁ ++ [u]).IsChain G.Adj := isChain_of_sup_edge hX.left_of_append (by
    simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨hvX₁, huv.symm⟩)
  have c2 : (v :: X₂).IsChain G.Adj := by
    rw [edge_comm] at hX
    exact isChain_of_sup_edge hX.right_of_append huX₂
  have hh1 : (X₁ ++ [u]).head? = some a := by
    cases X₁ with
    | nil => simpa using hh
    | cons x t => simpa using hh
  have hl2 : (v :: X₂).getLast? = some b := by
    rwa [List.getLast?_append_of_ne_nil _ (by simp)] at hl
  obtain ⟨p₁, hp₁⟩ := exists_walk_of_chain (u := a) (v := u) _ c1 hh1 (by simp)
  obtain ⟨p₂, hp₂⟩ := exists_walk_of_chain (u := v) (v := b) _ c2 (by simp) hl2
  refine ⟨p₁.append (W.append p₂), fun x hx => ?_⟩
  rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, hp₁, hp₂] at hx
  rcases hx with hx | hx | hx
  · left; rw [e1]; exact List.mem_append_left _ hx
  · exact Or.inr hx
  · left; rw [e1]; exact List.mem_append_right _ hx

/-- **Replacing an added edge by a walk.** Let `(Q, R)` be a crossing of `T` in `G + uv`, with `uv`
an edge of `Q` and `R` a path of `G` (as `isCrossed_sup_edge_cases'` gives). If some walk of `G`
from `u` to `v` misses `R`, then `T` is crossed in `G`. The new crossing keeps `R`; its other path
lies on `Q` and the walk. Section 5.3 of Humeau and Pous (pages 22 and 23) stops at a crossing in
the completed graph: "Returning this crossing then ... reduces to computing appropriate
$C\cup P$-paths from $Q$ or $R$ to $\mathring{P_1}$ and/or $\mathring{P_2}$." This lemma is the step
that removes one added edge. -/
theorem isCrossed_of_sup_edge_walk {T : List V} {u v a b c d : V}
    (Q : (G ⊔ edge u v).Walk a b) (R : G.Walk c d) (halt : Alternate T a b c d)
    (hQ : IsTPath (G ⊔ edge u v) T Q) (hQe : s(u, v) ∈ Q.edges) (hR : IsTPath G T R)
    (hdisj : Q.support.Disjoint R.support) (W : G.Walk u v)
    (hW : ∀ x ∈ W.support, x ∉ R.support) : IsCrossed G T := by
  obtain ⟨X₁, X₂, h | h⟩ := Walk.exists_split_of_mem_edges hQe
  · have hch := Q.isChain_adj_support
    have hnd := hQ.1.support_nodup
    have hh := head_support Q
    have hl := getLast_support Q
    rw [h] at hch hnd hh hl
    obtain ⟨p, hp⟩ := exists_walk_replace hch hnd hh hl W
    refine isCrossed_of_walk_avoiding halt hR p fun x hx hxR => ?_
    rcases hp x hx with hx | hx
    · exact hdisj (h ▸ hx) hxR
    · exact hW x hx hxR
  · have hch := Q.isChain_adj_support
    have hnd := hQ.1.support_nodup
    have hh := head_support Q
    have hl := getLast_support Q
    rw [h, edge_comm] at hch
    rw [h] at hnd hh hl
    obtain ⟨p, hp⟩ := exists_walk_replace hch hnd hh hl W.reverse
    refine isCrossed_of_walk_avoiding halt hR p fun x hx hxR => ?_
    rcases hp x hx with hx | hx
    · exact hdisj (h ▸ hx) hxR
    · exact hW x (by simpa using hx) hxR

variable {C A B L₁ N L₂ : List V} {a b y s : V} {k : ℕ} {P : G.Walk a b}

/-- **Rule 2 when `R` misses the pocket.** Let `P.support = L₁ ++ y :: N ++ s :: L₂`, and let `(Q, R)`
be a crossing of `T` in `G + ys` with `ys` on `Q`. If `R` misses `N`, then `T` is crossed in `G`: the
part `y N s` of `P` replaces the edge. -/
theorem undo_of_pocket_free {T : List V} (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    {a' b' c d : V} (Q : (G ⊔ edge y s).Walk a' b') (R : G.Walk c d) (halt : Alternate T a' b' c d)
    (hQ : IsTPath (G ⊔ edge y s) T Q) (hQe : s(y, s) ∈ Q.edges) (hR : IsTPath G T R)
    (hdisj : Q.support.Disjoint R.support) (hRN : ∀ x ∈ N, x ∉ R.support) : IsCrossed G T := by
  have hch : (y :: N ++ [s]).IsChain G.Adj := by
    have := P.isChain_adj_support
    rw [hsupp] at this
    exact this.infix ⟨L₁, L₂, by simp⟩
  obtain ⟨W, hW⟩ := exists_walk_of_chain (u := y) (v := s) _ hch (by simp)
    (List.getLast?_concat ..)
  have hyR : y ∉ R.support := fun h => hdisj (Q.fst_mem_support_of_mem_edges hQe) h
  have hsR : s ∉ R.support := fun h => hdisj (Q.snd_mem_support_of_mem_edges hQe) h
  refine isCrossed_of_sup_edge_walk Q R halt hQ hQe hR hdisj W fun x hx => ?_
  rw [hW] at hx
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | hx | rfl
  · exact hyR
  · exact hRN x hx
  · exact hsR

/-- A vertex off `X` on a path from `y` to `S` whose inner vertices are off `X` is joined to `S`
avoiding `X`. -/
private theorem isConnectedAvoiding_of_mem_path' [DecidableEq V] {X S : Set V} {y t w : V}
    (ht : t ∈ S) (p : G.Walk y t) (hp : p.IsPath) (hin : ∀ x ∈ p.support, x ≠ y → x ≠ t → x ∉ X)
    (hw : w ∈ p.support) (hwy : w ≠ y) : IsConnectedAvoiding G X w S := by
  refine isConnectedAvoiding_of_walk_mem ht (p.dropUntil w hw) fun x hx hxX => ?_
  have hx' := Walk.support_dropUntil_subset_support p hw hx
  have hxy : x ≠ y := fun h => start_notMem_support_dropUntil hp hw hwy (h ▸ hx)
  by_cases hxt : x = t
  · exact Or.inr hxt
  · exact absurd hxX (hin x hx' hxy hxt)

/-- **Rule 1 when `R` misses the world below the pocket.** Let `C = a A b B` up to rotation be a cycle
of `G`, `P` a `C`-path from `a` to `b`, and `X = C ∪ P`. Let `y` and `s` be on side `B`, and let
`(Q, R)` be a crossing of `C` in `G + ys` with `ys` on `Q`. If `R` misses `B` and every vertex off
`X` that is joined to `B` avoiding `X`, then `C` is crossed in `G`: the side paths of `y` and `s` and a
piece of `B` join `y` to `s` and miss `R`. -/
theorem undo_of_lower_free (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (P : G.Walk a b)
    (hy : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} y)
    (hs : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s)
    {a' b' c d : V} (Q : (G ⊔ edge y s).Walk a' b') (R : G.Walk c d) (halt : Alternate C a' b' c d)
    (hQ : IsTPath (G ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges) (hR : IsTPath G C R)
    (hdisj : Q.support.Disjoint R.support)
    (hRL : ∀ x ∈ R.support, x ∉ B ∧
      ¬ (x ∉ {x | x ∈ C ∨ x ∈ P.support} ∧
        IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} x {x | x ∈ B})) :
    IsCrossed G C := by
  classical
  set X : Set V := {x | x ∈ C ∨ x ∈ P.support} with hX
  obtain ⟨t, ht, py, hpy, hpyin⟩ := hy
  obtain ⟨t', ht', ps, hps, hpsin⟩ := hs
  -- the arc `B` is a chain of `G`
  have hBch : B.IsChain G.Adj := by
    have := ((hC.rotate k).isPathList (R := Set.univ) fun _ _ => trivial).2.1
    rw [hrot] at this
    exact this.infix ⟨a :: A ++ [b], [], by simp⟩
  obtain ⟨σ, hσ⟩ := exists_walk_of_isChain hBch ht ht'
  have hyR : y ∉ R.support := fun h => hdisj (Q.fst_mem_support_of_mem_edges hQe) h
  have hsR : s ∉ R.support := fun h => hdisj (Q.snd_mem_support_of_mem_edges hQe) h
  -- a vertex of a side path other than its start is in `B` or joined to `B` avoiding `X`
  have hside : ∀ {z t₀} (p : G.Walk z t₀), t₀ ∈ B → p.IsPath →
      (∀ x ∈ p.support, x ≠ z → x ≠ t₀ → x ∉ X) → z ∉ R.support →
      ∀ x ∈ p.support, x ∉ R.support := by
    intro z t₀ p ht₀ hp hpin hz x hx hxR
    by_cases hxz : x = z
    · exact hz (hxz ▸ hxR)
    · by_cases hxt : x = t₀
      · exact (hRL x hxR).1 (hxt ▸ ht₀)
      · exact (hRL x hxR).2 ⟨hpin x hx hxz hxt,
          isConnectedAvoiding_of_mem_path' ht₀ p hp hpin hx hxz⟩
  refine isCrossed_of_sup_edge_walk Q R halt hQ hQe hR hdisj (py.append (σ.append ps.reverse))
    fun x hx hxR => ?_
  rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
    List.mem_reverse] at hx
  rcases hx with hx | hx | hx
  · exact hside py ht hpy hpyin hyR x hx hxR
  · exact (hRL x hxR).1 (hσ x hx)
  · exact hside ps ht' hps hpsin hsR x hx hxR

/-! ### The bridge in `R` and Rule 3 when `R` meets both the pocket and the lower world -/

/-- If `[u, w]` is a sublist of a nodup list `l`, then `w` is not the head of `l`. -/
private theorem ne_head_of_sublist_two {l : List V} (hnd : l.Nodup) {u w c : V}
    (hh : l.head? = some c) (hsub : [u, w].Sublist l) : w ≠ c := by
  match l, hh with
  | c :: t, rfl =>
    rintro rfl
    have hct : w ∉ t := (List.nodup_cons.mp hnd).1
    rcases List.sublist_cons_iff.mp hsub with h | ⟨r, hr, h⟩
    · exact hct (h.subset (by simp))
    · simp only [List.cons.injEq] at hr
      exact hct (h.subset (hr.2 ▸ by simp))

/-- If `[u, w, v]` is a sublist of a nodup list `l`, then `w` is neither the first nor the last
entry of `l`. -/
private theorem ne_ends_of_sublist_three {l : List V} (hnd : l.Nodup) {u w v c d : V}
    (hh : l.head? = some c) (hl : l.getLast? = some d) (hsub : [u, w, v].Sublist l) :
    w ≠ c ∧ w ≠ d := by
  have hsub1 : [u, w].Sublist l := (show [u, w].Sublist [u, w, v] by simp).trans hsub
  have hsub2 : [v, w].Sublist l.reverse :=
    (show [v, w].Sublist [v, w, u] by simp).trans (List.sublist_reverse_iff.mpr hsub)
  exact ⟨ne_head_of_sublist_two hnd hh hsub1,
    ne_head_of_sublist_two (List.nodup_reverse.mpr hnd) (by rw [List.head?_reverse]; exact hl)
      hsub2⟩

/-- **The bridge in `R` when `R` meets both the pocket and the lower world.** Let `P` be an
induced, tight, separating `C`-path with `P.support = L₁ ++ y :: N ++ s :: L₂` and no vertex of
`N` on side `B`. Let `(Q, R)` be a crossing of `C` in `G + ys` with `ys` on `Q`. If `R` meets both
`N` and the lower world (either `B` or a vertex off `C ∪ P` joined to `B` avoiding `C ∪ P`), then
removing the third-kind vertices from `R` gives a chain `σ :: t :: T₂` from a vertex `σ ∈ N` to a
lower-world vertex `v₁` whose vertices after `σ` avoid `N` and `Q`, with `t` joined to `A` off `P`
and `v₁` joined to `B` off `P`, and whose prefix up to its first hit `z` on `P` is a bridge
`σ :: t :: K ++ [z]` to `z ∈ L₁ ∪ L₂` with `t :: K` off `C ∪ P ∪ Q`. -/
theorem exists_bridge_of_meets_pocket_and_lower (hCnd : C.Nodup)
    (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hind : ∀ u ∈ P.support, ∀ v ∈ P.support, G.Adj u v → IsListEdge P.support u v)
    (htight : IsTight G C A B P.support)
    (hsep : Separates G {x | x ∈ P.support} {x | x ∈ A} {x | x ∈ B})
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    {a' b' c d : V} (Q : (G ⊔ edge y s).Walk a' b') (R : G.Walk c d)
    (hQe : s(y, s) ∈ Q.edges) (hR : IsTPath G C R) (hdisj : Q.support.Disjoint R.support)
    {v₀ v₁ : V} (hv₀R : v₀ ∈ R.support) (hv₀N : v₀ ∈ N) (hv₁R : v₁ ∈ R.support)
    (hv₁L : v₁ ∈ B ∨ (v₁ ∉ {x | x ∈ C ∨ x ∈ P.support} ∧
      IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} v₁ {x | x ∈ B})) :
    ∃ (σ t z : V) (K R' : List V),
      σ ∈ N ∧ (z ∈ L₁ ∨ z ∈ L₂) ∧
      (σ :: t :: K ++ z :: R').IsChain G.Adj ∧ (σ :: t :: K ++ z :: R').Nodup ∧
      (t :: K ++ z :: R').getLast? = some v₁ ∧
      (∀ w ∈ t :: K ++ z :: R', w ∈ R.support ∧ w ∉ N ∧ w ∉ Q.support) ∧
      (∀ w ∈ t :: K, w ∉ C ∧ w ∉ P.support ∧ w ∉ Q.support) ∧
      ReachesOff G P.support A t ∧ ReachesOff G P.support B v₁ := by
  classical
  have hyQ : y ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hsQ : s ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  have hNP : ∀ w ∈ N, w ∈ P.support := fun w hw => by rw [hsupp]; simp [hw]
  have hv₁B : ReachesOff G P.support B v₁ := by
    rcases hv₁L with hB | ⟨hv₁X, b₀, hb₀, p, -, hin⟩
    · exact ⟨v₁, hB, .nil, by simpa using notMem_support_of_arc hCnd hrot hP (Or.inr hB)⟩
    · refine ⟨b₀, hb₀, p, fun w hw hwP => ?_⟩
      by_cases h1 : w = v₁
      · exact hv₁X (Or.inr (h1 ▸ hwP))
      · by_cases h2 : w = b₀
        · exact notMem_support_of_arc hCnd hrot hP (Or.inr hb₀) (h2 ▸ hwP)
        · exact hin w hw h1 h2 (Or.inr hwP)
  have hv₁P : v₁ ∉ P.support := by
    obtain ⟨b₀, -, p, hp⟩ := hv₁B
    exact hp v₁ p.start_mem_support
  have hv₁N : v₁ ∉ N := fun h => hv₁P (hNP v₁ h)
  -- filter third-kind vertices from `R.support`
  set Lr := R.support.filter fun u => !decide (IsThirdKind G C A B P.support u)
  have hLr_sub : Lr.Sublist R.support := List.filter_sublist
  have hLr_ch : Lr.IsChain G.Adj :=
    isChain_filter_thirdKind hrot htight le_rfl (fun _ _ h _ => h) R.isChain_adj_support
      hR.1.support_nodup
  have hLr_nd : Lr.Nodup := hR.1.support_nodup.sublist hLr_sub
  have hv₀Lr : v₀ ∈ Lr := List.mem_filter.mpr ⟨hv₀R, by
    simp [IsThirdKind, hNP v₀ hv₀N]⟩
  have hv₁Lr : v₁ ∈ Lr := List.mem_filter.mpr ⟨hv₁R, by
    rcases hv₁L with hB | ⟨-, b₀, hb₀, p, hp, hin⟩
    · have hv₁C : v₁ ∈ C := List.mem_rotate.mp (by rw [hrot]; simp [hB])
      simp [IsThirdKind, hv₁C]
    · have hconn' : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} v₁ {x | x ∈ A ∨ x ∈ B} :=
        ⟨b₀, Or.inr hb₀, p, hp, hin⟩
      simp [IsThirdKind, hconn']⟩
  -- orient `Lr` so that `v₀` appears before `v₁`
  obtain ⟨α₀, β₀, hLr_eq⟩ := List.append_of_mem hv₁Lr
  have hv₀_ab : v₀ ∈ α₀ ∨ v₀ ∈ β₀ := by
    have := hv₀Lr
    rw [hLr_eq] at this
    rcases List.mem_append.mp this with h | h
    · exact Or.inl h
    · rcases List.mem_cons.mp h with rfl | h
      · exact absurd hv₀N hv₁N
      · exact Or.inr h
  obtain ⟨L, α, β, hL_or, hL_eq, hv₀α⟩ :
      ∃ L α β, (L = Lr ∨ L = Lr.reverse) ∧ L = α ++ v₁ :: β ∧ v₀ ∈ α := by
    rcases hv₀_ab with h | h
    · exact ⟨Lr, α₀, β₀, Or.inl rfl, hLr_eq, h⟩
    · refine ⟨Lr.reverse, β₀.reverse, α₀.reverse, Or.inr rfl, ?_, List.mem_reverse.mpr h⟩
      rw [hLr_eq]; simp
  have hL_ch : L.IsChain G.Adj := by
    rcases hL_or with rfl | rfl
    · exact hLr_ch
    · exact List.isChain_reverse.mpr (hLr_ch.imp fun _ _ h => h.symm)
  have hL_nd : L.Nodup := by
    rcases hL_or with rfl | rfl
    · exact hLr_nd
    · exact List.nodup_reverse.mpr hLr_nd
  have hL_mem : ∀ w ∈ L, w ∈ R.support ∧ ¬ IsThirdKind G C A B P.support w ∧ w ∉ Q.support := by
    intro w hw
    have hwLr : w ∈ Lr := by
      rcases hL_or with rfl | rfl
      · exact hw
      · exact List.mem_reverse.mp hw
    obtain ⟨hwR, hw3⟩ := List.mem_filter.mp hwLr
    exact ⟨hwR, by simpa using hw3, fun h => hdisj h hwR⟩
  -- last vertex `σ ∈ N` in `α`
  obtain ⟨α₁, σ, α₂, rfl, hσN, hα₂⟩ :=
    exists_last_mem (Z := {w | w ∈ N}) α ⟨v₀, hv₀α, hv₀N⟩
  obtain ⟨t, T₂, hT₂⟩ : ∃ t T₂, α₂ ++ [v₁] = t :: T₂ :=
    List.exists_cons_of_ne_nil (by simp)
  have hinf : (σ :: t :: T₂) <:+: L := ⟨α₁, β, by rw [hL_eq, ← hT₂]; simp⟩
  have hch_T : (σ :: t :: T₂).IsChain G.Adj := hL_ch.infix hinf
  have hnd_T : (σ :: t :: T₂).Nodup := hL_nd.sublist hinf.sublist
  have hl_T : (t :: T₂).getLast? = some v₁ := by rw [← hT₂, List.getLast?_concat]
  have hmem_T : ∀ w ∈ t :: T₂, w ∈ R.support ∧ ¬ IsThirdKind G C A B P.support w ∧
      w ∉ N ∧ w ∉ Q.support := by
    intro w hw
    have hwL : w ∈ L := hinf.sublist.subset (List.mem_cons_of_mem _ hw)
    obtain ⟨hwR, hw3, hwQ⟩ := hL_mem w hwL
    have hwN : w ∉ N := by
      rw [← hT₂] at hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hα₂ w hw
      · rw [List.mem_singleton.mp hw]; exact hv₁N
    exact ⟨hwR, hw3, hwN, hwQ⟩
  -- `t` is off `P` and reaches `A` off `P`
  have hadj_σt : G.Adj σ t := (List.isChain_cons_cons.mp hch_T).1
  have ht_mem := hmem_T t (by simp)
  have htP : t ∉ P.support := by
    intro htP
    have hl := hind σ (hNP σ hσN) t htP hadj_σt
    rw [hsupp] at hl
    have hndP : (L₁ ++ y :: N ++ s :: L₂).Nodup := hsupp ▸ hP.1.support_nodup
    have htw := hl.mem_window hndP hσN
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at htw
    rcases htw with rfl | h | rfl
    · exact ht_mem.2.2.2 hyQ
    · exact ht_mem.2.2.1 h
    · exact ht_mem.2.2.2 hsQ
  have htA : ReachesOff G P.support A t :=
    reachesOff_of_pocket_adj hCnd hrot hP (hN σ hσN) hadj_σt htP ht_mem.2.1
  -- `t :: T₂` must hit `P.support` since `P` separates `A` from `B`
  have hhitP : ∃ w ∈ T₂, w ∈ P.support := by
    by_contra hno
    push Not at hno
    obtain ⟨W_T, hW_T⟩ := exists_walk_of_chain (t :: T₂) (List.isChain_cons_cons.mp hch_T).2
      rfl hl_T
    obtain ⟨a₀, ha₀, p_A, hp_A⟩ := htA
    obtain ⟨b₀, hb₀, p_B, hp_B⟩ := hv₁B
    obtain ⟨x, hx, hxP⟩ := hsep a₀ ha₀ b₀ hb₀ (p_A.reverse.append (W_T.append p_B))
    rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse, hW_T] at hx
    rcases hx with hx | hx | hx
    · exact hp_A x hx hxP
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact htP hxP
      · exact hno x hx hxP
    · exact hp_B x hx hxP
  obtain ⟨K, z, R', rfl, hzP, hK⟩ := exists_first_of_exists (fun w => w ∈ P.support) T₂ hhitP
  have hz_mem := hmem_T z (by simp)
  have hzL : z ∈ L₁ ∨ z ∈ L₂ := by
    rw [hsupp] at hzP
    simp only [List.mem_cons, List.mem_append] at hzP
    rcases hzP with (h | rfl | h) | rfl | h
    · exact Or.inl h
    · exact absurd hyQ hz_mem.2.2.2
    · exact absurd h hz_mem.2.2.1
    · exact absurd hsQ hz_mem.2.2.2
    · exact Or.inr h
  refine ⟨σ, t, z, K, R', hσN, hzL, by simpa using hch_T, by simpa using hnd_T,
    by simpa using hl_T, fun w hw => ?_, fun w hw => ?_, htA, hv₁B⟩
  · have hw' : w ∈ t :: (K ++ z :: R') := by simpa using hw
    exact ⟨(hmem_T w hw').1, (hmem_T w hw').2.2.1, (hmem_T w hw').2.2.2⟩
  · have hwT : w ∈ t :: (K ++ z :: R') := by
      rcases List.mem_cons.mp hw with rfl | hw
      · simp
      · simp [hw]
    have hwP : w ∉ P.support := by
      rcases List.mem_cons.mp hw with rfl | hw
      · exact htP
      · exact hK w hw
    have hw_sub : [σ, w, z].Sublist L := by
      have h1 : [σ, w, z].Sublist (σ :: (t :: K) ++ z :: R') := by
        rw [List.cons_append]
        refine List.Sublist.cons_cons σ ?_
        have h2 : ([w] ++ [z]).Sublist ((t :: K) ++ (z :: R')) :=
          List.Sublist.append (List.singleton_sublist.mpr hw) (by simp)
        simpa using h2
      exact (by simpa using h1 : [σ, w, z].Sublist (σ :: t :: (K ++ z :: R'))).trans hinf.sublist
    have hwc_d : w ≠ c ∧ w ≠ d := by
      rcases hL_or with rfl | rfl
      · exact ne_ends_of_sublist_three hR.1.support_nodup (head_support R) (getLast_support R)
          (hw_sub.trans hLr_sub)
      · have hrev : [z, w, σ].Sublist R.support :=
          (List.sublist_reverse_iff.mp (show [z, w, σ].reverse.Sublist Lr.reverse from hw_sub)).trans
            hLr_sub
        exact ne_ends_of_sublist_three hR.1.support_nodup (head_support R) (getLast_support R) hrev
    exact ⟨(hR.2.2.2 w (hmem_T w hwT).1 hwc_d.1 hwc_d.2).1, hwP, (hmem_T w hwT).2.2.2⟩

/-- Replacing a stretch `u :: N' ++ [v]` of `P` by a chain `u :: M ++ [v]` whose inner vertices `M`
are off `C ∪ P` gives a `C`-path `P'` that misses `N'`. -/
theorem exists_reroute_path_of_off {L₁' N' L₂' M : List V} {u v : V}
    (hP : IsTPath G C P) (hsupp : P.support = L₁' ++ u :: N' ++ v :: L₂')
    (hcM : (u :: M ++ [v]).IsChain G.Adj) (hndM : (u :: M ++ [v]).Nodup)
    (hM : ∀ w ∈ M, w ∉ C ∧ w ∉ P.support) :
    ∃ P' : G.Walk a b, IsTPath G C P' ∧ P'.support = L₁' ++ u :: M ++ v :: L₂' ∧
      (∀ w ∈ P'.support, w ∈ P.support ∨ w ∈ M) ∧
      ∀ w ∈ N', w ∉ P'.support := by
  have hnd : (L₁' ++ u :: N' ++ v :: L₂').Nodup := hsupp ▸ hP.1.support_nodup
  have hch : (L₁' ++ u :: N' ++ v :: L₂').IsChain G.Adj := hsupp ▸ P.isChain_adj_support
  have hc₁ : (L₁' ++ [u]).IsChain G.Adj := hch.infix ⟨[], N' ++ v :: L₂', by simp⟩
  have hc₂ : ([v] ++ L₂').IsChain G.Adj := hch.infix ⟨L₁' ++ u :: N', [], by simp⟩
  have hcW : ([u] ++ (M ++ [v])).IsChain G.Adj := by simpa using hcM
  have hc : (L₁' ++ u :: M ++ v :: L₂').IsChain G.Adj := by
    have h1 := hc₁.append_overlap hcW (by simp)
    have h2 := List.IsChain.append_overlap (l₁ := L₁' ++ [u] ++ M) (l₂ := [v]) (l₃ := L₂')
      (by simpa using h1) hc₂ (by simp)
    simpa using h2
  have hnd' : (L₁' ++ u :: M ++ v :: L₂').Nodup := by
    have h := nodup_replace (l₁ := L₁') (l₂ := u :: N' ++ [v]) (l₃ := L₂') (m := u :: M ++ [v])
      (by simpa using hnd) hndM (fun x hx => by
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | hx | rfl
        · exact Or.inl (by simp)
        · exact Or.inr fun h => (hM x hx).2 (by rw [hsupp]; simpa using h)
        · exact Or.inl (by simp))
    simpa using h
  have ha : (L₁' ++ u :: M ++ v :: L₂').head? = some a := by
    have h0 := head_support P
    rw [hsupp] at h0
    cases L₁' <;> simpa using h0
  have hb : (L₁' ++ u :: M ++ v :: L₂').getLast? = some b := by
    have h0 := getLast_support P
    rw [hsupp] at h0
    have e1 : L₁' ++ u :: N' ++ v :: L₂' = (L₁' ++ u :: N') ++ (v :: L₂') := by simp
    have e2 : L₁' ++ u :: M ++ v :: L₂' = (L₁' ++ u :: M) ++ (v :: L₂') := by simp
    rw [e1, List.getLast?_append_of_ne_nil _ (by simp)] at h0
    rw [e2, List.getLast?_append_of_ne_nil _ (by simp)]
    exact h0
  have hsub : ∀ w ∈ L₁' ++ u :: M ++ v :: L₂', w ∈ P.support ∨ w ∈ M := by
    intro w hw
    rw [hsupp]
    simp only [List.mem_append, List.mem_cons] at hw ⊢
    tauto
  obtain ⟨P', hP', hs⟩ := exists_tPath_of_list hc hnd' ha hb hP.2.1 hP.2.2.1 (fun w hw hwC => by
    rcases hsub w hw with hwP | hwM
    · by_contra hne
      push Not at hne
      exact (hP.2.2.2 w hwP hne.1 hne.2).1 hwC
    · exact absurd hwC (hM w hwM).1)
  refine ⟨P', hP', hs, fun w hw => hsub w (hs ▸ hw), fun w hw h => ?_⟩
  rw [hs] at h
  simp only [List.mem_append, List.mem_cons] at h
  have e : L₁' ++ u :: N' ++ v :: L₂' = (L₁' ++ [u]) ++ N' ++ (v :: L₂') := by simp
  rw [e, List.nodup_append, List.nodup_append] at hnd
  rcases h with (h | h | h) | h | h
  · exact hnd.1.2.2 w (by simp [h]) w hw rfl
  · exact hnd.1.2.2 w (by simp [h]) w hw rfl
  · exact (hM w h).2 (by rw [hsupp]; simp [hw])
  · exact hnd.2.2 w (by simp [hw]) w (by simp [h]) rfl
  · exact hnd.2.2 w (by simp [hw]) w (by simp [h]) rfl

/-- **Rerouting `P` along a bridge.** Given `P.support = L₁ ++ y :: N ++ s :: L₂`, `σ ∈ N`, and a
nodup chain `σ :: M ++ [z]` in `G` with `M` off `C ∪ P`, splicing the bridge into `P` produces a
`C`-path `P_new : G.Walk a b` in `G` whose vertices lie in `P.support ∪ M`, missing `y` when
`z ∈ L₁` and missing `s` when `z ∈ L₂`. -/
theorem exists_rerouted_path_of_bridge {M : List V} {σ z : V}
    (hP : IsTPath G C P) (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hσ : σ ∈ N) (hz : z ∈ L₁ ∨ z ∈ L₂)
    (hcM : (σ :: M ++ [z]).IsChain G.Adj) (hndM : (σ :: M ++ [z]).Nodup)
    (hM : ∀ w ∈ M, w ∉ C ∧ w ∉ P.support) :
    ∃ P_new : G.Walk a b, IsTPath G C P_new ∧
      (∀ w ∈ P_new.support, w ∈ P.support ∨ w ∈ M) ∧
      ((z ∈ L₁ ∧ y ∉ P_new.support) ∨ (z ∈ L₂ ∧ s ∉ P_new.support)) := by
  obtain ⟨N₀, N₁, rfl⟩ := List.append_of_mem hσ
  rcases hz with hz₁ | hz₂
  · obtain ⟨L₁₀, L₁₁, rfl⟩ := List.append_of_mem hz₁
    have hsupp' : P.support = L₁₀ ++ z :: (L₁₁ ++ y :: N₀) ++ σ :: (N₁ ++ s :: L₂) := by
      rw [hsupp]; simp
    have hrev_eq : (σ :: M ++ [z]).reverse = z :: M.reverse ++ [σ] := by simp
    have hcM' : (z :: M.reverse ++ [σ]).IsChain G.Adj := by
      rw [← hrev_eq, List.isChain_reverse]
      exact hcM.imp fun _ _ h => h.symm
    have hndM' : (z :: M.reverse ++ [σ]).Nodup := by
      rw [← hrev_eq]
      exact List.nodup_reverse.mpr hndM
    have hM' : ∀ w ∈ M.reverse, w ∉ C ∧ w ∉ P.support :=
      fun w hw => hM w (List.mem_reverse.mp hw)
    obtain ⟨P_new, hP_new, -, hsub, hmiss⟩ :=
      exists_reroute_path_of_off hP hsupp' hcM' hndM' hM'
    refine ⟨P_new, hP_new, fun w hw => (hsub w hw).imp id List.mem_reverse.mp,
      Or.inl ⟨by simp, hmiss y (by simp)⟩⟩
  · obtain ⟨L₂₀, L₂₁, rfl⟩ := List.append_of_mem hz₂
    have hsupp' : P.support = (L₁ ++ y :: N₀) ++ σ :: (N₁ ++ s :: L₂₀) ++ z :: L₂₁ := by
      rw [hsupp]; simp
    obtain ⟨P_new, hP_new, -, hsub, hmiss⟩ :=
      exists_reroute_path_of_off hP hsupp' hcM hndM hM
    exact ⟨P_new, hP_new, hsub, Or.inr ⟨by simp, hmiss s (by simp)⟩⟩

/-- **A side-`B` path misses the bridge.** Since no vertex of `N` is on side `B`, no path from a
vertex `u ∈ P.support` to `B` whose inner vertices avoid `C ∪ P` can meet a chain `t :: K` off
`C ∪ P` starting at a neighbour `t` of `σ ∈ N`. -/
theorem notMem_bridge_of_onSide_B {K : List V} {σ t u b₀ : V}
    (_hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hσ : σ ∈ N) (hc : (σ :: t :: K).IsChain G.Adj)
    (hK : ∀ w ∈ t :: K, w ∉ C ∧ w ∉ P.support)
    (hu : u ∈ P.support) (hb₀ : b₀ ∈ B) (p : G.Walk u b₀) (hp : p.IsPath)
    (hin : ∀ x ∈ p.support, x ≠ u → x ≠ b₀ → x ∉ {x | x ∈ C ∨ x ∈ P.support}) :
    ∀ w ∈ t :: K, w ∉ p.support := by
  classical
  intro w hw hwp
  have hwu : w ≠ u := fun h => (hK w hw).2 (h ▸ hu)
  have hwB : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {x | x ∈ B} :=
    isConnectedAvoiding_of_mem_path' hb₀ p hp hin hwp hwu
  obtain ⟨zB, hzB, qB, -, hqBin⟩ := hwB
  obtain ⟨qK, hqK⟩ := exists_walk_of_isChain (List.isChain_cons_cons.mp hc).2
    List.mem_cons_self hw
  have hadj : G.Adj σ t := (List.isChain_cons_cons.mp hc).1
  refine hN σ hσ (isConnectedAvoiding_of_walk_mem hzB (Walk.cons hadj (qK.append qB)) ?_)
  intro x hx hxX
  rw [Walk.support_cons, List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Or.inl rfl
  rw [Walk.mem_support_append_iff] at hx
  rcases hx with hx | hx
  · exact absurd hxX (by rintro (h | h); exacts [(hK x (hqK x hx)).1 h, (hK x (hqK x hx)).2 h])
  · by_cases h1 : x = w
    · subst h1
      exact absurd hxX (by rintro (h | h); exacts [(hK x hw).1 h, (hK x hw).2 h])
    · by_cases h2 : x = zB
      · exact Or.inr h2
      · exact absurd hxX (hqBin x hx h1 h2)

/-- **Rule 2 from the bridge.** If `t :: T₂` is a chain of `G` from `t` to `v₁` that misses `N` and
`Q`, and `t` is joined to `A` and `v₁` to `B` by walks that miss `Q` and `N`, then `C` is crossed in
`G`: replacing `ys` in `Q` by the pocket `y :: N ++ [s]` gives a walk between the two arcs cut by the
ends of `Q` (or from `a` to `b` when `Q` runs between `a` and `b`) that misses the `A`-`B` walk
through `t :: T₂`. -/
theorem undo_of_bridge_rule_two {T₂ : List V} {t v₁ a₀ b₀ : V}
    (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (Q : (G ⊔ edge y s).Walk a b) (hQ : IsTPath (G ⊔ edge y s) C Q) (hQe : s(y, s) ∈ Q.edges)
    (hcT : (t :: T₂).IsChain G.Adj) (hlT : (t :: T₂).getLast? = some v₁)
    (hT : ∀ w ∈ t :: T₂, w ∉ N ∧ w ∉ Q.support)
    (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ B) (p_A : G.Walk t a₀) (p_B : G.Walk v₁ b₀)
    (hpA : ∀ w ∈ p_A.support, w ∉ N ∧ w ∉ Q.support)
    (hpB : ∀ w ∈ p_B.support, w ∉ N ∧ w ∉ Q.support) :
    IsCrossed G C := by
  classical
  have hchN : (y :: N ++ [s]).IsChain G.Adj := by
    have := P.isChain_adj_support
    rw [hsupp] at this
    exact this.infix ⟨L₁, L₂, by simp⟩
  obtain ⟨W_N, hW_N⟩ := exists_walk_of_chain (u := y) (v := s) _ hchN (by simp)
    (List.getLast?_concat ..)
  have hQ' : ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ Q.support ∨ x ∈ N := by
    obtain ⟨X₁, X₂, h | h⟩ := Walk.exists_split_of_mem_edges hQe
    · have hch := Q.isChain_adj_support
      have hnd := hQ.1.support_nodup
      have hh := head_support Q
      have hl := getLast_support Q
      rw [h] at hch hnd hh hl
      obtain ⟨p, hp⟩ := exists_walk_replace hch hnd hh hl W_N
      refine ⟨p, fun x hx => ?_⟩
      rcases hp x hx with hx | hx
      · exact Or.inl (h ▸ hx)
      · rw [hW_N] at hx
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | hx | rfl
        · exact Or.inl (Q.fst_mem_support_of_mem_edges hQe)
        · exact Or.inr hx
        · exact Or.inl (Q.snd_mem_support_of_mem_edges hQe)
    · have hch := Q.isChain_adj_support
      have hnd := hQ.1.support_nodup
      have hh := head_support Q
      have hl := getLast_support Q
      rw [h, edge_comm] at hch
      rw [h] at hnd hh hl
      obtain ⟨p, hp⟩ := exists_walk_replace hch hnd hh hl W_N.reverse
      refine ⟨p, fun x hx => ?_⟩
      rcases hp x hx with hx | hx
      · exact Or.inl (h ▸ hx)
      · rw [Walk.support_reverse, List.mem_reverse, hW_N] at hx
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | hx | rfl
        · exact Or.inl (Q.fst_mem_support_of_mem_edges hQe)
        · exact Or.inr hx
        · exact Or.inl (Q.snd_mem_support_of_mem_edges hQe)
  obtain ⟨p, hp⟩ := hQ'
  have hp_in : IsTPath G C p.bypass := by
    refine ⟨p.bypass_isPath, hP.2.1, hP.2.2.1, fun x hx h1 h2 => ?_⟩
    have hx' := hp x (p.support_bypass_subset_support hx)
    have hxC : x ∉ C := by
      rcases hx' with hxQ | hxN
      · exact (hQ.2.2.2 x hxQ h1 h2).1
      · exact not_mem_C_of_mem_window hP hsupp hxN
    exact ⟨hxC, hxC⟩
  refine isCrossed_of_not_separates hrot hp_in fun hsep => ?_
  obtain ⟨W_T, hW_T⟩ := exists_walk_of_chain (t :: T₂) hcT rfl hlT
  obtain ⟨x, hx, hxp⟩ := hsep a₀ ha₀ b₀ hb₀ (p_A.reverse.append (W_T.append p_B))
  have hxp' := hp x (p.support_bypass_subset_support hxp)
  rw [Walk.mem_support_append_iff, Walk.mem_support_append_iff, Walk.support_reverse,
    List.mem_reverse, hW_T] at hx
  rcases hx with hx | hx | hx
  · exact hxp'.elim (hpA x hx).2 (hpA x hx).1
  · exact hxp'.elim (hT x hx).2 (hT x hx).1
  · exact hxp'.elim (hpB x hx).2 (hpB x hx).1

/-- **Rule 3: searching `G - P_new` between `A` and `B`.** If the rerouted `C`-path `P_new` does not
separate `A` from `B` in `G`, then `C` is crossed in `G`. In particular, when the bridge lands in
`L₁` (`z ∈ L₁`, so `y ∉ P_new.support`) and `y` is joined to `A` avoiding `P_new.support`, `y`'s
side-`B` path automatically avoids `P_new.support` (`notMem_bridge_of_onSide_B`), so `P_new` does
not separate `A` from `B` and Rule 3 finds a crossing of `C` in `G`. -/
theorem undo_of_bridge_rule_three_left {K : List V} {σ t z : V}
    (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hyB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} y)
    (hσ : σ ∈ N) (hcM : (σ :: t :: K ++ [z]).IsChain G.Adj)
    (hK : ∀ w ∈ t :: K, w ∉ C ∧ w ∉ P.support)
    {P_new : G.Walk a b} (hP_new : IsTPath G C P_new)
    (hsub : ∀ w ∈ P_new.support, w ∈ P.support ∨ w ∈ t :: K)
    (hyP : y ∉ P_new.support) (hyA : ReachesOff G P_new.support A y) :
    IsCrossed G C := by
  refine isCrossed_of_not_separates hrot hP_new fun hsep => ?_
  obtain ⟨a₀, ha₀, p_A, hp_A⟩ := hyA
  obtain ⟨b₀, hb₀, p_B, hp_B, hin_B⟩ := hyB
  have hcK : (σ :: t :: K).IsChain G.Adj := hcM.left_of_append
  have hyP₀ : y ∈ P.support := by rw [hsupp]; simp
  have hp_B_bridge := notMem_bridge_of_onSide_B hsupp hN hσ hcK hK hyP₀ hb₀ p_B hp_B hin_B
  have hb₀P : b₀ ∉ P.support := notMem_support_of_arc hCnd hrot hP (Or.inr hb₀)
  obtain ⟨x, hx, hxP'⟩ := hsep a₀ ha₀ b₀ hb₀ (p_A.reverse.append p_B)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx
  rcases hx with hx | hx
  · exact hp_A x hx hxP'
  · rcases hsub x hxP' with hxP₀ | hxK
    · by_cases h1 : x = y
      · exact hyP (h1 ▸ hxP')
      · by_cases h2 : x = b₀
        · exact hb₀P (h2 ▸ hxP₀)
        · exact hin_B x hx h1 h2 (Or.inr hxP₀)
    · exact hp_B_bridge x hxK hx

/-- **Rule 3 when the bridge lands in `L₂`.** Symmetrically, when `z ∈ L₂` (`s ∉ P_new.support`) and
`s` is joined to `A` avoiding `P_new.support`, `s`'s side-`B` path automatically avoids
`P_new.support`, so `P_new` does not separate `A` from `B` and Rule 3 finds a crossing of `C` in
`G`. -/
theorem undo_of_bridge_rule_three_right {K : List V} {σ t z : V}
    (hCnd : C.Nodup) (hrot : C.rotate k = a :: A ++ b :: B) (hP : IsTPath G C P)
    (hsupp : P.support = L₁ ++ y :: N ++ s :: L₂)
    (hN : ∀ v ∈ N, ¬ IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} v)
    (hsB : IsOnSide G {x | x ∈ C ∨ x ∈ P.support} {x | x ∈ B} s)
    (hσ : σ ∈ N) (hcM : (σ :: t :: K ++ [z]).IsChain G.Adj)
    (hK : ∀ w ∈ t :: K, w ∉ C ∧ w ∉ P.support)
    {P_new : G.Walk a b} (hP_new : IsTPath G C P_new)
    (hsub : ∀ w ∈ P_new.support, w ∈ P.support ∨ w ∈ t :: K)
    (hsP : s ∉ P_new.support) (hsA : ReachesOff G P_new.support A s) :
    IsCrossed G C := by
  refine isCrossed_of_not_separates hrot hP_new fun hsep => ?_
  obtain ⟨a₀, ha₀, p_A, hp_A⟩ := hsA
  obtain ⟨b₀, hb₀, p_B, hp_B, hin_B⟩ := hsB
  have hcK : (σ :: t :: K).IsChain G.Adj := hcM.left_of_append
  have hsP₀ : s ∈ P.support := by rw [hsupp]; simp
  have hp_B_bridge := notMem_bridge_of_onSide_B hsupp hN hσ hcK hK hsP₀ hb₀ p_B hp_B hin_B
  have hb₀P : b₀ ∉ P.support := notMem_support_of_arc hCnd hrot hP (Or.inr hb₀)
  obtain ⟨x, hx, hxP'⟩ := hsep a₀ ha₀ b₀ hb₀ (p_A.reverse.append p_B)
  rw [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse] at hx
  rcases hx with hx | hx
  · exact hp_A x hx hxP'
  · rcases hsub x hxP' with hxP₀ | hxK
    · by_cases h1 : x = s
      · exact hsP (h1 ▸ hxP')
      · by_cases h2 : x = b₀
        · exact hb₀P (h2 ▸ hxP₀)
        · exact hin_B x hx h1 h2 (Or.inr hxP₀)
    · exact hp_B_bridge x hxK hx

/-! ### Observations 2 and 3: subinstance crossings and the Figure 11 lift -/

/-- If `G ≤ H` and every edge of `H \ G` has both ends in `l`, then `H - l = G - l`. -/
theorem restrict_notMem_eq_of_adj_or_mem {H : SimpleGraph V} {l : List V} (hle : G ≤ H)
    (hH : ∀ x y, H.Adj x y → G.Adj x y ∨ (x ∈ l ∧ y ∈ l)) :
    restrict H {w | w ∉ l} = restrict G {w | w ∉ l} := by
  ext x y
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨(hH x y h1).resolve_right (fun h => h2 h.1), h2, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨hle h1, h2, h3⟩⟩

/-- Every list edge of `a :: m ++ [b]` is a cycle edge of `a :: A ++ b :: m.reverse`. -/
theorem IsListEdge.isCycleEdge_side₁ {a b : V} {A m : List V} {u v : V}
    (h : IsListEdge (a :: m ++ [b]) u v) :
    PlaneEmbedding.IsCycleEdge (a :: A ++ b :: m.reverse) u v := by
  rw [← isCycleEdge_rotate _ (A.length + 1)]
  have hrot' : (a :: A ++ b :: m.reverse).rotate (A.length + 1) = b :: (m.reverse ++ a :: A) := by
    rw [show a :: A ++ b :: m.reverse = (a :: A) ++ (b :: m.reverse) by simp,
      show A.length + 1 = (a :: A).length by simp, List.rotate_append_length_eq]
    simp
  rw [hrot']
  refine isCycleEdge_of_isListEdge ?_
  rw [show b :: (m.reverse ++ a :: A) ++ [b] = (b :: m.reverse ++ [a]) ++ (A ++ [b]) by simp]
  refine IsListEdge.append_left ?_
  have := h.reverse
  simpa using this

/-- Every list edge of `a :: m ++ [b]` is a cycle edge of `b :: B ++ a :: m`. -/
theorem IsListEdge.isCycleEdge_side₂ {a b : V} {B m : List V} {u v : V}
    (h : IsListEdge (a :: m ++ [b]) u v) :
    PlaneEmbedding.IsCycleEdge (b :: B ++ a :: m) u v := by
  have h' : IsListEdge (b :: m.reverse ++ [a]) u v := by simpa using h.reverse
  simpa using h'.isCycleEdge_side₁ (A := B)

/-- **Observation 2, path step:** If every edge of `H' \ G'` is a cycle edge of `T`, then a
`T`-path of `H'` whose ends are not consecutive on `T` uses no edge of `H' \ G'` and is a `T`-path
of `G'` with the same support. -/
theorem exists_tPath_of_not_isCycleEdge {G' H' : SimpleGraph V} {T : List V} {u v : V}
    (hH' : ∀ x y, H'.Adj x y → G'.Adj x y ∨ PlaneEmbedding.IsCycleEdge T x y)
    {p : H'.Walk u v} (hp : IsTPath H' T p) (hnot : ¬ PlaneEmbedding.IsCycleEdge T u v) :
    ∃ q : G'.Walk u v, IsTPath G' T q ∧ q.support = p.support := by
  have hsub : ∀ e ∈ p.edges, e ∈ G'.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hadj := p.adj_of_mem_edges he
      rcases hH' x y hadj with hG | hcyc
      · exact hG
      · exfalso
        rcases ends_of_mem_edges hp he hcyc.mem_left hcyc.symm.mem_left (H'.ne_of_adj hadj)
          with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hnot hcyc
        · exact hnot hcyc.symm
  refine ⟨p.transfer G' hsub, ⟨hp.1.transfer hsub, hp.2.1, hp.2.2.1, ?_⟩,
    Walk.support_transfer p hsub⟩
  rw [Walk.support_transfer]
  exact hp.2.2.2

/-- **Observation 2: a subinstance crossing uses no edge of `P'`.** If `T` is nodup and every edge
of `H' \ G'` is a cycle edge of `T`, then any crossing `(Q, R)` of `T` in `H'` transfers to a
crossing `(Q', R')` of `T` in `G'` with the same supports. -/
theorem exists_crossing_of_adj_or_isCycleEdge {G' H' : SimpleGraph V} {T : List V} (hnd : T.Nodup)
    (hH' : ∀ x y, H'.Adj x y → G'.Adj x y ∨ PlaneEmbedding.IsCycleEdge T x y)
    {u₁ v₁ u₂ v₂ : V} {Q : H'.Walk u₁ v₁} {R : H'.Walk u₂ v₂} (hcr : IsCrossing H' T Q R) :
    ∃ (Q' : G'.Walk u₁ v₁) (R' : G'.Walk u₂ v₂),
      IsCrossing G' T Q' R' ∧ Q'.support = Q.support ∧ R'.support = R.support := by
  obtain ⟨k₁, L₁, L₂, hrot₁, hc₁, hd₁⟩ := hcr.alternate
  obtain ⟨k₂, M₁, M₂, hrot₂, hc₂, hd₂⟩ := hcr.alternate.comm
  have hnotQ : ¬ PlaneEmbedding.IsCycleEdge T u₁ v₁ :=
    not_isCycleEdge_of_rotate hnd hrot₁ (List.ne_nil_of_mem hc₁) (List.ne_nil_of_mem hd₁)
  have hnotR : ¬ PlaneEmbedding.IsCycleEdge T u₂ v₂ :=
    not_isCycleEdge_of_rotate hnd hrot₂ (List.ne_nil_of_mem hc₂) (List.ne_nil_of_mem hd₂)
  obtain ⟨Q', hQ', hQs⟩ := exists_tPath_of_not_isCycleEdge hH' hcr.2.1 hnotQ
  obtain ⟨R', hR', hRs⟩ := exists_tPath_of_not_isCycleEdge hH' hcr.2.2.1 hnotR
  exact ⟨Q', R', ⟨hcr.1, hQ', hR', by rw [hQs, hRs]; exact hcr.2.2.2⟩, hQs, hRs⟩

/-- The vertex set of side `A` of a path `Pv` in `G`: `Pv` together with the vertices reached from
`A` in `G - Pv`. -/
@[expose] def sideSetOf (G : SimpleGraph V) (Pv A : List V) : Set V :=
  {v | v ∈ Pv} ∪ {v | ∃ u ∈ A, (restrict G {w | w ∉ Pv}).Reachable u v}

/-- The vertex set of the second subinstance of Proposition 5.1: `Pv` together with the vertices
not reached from `A` in `G - Pv`. -/
@[expose] def sideComplOf (G : SimpleGraph V) (Pv A : List V) : Set V :=
  {v | v ∈ Pv} ∪ {v | ∃ u ∈ A, (restrict G {w | w ∉ Pv}).Reachable u v}ᶜ

/-- A walk in `G` from `t ∈ sideSetOf G (a :: m ++ [b]) A` to `c ∈ A` whose vertices after `t`
avoid `a :: m ++ [b]` and whose inner vertices avoid `A` gives an avoiding path in
`restrict G (sideSetOf G (a :: m ++ [b]) A)`. -/
private theorem isConnectedAvoiding_restrict_sideSetOf_of_walk [DecidableEq V] {m : List V}
    {t c : V} (ht : t ∈ sideSetOf G (a :: m ++ [b]) A) (hc : c ∈ A)
    (q : G.Walk t c) (hq : ∀ x ∈ q.support, x ≠ t → x ∉ a :: m ++ [b] ∧ (x ≠ c → x ∉ A)) :
    IsConnectedAvoiding (restrict G (sideSetOf G (a :: m ++ [b]) A))
      {z | z ∈ a :: A ++ b :: m.reverse} t {z | z ∈ A} := by
  set p := q.bypass
  have hp_path : p.IsPath := q.bypass_isPath
  have hp_sub : ∀ x ∈ p.support, x ∈ q.support := fun _ hx => q.support_bypass_subset_support hx
  have hp_S₁ : ∀ x ∈ p.support, x ∈ sideSetOf G (a :: m ++ [b]) A := by
    intro x hx
    by_cases hxt : x = t
    · exact hxt ▸ ht
    · right
      have hoff : ∀ w ∈ (p.dropUntil x hx).support, w ∉ a :: m ++ [b] := fun w hw => by
        have hwt : w ≠ t := fun h =>
          start_notMem_support_dropUntil hp_path hx hxt (h ▸ hw)
        exact (hq w (hp_sub w (p.support_dropUntil_subset_support hx hw)) hwt).1
      have hE : ∀ e ∈ (p.dropUntil x hx).edges, e ∈ (restrict G {w | w ∉ a :: m ++ [b]}).edgeSet :=
        fun e he => by
          induction e using Sym2.ind with
          | _ u v =>
            exact ⟨(p.dropUntil x hx).adj_of_mem_edges he,
              hoff u ((p.dropUntil x hx).fst_mem_support_of_mem_edges he),
              hoff v ((p.dropUntil x hx).snd_mem_support_of_mem_edges he)⟩
      exact ⟨c, hc, Reachable.symm ⟨(p.dropUntil x hx).transfer _ hE⟩⟩
  have hE : ∀ e ∈ p.edges, e ∈ (restrict G (sideSetOf G (a :: m ++ [b]) A)).edgeSet :=
    fun e he => by
      induction e using Sym2.ind with
      | _ u v =>
        exact ⟨p.adj_of_mem_edges he, hp_S₁ u (p.fst_mem_support_of_mem_edges he),
          hp_S₁ v (p.snd_mem_support_of_mem_edges he)⟩
  refine ⟨c, hc, p.transfer _ hE, hp_path.transfer hE, fun x hx h1 h2 hxD => ?_⟩
  rw [Walk.support_transfer] at hx
  obtain ⟨hxP, hxA⟩ := hq x (hp_sub x hx) h1
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at hxD
  rcases hxD with rfl | h | rfl | h
  · exact hxP (by simp)
  · exact hxA h2 h
  · exact hxP (by simp)
  · exact hxP (by simp [h])

/-- The cycle and Claim 4.2 on `sideSetOf G (a :: m ++ [b]) A`. -/
private theorem side_cyc_and_claim {H : SimpleGraph V} {m : List V}
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hle : G ≤ H)
    {P' : H.Walk a b} (hP' : IsTPath H C P') (hm : P'.support = a :: m ++ [b])
    (hsideA : ∀ v ∈ P'.support, IsOnSide G {x | x ∈ C ∨ x ∈ P'.support} {x | x ∈ A} v) :
    (∀ v ∈ a :: A ++ b :: m.reverse, v ∈ sideSetOf G (a :: m ++ [b]) A) ∧
      IsCycleList (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ∧
      ∀ t ∈ sideSetOf G (a :: m ++ [b]) A,
        IsConnectedAvoiding (restrict H (sideSetOf G (a :: m ++ [b]) A))
          {z | z ∈ a :: A ++ b :: m.reverse} t {z | z ∈ A} := by
  classical
  set S₁ := sideSetOf G (a :: m ++ [b]) A
  have hframe : ∀ v ∈ a :: A ++ b :: m.reverse, v ∈ S₁ := by
    intro v hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_reverse] at hv
    rcases hv with rfl | hvA | rfl | hvm
    · exact Or.inl (by simp)
    · exact Or.inr ⟨v, hvA, Reachable.refl v⟩
    · exact Or.inl (by simp)
    · exact Or.inl (by simp [hvm])
  have hC' : IsCycleList G (a :: A ++ b :: B) := hrot ▸ hC.rotate k
  have hnd : (a :: A ++ b :: B).Nodup := hC'.2.1
  rw [List.cons_append, List.nodup_cons, List.nodup_append] at hnd
  have hPnd : (a :: m ++ [b]).Nodup := hm ▸ hP'.1.support_nodup
  have hPch : (a :: m ++ [b]).IsChain H.Adj := hm ▸ P'.isChain_adj_support
  have hP₁ := hC'.isPathList (R := Set.univ) fun _ _ => trivial
  rw [show a :: A ++ b :: B = (a :: A ++ [b]) ++ B by simp] at hP₁
  have hch₁ : (a :: A ++ [b]).IsChain (restrict H S₁).Adj :=
    isChain_restrict (hP₁.prefix.2.1.imp fun _ _ h => hle h) fun v hv => hframe v (by
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hv ⊢
      tauto)
  have hch₂ : (b :: m.reverse ++ [a]).IsChain (restrict H S₁).Adj := by
    have hr : (a :: m ++ [b]).reverse = b :: m.reverse ++ [a] := by simp
    have hch_rev : (b :: m.reverse ++ [a]).IsChain H.Adj := by
      rw [← hr, List.isChain_reverse]
      exact hPch.imp fun _ _ h => h.symm
    exact isChain_restrict hch_rev fun v hv => Or.inl (by rw [← hr, List.mem_reverse] at hv; exact hv)
  have h₁ : IsPathList (restrict H S₁) Set.univ (a :: A ++ [b]) :=
    ⟨hP₁.prefix.1, hch₁, fun _ _ => trivial⟩
  have h₂ : IsPathList (restrict H S₁) Set.univ (b :: m.reverse ++ [a]) := by
    have hr : (a :: m ++ [b]).reverse = b :: m.reverse ++ [a] := by simp
    exact ⟨by rw [← hr]; exact List.nodup_reverse.mpr hPnd, hch₂, fun _ _ => trivial⟩
  have hAP' : ∀ v ∈ A, v ∉ P'.support :=
    fun v hv => notMem_support_of_arc hC.2.1 hrot hP' (Or.inl hv)
  have hcyc : IsCycleList (restrict H S₁) (a :: A ++ b :: m.reverse) := by
    refine isCycleList_of_two_paths h₁ h₂ (fun v hv hvm => ?_) ?_ (Or.inl hA)
    · exact hAP' v hv (by rw [hm]; simp [List.mem_reverse.mp hvm])
    · intro e; subst e; exact hnd.1 (by simp)
  have hle_S₁ : restrict G S₁ ≤ restrict H S₁ := fun _ _ ⟨h1, h2⟩ => ⟨hle h1, h2⟩
  refine ⟨hframe, hcyc, fun t ht => ?_⟩
  refine (?_ : IsConnectedAvoiding (restrict G S₁) _ t _).mono hle_S₁ Set.Subset.rfl
  by_cases htP : t ∈ a :: m ++ [b]
  · obtain ⟨c, hc, q, -, hin⟩ := hsideA t (hm.symm ▸ htP)
    refine isConnectedAvoiding_restrict_sideSetOf_of_walk ht hc q fun x hx hxt => ?_
    by_cases hxc : x = c
    · subst hxc
      exact ⟨hm ▸ hAP' x hc, fun h => absurd rfl h⟩
    · have hxX := hin x hx hxt hxc
      have hxC : x ∉ C := fun h => hxX (Or.inl h)
      exact ⟨fun h => hxX (Or.inr (hm.symm ▸ h)),
        fun _ hA' => hxC (List.mem_rotate.mp (by rw [hrot]; simp [hA']))⟩
  · rcases ht with ht' | ⟨u, hu, ⟨q₀⟩⟩
    · exact absurd ht' htP
    · set q₁ := q₀.reverse.mapLe (restrict_le G _)
      have hq₁_off : ∀ x ∈ q₁.support, x ∉ a :: m ++ [b] := by
        intro x hx
        rw [support_mapLe] at hx
        by_cases hxt : x = t
        · exact hxt ▸ htP
        · exact mem_of_mem_support_restrict q₀.reverse hx hxt
      obtain ⟨c, hc, q, hq_sub, hq_in, -⟩ := exists_first_hit {z | z ∈ A} q₁ hu
      exact isConnectedAvoiding_restrict_sideSetOf_of_walk (Or.inr ⟨u, hu, ⟨q₀⟩⟩) hc q
        fun x hx hxt => ⟨hq₁_off x (hq_sub x hx), fun hxc => hq_in x hx hxc⟩

/-- **Observation 3: the Figure 11 setting holds directly from `OnBothSidesList` and `Separates`
in `G`, without web completions or Theorem 1.3.** -/
theorem setting_of_onBothSidesList {H : SimpleGraph V} {m : List V}
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    (hle : G ≤ H) {P' : H.Walk a b} (hP' : IsTPath H C P') (hm : P'.support = a :: m ++ [b])
    (hind : ∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v)
    (hsep : Separates G {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B})
    (hsides : OnBothSidesList G C A B P'.support) :
    Setting H (sideSetOf G (a :: m ++ [b]) A) (sideSetOf G (a :: m ++ [b]) B) a b m A B C k := by
  have h1 := side_cyc_and_claim hC hrot hA hle hP' hm fun v hv => (hsides v hv).1
  have hrot' : C.rotate (k + (A.length + 1)) = b :: B ++ a :: A := by
    rw [← List.rotate_rotate, hrot, rotate_cons_append_cons]
  have hm' : P'.reverse.support = b :: m.reverse ++ [a] := by
    rw [Walk.support_reverse, hm]; simp
  have hmem_rev : ∀ w, w ∈ b :: m.reverse ++ [a] ↔ w ∈ a :: m ++ [b] := by
    intro w
    have hr : (a :: m ++ [b]).reverse = b :: m.reverse ++ [a] := by simp
    rw [← hr, List.mem_reverse]
  have hset_eq : sideSetOf G (b :: m.reverse ++ [a]) B = sideSetOf G (a :: m ++ [b]) B := by
    have h1 : {v | v ∈ b :: m.reverse ++ [a]} = {v | v ∈ a :: m ++ [b]} := by
      ext w; exact hmem_rev w
    have h2 : {w | w ∉ b :: m.reverse ++ [a]} = {w | w ∉ a :: m ++ [b]} := by
      ext w; exact not_congr (hmem_rev w)
    simp only [sideSetOf, h1, h2]
  have hsideB : ∀ v ∈ P'.reverse.support,
      IsOnSide G {x | x ∈ C ∨ x ∈ P'.reverse.support} {x | x ∈ B} v := by
    intro v hv
    rw [Walk.support_reverse, List.mem_reverse] at hv
    have hX : {x | x ∈ C ∨ x ∈ P'.reverse.support} = {x | x ∈ C ∨ x ∈ P'.support} := by
      ext x; simp [Walk.support_reverse]
    rw [hX]
    exact (hsides v hv).2
  have h2 := side_cyc_and_claim hC hrot' hB hle hP'.reverse hm' hsideB
  rw [List.reverse_reverse, hset_eq] at h2
  have hAP' : ∀ v ∈ A, v ∉ P'.support :=
    fun v hv => notMem_support_of_arc hC.2.1 hrot hP' (Or.inl hv)
  refine ⟨?_, hm ▸ hind, h1.2.1, h1.1, h1.2.2, h2.2.1, h2.1, h2.2.2, hrot, hA, hB⟩
  ext v
  simp only [sideSetOf, Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨fun ⟨hA', hB'⟩ => ?_, fun hv => ⟨Or.inl hv, Or.inl hv⟩⟩
  by_contra hvP
  rcases hA' with h | ⟨u₁, hu₁, ⟨p₁⟩⟩
  · exact hvP h
  rcases hB' with h | ⟨u₂, hu₂, ⟨p₂⟩⟩
  · exact hvP h
  obtain ⟨w, hw, hwP'⟩ := hsep u₁ hu₁ u₂ hu₂ ((p₁.append p₂.reverse).mapLe (restrict_le G _))
  rw [support_mapLe] at hw
  have hwP : w ∈ a :: m ++ [b] := hm ▸ hwP'
  by_cases hwu₁ : w = u₁
  · exact hAP' u₁ hu₁ (hwu₁ ▸ hwP')
  · exact mem_of_mem_support_restrict (p₁.append p₂.reverse) hw hwu₁ hwP

/-- If `P` is tight, any `(b :: B ++ a :: m)`-path in `sideComplOf G (a :: m ++ [b]) A` whose ends
are not consecutive on `b :: B ++ a :: m` lies entirely in `sideSetOf G (a :: m ++ [b]) B`. -/
theorem exists_tPath_sideSetOf_B_of_tight {m : List V}
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hm : P.support = a :: m ++ [b])
    (htight : IsTight G C A B P.support) {u v : V}
    {Q : (restrict G (sideComplOf G (a :: m ++ [b]) A)).Walk u v}
    (hQ : IsTPath (restrict G (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m) Q)
    (hnot : ¬ PlaneEmbedding.IsCycleEdge (b :: B ++ a :: m) u v) :
    ∃ Q' : (restrict G (sideSetOf G (a :: m ++ [b]) B)).Walk u v,
      IsTPath (restrict G (sideSetOf G (a :: m ++ [b]) B)) (b :: B ++ a :: m) Q' ∧
      Q'.support = Q.support := by
  classical
  have hmem_P : ∀ w, w ∈ a :: m ++ [b] → w ∈ b :: B ++ a :: m := by
    intro w hw
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at hw ⊢
    tauto
  have hframe_B : ∀ w ∈ b :: B ++ a :: m, w ∈ sideSetOf G (a :: m ++ [b]) B := by
    intro w hw
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | hwB | rfl | hwm
    · exact Or.inl (by simp)
    · exact Or.inr ⟨w, hwB, Reachable.refl w⟩
    · exact Or.inl (by simp)
    · exact Or.inl (by simp [hwm])
  have hinner_off : ∀ x ∈ Q.support, x ≠ u → x ≠ v →
      x ∉ b :: B ++ a :: m ∧ x ∉ a :: m ++ [b] ∧ x ∉ P.support ∧ x ∉ C ∧
      ¬ ∃ a₀ ∈ A, (restrict G {z | z ∉ a :: m ++ [b]}).Reachable a₀ x := by
    intro x hx hxu hxv
    have hx_sub : x ∉ b :: B ++ a :: m := (hQ.2.2.2 x hx hxu hxv).1
    have hx_Pv : x ∉ a :: m ++ [b] := fun h => hx_sub (hmem_P x h)
    have hx_P : x ∉ P.support := hm ▸ hx_Pv
    have hx_compl : x ∈ sideComplOf G (a :: m ++ [b]) A := mem_of_mem_support_restrict Q hx hxu
    have hx_noA : ¬ ∃ a₀ ∈ A, (restrict G {z | z ∉ a :: m ++ [b]}).Reachable a₀ x := by
      rcases hx_compl with h | h
      · exact absurd h hx_Pv
      · exact h
    have hx_notA : x ∉ A := fun h => hx_noA ⟨x, h, Reachable.refl x⟩
    have hx_notC : x ∉ C := by
      intro hxC
      rcases mem_arcs_of_mem_C hrot hxC hx_P with h | h
      · exact hx_notA h
      · exact hx_sub (by simp [h])
    exact ⟨hx_sub, hx_Pv, hx_P, hx_notC, hx_noA⟩
  have hQ_B : ∀ w ∈ Q.support, w ∈ sideSetOf G (a :: m ++ [b]) B := by
    intro w hw
    by_cases hwu : w = u
    · exact hwu ▸ hframe_B u hQ.2.1
    by_cases hwv : w = v
    · exact hwv ▸ hframe_B v hQ.2.2.1
    obtain ⟨hw_sub, hw_Pv, hw_P, hw_C, hw_noA⟩ := hinner_off w hw hwu hwv
    by_contra hw_notB
    have hw_noB : ¬ ∃ b₀ ∈ B, (restrict G {z | z ∉ a :: m ++ [b]}).Reachable b₀ w :=
      fun h => hw_notB (Or.inr h)
    have hw_no_AB : ¬ IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {x | x ∈ A ∨ x ∈ B} := by
      rintro ⟨c, hc, p, -, hp_in⟩
      have hp_off : ∀ x ∈ p.support, x ∉ a :: m ++ [b] := by
        intro x hx
        by_cases hxw : x = w
        · exact hxw ▸ hw_Pv
        by_cases hxc : x = c
        · exact hm ▸ notMem_support_of_arc hC.2.1 hrot hP (hxc ▸ hc)
        · exact fun h => hp_in x hx hxw hxc (Or.inr (hm.symm ▸ h))
      have hE : ∀ e ∈ p.edges, e ∈ (restrict G {z | z ∉ a :: m ++ [b]}).edgeSet := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
          exact ⟨p.adj_of_mem_edges he, hp_off x (p.fst_mem_support_of_mem_edges he),
            hp_off y (p.snd_mem_support_of_mem_edges he)⟩
      have hreach : (restrict G {z | z ∉ a :: m ++ [b]}).Reachable c w :=
        Reachable.symm ⟨p.transfer _ hE⟩
      rcases hc with hcA | hcB
      · exact hw_noA ⟨c, hcA, hreach⟩
      · exact hw_noB ⟨c, hcB, hreach⟩
    have hconn₁ : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {u} := by
      set q₁ := (Q.takeUntil w hw).reverse.mapLe (restrict_le G _)
      refine ⟨u, rfl, q₁, ((hQ.1.takeUntil hw).reverse).mapLe _, fun x hx hxw hxu => ?_⟩
      rw [support_mapLe, Walk.support_reverse, List.mem_reverse] at hx
      have hxQ : x ∈ Q.support := Q.support_takeUntil_subset_support hw hx
      have hxv : x ≠ v := fun e =>
        Walk.endpoint_notMem_support_takeUntil hQ.1 hw (Ne.symm hwv) (e ▸ hx)
      obtain ⟨-, -, hx_P, hx_C, -⟩ := hinner_off x hxQ hxu hxv
      rintro (h | h)
      · exact hx_C h
      · exact hx_P h
    have hconn₂ : IsConnectedAvoiding G {x | x ∈ C ∨ x ∈ P.support} w {v} := by
      set q₂ := (Q.dropUntil w hw).mapLe (restrict_le G _)
      refine ⟨v, rfl, q₂, (hQ.1.dropUntil hw).mapLe _, fun x hx hxw hxv => ?_⟩
      rw [support_mapLe] at hx
      have hxQ : x ∈ Q.support := Q.support_dropUntil_subset_support hw hx
      have hxu : x ≠ u := fun e =>
        start_notMem_support_dropUntil hQ.1 hw hwu (e ▸ hx)
      obtain ⟨-, -, hx_P, hx_C, -⟩ := hinner_off x hxQ hxu hxv
      rintro (h | h)
      · exact hx_C h
      · exact hx_P h
    have huP : u ∈ P.support := by
      have hu_sub := hQ.2.1
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hu_sub
      rcases hu_sub with rfl | huB | rfl | hum
      · rw [hm]; simp
      · exfalso
        obtain ⟨z, rfl, q₁, hq₁, hin₁⟩ := hconn₁
        exact hw_no_AB ⟨z, Or.inr huB, q₁, hq₁, hin₁⟩
      · rw [hm]; simp
      · rw [hm]; simp [hum]
    have hvP : v ∈ P.support := by
      have hv_sub := hQ.2.2.1
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hv_sub
      rcases hv_sub with rfl | hvB | rfl | hvm
      · rw [hm]; simp
      · exfalso
        obtain ⟨z, rfl, q₂, hq₂, hin₂⟩ := hconn₂
        exact hw_no_AB ⟨z, Or.inr hvB, q₂, hq₂, hin₂⟩
      · rw [hm]; simp
      · rw [hm]; simp [hvm]
    have huv_ne : u ≠ v := fun e =>
      start_notMem_support_dropUntil hQ.1 hw hwu (e ▸ (Q.dropUntil w hw).end_mem_support)
    obtain ⟨v₀, w₀, hvw₀, honly⟩ := htight w hw_C hw_P hw_no_AB
    have hu₀ := honly u huP hconn₁
    have hv₀ := honly v hvP hconn₂
    have huv_edge : IsListEdge P.support u v := by
      rcases hu₀ with rfl | rfl <;> rcases hv₀ with rfl | rfl
      · exact absurd rfl huv_ne
      · exact hvw₀
      · exact hvw₀.symm
      · exact absurd rfl huv_ne
    exact hnot (IsListEdge.isCycleEdge_side₂ (hm ▸ huv_edge))
  set Q₀ := Q.mapLe (restrict_le G _)
  have hE : ∀ e ∈ Q₀.edges, e ∈ (restrict G (sideSetOf G (a :: m ++ [b]) B)).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ Q.support := by
        have := Q₀.fst_mem_support_of_mem_edges he
        rwa [support_mapLe] at this
      have hy : y ∈ Q.support := by
        have := Q₀.snd_mem_support_of_mem_edges he
        rwa [support_mapLe] at this
      exact ⟨Q₀.adj_of_mem_edges he, hQ_B x hx, hQ_B y hy⟩
  have hQ₀_path : Q₀.IsPath := (hQ.1).mapLe _
  have hsup : (Q₀.transfer (restrict G (sideSetOf G (a :: m ++ [b]) B)) hE).support = Q.support := by
    rw [Walk.support_transfer, support_mapLe]
  refine ⟨Q₀.transfer _ hE, ⟨hQ₀_path.transfer hE, hQ.2.1, hQ.2.2.1, ?_⟩, hsup⟩
  rw [hsup]
  exact hQ.2.2.2

/-- If `P` is tight and `b :: B ++ a :: m` is nodup, a crossing of `b :: B ++ a :: m` in
`restrict G (sideComplOf G (a :: m ++ [b]) A)` gives a crossing in
`restrict G (sideSetOf G (a :: m ++ [b]) B)`. -/
theorem isCrossed_sideSetOf_B_of_sideComplOf {m : List V}
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B)
    (hP : IsTPath G C P) (hm : P.support = a :: m ++ [b])
    (htight : IsTight G C A B P.support)
    (hnd : (b :: B ++ a :: m).Nodup)
    (hcr : IsCrossed (restrict G (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    IsCrossed (restrict G (sideSetOf G (a :: m ++ [b]) B)) (b :: B ++ a :: m) := by
  obtain ⟨u₁, v₁, u₂, v₂, Q, R, hQR⟩ := hcr
  obtain ⟨k₁, L₁, L₂, hrot₁, hc₁, hd₁⟩ := hQR.alternate
  obtain ⟨k₂, M₁, M₂, hrot₂, hc₂, hd₂⟩ := hQR.alternate.comm
  have hnotQ : ¬ PlaneEmbedding.IsCycleEdge (b :: B ++ a :: m) u₁ v₁ :=
    not_isCycleEdge_of_rotate hnd hrot₁ (List.ne_nil_of_mem hc₁) (List.ne_nil_of_mem hd₁)
  have hnotR : ¬ PlaneEmbedding.IsCycleEdge (b :: B ++ a :: m) u₂ v₂ :=
    not_isCycleEdge_of_rotate hnd hrot₂ (List.ne_nil_of_mem hc₂) (List.ne_nil_of_mem hd₂)
  obtain ⟨Q', hQ', hQs⟩ := exists_tPath_sideSetOf_B_of_tight hC hrot hP hm htight hQR.2.1 hnotQ
  obtain ⟨R', hR', hRs⟩ := exists_tPath_sideSetOf_B_of_tight hC hrot hP hm htight hQR.2.2.1 hnotR
  exact ⟨u₁, v₁, u₂, v₂, Q', R', hQR.1, hQ', hR', by rw [hQs, hRs]; exact hQR.2.2.2⟩

/-- **Lifting a crossing from either subinstance of Proposition 5.1.** After the completion loop
produces `(H, P')`, any crossing of the first subinstance `(sideSetOf G (a :: m ++ [b]) A,
a :: A ++ b :: m.reverse)` or of the second subinstance `(sideComplOf G (a :: m ++ [b]) A,
b :: B ++ a :: m)` in `H` lifts via the five cases of Figure 11 (`Setting.cross_of_side`) to a
crossing of `C` in `H`. -/
theorem isCrossed_of_sub_crossed {H : SimpleGraph V} {m : List V}
    (hC : IsCycleList G C) (hrot : C.rotate k = a :: A ++ b :: B) (hA : A ≠ []) (hB : B ≠ [])
    (hle : G ≤ H) {P' : H.Walk a b}
    (hH : ∀ u v, H.Adj u v → G.Adj u v ∨ IsListEdge P'.support u v)
    (hP' : IsTPath H C P') (hm : P'.support = a :: m ++ [b])
    (hind : ∀ u ∈ P'.support, ∀ v ∈ P'.support, H.Adj u v → IsListEdge P'.support u v)
    (hsep : Separates G {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B})
    (hsides : OnBothSidesList G C A B P'.support)
    (htight : IsTight H C A B P'.support)
    (hsub : IsCrossed (restrict H (sideSetOf G (a :: m ++ [b]) A)) (a :: A ++ b :: m.reverse) ∨
      IsCrossed (restrict H (sideComplOf G (a :: m ++ [b]) A)) (b :: B ++ a :: m)) :
    IsCrossed H C := by
  have hS := setting_of_onBothSidesList hC hrot hA hB hle hP' hm hind hsep hsides
  have hbot : ∀ z : V, SimpleGraph.edge z z = (⊥ : SimpleGraph V) := by
    intro z; ext x y; simp
  rcases hsub with hsub₁ | hsub₂
  · have h := hS.cross_of_side (x := a) (y := a) (hS.l_S₁ (by simp)) (hS.l_S₁ (by simp))
      (by rw [hbot, sup_bot_eq]; exact hsub₁)
    rwa [hbot, sup_bot_eq] at h
  · have hrest : restrict H {w | w ∉ a :: m ++ [b]} = restrict G {w | w ∉ a :: m ++ [b]} :=
      hm ▸ restrict_notMem_eq_of_adj_or_mem hle fun u v huv =>
        (hH u v huv).imp_right fun h => ⟨h.mem_left, h.mem_right⟩
    have hcompl_eq : sideComplOf H (a :: m ++ [b]) A = sideComplOf G (a :: m ++ [b]) A := by
      simp only [sideComplOf, hrest]
    have hsideB_eq : sideSetOf H (a :: m ++ [b]) B = sideSetOf G (a :: m ++ [b]) B := by
      simp only [sideSetOf, hrest]
    have hsub₂' : IsCrossed (restrict H (sideSetOf G (a :: m ++ [b]) B)) (b :: B ++ a :: m) := by
      rw [← hsideB_eq]
      rw [← hcompl_eq] at hsub₂
      exact isCrossed_sideSetOf_B_of_sideComplOf (hC.mono hle) hrot hP' hm htight hS.cycK.2.1 hsub₂
    have h := hS.symm.cross_of_side (x := b) (y := b)
      (hS.symm.l_S₁ (by simp)) (hS.symm.l_S₁ (by simp))
      (by rw [hbot, sup_bot_eq, List.reverse_reverse]; exact hsub₂')
    rwa [hbot, sup_bot_eq] at h

end GraphMinor.HP25
