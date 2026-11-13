module

public import GraphMinor.GM08.Defs
public import Mathlib.Combinatorics.Graph.Lattice
import Mathlib.Data.Set.Card

/-!
# Graph Minors VIII, Section 14 (Part 1): Path-Decompositions, $k$-Chains, and (14.1)

This file formalizes the first part of Section 14 of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- Structural lemmas on `GraftPathDecomposition` and `GraphPathIn` (subpaths, separator properties of
  $V(G_i)$ and $Y_i$, cut-point indices along disjoint paths).
- `theorem_14_1`: (14.1) (pages 275–276), establishing properties (i)–(v) of a $k$-chain and its
  $k$ mutually vertex-disjoint paths $P_1, \dots, P_k$ from $Y_0$ to $Y_r$.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph

universe u v

/-! ## Basic properties of `GraftPathDecomposition` -/

/-- In a path-decomposition $D$, for any $h \le j$ in `Fin D.r` and any $i$ with $h \le i \le j$,
$V(G_h) \cap V(G_j) \subseteq V(G_i)$. Moreover, if $h \le i < j$ with $i.1 + 1 < D.r$, then
$V(G_h) \cap V(G_j) \subseteq Y_{i+1}$. -/
theorem GraftPathDecomposition.inter_subset_Y_succ {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {h i j : Fin D.r} (hhi : h ≤ i) (hij : i < j) (hi_succ : i.1 + 1 < D.r) :
    V(D.G h) ∩ V(D.G j) ⊆ D.Y i.succ := by
  let i1 : Fin D.r := ⟨i.1 + 1, hi_succ⟩
  have hi1_le_j : i1 ≤ j := Nat.succ_le_of_lt hij
  have hle_i1 : h ≤ i1 := le_trans hhi (Nat.le_succ i.1)
  intro x hx
  rw [← D.adj_vertex_inter i hi_succ]
  exact ⟨D.vertex_inter_subset h i j hhi (le_of_lt hij) hx,
    D.vertex_inter_subset h i1 j hle_i1 hi1_le_j hx⟩

/-- Every edge $e \in E(X.G)$ belongs to $E(D.G h)$ for a unique $h : \text{Fin } D.r$. -/
theorem GraftPathDecomposition.exists_mem_edgeSet {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {e : β} (he : e ∈ E(X.G)) :
    ∃ h : Fin D.r, e ∈ E(D.G h) := by
  rw [← D.edgeSet_iUnion, mem_iUnion] at he
  exact he

/-- **Graph Minors VIII, (14.1)(i)** (page 276):
for $1 \le i \le r$, there is no edge of $G$ with one end in $\bigcup_{j < i} V(G_j)$, the other in
$\bigcup_{j > i} V(G_j)$, and neither end in $V(G_i)$. -/
theorem GraftPathDecomposition.no_jumping_edge {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    (i : Fin D.r) {e : β} {x y : α} (hl : X.G.IsLink e x y)
    (hx : x ∈ ⋃ (j : Fin D.r) (_ : j < i), V(D.G j))
    (hy : y ∈ ⋃ (j : Fin D.r) (_ : i < j), V(D.G j)) :
    x ∈ V(D.G i) ∨ y ∈ V(D.G i) := by
  simp only [mem_iUnion, exists_prop] at hx hy
  obtain ⟨j₁, hj₁_lt, hxj₁⟩ := hx
  obtain ⟨j₂, hj₂_gt, hyj₂⟩ := hy
  obtain ⟨h, heh⟩ := D.exists_mem_edgeSet hl.edge_mem
  have hl_h : (D.G h).IsLink e x y := ((D.le_G h).isLink_iff heh).mpr hl
  rcases le_or_gt h i with hhi | hih
  · right
    exact D.vertex_inter_subset h i j₂ hhi (le_of_lt hj₂_gt) ⟨hl_h.right_mem, hyj₂⟩
  · left
    exact D.vertex_inter_subset j₁ i h (le_of_lt hj₁_lt) (le_of_lt hih) ⟨hxj₁, hl_h.left_mem⟩

/-- Transition across $i$: if $X.G.\text{IsLink } e\ x\ y$ with $x \in \bigcup_{l \le i} V(G_l)$ and
$y \notin \bigcup_{l \le i} V(G_l)$, and $i.1 + 1 < D.r$, then the edge $e$ belongs to $E(G_m)$ for
some $m > i$ and $x \in Y_{i+1}$. -/
theorem GraftPathDecomposition.left_mem_Y_succ_of_isLink_notMem_le {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {i : Fin D.r} (hi_succ : i.1 + 1 < D.r) {e : β} {x y : α}
    (hl : X.G.IsLink e x y)
    (hx : x ∈ ⋃ (l : Fin D.r) (_ : l ≤ i), V(D.G l))
    (hy : y ∉ ⋃ (l : Fin D.r) (_ : l ≤ i), V(D.G l)) :
    x ∈ D.Y i.succ := by
  simp only [mem_iUnion, exists_prop] at hx hy
  push Not at hy
  obtain ⟨l, hli, hxl⟩ := hx
  obtain ⟨m, hem⟩ := D.exists_mem_edgeSet hl.edge_mem
  have hl_m : (D.G m).IsLink e x y := ((D.le_G m).isLink_iff hem).mpr hl
  have him : i < m := by
    by_contra hle
    exact hy m (not_lt.mp hle) hl_m.right_mem
  exact D.inter_subset_Y_succ hli him hi_succ ⟨hxl, hl_m.left_mem⟩

/-! ## Subpaths and path properties for `GraphPathIn` -/

/-- Every vertex `wp.verts[s]` along a path `wp : GraphPathIn G P u v` belongs to $V(P)$ and $V(G)$. -/
theorem GraphPathIn.getElem_verts_mem {α : Type u} {β : Type v}
    {G P : Graph α β} {u v : α} (wp : GraphPathIn G P u v)
    (s : ℕ) (hs : s < wp.verts.length) :
    wp.verts[s] ∈ V(P) := by
  rw [wp.vertexSet_eq]
  exact List.getElem_mem hs

theorem GraphPathIn.head_mem {α : Type u} {β : Type v}
    {G P : Graph α β} {u v : α} (wp : GraphPathIn G P u v) :
    u ∈ V(P) := by
  have hlen := wp.length_verts
  rw [← wp.head_eq]
  exact wp.getElem_verts_mem 0 (by omega)

theorem GraphPathIn.last_mem {α : Type u} {β : Type v}
    {G P : Graph α β} {u v : α} (wp : GraphPathIn G P u v) :
    v ∈ V(P) := by
  have hlen := wp.length_verts
  rw [← wp.last_eq]
  exact wp.getElem_verts_mem wp.edges.length (by omega)

/-- Discrete intermediate value lemma for `verts` of a path: if $S \subseteq \alpha$ contains
`wp.verts[a]` and does not contain `wp.verts[b]` with $a \le b < \text{wp.verts.length}$, then there
exists $s$ with $a \le s < b$ such that `wp.verts[s] ∈ S` and `wp.verts[s + 1] ∉ S`. -/
theorem GraphPathIn.exists_step_exit {α : Type u} {β : Type v}
    {G P : Graph α β} {u v : α} (wp : GraphPathIn G P u v)
    (S : Set α) {a b : ℕ} (hab : a ≤ b) (hb : b < wp.verts.length)
    (haS : wp.verts[a]'(by omega) ∈ S) (hbS : wp.verts[b]'hb ∉ S) :
    ∃ (s : ℕ) (hs : s < wp.edges.length),
      a ≤ s ∧ s < b ∧ wp.verts[s]'(by have := wp.length_verts; omega) ∈ S ∧
        wp.verts[s + 1]'(by have := wp.length_verts; omega) ∉ S := by
  have hlen := wp.length_verts
  induction b with
  | zero =>
    obtain rfl : a = 0 := Nat.eq_zero_of_le_zero hab
    exact False.elim (hbS haS)
  | succ b ih =>
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact False.elim (hbS haS)
    · have hab' : a ≤ b := Nat.le_of_lt_succ hlt
      by_cases hb1 : wp.verts[b]'(by omega) ∈ S
      · refine ⟨b, by omega, hab', Nat.lt_succ_self b, hb1, hbS⟩
      · obtain ⟨s, hs, has, hsb, hsS, hs1S⟩ := ih hab' (by omega) haS hb1
        exact ⟨s, hs, has, Nat.lt_succ_of_lt hsb, hsS, hs1S⟩

/-- Dual discrete intermediate value lemma: if $S \subseteq \alpha$ does not contain `wp.verts[a]`
and contains `wp.verts[b]` with $a \le b < \text{wp.verts.length}$, then there exists $s$ with
$a \le s < b$ such that `wp.verts[s] ∉ S` and `wp.verts[s + 1] ∈ S`. -/
theorem GraphPathIn.exists_step_enter {α : Type u} {β : Type v}
    {G P : Graph α β} {u v : α} (wp : GraphPathIn G P u v)
    (S : Set α) {a b : ℕ} (hab : a ≤ b) (hb : b < wp.verts.length)
    (haS : wp.verts[a]'(by omega) ∉ S) (hbS : wp.verts[b]'hb ∈ S) :
    ∃ (s : ℕ) (hs : s < wp.edges.length),
      a ≤ s ∧ s < b ∧ wp.verts[s]'(by have := wp.length_verts; omega) ∉ S ∧
        wp.verts[s + 1]'(by have := wp.length_verts; omega) ∈ S := by
  obtain ⟨s, hs, has, hsb, hsS, hs1S⟩ :=
    wp.exists_step_exit Sᶜ hab hb haS (not_not.mpr hbS)
  exact ⟨s, hs, has, hsb, hsS, not_not.mp hs1S⟩

/-- **Graph Minors VIII, (14.1)(ii)** (page 276):
if $1 \le h \le i \le j \le r$, every path of $G$ from $V(G_h)$ to $V(G_j)$ meets $V(G_i)$. -/
theorem GraftPathDecomposition.path_meets_middle {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {h i j : Fin D.r} (hhi : h ≤ i) (hij : i ≤ j)
    {Q : Graph α β} (hQ : IsGraphPathFromTo X.G Q V(D.G h) V(D.G j)) :
    (V(Q) ∩ V(D.G i)).Nonempty := by
  obtain ⟨u, hu, v, hv, ⟨wq⟩⟩ := hQ
  have hlen := wq.length_verts
  let S : Set α := ⋃ (l : Fin D.r) (_ : l ≤ i), V(D.G l)
  have huS : wq.verts[0]'(by omega) ∈ S := by
    rw [wq.head_eq]
    exact mem_biUnion hhi hu
  by_cases hvS : wq.verts[wq.edges.length]'(by omega) ∈ S
  · rw [wq.last_eq] at hvS
    simp only [S, mem_iUnion, exists_prop] at hvS
    obtain ⟨l, hli, hvl⟩ := hvS
    exact ⟨v, wq.last_mem, D.vertex_inter_subset l i j hli hij ⟨hvl, hv⟩⟩
  · obtain ⟨s, hs, _, _, hsS, hs1S⟩ :=
      wq.exists_step_exit S (Nat.zero_le _) (by omega) huS hvS
    have hlG : X.G.IsLink (wq.edges[s]'hs) (wq.verts[s]'(by omega)) (wq.verts[s + 1]'(by omega)) :=
      (wq.isLink_step s hs).mono wq.le_G
    have he_mem_G : wq.edges[s]'hs ∈ E(X.G) := hlG.edge_mem
    rw [← D.edgeSet_iUnion, mem_iUnion] at he_mem_G
    obtain ⟨m, hem⟩ := he_mem_G
    have hlGm : (D.G m).IsLink (wq.edges[s]'hs)
        (wq.verts[s]'(by omega)) (wq.verts[s + 1]'(by omega)) :=
      ((D.le_G m).isLink_iff hem).mpr hlG
    have him : i < m := by
      by_contra hle
      exact hs1S (mem_biUnion (not_lt.mp hle) hlGm.right_mem)
    simp only [S, mem_iUnion, exists_prop] at hsS
    obtain ⟨l, hli, hxl⟩ := hsS
    exact ⟨wq.verts[s]'(by omega), wq.getElem_verts_mem s (by omega),
      D.vertex_inter_subset l i m hli (le_of_lt him) ⟨hxl, hlGm.left_mem⟩⟩

/-- Every path of $G$ from $Y_0$ to $Y_r$ meets $Y_i$ for every $0 \le i \le r$. -/
theorem GraftPathDecomposition.path_meets_Y {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {Q : Graph α β}
    (hQ : IsGraphPathFromTo X.G Q (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)))
    (i : Fin (D.r + 1)) :
    (V(Q) ∩ D.Y i).Nonempty := by
  obtain ⟨u, hu, v, hv, ⟨wq⟩⟩ := hQ
  have hlen := wq.length_verts
  have hhr := D.hr
  rcases eq_or_ne i.1 0 with hi0 | hi_pos
  · have hi_eq : i = ⟨0, Nat.zero_lt_succ D.r⟩ := Fin.ext hi0
    rw [hi_eq]
    exact ⟨u, wq.head_mem, hu⟩
  · rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with hi_r | hi_lt
    · have hi_eq : i = Fin.last D.r := Fin.ext hi_r
      rw [hi_eq]
      exact ⟨v, wq.last_mem, hv⟩
    · let i' : Fin D.r := ⟨i.1 - 1, by omega⟩
      have hi'_succ_lt : i'.1 + 1 < D.r := by dsimp [i']; omega
      have hi'_succ_eq : i'.succ = i := Fin.ext (by dsimp [i']; omega)
      rw [← hi'_succ_eq]
      let S : Set α := ⋃ (l : Fin D.r) (_ : l ≤ i'), V(D.G l)
      have h0 : (⟨0, D.hr⟩ : Fin D.r) ≤ i' := Nat.zero_le _
      have hu_G0 : u ∈ V(D.G ⟨0, D.hr⟩) :=
        D.Y_subset ⟨0, D.hr⟩ (Or.inl hu)
      have huS : wq.verts[0]'(by omega) ∈ S := by
        rw [wq.head_eq]
        exact mem_biUnion h0 hu_G0
      by_cases hvS : wq.verts[wq.edges.length]'(by omega) ∈ S
      · rw [wq.last_eq] at hvS
        simp only [S, mem_iUnion, exists_prop] at hvS
        obtain ⟨l, hli', hvl⟩ := hvS
        let lastG : Fin D.r := ⟨D.r - 1, by omega⟩
        have hv_last : v ∈ V(D.G lastG) := by
          have hlast_eq : lastG.succ = Fin.last D.r := Fin.ext (by dsimp [lastG]; omega)
          exact D.Y_subset lastG (Or.inr (hlast_eq ▸ hv))
        have hi'_lt_last : i' < lastG := by
          change i.1 - 1 < D.r - 1
          omega
        exact ⟨v, wq.last_mem,
          D.inter_subset_Y_succ hli' hi'_lt_last hi'_succ_lt ⟨hvl, hv_last⟩⟩
      · obtain ⟨s, hs, _, _, hsS, hs1S⟩ :=
          wq.exists_step_exit S (Nat.zero_le _) (by omega) huS hvS
        have hlG : X.G.IsLink (wq.edges[s]'hs) (wq.verts[s]'(by omega))
            (wq.verts[s + 1]'(by omega)) :=
          (wq.isLink_step s hs).mono wq.le_G
        exact ⟨wq.verts[s]'(by omega), wq.getElem_verts_mem s (by omega),
          D.left_mem_Y_succ_of_isLink_notMem_le hi'_succ_lt hlG hsS hs1S⟩

/-- Pigeonhole principle on finite sets: if $A_0, \dots, A_{k-1}$ are $k$ pairwise disjoint
nonempty subsets of a finite set $Y$ with $Y.\text{ncard} = k$, then each $A_p$ has
$(A_p).\text{ncard} = 1$ and $\bigcup_p A_p = Y$. -/
theorem ncard_eq_one_and_iUnion_eq_of_disjoint_nonempty {α : Type u} {k : ℕ}
    {Y : Set α} (hY_fin : Y.Finite) (hY_card : Y.ncard = k)
    {A : Fin k → Set α} (hA_sub : ∀ p, A p ⊆ Y)
    (hA_nonempty : ∀ p, (A p).Nonempty)
    (hA_disj : ∀ p q, p ≠ q → Disjoint (A p) (A q)) :
    (∀ p : Fin k, (A p).ncard = 1) ∧ (⋃ p : Fin k, A p) = Y := by
  classical
  have hA_fin : ∀ p, (A p).Finite := fun p => hY_fin.subset (hA_sub p)
  have hA_pos : ∀ p, 1 ≤ (A p).ncard := fun p =>
    (ncard_pos (hA_fin p)).mpr (hA_nonempty p)
  let F : Fin k → Finset α := fun p => (hA_fin p).toFinset
  let FY : Finset α := hY_fin.toFinset
  have hF_card : ∀ p, (F p).card = (A p).ncard := fun p =>
    (ncard_eq_toFinset_card (A p) (hA_fin p)).symm
  have hFY_card : FY.card = k := by
    rw [← ncard_eq_toFinset_card Y hY_fin, hY_card]
  have hF_disj : Pairwise (fun p q => Disjoint (F p) (F q)) := by
    intro p q hpq
    rw [Finset.disjoint_left]
    intro x hxp hxq
    rw [Finite.mem_toFinset] at hxp hxq
    exact (hA_disj p q hpq).notMem_of_mem_left hxp hxq
  have hbiUnion_sub : Finset.univ.biUnion F ⊆ FY := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨p, _, hxp⟩ := hx
    rw [Finite.mem_toFinset] at hxp ⊢
    exact hA_sub p hxp
  have hsum_le : (∑ p : Fin k, (F p).card) ≤ k := by
    calc (∑ p : Fin k, (F p).card)
      _ = (Finset.univ.biUnion F).card :=
          (Finset.card_biUnion (fun p _ q _ hpq => hF_disj hpq)).symm
      _ ≤ FY.card := Finset.card_le_card hbiUnion_sub
      _ = k := hFY_card
  have hk_le_sum : k ≤ ∑ p : Fin k, (F p).card := by
    calc k = ∑ _p : Fin k, 1 := by simp
      _ ≤ ∑ p : Fin k, (F p).card := Finset.sum_le_sum (fun p _ => by rw [hF_card]; exact hA_pos p)
  have hsum_eq : (∑ p : Fin k, (F p).card) = ∑ _p : Fin k, 1 := by
    have : ∑ _p : Fin k, 1 = k := by simp
    omega
  have hall_one : ∀ p : Fin k, (F p).card = 1 := by
    by_contra! hne
    obtain ⟨p₀, hp₀⟩ := hne
    have hp₀_gt : 1 < (F p₀).card := by
      have := hA_pos p₀
      rw [← hF_card p₀] at this
      omega
    have hlt : (∑ _p : Fin k, 1) < ∑ p : Fin k, (F p).card :=
      Finset.sum_lt_sum (fun p _ => by rw [hF_card]; exact hA_pos p)
        ⟨p₀, Finset.mem_univ p₀, hp₀_gt⟩
    omega
  refine ⟨fun p => by rw [← hF_card p, hall_one p], ?_⟩
  have hcard_eq : (Finset.univ.biUnion F).card = FY.card := by
    rw [Finset.card_biUnion (fun p _ q _ hpq => hF_disj hpq), hFY_card]
    have : ∑ _p : Fin k, 1 = k := by simp
    omega
  have hfinset_eq : Finset.univ.biUnion F = FY :=
    Finset.eq_of_subset_of_card_le hbiUnion_sub (ge_of_eq hcard_eq)
  ext x
  have hiff := Finset.ext_iff.mp hfinset_eq x
  simpa [F, FY, Finset.mem_biUnion] using hiff

/-- **Graph Minors VIII, (14.1)(iii)** (page 276):
for $0 \le i \le r$ and $1 \le p \le k$, $|Y_i \cap V(P_p)| = 1$ (and $\bigcup_p (Y_i \cap V(P_p)) = Y_i$). -/
theorem GraftPathDecomposition.ncard_Y_inter_path_eq_one {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (hY_card : ∀ i : Fin (D.r + 1), (D.Y i).ncard = k)
    {P : Fin k → Graph α β}
    (hP_path : ∀ p : Fin k,
      IsGraphPathFromTo X.G (P p) (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)))
    (hP_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q))
    (i : Fin (D.r + 1)) :
    (∀ p : Fin k, (D.Y i ∩ V(P p)).ncard = 1) ∧
    (⋃ p : Fin k, (D.Y i ∩ V(P p))) = D.Y i := by
  have hhr := D.hr
  have hYi_sub : D.Y i ⊆ V(X.G) := by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with hi_r | hi_lt
    · have hi_eq : i = Fin.last D.r := Fin.ext hi_r
      rw [hi_eq]
      let lastG : Fin D.r := ⟨D.r - 1, by omega⟩
      have hlast_eq : lastG.succ = Fin.last D.r := Fin.ext (by dsimp [lastG]; omega)
      rw [← hlast_eq]
      exact (subset_union_right.trans (D.Y_subset lastG)).trans (D.le_G lastG).vertexSet_mono
    · let i' : Fin D.r := ⟨i.1, hi_lt⟩
      have hi'_eq : i'.castSucc = i := Fin.ext rfl
      rw [← hi'_eq]
      exact (subset_union_left.trans (D.Y_subset i')).trans (D.le_G i').vertexSet_mono
  have hYi_fin : (D.Y i).Finite := X.finite_G.1.subset hYi_sub
  exact ncard_eq_one_and_iUnion_eq_of_disjoint_nonempty hYi_fin (hY_card i)
    (fun _ => inter_subset_left)
    (fun p => by
      rw [inter_comm]
      exact D.path_meets_Y (hP_path p) i)
    (fun p q hpq => (hP_disj p q hpq).mono inter_subset_right inter_subset_right)

/-- Subpath construction: given `wp : GraphPathIn G P u v` and indices $a \le b \le \text{wp.edges.length}$,
if a subgraph $Q \le P$ has vertex set $\{\text{wp.verts}[s] \mid a \le s \le b\}$ and edge set
$\{\text{wp.edges}[s] \mid a \le s < b\}$, then `IsGraphPath G Q` holds (specifically, there is a
`GraphPathIn G Q (wp.verts[a]) (wp.verts[b])`). -/
theorem GraphPathIn.subpath_isGraphPath {α : Type u} {β : Type v}
    {G P Q : Graph α β} {u v : α} (wp : GraphPathIn G P u v)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ wp.edges.length)
    (hQ_le : Q ≤ P)
    (hQV : V(Q) = {x | ∃ s : ℕ, a ≤ s ∧ s ≤ b ∧ ∃ hs : s < wp.verts.length, wp.verts[s]'hs = x})
    (hQE : E(Q) = {e | ∃ s : ℕ, a ≤ s ∧ s < b ∧ ∃ hs : s < wp.edges.length, wp.edges[s]'hs = e}) :
    Nonempty (GraphPathIn G Q (wp.verts[a]'(by have := wp.length_verts; omega))
      (wp.verts[b]'(by have := wp.length_verts; omega))) := by
  have hlen := wp.length_verts
  let subVerts : List α := (List.range (b - a + 1)).attach.map
    (fun ⟨d, hd⟩ => wp.verts[a + d]'(by rw [List.mem_range] at hd; omega))
  let subEdges : List β := (List.range (b - a)).attach.map
    (fun ⟨d, hd⟩ => wp.edges[a + d]'(by rw [List.mem_range] at hd; omega))
  have hlen_V : subVerts.length = b - a + 1 := by simp [subVerts]
  have hlen_E : subEdges.length = b - a := by simp [subEdges]
  have hget_V : ∀ (d : ℕ) (hd : d < b - a + 1),
      subVerts[d]'(by omega) = wp.verts[a + d]'(by omega) := by
    intro d hd
    simp [subVerts]
  have hget_E : ∀ (d : ℕ) (hd : d < b - a),
      subEdges[d]'(by omega) = wp.edges[a + d]'(by omega) := by
    intro d hd
    simp [subEdges]
  have hnodup : subVerts.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩ heq
    have h₁ : subVerts[d₁]'hd₁ = wp.verts[a + d₁]'(by omega) := hget_V d₁ (by omega)
    have h₂ : subVerts[d₂]'hd₂ = wp.verts[a + d₂]'(by omega) := hget_V d₂ (by omega)
    have heq' : wp.verts[a + d₁]'(by omega) = wp.verts[a + d₂]'(by omega) :=
      h₁.symm.trans (heq.trans h₂)
    have hinj := (List.nodup_iff_injective_getElem.mp wp.nodup_verts)
      (a₁ := ⟨a + d₁, by omega⟩) (a₂ := ⟨a + d₂, by omega⟩) heq'
    have hinj' : a + d₁ = a + d₂ := Fin.ext_iff.mp hinj
    have hd12 : d₁ = d₂ := by omega
    exact Fin.ext hd12
  refine ⟨{
    verts := subVerts
    edges := subEdges
    le_G := hQ_le.trans wp.le_G
    length_verts := by omega
    nodup_verts := hnodup
    head_eq := by
      rw [hget_V 0 (by omega)]
      congr 1
    last_eq := by
      have hd : subEdges.length < b - a + 1 := by omega
      rw [hget_V subEdges.length hd]
      congr 1
      omega
    vertexSet_eq := by
      rw [hQV]
      ext x
      simp only [mem_ofPred_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨s, has, hsb, hs_lt, rfl⟩
        refine ⟨s - a, by omega, ?_⟩
        rw [hget_V (s - a) (by omega)]
        congr 1
        omega
      · rintro ⟨d, hd, rfl⟩
        rw [hget_V d (by omega)]
        exact ⟨a + d, by omega, by omega, by omega, rfl⟩
    edgeSet_eq := by
      rw [hQE]
      ext e
      simp only [mem_ofPred_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨s, has, hsb, hs_lt, rfl⟩
        refine ⟨s - a, by omega, ?_⟩
        rw [hget_E (s - a) (by omega)]
        congr 1
        omega
      · rintro ⟨d, hd, rfl⟩
        rw [hget_E d (by omega)]
        exact ⟨a + d, by omega, by omega, by omega, rfl⟩
    isLink_step := by
      intro d hd
      have hd' : d < b - a := by omega
      rw [hget_E d hd', hget_V d (by omega), hget_V (d + 1) (by omega)]
      have hlP := wp.isLink_step (a + d) (by omega)
      have heQ : wp.edges[a + d]'(by omega) ∈ E(Q) := by
        rw [hQE]
        exact ⟨a + d, by omega, by omega, by omega, rfl⟩
      have hlink := (hQ_le.isLink_iff heQ).mpr hlP
      convert hlink using 2
  }⟩

/-- Key cut-index decomposition of a path $P_p$ in a $k$-chain: for each $p : \text{Fin } k$ and
`wp : GraphPathIn X.G (P p) u v` (with $u \in Y_0$, $v \in Y_r$), there exists a monotone sequence
$c : \text{Fin }(D.r + 1) \to \mathbb{N}$ with $c(0) = 0$ and $c(r) = \text{wp.edges.length}$ such
that:
1. For every $i : \text{Fin }(D.r + 1)$, $\text{wp.verts}[c(i)]$ is the unique vertex in
   $D.Y\ i \cap V(P\ p)$.
2. For every $i : \text{Fin } D.r$ and $s < \text{wp.verts.length}$,
   $\text{wp.verts}[s] \in V(D.G\ i) \iff c(i.\text{castSucc}) \le s \wedge s \le c(i.\text{succ})$.
3. For every $i : \text{Fin } D.r$ and $s < \text{wp.edges.length}$,
   $\text{wp.edges}[s] \in E(D.G\ i) \iff c(i.\text{castSucc}) \le s \wedge s < c(i.\text{succ})$. -/
theorem GraftPathDecomposition.exists_cut_indices_of_kChain {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (hY_card : ∀ i : Fin (D.r + 1), (D.Y i).ncard = k)
    {P : Fin k → Graph α β}
    (hP_path : ∀ p : Fin k,
      IsGraphPathFromTo X.G (P p) (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)))
    (hP_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q))
    (p : Fin k) {u v : α} (hu : u ∈ D.Y ⟨0, Nat.zero_lt_succ D.r⟩)
    (hv : v ∈ D.Y (Fin.last D.r)) (wp : GraphPathIn X.G (P p) u v) :
    ∃ (c : Fin (D.r + 1) → ℕ) (hc_lt : ∀ i, c i < wp.verts.length),
      c ⟨0, Nat.zero_lt_succ D.r⟩ = 0 ∧
      c (Fin.last D.r) = wp.edges.length ∧
      Monotone c ∧
      (∀ i : Fin (D.r + 1), D.Y i ∩ V(P p) = {wp.verts[c i]'(hc_lt i)}) ∧
      (∀ (i : Fin D.r) (s : ℕ) (hs : s < wp.verts.length),
        wp.verts[s]'hs ∈ V(D.G i) ↔ c i.castSucc ≤ s ∧ s ≤ c i.succ) ∧
      (∀ (i : Fin D.r) (s : ℕ) (hs : s < wp.edges.length),
        wp.edges[s]'hs ∈ E(D.G i) ↔ c i.castSucc ≤ s ∧ s < c i.succ) := by
  classical
  have hlen := wp.length_verts
  have hhr := D.hr
  have hcard1 : ∀ i : Fin (D.r + 1), (D.Y i ∩ V(P p)).ncard = 1 :=
    fun i => (D.ncard_Y_inter_path_eq_one hY_card hP_path hP_disj i).1 p
  have hex_unique_idx : ∀ i : Fin (D.r + 1),
      ∃ s : ℕ, ∃ hs : s < wp.verts.length,
        D.Y i ∩ V(P p) = {wp.verts[s]'hs} := by
    intro i
    obtain ⟨y, hy⟩ := ncard_eq_one.mp (hcard1 i)
    have hy_mem : y ∈ D.Y i ∩ V(P p) := hy ▸ mem_singleton y
    have hy_verts : y ∈ wp.verts := by
      have h := hy_mem.2
      rwa [wp.vertexSet_eq, mem_ofPred_eq] at h
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hy_verts
    exact ⟨s, hs, hy⟩
  choose c hc_lt hc_eq using hex_unique_idx
  have hc_iff : ∀ (i : Fin (D.r + 1)) (s : ℕ) (hs : s < wp.verts.length),
      wp.verts[s]'hs ∈ D.Y i ↔ s = c i := by
    intro i s hs
    constructor
    · intro hmem
      have hmem_inter : wp.verts[s]'hs ∈ D.Y i ∩ V(P p) :=
        ⟨hmem, wp.getElem_verts_mem s hs⟩
      rw [hc_eq i, mem_singleton_iff] at hmem_inter
      have hinj := (List.nodup_iff_injective_getElem.mp wp.nodup_verts)
        (a₁ := ⟨s, hs⟩) (a₂ := ⟨c i, hc_lt i⟩) hmem_inter
      exact congrArg Fin.val hinj
    · rintro rfl
      have hmem_inter : wp.verts[c i]'(hc_lt i) ∈ D.Y i ∩ V(P p) := by
        rw [hc_eq i]
        exact mem_singleton _
      exact hmem_inter.1
  have hc0 : c ⟨0, Nat.zero_lt_succ D.r⟩ = 0 := by
    symm
    apply (hc_iff ⟨0, Nat.zero_lt_succ D.r⟩ 0 (by omega)).mp
    rw [wp.head_eq]
    exact hu
  have hcr : c (Fin.last D.r) = wp.edges.length := by
    symm
    apply (hc_iff (Fin.last D.r) wp.edges.length (by omega)).mp
    rw [wp.last_eq]
    exact hv
  -- Prefix/suffix separation across every internal cut j (with j.1 + 1 < D.r):
  have hsep_left : ∀ (j : Fin D.r) (hj : j.1 + 1 < D.r) (s : ℕ) (hs : s < wp.verts.length),
      s ≤ c j.succ → wp.verts[s]'hs ∈ ⋃ (l : Fin D.r) (_ : l ≤ j), V(D.G l) := by
    intro j hj s hs hsl
    let S : Set α := ⋃ (l : Fin D.r) (_ : l ≤ j), V(D.G l)
    by_contra hnot
    have h0S : wp.verts[0]'(by omega) ∈ S := by
      rw [wp.head_eq]
      exact mem_biUnion (Nat.zero_le j) (D.Y_subset ⟨0, D.hr⟩ (Or.inl hu))
    obtain ⟨t, ht, _, hts, htS, ht1S⟩ :=
      wp.exists_step_exit S (Nat.zero_le s) hs h0S hnot
    have hlG : X.G.IsLink (wp.edges[t]'ht) (wp.verts[t]'(by omega))
        (wp.verts[t + 1]'(by omega)) :=
      (wp.isLink_step t ht).mono wp.le_G
    have ht_Y : wp.verts[t]'(by omega) ∈ D.Y j.succ :=
      D.left_mem_Y_succ_of_isLink_notMem_le hj hlG htS ht1S
    have ht_eq : t = c j.succ := (hc_iff j.succ t (by omega)).mp ht_Y
    omega
  have hsep_right : ∀ (j : Fin D.r) (hj : j.1 + 1 < D.r) (s : ℕ) (hs : s < wp.verts.length),
      c j.succ ≤ s → wp.verts[s]'hs ∈ ⋃ (l : Fin D.r) (_ : j < l), V(D.G l) := by
    intro j hj s hs hsr
    let S : Set α := ⋃ (l : Fin D.r) (_ : l ≤ j), V(D.G l)
    -- First show for s > c j.succ, wp.verts[s] ∉ S:
    rcases eq_or_lt_of_le hsr with rfl | hlt
    · -- At s = c j.succ, wp.verts[c j.succ] ∈ Y j.succ ⊆ V(G (j + 1))
      have hmem_Y : wp.verts[c j.succ]'hs ∈ D.Y j.succ :=
        (hc_iff j.succ (c j.succ) hs).mpr rfl
      rw [← D.adj_vertex_inter j hj] at hmem_Y
      exact mem_biUnion (Nat.lt_succ_self j.1) hmem_Y.2
    · have hnotS : wp.verts[s]'hs ∉ S := by
        intro hsS
        have hlast_notS : wp.verts[wp.edges.length]'(by omega) ∉ S := by
          intro hlastS
          simp only [S, mem_iUnion, exists_prop] at hlastS
          obtain ⟨l, hlj, hvl⟩ := hlastS
          let lastG : Fin D.r := ⟨D.r - 1, by omega⟩
          have hv_last : wp.verts[wp.edges.length]'(by omega) ∈ V(D.G lastG) := by
            rw [wp.last_eq]
            have hlast_eq : lastG.succ = Fin.last D.r := Fin.ext (by dsimp [lastG]; omega)
            exact D.Y_subset lastG (Or.inr (hlast_eq ▸ hv))
          have hj_lt_last : j < lastG := by change j.1 < D.r - 1; omega
          have hv_Yj : wp.verts[wp.edges.length]'(by omega) ∈ D.Y j.succ :=
            D.inter_subset_Y_succ hlj hj_lt_last hj ⟨hvl, hv_last⟩
          have h_eq : wp.edges.length = c j.succ :=
            (hc_iff j.succ wp.edges.length (by omega)).mp hv_Yj
          omega
        obtain ⟨t, ht, hst, _, htS, ht1S⟩ :=
          wp.exists_step_exit S (by omega) (by omega) hsS hlast_notS
        have hlG : X.G.IsLink (wp.edges[t]'ht) (wp.verts[t]'(by omega))
            (wp.verts[t + 1]'(by omega)) :=
          (wp.isLink_step t ht).mono wp.le_G
        have ht_Y : wp.verts[t]'(by omega) ∈ D.Y j.succ :=
          D.left_mem_Y_succ_of_isLink_notMem_le hj hlG htS ht1S
        have ht_eq : t = c j.succ := (hc_iff j.succ t (by omega)).mp ht_Y
        omega
      have hx_G : wp.verts[s]'hs ∈ V(X.G) :=
        wp.le_G.vertexSet_mono (wp.getElem_verts_mem s hs)
      rw [← D.vertexSet_iUnion, mem_iUnion] at hx_G
      obtain ⟨m, hxm⟩ := hx_G
      have hjm : j < m := by
        by_contra hle
        exact hnotS (mem_biUnion (not_lt.mp hle) hxm)
      exact mem_biUnion hjm hxm
  -- From hsep_left and hsep_right, characterize V(G i) and E(G i) along wp:
  have hnot_gt_of_lt : ∀ (j : Fin D.r) (hj : j.1 + 1 < D.r) (s : ℕ) (hs : s < wp.verts.length),
      s < c j.succ → wp.verts[s]'hs ∉ ⋃ (l : Fin D.r) (_ : j < l), V(D.G l) := by
    intro j hj s hs hsl hmem_gt
    have hmem_le := hsep_left j hj s hs (le_of_lt hsl)
    simp only [mem_iUnion, exists_prop] at hmem_le hmem_gt
    obtain ⟨l₁, hl₁, hxl₁⟩ := hmem_le
    obtain ⟨l₂, hl₂, hxl₂⟩ := hmem_gt
    have hx_Y : wp.verts[s]'hs ∈ D.Y j.succ :=
      D.inter_subset_Y_succ hl₁ hl₂ hj ⟨hxl₁, hxl₂⟩
    have hs_eq := (hc_iff j.succ s hs).mp hx_Y
    omega
  have hnot_le_of_gt : ∀ (j : Fin D.r) (hj : j.1 + 1 < D.r) (s : ℕ) (hs : s < wp.verts.length),
      c j.succ < s → wp.verts[s]'hs ∉ ⋃ (l : Fin D.r) (_ : l ≤ j), V(D.G l) := by
    intro j hj s hs hsr hmem_le
    have hmem_gt := hsep_right j hj s hs (le_of_lt hsr)
    simp only [mem_iUnion, exists_prop] at hmem_le hmem_gt
    obtain ⟨l₁, hl₁, hxl₁⟩ := hmem_le
    obtain ⟨l₂, hl₂, hxl₂⟩ := hmem_gt
    have hx_Y : wp.verts[s]'hs ∈ D.Y j.succ :=
      D.inter_subset_Y_succ hl₁ hl₂ hj ⟨hxl₁, hxl₂⟩
    have hs_eq := (hc_iff j.succ s hs).mp hx_Y
    omega
  have hc_step : ∀ i : Fin D.r, c i.castSucc ≤ c i.succ := by
    intro i
    rcases eq_or_ne i.1 0 with hi0 | hi_pos
    · have hi_eq : i.castSucc = ⟨0, Nat.zero_lt_succ D.r⟩ := Fin.ext hi0
      rw [hi_eq, hc0]
      exact Nat.zero_le _
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.2) with hi_r | hi_lt
      · have hi_eq : i.succ = Fin.last D.r := Fin.ext hi_r
        rw [hi_eq, hcr]
        have := hc_lt i.castSucc
        omega
      · by_contra! hgt
        let j : Fin D.r := ⟨i.1 - 1, by omega⟩
        have hj_lt : j.1 + 1 < D.r := by dsimp [j]; omega
        have hj_succ : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
        have hmem_Y : wp.verts[c i.castSucc]'(hc_lt i.castSucc) ∈ D.Y i.castSucc :=
          (hc_iff i.castSucc (c i.castSucc) (hc_lt i.castSucc)).mpr rfl
        have hmem_Gi : wp.verts[c i.castSucc]'(hc_lt i.castSucc) ∈ V(D.G i) :=
          D.Y_subset i (Or.inl hmem_Y)
        have hnot := hnot_le_of_gt i hi_lt (c i.castSucc) (hc_lt i.castSucc) hgt
        exact hnot (mem_biUnion (le_refl i) hmem_Gi)
  have hc_mono : Monotone c := by
    intro a b hab
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
    have haux : ∀ (d : ℕ) (a : Fin (D.r + 1)) (h : a.1 + d < D.r + 1),
        c a ≤ c ⟨a.1 + d, h⟩ := by
      intro d
      induction d with
      | zero =>
        intro a h
        have : (⟨a.1 + 0, h⟩ : Fin (D.r + 1)) = a := Fin.ext (Nat.add_zero a.1)
        rw [this]
      | succ d ih =>
        intro a h
        let mid : Fin D.r := ⟨a.1 + d, by omega⟩
        have hmid_cast : mid.castSucc = ⟨a.1 + d, by omega⟩ := rfl
        have hmid_succ : mid.succ = ⟨a.1 + (d + 1), h⟩ := rfl
        exact le_trans (ih a (by omega)) (hmid_succ ▸ hmid_cast ▸ hc_step mid)
    have hb_eq : b = ⟨a.1 + d, by omega⟩ := Fin.ext hd
    rw [hb_eq]
    exact haux d a (by omega)
  have hverts_iff : ∀ (i : Fin D.r) (s : ℕ) (hs : s < wp.verts.length),
      wp.verts[s]'hs ∈ V(D.G i) ↔ c i.castSucc ≤ s ∧ s ≤ c i.succ := by
    intro i s hs
    constructor
    · intro hmem
      refine ⟨?_, ?_⟩
      · rcases eq_or_ne i.1 0 with hi0 | hi_pos
        · have hi_eq : i.castSucc = ⟨0, Nat.zero_lt_succ D.r⟩ := Fin.ext hi0
          rw [hi_eq, hc0]
          exact Nat.zero_le s
        · let j : Fin D.r := ⟨i.1 - 1, by omega⟩
          have hj_lt : j.1 + 1 < D.r := by dsimp [j]; omega
          have hj_succ : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
          have hji : j < i := by change i.1 - 1 < i.1; omega
          rw [← hj_succ]
          by_contra! hslt
          exact hnot_gt_of_lt j hj_lt s hs hslt (mem_biUnion hji hmem)
      · rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.2) with hi_r | hi_lt
        · have hi_eq : i.succ = Fin.last D.r := Fin.ext hi_r
          rw [hi_eq, hcr]
          omega
        · by_contra! hsgt
          exact hnot_le_of_gt i hi_lt s hs hsgt (mem_biUnion (le_refl i) hmem)
    · rintro ⟨hs_ge, hs_le⟩
      have hle_right : wp.verts[s]'hs ∈ ⋃ (l : Fin D.r) (_ : l ≤ i), V(D.G l) := by
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt i.2) with hi_r | hi_lt
        · have hx_G : wp.verts[s]'hs ∈ V(X.G) :=
            wp.le_G.vertexSet_mono (wp.getElem_verts_mem s hs)
          rw [← D.vertexSet_iUnion, mem_iUnion] at hx_G
          obtain ⟨l, hxl⟩ := hx_G
          have hli : l ≤ i := by
            change l.1 ≤ i.1
            have := l.2
            omega
          exact mem_biUnion hli hxl
        · exact hsep_left i hi_lt s hs hs_le
      have hge_left : wp.verts[s]'hs ∈ ⋃ (l : Fin D.r) (_ : i ≤ l), V(D.G l) := by
        rcases eq_or_ne i.1 0 with hi0 | hi_pos
        · have hx_G : wp.verts[s]'hs ∈ V(X.G) :=
            wp.le_G.vertexSet_mono (wp.getElem_verts_mem s hs)
          rw [← D.vertexSet_iUnion, mem_iUnion] at hx_G
          obtain ⟨l, hxl⟩ := hx_G
          have hil : i ≤ l := by
            change i.1 ≤ l.1
            omega
          exact mem_biUnion hil hxl
        · let j : Fin D.r := ⟨i.1 - 1, by omega⟩
          have hj_lt : j.1 + 1 < D.r := by dsimp [j]; omega
          have hj_succ : j.succ = i.castSucc := Fin.ext (by dsimp [j]; omega)
          rw [← hj_succ] at hs_ge
          have h := hsep_right j hj_lt s hs hs_ge
          simp only [mem_iUnion, exists_prop] at h ⊢
          obtain ⟨l, hjl, hxl⟩ := h
          exact ⟨l, by change i.1 ≤ l.1; have : i.1 - 1 < l.1 := hjl; omega, hxl⟩
      simp only [mem_iUnion, exists_prop] at hle_right hge_left
      obtain ⟨l₁, hl₁, hxl₁⟩ := hle_right
      obtain ⟨l₂, hl₂, hxl₂⟩ := hge_left
      exact D.vertex_inter_subset l₁ i l₂ hl₁ hl₂ ⟨hxl₁, hxl₂⟩
  have hedges_iff : ∀ (i : Fin D.r) (s : ℕ) (hs : s < wp.edges.length),
      wp.edges[s]'hs ∈ E(D.G i) ↔ c i.castSucc ≤ s ∧ s < c i.succ := by
    intro i s hs
    have hlG : X.G.IsLink (wp.edges[s]'hs) (wp.verts[s]'(by omega))
        (wp.verts[s + 1]'(by omega)) :=
      (wp.isLink_step s hs).mono wp.le_G
    constructor
    · intro he_mem
      have hl_i : (D.G i).IsLink (wp.edges[s]'hs) (wp.verts[s]'(by omega))
          (wp.verts[s + 1]'(by omega)) :=
        ((D.le_G i).isLink_iff he_mem).mpr hlG
      have hs1 := (hverts_iff i s (by omega)).mp hl_i.left_mem
      have hs2 := (hverts_iff i (s + 1) (by omega)).mp hl_i.right_mem
      omega
    · rintro ⟨hs_ge, hs_lt⟩
      obtain ⟨m, hem⟩ := D.exists_mem_edgeSet hlG.edge_mem
      have hl_m : (D.G m).IsLink (wp.edges[s]'hs) (wp.verts[s]'(by omega))
          (wp.verts[s + 1]'(by omega)) :=
        ((D.le_G m).isLink_iff hem).mpr hlG
      have hms1 := (hverts_iff m s (by omega)).mp hl_m.left_mem
      have hms2 := (hverts_iff m (s + 1) (by omega)).mp hl_m.right_mem
      have hmi : m = i := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle_idx : m.succ ≤ i.castSucc := Nat.succ_le_of_lt hlt
          have hcm : c m.succ ≤ c i.castSucc := hc_mono hle_idx
          omega
        · have hle_idx : i.succ ≤ m.castSucc := Nat.succ_le_of_lt hgt
          have hcm : c i.succ ≤ c m.castSucc := hc_mono hle_idx
          omega
      exact hmi ▸ hem
  exact ⟨c, hc_lt, hc0, hcr, hc_mono, hc_eq, hverts_iff, hedges_iff⟩

/-- **Graph Minors VIII, (14.1)** (pages 275–276):
"(14.1) *Let $(G, T)$ be a $k$-chain, and let $(G_i, Y_{i-1}, Y_i)$ ($1 \le i \le r$) be a
path-decomposition with $|Y_i| = k$ ($0 \le i \le r$). Let $P_1, \dots, P_k$ be mutually disjoint
paths of $G$ from $Y_0$ to $Y_r$. Then*
(i) *for $1 \le i \le r$, there is no edge of $G$ with one end in $\bigcup_{j < i} V(G_j)$, the
other in $\bigcup_{j > i} V(G_j)$, and neither end in $V(G_i)$*
(ii) *if $1 \le h \le i \le j \le r$, every path of $G$ from $V(G_h)$ to $V(G_j)$ meets $V(G_i)$*
(iii) *for $0 \le i \le r$ and $1 \le p \le k$, $|Y_i \cap V(P_p)| = 1$*
(iv) *for $1 \le i \le r$ and $1 \le p \le k$ the intersection of $P_p$ and $G_i$ is a path*
(v) *for $1 \le p \le k$, $P_p$ is obtained from the paths $P_p \cap G_i$ ($i = 1, 2, \dots, r$)
by concatenating them in order.*" -/
theorem theorem_14_1_proof {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (hY_card : ∀ i : Fin (D.r + 1), (D.Y i).ncard = k)
    {P : Fin k → Graph α β}
    (hP_path : ∀ p : Fin k,
      IsGraphPathFromTo X.G (P p) (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)))
    (hP_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q)) :
    (∀ (i : Fin D.r) (e : β) (x y : α),
      X.G.IsLink e x y →
      x ∈ (⋃ (j : Fin D.r) (_ : j < i), V(D.G j)) →
      y ∈ (⋃ (j : Fin D.r) (_ : i < j), V(D.G j)) →
      x ∈ V(D.G i) ∨ y ∈ V(D.G i)) ∧
    (∀ (h i j : Fin D.r), h ≤ i → i ≤ j →
      ∀ Q : Graph α β, IsGraphPathFromTo X.G Q V(D.G h) V(D.G j) →
        (V(Q) ∩ V(D.G i)).Nonempty) ∧
    (∀ (i : Fin (D.r + 1)) (p : Fin k), (D.Y i ∩ V(P p)).ncard = 1) ∧
    (∀ (i : Fin D.r) (p : Fin k), IsGraphPath X.G (P p ⊓ D.G i)) ∧
    (∀ p : Fin k, IsConcatenatedPath X.G (P p) (fun i : Fin D.r => P p ⊓ D.G i)) := by
  refine ⟨fun i e x y hl hx hy => D.no_jumping_edge i hl hx hy,
    fun h i j hhi hij Q hQ => D.path_meets_middle hhi hij hQ,
    fun i p => (D.ncard_Y_inter_path_eq_one hY_card hP_path hP_disj i).1 p, ?_, ?_⟩
  · intro i p
    obtain ⟨u, hu, v, hv, ⟨wp⟩⟩ := hP_path p
    obtain ⟨c, hc_lt, _, hcr, hc_mono, _, hverts_iff, hedges_iff⟩ :=
      D.exists_cut_indices_of_kChain hY_card hP_path hP_disj p hu hv wp
    have hab : c i.castSucc ≤ c i.succ := hc_mono (Fin.castSucc_le_succ i)
    have hb : c i.succ ≤ wp.edges.length := by
      rw [← hcr]
      exact hc_mono (Fin.le_last i.succ)
    have hcomp : (P p).Compatible (D.G i) := Compatible.of_le_le wp.le_G (D.le_G i)
    have hQV : V(P p ⊓ D.G i) =
        {x | ∃ s : ℕ, c i.castSucc ≤ s ∧ s ≤ c i.succ ∧
          ∃ hs : s < wp.verts.length, wp.verts[s]'hs = x} := by
      ext x
      rw [vertexSet_inf, mem_inter_iff, wp.vertexSet_eq, mem_ofPred_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, hxG⟩
        obtain ⟨h1, h2⟩ := (hverts_iff i s hs).mp hxG
        exact ⟨s, h1, h2, hs, rfl⟩
      · rintro ⟨s, h1, h2, hs, rfl⟩
        exact ⟨⟨s, hs, rfl⟩, (hverts_iff i s hs).mpr ⟨h1, h2⟩⟩
    have hQE : E(P p ⊓ D.G i) =
        {e | ∃ s : ℕ, c i.castSucc ≤ s ∧ s < c i.succ ∧
          ∃ hs : s < wp.edges.length, wp.edges[s]'hs = e} := by
      ext e
      rw [hcomp.edgeSet_inf, mem_inter_iff, wp.edgeSet_eq, mem_ofPred_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, heG⟩
        obtain ⟨h1, h2⟩ := (hedges_iff i s hs).mp heG
        exact ⟨s, h1, h2, hs, rfl⟩
      · rintro ⟨s, h1, h2, hs, rfl⟩
        exact ⟨⟨s, hs, rfl⟩, (hedges_iff i s hs).mpr ⟨h1, h2⟩⟩
    exact ⟨_, _, wp.subpath_isGraphPath hab hb inf_le_left hQV hQE⟩
  · intro p
    obtain ⟨u, hu, v, hv, ⟨wp⟩⟩ := hP_path p
    obtain ⟨c, _, hc0, hcr, hc_mono, _, hverts_iff, hedges_iff⟩ :=
      D.exists_cut_indices_of_kChain hY_card hP_path hP_disj p hu hv wp
    refine ⟨u, v, wp, c, hc0, hcr, hc_mono, fun i => ⟨?_, ?_, inf_le_left⟩⟩
    · ext x
      rw [vertexSet_inf, mem_inter_iff, wp.vertexSet_eq, mem_ofPred_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, hxG⟩
        obtain ⟨h1, h2⟩ := (hverts_iff i s hs).mp hxG
        exact ⟨s, h1, h2, hs, rfl⟩
      · rintro ⟨s, h1, h2, hs, rfl⟩
        exact ⟨⟨s, hs, rfl⟩, (hverts_iff i s hs).mpr ⟨h1, h2⟩⟩
    · have hcomp : (P p).Compatible (D.G i) := Compatible.of_le_le wp.le_G (D.le_G i)
      ext e
      rw [hcomp.edgeSet_inf, mem_inter_iff, wp.edgeSet_eq, mem_ofPred_eq, List.mem_iff_getElem]
      constructor
      · rintro ⟨⟨s, hs, rfl⟩, heG⟩
        obtain ⟨h1, h2⟩ := (hedges_iff i s hs).mp heG
        exact ⟨s, h1, h2, hs, rfl⟩
      · rintro ⟨s, h1, h2, hs, rfl⟩
        exact ⟨⟨s, hs, rfl⟩, (hedges_iff i s hs).mpr ⟨h1, h2⟩⟩

end GraphMinor.GM08
