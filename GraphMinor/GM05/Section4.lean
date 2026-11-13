module

public import GraphMinor.GM05.Section4Aux
import GraphMinor.GM05.Quoted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graph Minors V, Section 4 (Part 3): (4.4), (4.5), and (4.6)

This file formalizes (4.4), (4.5), and (4.6) of Section 4 of N. Robertson and P. D. Seymour,
*Graph Minors. V. Excluding a planar graph*, J. Combin. Theory Ser. B **41** (1986), 92–114
(pages 98–100):

- `theorem_4_4`: if `G ∈ 𝓕_θ` has an `(m, n)`-web with `m = p 2^{p θ²}` and `n = p + q + m`, then
  it has a `(p, q)`-subweb with a spider.
- `theorem_4_5`: for `0 ≤ k < θ₁`, if `G ∈ 𝓕_θ` has a `(φ_k, ψ_k)`-web with `k` edge-disjoint
  spiders, then it has a `(φ_{k+1}, ψ_{k+1})`-web with `k + 1` edge-disjoint spiders.
- `theorem_4_6`: if `G ∈ 𝓕_θ`, then `G` has no `(θ₂, θ₂)`-web.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set GM01

universe u

variable {V : Type u}

/-! ### Subwebs and edge-disjointness of spiders -/

/-- Restricting an `(m, n)`-web `(A, B)` along embeddings `embI : Fin p ↪ Fin m` and
`embJ : Fin q ↪ Fin n` gives a `(p, q)`-web. -/
lemma IsWeb.subweb {G : (⊤ : SimpleGraph V).Subgraph} {m n p q : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} (hweb : IsWeb G A B)
    (embI : Fin p ↪ Fin m) (embJ : Fin q ↪ Fin n) :
    IsWeb G (fun i ↦ A (embI i)) (fun j ↦ B (embJ j)) where
  isIn_left i := hweb.isIn_left (embI i)
  isIn_right j := hweb.isIn_right (embJ j)
  disjoint_left _ _ hne := hweb.disjoint_left (embI.injective.ne hne)
  disjoint_right _ _ hne := hweb.disjoint_right (embJ.injective.ne hne)
  meets i j := hweb.meets (embI i) (embJ j)
  edge_disjoint i j := hweb.edge_disjoint (embI i) (embJ j)

/-- A spider `C` of an `(m, n)`-web `(A, B)` is also a spider of any subweb. -/
lemma IsSpider.subweb {G : (⊤ : SimpleGraph V).Subgraph} {m n p q : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} {C : (⊤ : SimpleGraph V).Subgraph}
    (hsp : IsSpider G A B C) (embI : Fin p ↪ Fin m) (embJ : Fin q ↪ Fin n) :
    IsSpider G (fun i ↦ A (embI i)) (fun j ↦ B (embJ j)) C where
  le := hsp.le
  connected := hsp.connected
  edge_disjoint j := hsp.edge_disjoint (embJ j)
  unique_leaf i := hsp.unique_leaf (embI i)

/-- Every spider `C` of an `(m, n)`-web `(A, B)` is edge-disjoint from `A_i` for every `i`
(since `C` has only one vertex in common with `A_i`). -/
lemma IsSpider.edge_disjoint_left {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} {C : (⊤ : SimpleGraph V).Subgraph}
    (hsp : IsSpider G A B C) (i : Fin m) :
    Disjoint C.edgeSet (A i).edgeSet := by
  rw [Set.disjoint_left]
  intro e heC heA
  induction e with | h x y =>
  have hadjC : C.Adj x y := heC
  have hadjA : (A i).toSubgraph.Adj x y := heA
  obtain ⟨v, hv_inter, _⟩ := hsp.unique_leaf i
  have hx : x ∈ C.verts ∩ (A i).verts := ⟨C.edge_vert hadjC, (A i).toSubgraph.edge_vert hadjA⟩
  have hy : y ∈ C.verts ∩ (A i).verts :=
    ⟨C.edge_vert hadjC.symm, (A i).toSubgraph.edge_vert hadjA.symm⟩
  rw [hv_inter, Set.mem_singleton_iff] at hx hy
  exact hadjC.ne (hx.trans hy.symm)

/-! ### External neighborhood and BFS layers in `webAuxGraph` -/

/-- For `X ⊆ V(L)`, `extNeigh L X` (`N(X)` in the paper, page 98) is the set of vertices of `L`
not in `X` that are adjacent in `L` to a vertex of `X`. -/
def extNeigh {α : Type*} (L : SimpleGraph α) (X : Set α) : Set α :=
  {y | y ∉ X ∧ ∃ x ∈ X, L.Adj x y}

/-- Any walk in `L` from `a ∈ X` to `b ∉ X` contains a vertex of `extNeigh L X`. -/
private lemma exists_mem_extNeigh_of_walk {α : Type*} {L : SimpleGraph α} {X : Set α}
    {a b : α} (ha : a ∈ X) (hb : b ∉ X) (w : L.Walk a b) :
    ∃ y ∈ w.support, y ∈ extNeigh L X := by
  induction w with
  | nil => exact absurd ha hb
  | @cons a c b hadj rest ih =>
    by_cases hc : c ∈ X
    · obtain ⟨y, hy_supp, hy_ext⟩ := ih hc hb
      exact ⟨y, List.mem_cons_of_mem a hy_supp, hy_ext⟩
    · exact ⟨c, by simp, hc, a, ha, hadj⟩

/-- `IsWalkConnectedIn L a X` means `a ∈ X` and every vertex `x ∈ X` can be joined to `a` by a walk
in `L` whose vertices all lie in `X`. -/
def IsWalkConnectedIn {α : Type*} (L : SimpleGraph α) (a : α) (X : Set α) : Prop :=
  a ∈ X ∧ ∀ x ∈ X, ∃ w : L.Walk x a, ∀ z ∈ w.support, z ∈ X

/-- Cumulative BFS balls `Z_k = Y_1 ∪ ⋯ ∪ Y_{k+1}` in `L` starting from `a`. -/
def bfsCumul {α : Type*} (L : SimpleGraph α) (a : α) : ℕ → Set α
  | 0 => {a}
  | k + 1 => bfsCumul L a k ∪ extNeigh L (bfsCumul L a k)

/-- BFS layers `Y_{k+1}` in `L` starting from `a` (0-indexed: `bfsLayer L a 0 = {a}`). -/
def bfsLayer {α : Type*} (L : SimpleGraph α) (a : α) : ℕ → Set α
  | 0 => {a}
  | k + 1 => extNeigh L (bfsCumul L a k)

private lemma bfsCumul_mono {α : Type*} (L : SimpleGraph α) (a : α) {k₁ k₂ : ℕ}
    (hle : k₁ ≤ k₂) : bfsCumul L a k₁ ⊆ bfsCumul L a k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => exact Subset.rfl
  | succ d ih => exact ih.trans Set.subset_union_left

private lemma bfsLayer_subset_bfsCumul {α : Type*} (L : SimpleGraph α) (a : α) (k : ℕ) :
    bfsLayer L a k ⊆ bfsCumul L a k := by
  cases k with
  | zero => exact Subset.rfl
  | succ k => exact Set.subset_union_right

private lemma bfsLayer_pairwise_disjoint {α : Type*} (L : SimpleGraph α) (a : α) :
    Pairwise fun k₁ k₂ ↦ Disjoint (bfsLayer L a k₁) (bfsLayer L a k₂) := by
  have hlt : ∀ {k₁ k₂ : ℕ}, k₁ < k₂ → Disjoint (bfsLayer L a k₁) (bfsLayer L a k₂) := by
    intro k₁ k₂ h
    cases k₂ with
    | zero => omega
    | succ k₂ =>
      have hk : k₁ ≤ k₂ := by omega
      rw [Set.disjoint_left]
      intro x hx₁ hx₂
      exact hx₂.1 (bfsCumul_mono L a hk (bfsLayer_subset_bfsCumul L a k₁ hx₁))
  intro k₁ k₂ hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hlt h
  · exact (hlt h).symm

private lemma isWalkConnectedIn_bfsCumul {α : Type*} (L : SimpleGraph α) (a : α) (k : ℕ) :
    IsWalkConnectedIn L a (bfsCumul L a k) := by
  induction k with
  | zero =>
    refine ⟨Set.mem_singleton a, fun x hx ↦ ?_⟩
    rw [bfsCumul, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨.nil, by simp [bfsCumul]⟩
  | succ k ih =>
    refine ⟨Or.inl ih.1, fun x hx ↦ ?_⟩
    rcases hx with hx_old | ⟨_, u, hu, hadj⟩
    · obtain ⟨w, hw⟩ := ih.2 x hx_old
      exact ⟨w, fun z hz ↦ Or.inl (hw z hz)⟩
    · obtain ⟨w, hw⟩ := ih.2 u hu
      refine ⟨.cons hadj.symm w, fun z hz ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inr ⟨‹_›, u, hu, hadj⟩
      · exact Or.inl (hw z hz)

/-! ### Case 1 and Case 2 of (4.4) -/

/-- Case 1 of the proof of Graph Minors V, (4.4) (pages 98–99):
if `|N(V(L'))| < p` for every connected subgraph `L'` of `L`, then the BFS layers `Y_1, …, Y_{m'}`
yield `m' = 2^{p θ²}` disjoint subgraphs `D_k` of `G` separating `A₁` and `A₂`, each with at most
`p - 1` components, contradicting (4.3). -/
theorem theorem_4_4_case_1 {G : (⊤ : SimpleGraph V).Subgraph}
    {θ p q : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (hp : 1 ≤ p)
    {A : Fin (p * 2 ^ (p * θ ^ 2)) → GM01.Path V}
    {B : Fin (p + q + p * 2 ^ (p * θ ^ 2)) → GM01.Path V}
    (hweb : VertexWeb G A B)
    (hcase1 : ∀ (a : Fin (p * 2 ^ (p * θ ^ 2))) (X : Set (Fin (p * 2 ^ (p * θ ^ 2)))),
      IsWalkConnectedIn (webAuxGraph A B) a X → (extNeigh (webAuxGraph A B) X).ncard < p) :
    False := by
  classical
  let m' : ℕ := 2 ^ (p * θ ^ 2)
  let m : ℕ := p * m'
  let n : ℕ := p + q + m
  have hm'_ge : 2 ≤ m' := by
    dsimp [m']
    have h1 : 1 ≤ p * θ ^ 2 := by
      have hθ1 : 1 ≤ θ ^ 2 := by
        have := Nat.mul_le_mul hθ hθ
        rw [sq]
        omega
      have := Nat.mul_le_mul hp hθ1
      omega
    exact Nat.le_self_pow (by omega) 2
  have hm_ge : 2 ≤ m := by
    dsimp [m]
    calc
      2 = 1 * 2 := by ring
      _ ≤ p * m' := Nat.mul_le_mul hp hm'_ge
  have hn_pos : 0 < n := by
    dsimp [n]
    omega
  let L := webAuxGraph A B
  have hm_pos : 0 < p * 2 ^ (p * θ ^ 2) := by
    change 0 < m
    omega
  have hL_conn : L.Connected := webAuxGraph_connected hweb hm_pos hn_pos
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hi₀_ne_i₁ : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    dsimp [i₀, i₁] at this
    omega
  have hp2 : 2 ≤ p := by
    obtain ⟨w⟩ := hL_conn.preconnected i₀ i₁
    obtain ⟨y, _, hy_ext⟩ := exists_mem_extNeigh_of_walk (Set.mem_singleton i₀)
      (by simpa [Set.mem_singleton_iff] using hi₀_ne_i₁.symm) w
    have hpos : 0 < (extNeigh (webAuxGraph A B) {i₀}).ncard :=
      Set.ncard_pos (Set.toFinite _) |>.2 ⟨y, hy_ext⟩
    have hlt := hcase1 i₀ {i₀} (isWalkConnectedIn_bfsCumul L i₀ 0)
    omega
  have hlayer_le : ∀ k : ℕ, (bfsLayer L i₀ k).ncard ≤ p - 1 := by
    intro k
    cases k with
    | zero =>
      rw [bfsLayer, Set.ncard_singleton]
      omega
    | succ k =>
      have hlt : (bfsLayer L i₀ (k + 1)).ncard < p :=
        hcase1 i₀ (bfsCumul L i₀ k) (isWalkConnectedIn_bfsCumul L i₀ k)
      omega
  have hcumul_le : ∀ k : ℕ, (bfsCumul L i₀ k).ncard ≤ (k + 1) * (p - 1) := by
    intro k
    induction k with
    | zero =>
      rw [bfsCumul, Set.ncard_singleton]
      omega
    | succ k ih =>
      have hunion : (bfsCumul L i₀ (k + 1)).ncard ≤
          (bfsCumul L i₀ k).ncard + (bfsLayer L i₀ (k + 1)).ncard :=
        Set.ncard_union_le _ _
      have hlay := hlayer_le (k + 1)
      calc
        (bfsCumul L i₀ (k + 1)).ncard ≤ (k + 1) * (p - 1) + (p - 1) := by omega
        _ = (k + 1 + 1) * (p - 1) := by ring
  have hcumul_lt_m : (bfsCumul L i₀ (m' - 2)).ncard < m := by
    have hle := hcumul_le (m' - 2)
    have h1 : m' - 2 + 1 = m' - 1 := by omega
    rw [h1] at hle
    have h2 : (m' - 1) * (p - 1) < p * m' := by
      calc
        (m' - 1) * (p - 1) ≤ (m' - 1) * p := Nat.mul_le_mul_left (m' - 1) (by omega)
        _ < m' * p := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        _ = p * m' := mul_comm _ _
    exact lt_of_le_of_lt hle h2
  have hex_outside : ∃ i_star : Fin m, i_star ∉ bfsCumul L i₀ (m' - 2) := by
    by_contra! hall
    have heq_univ : bfsCumul L i₀ (m' - 2) = Set.univ := Set.eq_univ_of_forall hall
    rw [heq_univ, Set.ncard_univ, Nat.card_fin] at hcumul_lt_m
    exact Nat.lt_irrefl m hcumul_lt_m
  obtain ⟨i_star, hi_star_not⟩ := hex_outside
  let G' := webSubgraph A B
  have hG'_le : G' ≤ G := webSubgraph_le hweb
  have hG'_fin : G'.verts.Finite := hG_fin.subset hG'_le.1
  have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
  have hAi_sub : ∀ i : Fin m, (A i).verts ⊆ G'.verts := fun i ↦
    (le_sup_of_le_left (le_iSup (fun s ↦ (A s).toSubgraph) i)).1
  let D : Fin m' → (⊤ : SimpleGraph V).Subgraph := fun k ↦
    ⨆ r ∈ bfsLayer L i₀ k.1, (A r).toSubgraph
  have hD_le : ∀ k : Fin m', D k ≤ G' := fun k ↦
    le_sup_of_le_left (iSup₂_le fun r _ ↦ le_iSup (fun s ↦ (A s).toSubgraph) r)
  have hD_disj : Pairwise fun k₁ k₂ : Fin m' ↦ Disjoint (D k₁).verts (D k₂).verts := by
    intro k₁ k₂ hne
    have hlay_disj := bfsLayer_pairwise_disjoint L i₀ (Fin.val_ne_of_ne hne)
    rw [Set.disjoint_left]
    intro v hv₁ hv₂
    simp only [D, Subgraph.verts_iSup, Set.mem_iUnion] at hv₁ hv₂
    obtain ⟨r₁, hr₁, hvAr₁⟩ := hv₁
    obtain ⟨r₂, hr₂, hvAr₂⟩ := hv₂
    have hr_ne : r₁ ≠ r₂ := fun h ↦ Set.disjoint_left.1 hlay_disj hr₁ (h ▸ hr₂)
    exact Set.disjoint_left.1 (hweb.disjoint_left hr_ne) hvAr₁ hvAr₂
  have hD_comp : ∀ k : Fin m', numComponents (D k) ≤ p - 1 := fun k ↦
    (numComponents_biSup_path_le A (bfsLayer L i₀ k.1)).trans (hlayer_le k.1)
  have hex_paths : ∃ P : Fin n → GM01.Path V,
      IsDisjointPathFamily G' (A i₀).verts (A i_star).verts P := by
    have hB_le : ∀ j : Fin n, (B j).toSubgraph ≤ G' := fun j ↦
      le_sup_of_le_right (le_iSup (fun s ↦ (B s).toSubgraph) j)
    have hsub : ∀ j : Fin n, ∃ P : GM01.Path V,
        P.toSubgraph ≤ (B j).toSubgraph ∧ P.first ∈ (A i₀).verts ∧ P.last ∈ (A i_star).verts := by
      intro j
      obtain ⟨P, hP, _, _⟩ := exists_minimal_path_from_to (B j).connected_toSubgraph.preconnected
        (by rw [Set.inter_comm]; exact hweb.meets i₀ j)
        (by rw [Set.inter_comm]; exact hweb.meets i_star j)
      exact ⟨P, hP.1, hP.2.1, hP.2.2⟩
    choose P hPB hPfirst hPlast using hsub
    refine ⟨P, ⟨fun j ↦ ⟨(hPB j).trans (hB_le j), hPfirst j, hPlast j⟩, fun j₁ j₂ hne ↦ ?_⟩⟩
    exact Disjoint.mono (hPB j₁).1 (hPB j₂).1 (hweb.disjoint_right hne)
  have hD_sep : ∀ k : Fin m', Separates G' (D k).verts (A i₀).verts (A i_star).verts := by
    intro k Q ⟨hQG', hQfirst, hQlast⟩ havoid
    obtain ⟨w, hw⟩ := exists_walk_webAuxGraph_of_path hweb hQG' hQfirst hQlast
    have hex_r : ∃ r ∈ w.support, r ∈ bfsLayer L i₀ k.1 := by
      rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
      · refine ⟨i₀, Walk.start_mem_support w, ?_⟩
        rw [hk0, bfsLayer]
        exact Set.mem_singleton i₀
      · have hk_eq : k.1 = (k.1 - 1) + 1 := by omega
        have hi₀_mem : i₀ ∈ bfsCumul L i₀ (k.1 - 1) :=
          (isWalkConnectedIn_bfsCumul L i₀ (k.1 - 1)).1
        have hi_star_not' : i_star ∉ bfsCumul L i₀ (k.1 - 1) := fun h ↦
          hi_star_not (bfsCumul_mono L i₀ (by omega) h)
        obtain ⟨r, hr_supp, hr_ext⟩ := exists_mem_extNeigh_of_walk hi₀_mem hi_star_not' w
        refine ⟨r, hr_supp, ?_⟩
        rw [hk_eq, bfsLayer]
        exact hr_ext
    obtain ⟨r, hr_supp, hr_lay⟩ := hex_r
    obtain ⟨v, hvAr, hvQ⟩ := hw r hr_supp
    have hvD : v ∈ (D k).verts := by
      simp only [D, Subgraph.verts_iSup, Set.mem_iUnion]
      exact ⟨r, hr_lay, hvAr⟩
    exact Set.disjoint_left.1 havoid hvQ hvD
  rcases theorem_4_3_simple hθ heven (by omega) hG'_fin hG'_mem (A i₀).verts (A i_star).verts
      (hAi_sub i₀) (hAi_sub i_star) D hD_le hD_disj hD_comp hex_paths hD_sep with hlt1 | hlt2
  · exact theorem_4_4_arith_left hp hlt1
  · exact theorem_4_4_arith_right hθ heven hp2 hlt2

/-- Case 2 of the proof of Graph Minors V, (4.4) (page 99):
if `|N(V(L'))| ≥ p` for some connected subgraph `L'` of `L`, a spanning tree of `L'` together with
connecting subpaths `P_i` (`i ∈ I`) and `Q_e` (`e ∈ E'`) forms a spider `C` for a `(p, q)`-subweb.
-/
theorem spider_support_of_large_boundary {G : (⊤ : SimpleGraph V).Subgraph}
    {p q m : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin (p + q + m) → GM01.Path V}
    (hweb : VertexWeb G A B)
    {a₀ : Fin m} {X : Set (Fin m)}
    (hX_conn : IsWalkConnectedIn (webAuxGraph A B) a₀ X)
    (hcase2 : p ≤ (extNeigh (webAuxGraph A B) X).ncard) :
    ∃ (embI : Fin p ↪ Fin m) (embJ : Fin q ↪ Fin (p + q + m))
      (C : (⊤ : SimpleGraph V).Subgraph),
      C ≤ G ∧ C.Connected ∧
      (∀ i : Fin p, ∃ v, C.verts ∩ (A (embI i)).verts = {v} ∧ IsLeafOf C v) ∧
      C ≤ (⨆ i, (A i).toSubgraph) ⊔
        (⨆ j ∉ Set.range embJ, (B j).toSubgraph) := by
  classical
  let L := webAuxGraph A B
  let n := p + q + m
  have hext_fin : (extNeigh L X).Finite := Set.toFinite _
  have hp_le_card : p ≤ hext_fin.toFinset.card := by
    rwa [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  obtain ⟨I, hI_sub, hI_card⟩ := Finset.exists_subset_card_eq hp_le_card
  let eI : Fin p ≃ I := (Finset.equivFinOfCardEq hI_card).symm
  let embI : Fin p ↪ Fin m :=
    eI.toEmbedding.trans (Function.Embedding.subtype _)
  have hembI_ext : ∀ r : Fin p, embI r ∈ extNeigh L X := fun r ↦
    hext_fin.mem_toFinset.1 (hI_sub (eI r).2)
  have hPI_ex : ∀ r : Fin p, ∃ (h : Fin m) (j : Fin n) (P : GM01.Path V),
      h ∈ X ∧ IsDirectBPath A B j (embI r) h P := by
    intro r
    obtain ⟨_, h, hhX, hadj⟩ := hembI_ext r
    obtain ⟨_, j, P, hP⟩ := hadj.symm
    exact ⟨h, j, P, hhX, hP⟩
  choose hI jI PI hhI_X hPI using hPI_ex
  have hex_walk : ∀ (x : Fin m), x ∈ X →
      ∃ l : ℕ, ∃ w : L.Walk x a₀, w.length = l ∧ ∀ z ∈ w.support, z ∈ X := by
    intro x hx
    obtain ⟨w, hw⟩ := hX_conn.2 x hx
    exact ⟨w.length, w, rfl, hw⟩
  let distX : Fin m → ℕ := fun x ↦
    if hx : x ∈ X then Nat.find (hex_walk x hx) else 0
  have hQX_ex : ∀ x : ↥(X \ {a₀}),
      ∃ (y : Fin m) (j : Fin n) (Q : GM01.Path V),
        y ∈ X ∧ distX y < distX x.1 ∧ IsDirectBPath A B j x.1 y Q := by
    rintro ⟨x, hxX, hxa₀⟩
    rw [Set.mem_singleton_iff] at hxa₀
    obtain ⟨w, hw_len, hw_supp⟩ := Nat.find_spec (hex_walk x hxX)
    cases w with
    | nil => exact absurd rfl hxa₀
    | @cons _ y _ hadj rest =>
      have hyX : y ∈ X := hw_supp y (by simp)
      have hdist_y : distX y < distX x := by
        dsimp [distX]
        simp only [hyX, hxX, ↓reduceDIte, ← hw_len, Walk.length_cons]
        have hle : Nat.find (hex_walk y hyX) ≤ rest.length :=
          Nat.find_le ⟨rest, rfl, fun z hz ↦ hw_supp z (List.mem_cons_of_mem x hz)⟩
        omega
      obtain ⟨_, j, Q, hQ⟩ := hadj
      exact ⟨y, j, Q, hyX, hdist_y, hQ⟩
  choose parent jX QX hparent_X hparent_dist hQX using hQX_ex
  let C₀ : (⊤ : SimpleGraph V).Subgraph :=
    (⨆ x ∈ X, (A x).toSubgraph) ⊔ (⨆ x : ↥(X \ {a₀}), (QX x).toSubgraph)
  let C : (⊤ : SimpleGraph V).Subgraph :=
    (⨆ r : Fin p, (PI r).toSubgraph) ⊔ C₀
  have hC_le : C ≤ G := by
    refine sup_le (iSup_le fun r ↦ (hPI r).1.trans (hweb.isIn_right (jI r))) ?_
    exact sup_le (iSup₂_le fun x _ ↦ hweb.isIn_left x)
      (iSup_le fun x ↦ (hQX x).1.trans (hweb.isIn_right (jX x)))
  have hC_conn : C.Connected := by
    let v₀ : V := (A a₀).first
    have ha₀_le : (A a₀).toSubgraph ≤ C :=
      le_sup_of_le_right (le_sup_of_le_left (le_biSup (fun x ↦ (A x).toSubgraph) hX_conn.1))
    have hv₀_C : v₀ ∈ C.verts := ha₀_le.1 (A a₀).first_mem_verts
    have hreach_X : ∀ (d : ℕ) (x : Fin m), x ∈ X → distX x ≤ d →
        ∀ u ∈ (A x).verts, ∃ w : (⊤ : SimpleGraph V).Walk v₀ u, w.toSubgraph ≤ C := by
      intro d
      induction d with
      | zero =>
        intro x hxX hd0 u hu
        have hxa₀ : x = a₀ := by
          dsimp [distX] at hd0
          simp only [hxX, ↓reduceDIte, Nat.le_zero] at hd0
          obtain ⟨w, hw_len, _⟩ := Nat.find_spec (hex_walk x hxX)
          exact Walk.eq_of_length_eq_zero (hw_len.trans hd0)
        subst hxa₀
        obtain ⟨w, hw⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph (A x).toSubgraph).1
          (A x).connected_toSubgraph).2 (A x).first_mem_verts hu
        exact ⟨w, hw.trans ha₀_le⟩
      | succ d ih =>
        intro x hxX hd u hu
        by_cases hxa₀ : x = a₀
        · subst hxa₀
          obtain ⟨w, hw⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph (A x).toSubgraph).1
            (A x).connected_toSubgraph).2 (A x).first_mem_verts hu
          exact ⟨w, hw.trans ha₀_le⟩
        · let x' : ↥(X \ {a₀}) := ⟨x, hxX, hxa₀⟩
          have hdist_p : distX (parent x') ≤ d := by
            have hlt : distX (parent x') < distX x := hparent_dist x'
            omega
          obtain ⟨w₁, hw₁⟩ := ih (parent x') (hparent_X x') hdist_p
            (QX x').last (hQX x').2.2.1
          have hQX_le : (QX x').toSubgraph ≤ C :=
            le_sup_of_le_right (le_sup_of_le_right (le_iSup (fun s ↦ (QX s).toSubgraph) x'))
          obtain ⟨w₂, hw₂⟩ :=
            ((Subgraph.connected_iff_forall_exists_walk_subgraph (QX x').toSubgraph).1
              (QX x').connected_toSubgraph).2 (QX x').last_mem_verts (QX x').first_mem_verts
          have hAx_le : (A x).toSubgraph ≤ C :=
            le_sup_of_le_right (le_sup_of_le_left (le_biSup (fun s ↦ (A s).toSubgraph) hxX))
          obtain ⟨w₃, hw₃⟩ :=
            ((Subgraph.connected_iff_forall_exists_walk_subgraph (A x).toSubgraph).1
              (A x).connected_toSubgraph).2 (hQX x').2.1 hu
          refine ⟨(w₁.append w₂).append w₃, ?_⟩
          rw [Walk.toSubgraph_append, Walk.toSubgraph_append]
          exact sup_le (sup_le hw₁ (hw₂.trans hQX_le)) (hw₃.trans hAx_le)
    have hreach_all : ∀ u ∈ C.verts, ∃ w : (⊤ : SimpleGraph V).Walk v₀ u, w.toSubgraph ≤ C := by
      intro u hu
      simp only [C, C₀, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union,
        Set.mem_iUnion] at hu
      rcases hu with ⟨r, huPI⟩ | ⟨x, hxX, huAx⟩ | ⟨x, huQX⟩
      · obtain ⟨w₁, hw₁⟩ := hreach_X (distX (hI r)) (hI r) (hhI_X r) le_rfl
          (PI r).last (hPI r).2.2.1
        have hPI_le : (PI r).toSubgraph ≤ C :=
          le_sup_of_le_left (le_iSup (fun s ↦ (PI s).toSubgraph) r)
        obtain ⟨w₂, hw₂⟩ :=
          ((Subgraph.connected_iff_forall_exists_walk_subgraph (PI r).toSubgraph).1
            (PI r).connected_toSubgraph).2 (PI r).last_mem_verts huPI
        refine ⟨w₁.append w₂, ?_⟩
        rw [Walk.toSubgraph_append]
        exact sup_le hw₁ (hw₂.trans hPI_le)
      · exact hreach_X (distX x) x hxX le_rfl u huAx
      · obtain ⟨w₁, hw₁⟩ := hreach_X (distX (parent x)) (parent x) (hparent_X x) le_rfl
          (QX x).last (hQX x).2.2.1
        have hQX_le : (QX x).toSubgraph ≤ C :=
          le_sup_of_le_right (le_sup_of_le_right (le_iSup (fun s ↦ (QX s).toSubgraph) x))
        obtain ⟨w₂, hw₂⟩ :=
          ((Subgraph.connected_iff_forall_exists_walk_subgraph (QX x).toSubgraph).1
            (QX x).connected_toSubgraph).2 (QX x).last_mem_verts huQX
        refine ⟨w₁.append w₂, ?_⟩
        rw [Walk.toSubgraph_append]
        exact sup_le hw₁ (hw₂.trans hQX_le)
    rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
    refine ⟨⟨v₀, hv₀_C⟩, fun {u₁ u₂} hu₁ hu₂ ↦ ?_⟩
    obtain ⟨w₁, hw₁⟩ := hreach_all u₁ hu₁
    obtain ⟨w₂, hw₂⟩ := hreach_all u₂ hu₂
    refine ⟨w₁.reverse.append w₂, ?_⟩
    rw [Walk.toSubgraph_append, Walk.toSubgraph_reverse]
    exact sup_le hw₁ hw₂
  have hC_leaf : ∀ r : Fin p,
      ∃ v : V, C.verts ∩ (A (embI r)).verts = {v} ∧ IsLeafOf C v := by
    intro r
    let R : (⊤ : SimpleGraph V).Subgraph :=
      (⨆ r' ≠ r, (PI r').toSubgraph) ⊔ C₀
    have hC_eq : C = (PI r).toSubgraph ⊔ R := by
      ext x y
      · simp only [C, R, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro (⟨r', hx⟩ | hxC₀)
          · by_cases hr' : r' = r
            · subst hr'
              exact Or.inl hx
            · exact Or.inr (Or.inl ⟨r', hr', hx⟩)
          · exact Or.inr (Or.inr hxC₀)
        · rintro (hx | ⟨r', _, hx⟩ | hxC₀)
          · exact Or.inl ⟨r, hx⟩
          · exact Or.inl ⟨r', hx⟩
          · exact Or.inr hxC₀
      · simp only [C, R, Subgraph.sup_adj, Subgraph.iSup_adj]
        constructor
        · rintro (⟨r', hxy⟩ | hxyC₀)
          · by_cases hr' : r' = r
            · subst hr'
              exact Or.inl hxy
            · exact Or.inr (Or.inl ⟨r', hr', hxy⟩)
          · exact Or.inr (Or.inr hxyC₀)
        · rintro (hxy | ⟨r', _, hxy⟩ | hxyC₀)
          · exact Or.inl ⟨r, hxy⟩
          · exact Or.inl ⟨r', hxy⟩
          · exact Or.inr hxyC₀
    have hR_disj : Disjoint R.verts (A (embI r)).verts := by
      rw [Set.disjoint_left]
      intro v hvR hvAr
      simp only [R, C₀, Subgraph.verts_sup, Subgraph.verts_iSup, Set.mem_union,
        Set.mem_iUnion] at hvR
      rcases hvR with ⟨r', hr', hvPI⟩ | ⟨x, hxX, hvAx⟩ | ⟨x, hvQX⟩
      · have hne1 : embI r ≠ embI r' := embI.injective.ne (Ne.symm hr')
        have hne2 : embI r ≠ hI r' := fun h ↦ (hembI_ext r).1 (h ▸ hhI_X r')
        exact Set.disjoint_left.1
          ((hPI r').disjoint_other hweb.disjoint_left hne1 hne2) hvPI hvAr
      · have hne : x ≠ embI r := fun h ↦ (hembI_ext r).1 (h ▸ hxX)
        exact Set.disjoint_left.1 (hweb.disjoint_left hne) hvAx hvAr
      · have hne1 : embI r ≠ x.1 := fun h ↦ (hembI_ext r).1 (h ▸ x.2.1)
        have hne2 : embI r ≠ parent x := fun h ↦ (hembI_ext r).1 (h ▸ hparent_X x)
        exact Set.disjoint_left.1
          ((hQX x).disjoint_other hweb.disjoint_left hne1 hne2) hvQX hvAr
    have hne_rh : embI r ≠ hI r := fun h ↦ (hembI_ext r).1 (h ▸ hhI_X r)
    have hinter_PI : (PI r).toSubgraph.verts ∩ (A (embI r)).verts = {(PI r).first} :=
      (hPI r).verts_inter_left hweb.disjoint_left hne_rh
    have hinter_C : C.verts ∩ (A (embI r)).verts = {(PI r).first} := by
      rw [hC_eq, Subgraph.verts_sup, Set.union_inter_distrib_right, hinter_PI,
        Set.disjoint_iff_inter_eq_empty.1 hR_disj, Set.union_empty]
    have hfirst_not_R : (PI r).first ∉ R.verts := fun h ↦
      Set.disjoint_left.1 hR_disj h (hPI r).2.1
    have hleaf_PI : IsLeafOf (PI r).toSubgraph (PI r).first :=
      Path.isLeafOf_first_of_ne (PI r) ((hPI r).first_ne_last hweb.disjoint_left hne_rh)
    refine ⟨(PI r).first, hinter_C, ?_⟩
    rw [hC_eq]
    exact isLeafOf_sup_of_notMem_right hleaf_PI hfirst_not_R
  let usedJ : Finset (Fin n) := Finset.univ.image jI ∪ Finset.univ.image jX
  have husedJ_card : usedJ.card ≤ p + m := by
    have h1 : (Finset.univ.image jI).card ≤ p :=
      Finset.card_image_le.trans (by simp)
    have h2 : (Finset.univ.image jX).card ≤ m := by
      have hcard_sub : Fintype.card ↥(X \ {a₀}) ≤ m := by
        rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        exact (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)).trans (by simp)
      exact Finset.card_image_le.trans (by simpa using hcard_sub)
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)
  have hcompl_card : q ≤ (Finset.univ \ usedJ).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    dsimp [n]
    omega
  obtain ⟨J, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq hcompl_card
  let eJ : Fin q ≃ J := (Finset.equivFinOfCardEq hJ_card).symm
  let embJ : Fin q ↪ Fin n :=
    eJ.toEmbedding.trans (Function.Embedding.subtype _)
  have hunusedI : ∀ r, jI r ∉ Set.range embJ := by
    intro r ⟨j, hj⟩
    have hnot := (Finset.mem_sdiff.mp (hJ_sub (eJ j).property)).2
    exact hnot (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, hj.symm⟩))
  have hunusedX : ∀ x, jX x ∉ Set.range embJ := by
    intro x ⟨j, hj⟩
    have hnot := (Finset.mem_sdiff.mp (hJ_sub (eJ j).property)).2
    exact hnot (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hj.symm⟩))
  refine ⟨embI, embJ, C, hC_le, hC_conn, hC_leaf, ?_⟩
  refine sup_le (iSup_le fun r => le_sup_of_le_right
    ((hPI r).1.trans (le_biSup (fun j => (B j).toSubgraph) (hunusedI r)))) ?_
  refine sup_le (iSup₂_le fun x _ => le_sup_of_le_left
    (le_iSup (fun i => (A i).toSubgraph) x)) ?_
  exact iSup_le fun x => le_sup_of_le_right
    ((hQX x).1.trans (le_biSup (fun j => (B j).toSubgraph) (hunusedX x)))

/-- Case 2 of V (4.4), page 99: for a web, the selected support is
edge-disjoint from the retained `B` paths and is therefore a spider. -/
theorem theorem_4_4_case_2 {G : (⊤ : SimpleGraph V).Subgraph}
    {p q m : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin (p + q + m) → GM01.Path V}
    (hweb : IsWeb G A B)
    {a₀ : Fin m} {X : Set (Fin m)}
    (hX_conn : IsWalkConnectedIn (webAuxGraph A B) a₀ X)
    (hcase2 : p ≤ (extNeigh (webAuxGraph A B) X).ncard) :
    ∃ (embI : Fin p ↪ Fin m) (embJ : Fin q ↪ Fin (p + q + m))
      (C : (⊤ : SimpleGraph V).Subgraph),
      IsSpider G (fun i : Fin p ↦ A (embI i)) (fun j : Fin q ↦ B (embJ j)) C := by
  obtain ⟨embI, embJ, C, hC, hc, hleaf, hsupp⟩ :=
    spider_support_of_large_boundary hweb.vertexWeb hX_conn hcase2
  refine ⟨embI, embJ, C, hC, hc, ?_, hleaf⟩
  intro j
  rw [Set.disjoint_left]
  intro e heC heB
  induction e with | h x y =>
    have hadjC : C.Adj x y := heC
    have hadj := hsupp.2 hadjC
    simp only [Subgraph.sup_adj, Subgraph.iSup_adj] at hadj
    rcases hadj with ⟨i, hi⟩ | ⟨k, hk, hxy⟩
    · exact Set.disjoint_left.mp (hweb.edge_disjoint i (embJ j)) hi heB
    · have hne : k ≠ embJ j := fun h => hk ⟨j, h.symm⟩
      exact Set.disjoint_left.mp (hweb.disjoint_right hne)
        ((B k).toSubgraph.edge_vert hxy) ((B (embJ j)).toSubgraph.edge_vert heB)

/-! ### Main Theorems (4.4), (4.5), and (4.6) -/

/-- Graph Minors V, (4.4) (page 98):
"Let $G \in \mathcal{F}_\theta$, and let $p, q \ge 0$ be integers. Let $m = p 2^{p\theta^2}$,
$n = p + q + m$. Suppose that $((A_1, \dots, A_m), (B_1, \dots, B_n))$ is an ($m, n$)-web in
$G$. Then there exists $I \subseteq \{1, \dots, m\}$, $J \subseteq \{1, \dots, n\}$ such
that $|I| = p$, $|J| = q$, and $((A_i \colon i \in I), (B_j \colon j \in J))$ is a ($p,
q$)-web with a spider."

The hypothesis `0 < p` excludes the false empty case of the printed statement:
when `p = q = 0` and `G` is empty, the empty web exists but has no connected
spider. -/
theorem theorem_4_4_simple {G : (⊤ : SimpleGraph V).Subgraph} {θ p q : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (hp : 0 < p)
    {A : Fin (p * 2 ^ (p * θ ^ 2)) → GM01.Path V}
    {B : Fin (p + q + p * 2 ^ (p * θ ^ 2)) → GM01.Path V}
    (hweb : IsWeb G A B) :
    ∃ (embI : Fin p ↪ Fin (p * 2 ^ (p * θ ^ 2)))
      (embJ : Fin q ↪ Fin (p + q + p * 2 ^ (p * θ ^ 2)))
      (C : (⊤ : SimpleGraph V).Subgraph),
      IsSpider G (fun i : Fin p ↦ A (embI i)) (fun j : Fin q ↦ B (embJ j)) C := by
  by_cases hcase1 : ∀ (a : Fin (p * 2 ^ (p * θ ^ 2))) (X : Set (Fin (p * 2 ^ (p * θ ^ 2)))),
      IsWalkConnectedIn (webAuxGraph A B) a X → (extNeigh (webAuxGraph A B) X).ncard < p
  · exact False.elim (theorem_4_4_case_1 hθ heven hG_fin hG hp hweb.vertexWeb hcase1)
  · push Not at hcase1
    obtain ⟨a₀, X, hX_conn, hcase2⟩ := hcase1
    exact theorem_4_4_case_2 hweb hX_conn hcase2

/-- Graph Minors V, (4.5) (page 99):
"For $0 \le k < \theta_2$, if $G \in \mathcal{F}_\theta$ has a ($\phi_k, \psi_k$)-web with $k$
edge-disjoint spiders, then it has a ($\phi_{k+1}, \psi_{k+1}$)-web with $k + 1$ edge-disjoint
spiders."
(Note: the printed statement on page 99 writes `0 ≤ k < θ₂`, a typographical slip for `0 ≤ k < θ₁`:
`ψ_k` is defined in the preceding sentence for `0 ≤ k < θ₁`, and (4.6) applies (4.5) up to `θ₁`.)
-/
theorem theorem_4_5_simple {G : (⊤ : SimpleGraph V).Subgraph} {θ k : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (hk : k < θ₁ θ) (h : HasWebWithSpiders G (φ θ k) (ψ θ k) k) :
    HasWebWithSpiders G (φ θ (k + 1)) (ψ θ (k + 1)) (k + 1) := by
  obtain ⟨A, B, C, hweb, hsp, hedisj⟩ := h
  let E_sp : Set (Sym2 V) := ⋃ l : Fin k, (C l).edgeSet
  let G' : (⊤ : SimpleGraph V).Subgraph := G.deleteEdges E_sp
  have hG'_le : G' ≤ G := Subgraph.deleteEdges_le _
  have hG'_fin : G'.verts.Finite := hG_fin.subset hG'_le.1
  have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
  have hweb_G' : IsWeb G' A B := by
    refine
      { isIn_left := fun i ↦ ⟨(hweb.isIn_left i).1, fun x y hxy ↦ ?_⟩
        isIn_right := fun j ↦ ⟨(hweb.isIn_right j).1, fun x y hxy ↦ ?_⟩
        disjoint_left := hweb.disjoint_left
        disjoint_right := hweb.disjoint_right
        meets := hweb.meets
        edge_disjoint := hweb.edge_disjoint }
    · rw [Subgraph.deleteEdges_adj]
      refine ⟨(hweb.isIn_left i).2 hxy, ?_⟩
      rintro ⟨_, ⟨l, rfl⟩, heC⟩
      exact Set.disjoint_left.1 ((hsp l).edge_disjoint_left i) heC hxy
    · rw [Subgraph.deleteEdges_adj]
      refine ⟨(hweb.isIn_right j).2 hxy, ?_⟩
      rintro ⟨_, ⟨l, rfl⟩, heC⟩
      exact Set.disjoint_left.1 ((hsp l).edge_disjoint j) heC hxy
  let p := φ θ (k + 1)
  let q := ψ θ (k + 1)
  have hp_pos : 0 < p := φ_pos hθ (k + 1)
  have hm_eq : φ θ k = p * 2 ^ (p * θ ^ 2) := φ_of_lt θ hk
  have hn_eq : ψ θ k = p + q + p * 2 ^ (p * θ ^ 2) := by
    rw [ψ_of_lt θ hk, ← hm_eq]
    ring
  let e_m : Fin (p * 2 ^ (p * θ ^ 2)) ≃ Fin (φ θ k) := ( finCongr hm_eq ).symm
  let e_n : Fin (p + q + p * 2 ^ (p * θ ^ 2)) ≃ Fin (ψ θ k) := ( finCongr hn_eq ).symm
  have hweb_cast : IsWeb G' (fun i ↦ A (e_m i)) (fun j ↦ B (e_n j)) :=
    hweb_G'.subweb e_m.toEmbedding e_n.toEmbedding
  obtain ⟨embI₀, embJ₀, C_new, hsp_new⟩ :=
    theorem_4_4_simple hθ heven hG'_fin hG'_mem hp_pos hweb_cast
  let embI : Fin p ↪ Fin (φ θ k) := embI₀.trans e_m.toEmbedding
  let embJ : Fin q ↪ Fin (ψ θ k) := embJ₀.trans e_n.toEmbedding
  have hsp_new_G : IsSpider G (fun i ↦ A (embI i)) (fun j ↦ B (embJ j)) C_new :=
    { le := hsp_new.le.trans hG'_le
      connected := hsp_new.connected
      edge_disjoint := hsp_new.edge_disjoint
      unique_leaf := hsp_new.unique_leaf }
  have hC_new_disj : ∀ l : Fin k, Disjoint (C l).edgeSet C_new.edgeSet := by
    intro l
    rw [Set.disjoint_left]
    intro e he_l he_new
    induction e with | h x y =>
    have hadj_G' : G'.Adj x y := hsp_new.le.2 he_new
    rw [Subgraph.deleteEdges_adj] at hadj_G'
    exact hadj_G'.2 (Set.mem_iUnion.2 ⟨l, he_l⟩)
  let C' : Fin (k + 1) → (⊤ : SimpleGraph V).Subgraph := Fin.snoc C C_new
  refine ⟨fun i ↦ A (embI i), fun j ↦ B (embJ j), C',
    hweb.subweb embI embJ, ?_, ?_⟩
  · intro l
    induction l using Fin.lastCases with
    | last =>
      simpa [C'] using hsp_new_G
    | cast l₀ =>
      simpa [C'] using (hsp l₀).subweb embI embJ
  · intro l₁ l₂ hne
    induction l₁ using Fin.lastCases with
    | last =>
      induction l₂ using Fin.lastCases with
      | last => exact absurd rfl hne
      | cast l₂₀ =>
        simpa [C'] using (hC_new_disj l₂₀).symm
    | cast l₁₀ =>
      induction l₂ using Fin.lastCases with
      | last =>
        simpa [C'] using hC_new_disj l₁₀
      | cast l₂₀ =>
        have hne₀ : l₁₀ ≠ l₂₀ := fun h ↦ hne (congrArg Fin.castSucc h)
        simpa [C'] using hedisj hne₀

/-! ### Degree bound in `webSubgraph` and Theorem (4.6) -/

/-- The initial vertex of a simple path `w` (`w.IsPath`) has at most `1` neighbor in
`w.toSubgraph`. -/
private lemma walk_neighborSet_start_ncard_le_one {x y : V}
    (w : (⊤ : SimpleGraph V).Walk x y) (hw : w.IsPath) :
    (w.toSubgraph.neighborSet x).ncard ≤ 1 := by
  cases w with
  | nil =>
    have h_empty : (Walk.nil : (⊤ : SimpleGraph V).Walk x x).toSubgraph.neighborSet x = ∅ := by
      ext z
      simp
    rw [h_empty, Set.ncard_empty]
    omega
  | @cons x x' y hadj rest =>
    rw [Walk.cons_isPath_iff] at hw
    have hsub : (Walk.cons hadj rest).toSubgraph.neighborSet x ⊆ {x'} := by
      intro z hz
      simp only [Subgraph.mem_neighborSet, Walk.toSubgraph, Subgraph.sup_adj,
        subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
        Set.mem_singleton_iff] at hz ⊢
      rcases hz with (⟨_, rfl⟩ | ⟨_, rfl⟩) | hadj_rest
      · rfl
      · exact absurd rfl hadj.ne
      · have hx_rest : x ∈ rest.support :=
          rest.mem_verts_toSubgraph.1 (rest.toSubgraph.edge_vert hadj_rest)
        exact absurd hx_rest hw.2
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by simp)

/-- Every vertex has at most `2` neighbors in the subgraph of a simple path `w` (`w.IsPath`). -/
lemma walk_neighborSet_ncard_le_two {x y : V}
    (w : (⊤ : SimpleGraph V).Walk x y) (hw : w.IsPath) (v : V) :
    (w.toSubgraph.neighborSet v).ncard ≤ 2 := by
  induction w with
  | @nil u =>
    have h_empty : (Walk.nil : (⊤ : SimpleGraph V).Walk u u).toSubgraph.neighborSet v = ∅ := by
      ext z
      simp
    rw [h_empty, Set.ncard_empty]
    omega
  | @cons x x' y hadj rest ih =>
    rw [Walk.cons_isPath_iff] at hw
    by_cases hvx : v = x
    · subst hvx
      exact (walk_neighborSet_start_ncard_le_one (Walk.cons hadj rest)
        ((Walk.cons_isPath_iff hadj rest).2 hw)).trans (by decide)
    · by_cases hvx' : v = x'
      · subst hvx'
        have hsub : (Walk.cons hadj rest).toSubgraph.neighborSet v ⊆
            insert x (rest.toSubgraph.neighborSet v) := by
          intro z hz
          simp only [Subgraph.mem_neighborSet, Walk.toSubgraph, Subgraph.sup_adj,
            subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
            Set.mem_insert_iff] at hz ⊢
          rcases hz with (⟨h1, _⟩ | ⟨rfl, _⟩) | hadj_rest
          · exact absurd h1.symm hvx
          · exact Or.inl rfl
          · exact Or.inr hadj_rest
        have hfin_rest : (rest.toSubgraph.neighborSet v).Finite :=
          (List.finite_toSet rest.support).subset (fun z hz ↦
            rest.mem_verts_toSubgraph.1 (rest.toSubgraph.edge_vert
              ((rest.toSubgraph.mem_neighborSet v z).1 hz).symm))
        have hle1 := walk_neighborSet_start_ncard_le_one rest hw.1
        have hle_ins : (insert x (rest.toSubgraph.neighborSet v)).ncard ≤ 2 :=
          (Set.ncard_insert_le x _).trans (by omega)
        exact (Set.ncard_le_ncard hsub (hfin_rest.insert x)).trans hle_ins
      · have heq : (Walk.cons hadj rest).toSubgraph.neighborSet v =
            rest.toSubgraph.neighborSet v := by
          ext z
          simp only [Subgraph.mem_neighborSet, Walk.toSubgraph, Subgraph.sup_adj,
            subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
          refine ⟨fun h ↦ ?_, Or.inr⟩
          rcases h with (⟨h1, _⟩ | ⟨_, h2⟩) | hadj_rest
          · exact absurd h1.symm hvx
          · exact absurd h2.symm hvx'
          · exact hadj_rest
        rw [heq]
        exact ih hw.1

/-- In a family of pairwise vertex-disjoint paths `P : Fin m → GM01.Path V`, every vertex `v` has
at most `2` neighbors in `⨆ i, (P i).toSubgraph`. -/
private lemma iSup_path_neighborSet_ncard_le_two {m : ℕ} (P : Fin m → GM01.Path V)
    (hdisj : Pairwise fun i i' ↦ Disjoint (P i).verts (P i').verts) (v : V) :
    ((⨆ i, (P i).toSubgraph).neighborSet v).ncard ≤ 2 := by
  by_cases hex : ∃ i : Fin m, v ∈ (P i).verts
  · obtain ⟨i₀, hi₀⟩ := hex
    have heq : (⨆ i, (P i).toSubgraph).neighborSet v = (P i₀).toSubgraph.neighborSet v := by
      ext z
      simp only [Subgraph.mem_neighborSet, Subgraph.iSup_adj]
      refine ⟨fun ⟨i, hadj⟩ ↦ ?_, fun hadj ↦ ⟨i₀, hadj⟩⟩
      have hvi : v ∈ (P i).verts := (P i).toSubgraph.edge_vert hadj
      have hii₀ : i = i₀ := by
        by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) hvi hi₀
      exact hii₀ ▸ hadj
    rw [heq]
    exact walk_neighborSet_ncard_le_two (P i₀).walk (P i₀).isPath v
  · push Not at hex
    have hempty : (⨆ i, (P i).toSubgraph).neighborSet v = ∅ := by
      ext z
      simp only [Subgraph.mem_neighborSet, Subgraph.iSup_adj, Set.mem_empty_iff_false, iff_false,
        not_exists]
      intro i hadj
      exact hex i ((P i).toSubgraph.edge_vert hadj)
    rw [hempty, Set.ncard_empty]
    omega

/-- In `webSubgraph A B` for a web `(A, B)`, every vertex `v` has valency at most `4`. -/
lemma webSubgraph_neighborSet_ncard_le_four {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} (hweb : IsWeb G A B) (v : V) :
    ((webSubgraph A B).neighborSet v).ncard ≤ 4 := by
  have heq : (webSubgraph A B).neighborSet v =
      (⨆ i, (A i).toSubgraph).neighborSet v ∪ (⨆ j, (B j).toSubgraph).neighborSet v := by
    ext z
    simp [webSubgraph, Subgraph.mem_neighborSet]
  rw [heq]
  have h1 := iSup_path_neighborSet_ncard_le_two A hweb.disjoint_left v
  have h2 := iSup_path_neighborSet_ncard_le_two B hweb.disjoint_right v
  exact (Set.ncard_union_le _ _).trans (by omega)

/-- Graph Minors V, (4.6) (page 100):
"If $G \in \mathcal{F}_\theta$ then $G$ has no $(\theta_2, \theta_2)$-web." -/
theorem theorem_4_6_simple
    {G : (⊤ : SimpleGraph V).Subgraph} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ) :
    ¬ HasWeb G (θ₂ θ) (θ₂ θ) := by
  rintro ⟨A, B, hweb⟩
  let G' := webSubgraph A B
  have hG'_le : G' ≤ G := webSubgraph_le hweb.vertexWeb
  have hG'_fin : G'.verts.Finite := hG_fin.subset hG'_le.1
  have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
  have hG'_deg : ∀ v ∈ G'.verts, (G'.neighborSet v).ncard ≤ 4 :=
    fun v _ ↦ webSubgraph_neighborSet_ncard_le_four hweb v
  have hweb_G' : IsWeb G' A B :=
    { isIn_left := fun i ↦ le_sup_of_le_left (le_iSup (fun s ↦ (A s).toSubgraph) i)
      isIn_right := fun j ↦ le_sup_of_le_right (le_iSup (fun s ↦ (B s).toSubgraph) j)
      disjoint_left := hweb.disjoint_left
      disjoint_right := hweb.disjoint_right
      meets := hweb.meets
      edge_disjoint := hweb.edge_disjoint }
  have h_spiders_0 : HasWebWithSpiders G' (φ θ 0) (ψ θ 0) 0 := by
    have hφ0 : φ θ 0 ≤ θ₂ θ := φ_zero_le_θ₂ θ
    have hψ0 : ψ θ 0 ≤ θ₂ θ := (ψ_zero θ).le
    refine ⟨fun i ↦ A (Fin.castLE hφ0 i), fun j ↦ B (Fin.castLE hψ0 j), Fin.elim0,
      hweb_G'.subweb (Fin.castLEEmb hφ0) (Fin.castLEEmb hψ0),
      fun l ↦ Fin.elim0 l, fun l ↦ Fin.elim0 l⟩
  have h_spiders_k : ∀ k ≤ θ₁ θ, HasWebWithSpiders G' (φ θ k) (ψ θ k) k := by
    intro k
    induction k with
    | zero => exact fun _ ↦ h_spiders_0
    | succ k ih =>
      intro hk
      exact theorem_4_5_simple hθ heven hG'_fin hG'_mem (Nat.lt_of_succ_le hk)
        (ih (Nat.le_of_succ_le hk))
  obtain ⟨A_end, B_end, C_end, hweb_end, hsp_end, hedisj_end⟩ :=
    h_spiders_k (θ₁ θ) le_rfl
  let e_end : Fin (θ ^ 2 / 2) ≃ Fin (φ θ (θ₁ θ)) := (finCongr (φ_θ₁ θ)).symm
  have h42 := theorem_4_2_simple hθ heven hG'_fin hG'_mem
    (fun i ↦ (A_end (e_end i)).toSubgraph) C_end
    (fun i ↦ hweb_end.isIn_left (e_end i))
    (fun i ↦ (A_end (e_end i)).connected_toSubgraph)
    (fun i₁ i₂ hne ↦ hweb_end.disjoint_left (e_end.injective.ne hne))
    (fun l ↦ (hsp_end l).le)
    (fun l ↦ (hsp_end l).connected)
    hedisj_end
    (fun i l ↦ by
      obtain ⟨v, hv_inter, hv_leaf⟩ := (hsp_end l).unique_leaf (e_end i)
      exact ⟨v, by rw [Set.inter_comm]; exact hv_inter, hv_leaf⟩)
    hG'_deg
  exact Nat.lt_irrefl (θ₁ θ) h42

end GraphMinor.GM05
