module

public import GraphMinor.GM08.Section3
public import GraphMinor.GM08.Section4
public import GraphMinor.GM08.Section13
public import GraphMinor.GM08.Section14Chain

/-!
# Graph Minors VIII, Section 14 (Part 2): Well-Rootedness of $k$-Chains (pages 276–278)

This file formalizes **(14.2)** and its numbered claims **(1)–(4)** from Section 14 of
N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- `lemma_14_2_claim_1`: Claim (1) in the proof of (14.2) (page 277).
- `lemma_14_2_claim_2`: Claim (2) in the proof of (14.2) (page 277).
- `lemma_14_2_claim_3`: Claim (3) in the proof of (14.2) (page 278).
- `lemma_14_2_claim_4`: Claim (4) in the proof of (14.2) (page 278).
- `theorem_14_2`: (14.2) (pages 276–278), if $\mathscr{A}$ is well-rooted and $k \ge 0$, the class
  of all $k$-chains over $\mathscr{A}$ is well-rooted.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph

universe u v

/-! ## Additional `GraftPathDecomposition` helpers -/

theorem GraftPathDecomposition.Y_castSucc_subset_G {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (j : Fin D.r) :
    D.Y j.castSucc ⊆ V(D.G j) :=
  fun _ hx => D.Y_subset j (Or.inl hx)

theorem GraftPathDecomposition.Y_succ_subset_G {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X) (j : Fin D.r) :
    D.Y j.succ ⊆ V(D.G j) :=
  fun _ hx => D.Y_subset j (Or.inr hx)

theorem GraftPathDecomposition.exists_mem_vertexSet {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {v : α} (hv : v ∈ V(X.G)) :
    ∃ h : Fin D.r, v ∈ V(D.G h) := by
  rw [← D.vertexSet_iUnion, mem_iUnion] at hv
  exact hv

theorem GraftPathDecomposition.inter_subset_Y_castSucc {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {h i j : Fin D.r} (hhi : h < i) (hij : i ≤ j) :
    V(D.G h) ∩ V(D.G j) ⊆ D.Y i.castSucc := by
  have hi_pos : 0 < i.1 := by change h.1 < i.1 at hhi; omega
  let i₀ : Fin D.r := ⟨i.1 - 1, by have := i.2; omega⟩
  have hi₀_succ : i₀.succ = i.castSucc := Fin.ext (by dsimp [i₀]; omega)
  rw [← hi₀_succ]
  exact D.inter_subset_Y_succ (by change h.1 ≤ i.1 - 1; change h.1 < i.1 at hhi; omega)
    (by change i.1 - 1 < j.1; change i.1 ≤ j.1 at hij; omega)
    (by dsimp [i₀]; have := i.2; omega)

/-! ## General helper for `IsGraphSimulation` (`IsMinorModel`) -/

/-- In any graph simulation `(ηv, ηe)` of `H` in `G`, if `e ∈ E(H)` and `G.Inc (ηe e) x`, then
there exists an endpoint `u ∈ V(H)` of `e` in `H` (`H.Inc e u`) such that `x ∈ ηv u`. -/
theorem exists_inc_and_mem_eta_of_inc {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}
    {H : Graph α' β'} {G : Graph α β} {ηv : α' → Set α} {ηe : β' → β}
    (hsim : IsGraphSimulation H G ηv ηe) {e : β'} (he : e ∈ E(H))
    {x : α} (hinc : G.Inc (ηe e) x) :
    ∃ u ∈ V(H), H.Inc e u ∧ x ∈ ηv u := by
  obtain ⟨a, b, hlH⟩ := exists_isLink_of_mem_edgeSet he
  by_cases hloop : H.IsLoopAt e a
  · exact ⟨a, hlH.left_mem, hlH.inc_left, (hsim.isLoopAt_iff a hlH.left_mem e he).1 hloop x hinc⟩
  · have hab_ne : a ≠ b := fun h' => hloop (h' ▸ hlH)
    obtain ⟨x₁, hx₁, y₁, hlG₁⟩ := (hsim.inc_iff a hlH.left_mem e he).1 hlH.inc_left
    obtain ⟨x₂, hx₂, hinc₂⟩ := (hsim.inc_iff b hlH.right_mem e he).1 hlH.inc_right
    have hx₁x₂ : x₁ ≠ x₂ :=
      (hsim.vertex_disjoint a hlH.left_mem b hlH.right_mem hab_ne).ne_of_mem hx₁ hx₂
    have hx₂y₁ : x₂ = y₁ := hinc₂.eq_of_isLink_of_ne_left hlG₁ hx₁x₂.symm
    obtain rfl | rfl := hinc.eq_or_eq_of_isLink hlG₁
    · exact ⟨a, hlH.left_mem, hlH.inc_left, hx₁⟩
    · exact ⟨b, hlH.right_mem, hlH.inc_right, hx₂y₁ ▸ hx₂⟩

/-! ## Sublist index extraction for `List.SublistForall₂` -/

/-- If `List.SublistForall₂ R L₁ L₂` holds, there is a strictly increasing map
`φ : Fin L₁.length → Fin L₂.length` such that `R L₁[i] L₂[φ i]` for all `i`. -/
theorem exists_strictMono_of_sublistForall₂ {α : Type u} {β : Type v}
    {R : α → β → Prop} {L₁ : List α} {L₂ : List β}
    (h : List.SublistForall₂ R L₁ L₂) :
    ∃ φ : Fin L₁.length → Fin L₂.length,
      StrictMono φ ∧ ∀ i : Fin L₁.length, R (L₁[i.1]'i.2) (L₂[(φ i).1]'(φ i).2) := by
  induction h with
  | nil =>
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | @cons a b l₁ l₂ hr _ ih =>
    obtain ⟨φ, hφ_mono, hφ_rel⟩ := ih
    refine ⟨Fin.cases ⟨0, Nat.zero_lt_succ l₂.length⟩ (fun i => (φ i).succ), ?_, ?_⟩
    · intro i j hij
      revert hij
      refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
      · intro h
        exact False.elim (lt_irrefl _ h)
      · intro _
        simp only [Fin.cases_zero, Fin.cases_succ]
        exact Fin.succ_pos (φ j')
      · intro h
        exact False.elim (Nat.not_lt_zero _ h)
      · intro hij'
        simp only [Fin.cases_succ]
        exact Fin.succ_lt_succ_iff.mpr (hφ_mono (Fin.succ_lt_succ_iff.mp hij'))
    · intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp only [Fin.cases_zero, Fin.val_zero, List.getElem_cons_zero]
        exact hr
      · simp only [Fin.cases_succ, Fin.val_succ, List.getElem_cons_succ]
        exact hφ_rel i'
  | @cons_right b l₁ l₂ _ ih =>
    obtain ⟨φ, hφ_mono, hφ_rel⟩ := ih
    refine ⟨fun i => (φ i).succ, fun i j hij => Fin.succ_lt_succ_iff.mpr (hφ_mono hij), ?_⟩
    intro i
    simp only [Fin.val_succ, List.getElem_cons_succ]
    exact hφ_rel i

/-- Index extraction for `List.SublistForall₂ R (List.ofFn f) (List.ofFn g)`. -/
theorem exists_strictMono_of_sublistForall₂_ofFn {α : Type u} {β : Type v}
    {R : α → β → Prop} {m n : ℕ} (f : Fin m → α) (g : Fin n → β)
    (h : List.SublistForall₂ R (List.ofFn f) (List.ofFn g)) :
    ∃ φ : Fin m → Fin n, StrictMono φ ∧ ∀ i : Fin m, R (f i) (g (φ i)) := by
  obtain ⟨φ₀, hφ₀_mono, hφ₀_rel⟩ := exists_strictMono_of_sublistForall₂ h
  have hm : (List.ofFn f).length = m := List.length_ofFn
  have hn : (List.ofFn g).length = n := List.length_ofFn
  let φ : Fin m → Fin n := fun i => (φ₀ (i.cast hm.symm)).cast hn
  refine ⟨φ, fun i j hij => hφ₀_mono hij, fun i => ?_⟩
  have hrel := hφ₀_rel (i.cast hm.symm)
  simp only [List.getElem_ofFn] at hrel
  exact hrel

/-! ## Subgraph constructor from vertex and edge subsets -/

/-- The subgraph of `G` with vertex set `V₀` and edge set `E₀ ∩ E(G)`, provided `V₀ ⊆ V(G)` and
every edge in `E₀` has its endpoints in `V₀`. -/
def subgraphOfVertsEdges {α : Type u} {β : Type v}
    (G : Graph α β) (V₀ : Set α) (E₀ : Set β)
    (_hV : V₀ ⊆ V(G))
    (hE : ∀ ⦃e x y⦄, e ∈ E₀ → G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) : Graph α β where
  vertexSet := V₀
  IsLink e x y := e ∈ E₀ ∧ G.IsLink e x y
  isLink_symm _ _ := ⟨fun _ _ h => ⟨h.1, h.2.symm⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h h' := G.eq_or_eq_of_isLink_of_isLink h.2 h'.2
  left_mem_of_isLink _ _ _ h := (hE h.1 h.2).1

@[simp]
theorem subgraphOfVertsEdges_vertexSet {α : Type u} {β : Type v}
    (G : Graph α β) (V₀ : Set α) (E₀ : Set β) (hV : V₀ ⊆ V(G))
    (hE : ∀ ⦃e x y⦄, e ∈ E₀ → G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) :
    V(subgraphOfVertsEdges G V₀ E₀ hV hE) = V₀ :=
  rfl

@[simp]
theorem subgraphOfVertsEdges_isLink {α : Type u} {β : Type v}
    (G : Graph α β) (V₀ : Set α) (E₀ : Set β) (hV : V₀ ⊆ V(G))
    (hE : ∀ ⦃e x y⦄, e ∈ E₀ → G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) (e : β) (x y : α) :
    (subgraphOfVertsEdges G V₀ E₀ hV hE).IsLink e x y ↔ e ∈ E₀ ∧ G.IsLink e x y :=
  Iff.rfl

theorem subgraphOfVertsEdges_le {α : Type u} {β : Type v}
    (G : Graph α β) (V₀ : Set α) (E₀ : Set β) (hV : V₀ ⊆ V(G))
    (hE : ∀ ⦃e x y⦄, e ∈ E₀ → G.IsLink e x y → x ∈ V₀ ∧ y ∈ V₀) :
    subgraphOfVertsEdges G V₀ E₀ hV hE ≤ G :=
  ⟨hV, fun _ _ _ h => h.2⟩

/-! ## Rooted graphs associated with a $k$-chain decomposition -/

/-- Given a $k$-chain decomposition `D` and cut-vertices `y : Fin (D.r + 1) → Fin k → α` on the
$k$ disjoint paths, the root list `τ_j` of length `2k` for piece `j : Fin D.r` lists
`y j.castSucc 0, ..., y j.castSucc (k-1), y j.succ 0, ..., y j.succ (k-1)`. -/
def kChainPartRootList {α : Type u} {r k : ℕ}
    (y : Fin (r + 1) → Fin k → α) (j : Fin r) : List α :=
  List.ofFn (fun q : Fin (2 * k) =>
    if h : q.1 < k then y j.castSucc ⟨q.1, h⟩ else y j.succ ⟨q.1 - k, by omega⟩)

@[simp]
theorem kChainPartRootList_length {α : Type u} {r k : ℕ}
    (y : Fin (r + 1) → Fin k → α) (j : Fin r) :
    (kChainPartRootList y j).length = 2 * k :=
  List.length_ofFn

theorem kChainPartRootList_getElem_left {α : Type u} {r k : ℕ}
    (y : Fin (r + 1) → Fin k → α) (j : Fin r) (p : Fin k) :
    (kChainPartRootList y j)[p.1]'(by simp; omega) = y j.castSucc p := by
  simp [kChainPartRootList, p.2]

theorem kChainPartRootList_getElem_right {α : Type u} {r k : ℕ}
    (y : Fin (r + 1) → Fin k → α) (j : Fin r) (p : Fin k) :
    (kChainPartRootList y j)[p.1 + k]'(by simp; omega) = y j.succ p := by
  have hnot : ¬ (p.1 + k < k) := by omega
  simp [kChainPartRootList, hnot]

theorem mem_kChainPartRootList_iff {α : Type u} {r k : ℕ}
    (y : Fin (r + 1) → Fin k → α) (j : Fin r) (x : α) :
    x ∈ kChainPartRootList y j ↔
      (∃ p : Fin k, y j.castSucc p = x) ∨ (∃ p : Fin k, y j.succ p = x) := by
  simp only [kChainPartRootList, List.mem_ofFn]
  constructor
  · rintro ⟨q, rfl⟩
    by_cases h : q.1 < k
    · simp only [h, ↓reduceDIte]
      exact Or.inl ⟨⟨q.1, h⟩, rfl⟩
    · simp only [h, ↓reduceDIte]
      exact Or.inr ⟨⟨q.1 - k, by omega⟩, rfl⟩
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · refine ⟨⟨p.1, by omega⟩, ?_⟩
      simp [p.2]
    · refine ⟨⟨p.1 + k, by omega⟩, ?_⟩
      have hnot : ¬ (p.1 + k < k) := by omega
      simp [hnot]

/-- The rooted graph $(G_j, \tau_j)$ of index $2k$ for piece $j$ of a $k$-chain decomposition. -/
def kChainPartRootedGraph {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (y : Fin (D.r + 1) → Fin k → α)
    (hy_mem : ∀ (l : Fin (D.r + 1)) (p : Fin k), y l p ∈ D.Y l)
    (j : Fin D.r) : RootedGraph α β where
  G := D.G j
  τ := kChainPartRootList y j
  τ_subset := by
    intro v hv
    rw [mem_kChainPartRootList_iff] at hv
    rcases hv with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact D.Y_castSucc_subset_G j (hy_mem j.castSucc p)
    · exact D.Y_succ_subset_G j (hy_mem j.succ p)
  finite_G := (D.partGraft j).finite_G

theorem kChainPartRootedGraph_toGraft_eq {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (y : Fin (D.r + 1) → Fin k → α)
    (hy_mem : ∀ (l : Fin (D.r + 1)) (p : Fin k), y l p ∈ D.Y l)
    (hy_surj : ∀ (l : Fin (D.r + 1)) (x : α), x ∈ D.Y l → ∃ p : Fin k, y l p = x)
    (j : Fin D.r) :
    (kChainPartRootedGraph D y hy_mem j).toGraft = D.partGraft j := by
  apply Graft.ext
  · rfl
  · ext x
    simp only [RootedGraph.toGraft, kChainPartRootedGraph, GraftPathDecomposition.partGraft,
      mem_ofPred_eq, mem_kChainPartRootList_iff, mem_union]
    exact ⟨fun h => h.elim (fun ⟨p, hp⟩ => Or.inl (hp ▸ hy_mem j.castSucc p))
        (fun ⟨p, hp⟩ => Or.inr (hp ▸ hy_mem j.succ p)),
      fun h => h.elim (fun hx => Or.inl (hy_surj j.castSucc x hx))
        (fun hx => Or.inr (hy_surj j.succ x hx))⟩

/-! ## Extracting cut-vertex data for a $k$-chain -/

/-- Bundled cut-vertex data for a $k$-chain decomposition `D` and $k$ disjoint paths `P`. -/
structure KChainCutData {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    (k : ℕ) (P : Fin k → Graph α β) where
  /-- Starting vertex of `P p` in `Y_0`. -/
  u : Fin k → α
  /-- Ending vertex of `P p` in `Y_r`. -/
  v : Fin k → α
  /-- Path structure of `P p`. -/
  wp : ∀ p : Fin k, GraphPathIn X.G (P p) (u p) (v p)
  /-- Pairwise vertex-disjointness of `P`. -/
  P_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q)
  /-- Cut index `c p l` along `wp p` at `Y_l`. -/
  c : Fin k → Fin (D.r + 1) → ℕ
  /-- `c p l < (wp p).verts.length`. -/
  c_lt : ∀ (p : Fin k) (l : Fin (D.r + 1)), c p l < (wp p).verts.length
  /-- `c p 0 = 0`. -/
  c_zero : ∀ p : Fin k, c p ⟨0, Nat.zero_lt_succ D.r⟩ = 0
  /-- `c p r = (wp p).edges.length`. -/
  c_last : ∀ p : Fin k, c p (Fin.last D.r) = (wp p).edges.length
  /-- `c p` is monotone. -/
  c_mono : ∀ p : Fin k, Monotone (c p)
  /-- `D.Y l ∩ V(P p) = {(wp p).verts[c p l]}`. -/
  Y_inter_eq : ∀ (p : Fin k) (l : Fin (D.r + 1)),
    D.Y l ∩ V(P p) = {(wp p).verts[c p l]'(c_lt p l)}
  /-- Every vertex of `D.Y l` is the cut vertex of some `p : Fin k`. -/
  Y_surj : ∀ (l : Fin (D.r + 1)) (x : α), x ∈ D.Y l →
    ∃ p : Fin k, (wp p).verts[c p l]'(c_lt p l) = x
  /-- Vertex interval characterization of `V(D.G j)` along `wp p`. -/
  verts_mem_iff : ∀ (p : Fin k) (j : Fin D.r) (s : ℕ) (hs : s < (wp p).verts.length),
    (wp p).verts[s]'hs ∈ V(D.G j) ↔ c p j.castSucc ≤ s ∧ s ≤ c p j.succ
  /-- Edge interval characterization of `E(D.G j)` along `wp p`. -/
  edges_mem_iff : ∀ (p : Fin k) (j : Fin D.r) (s : ℕ) (hs : s < (wp p).edges.length),
    (wp p).edges[s]'hs ∈ E(D.G j) ↔ c p j.castSucc ≤ s ∧ s < c p j.succ

/-- Existence of `KChainCutData` for any $k$-chain decomposition. -/
noncomputable def GraftPathDecomposition.mkKChainCutData {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X : Graft α β} (D : GraftPathDecomposition 𝒜 X)
    {k : ℕ} (hY_card : ∀ i : Fin (D.r + 1), (D.Y i).ncard = k)
    {P : Fin k → Graph α β}
    (hP_path : ∀ p : Fin k,
      IsGraphPathFromTo X.G (P p) (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)))
    (hP_disj : ∀ p q : Fin k, p ≠ q → Disjoint V(P p) V(P q)) :
    KChainCutData D k P := by
  have hP_path' := hP_path
  choose u hu v hv hwp using hP_path'
  have hwp' : ∀ p, GraphPathIn X.G (P p) (u p) (v p) := fun p => Classical.choice (hwp p)
  have hex := fun p =>
    D.exists_cut_indices_of_kChain hY_card hP_path hP_disj p (hu p) (hv p) (hwp' p)
  choose c hc_lt hc0 hcr hc_mono hc_eq hverts hedges using hex
  refine {
    u := u
    v := v
    wp := hwp'
    P_disj := hP_disj
    c := c
    c_lt := hc_lt
    c_zero := hc0
    c_last := hcr
    c_mono := hc_mono
    Y_inter_eq := hc_eq
    Y_surj := ?_
    verts_mem_iff := hverts
    edges_mem_iff := hedges
  }
  intro l x hx
  have hunion := (D.ncard_Y_inter_path_eq_one hY_card hP_path hP_disj l).2
  rw [← hunion, mem_iUnion] at hx
  obtain ⟨p, hxp⟩ := hx
  rw [hc_eq p l, mem_singleton_iff] at hxp
  exact ⟨p, hxp.symm⟩

namespace KChainCutData

variable {α : Type u} {β : Type v}
  {𝒜 : Set (Graft α β)} {X : Graft α β} {D : GraftPathDecomposition 𝒜 X}
  {k : ℕ} {P : Fin k → Graph α β} (cd : KChainCutData D k P)

/-- The cut vertex `y l p := (wp p).verts[c p l]` in `D.Y l ∩ V(P p)`. -/
def y (l : Fin (D.r + 1)) (p : Fin k) : α :=
  (cd.wp p).verts[cd.c p l]'(cd.c_lt p l)

theorem y_mem_Y (l : Fin (D.r + 1)) (p : Fin k) : cd.y l p ∈ D.Y l := by
  have h : cd.y l p ∈ D.Y l ∩ V(P p) := by
    rw [cd.Y_inter_eq p l]
    exact rfl
  exact h.1

theorem y_mem_P (l : Fin (D.r + 1)) (p : Fin k) : cd.y l p ∈ V(P p) := by
  have h : cd.y l p ∈ D.Y l ∩ V(P p) := by
    rw [cd.Y_inter_eq p l]
    exact rfl
  exact h.2

theorem eq_y_of_mem_Y_inter_P {l : Fin (D.r + 1)} {p : Fin k} {x : α}
    (hxY : x ∈ D.Y l) (hxP : x ∈ V(P p)) :
    x = cd.y l p := by
  have h : x ∈ D.Y l ∩ V(P p) := ⟨hxY, hxP⟩
  rw [cd.Y_inter_eq p l, mem_singleton_iff] at h
  exact h

theorem y_surj (l : Fin (D.r + 1)) (x : α) (hx : x ∈ D.Y l) :
    ∃ p : Fin k, cd.y l p = x :=
  cd.Y_surj l x hx

theorem y_mem_G_castSucc (j : Fin D.r) (p : Fin k) :
    cd.y j.castSucc p ∈ V(D.G j) :=
  D.Y_castSucc_subset_G j (cd.y_mem_Y j.castSucc p)

theorem y_mem_G_succ (j : Fin D.r) (p : Fin k) :
    cd.y j.succ p ∈ V(D.G j) :=
  D.Y_succ_subset_G j (cd.y_mem_Y j.succ p)

/-- The rooted graph $(G_j, \tau_j)$ associated with piece `j` of `cd`. -/
def partRootedGraph (j : Fin D.r) : RootedGraph α β :=
  kChainPartRootedGraph D cd.y cd.y_mem_Y j

theorem partRootedGraph_toGraft_eq (j : Fin D.r) :
    (cd.partRootedGraph j).toGraft = D.partGraft j :=
  kChainPartRootedGraph_toGraft_eq D cd.y cd.y_mem_Y cd.y_surj j

end KChainCutData

/-! ## Construction of $Q$, $R$, $G$ and Claims (1)–(4) in the proof of (14.2) -/

/-- Chosen connected subgraph $K_n(v) \le (D_2.G(\phi(n))).\text{deleteEdges}(\eta_{e,n} '' E(D_1.G\ n))$
with vertex set $\eta_{v,n}(v)$ for $v \in V(D_1.G\ n)$. -/
noncomputable def simSubgraph {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))
    (n : Fin D₁.r) (v : α) (hv : v ∈ V(D₁.G n)) : Graph α β :=
  Classical.choose ((hsim n).1.connected v hv)

theorem simSubgraph_le {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))
    (n : Fin D₁.r) (v : α) (hv : v ∈ V(D₁.G n)) :
    simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv ≤
      (D₂.G (φ n)).deleteEdges (ηe n '' E(D₁.G n)) :=
  (Classical.choose_spec ((hsim n).1.connected v hv)).1

theorem simSubgraph_vertexSet {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))
    (n : Fin D₁.r) (v : α) (hv : v ∈ V(D₁.G n)) :
    V(simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv) = ηv n v :=
  (Classical.choose_spec ((hsim n).1.connected v hv)).2.1

theorem simSubgraph_connected {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))
    (n : Fin D₁.r) (v : α) (hv : v ∈ V(D₁.G n)) :
    GraphConnected (simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv) :=
  (Classical.choose_spec ((hsim n).1.connected v hv)).2.2

/-- Vertex set of $Q$: union of $\eta_{v,n}(v)$ over $n : \operatorname{Fin} D_1.r$ and
$v \in V(D_1.G\ n)$. -/
def QVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (ηv : Fin D₁.r → α → Set α) : Set α :=
  ⋃ (n : Fin D₁.r) (v : α) (_ : v ∈ V(D₁.G n)), ηv n v

/-- Edge set of $Q$: union of $E(K_n(v))$ over $n : \operatorname{Fin} D_1.r$ and
$v \in V(D_1.G\ n)$. -/
def QEdges {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n)) :
    Set β :=
  ⋃ (n : Fin D₁.r) (v : α) (hv : v ∈ V(D₁.G n)),
    E(simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv)

/-- Vertex set of $R$: union of $V(P_2(p) \sqcap D_2.G(j))$ over $p : \operatorname{Fin} k$ and
$j \notin \operatorname{range}(\phi)$. -/
def RVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} (P₂ : Fin k → Graph α β) (φ : Fin D₁.r → Fin D₂.r) : Set α :=
  ⋃ (p : Fin k) (j : Fin D₂.r) (_ : j ∉ range φ), V(P₂ p ⊓ D₂.G j)

/-- Edge set of $R$: union of $E(P_2(p) \sqcap D_2.G(j))$ over $p : \operatorname{Fin} k$ and
$j \notin \operatorname{range}(\phi)$. -/
def REdges {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} (P₂ : Fin k → Graph α β) (φ : Fin D₁.r → Fin D₂.r) : Set β :=
  ⋃ (p : Fin k) (j : Fin D₂.r) (_ : j ∉ range φ), E(P₂ p ⊓ D₂.G j)

theorem QVerts_subset_V {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n)) :
    QVerts D₁ ηv ⊆ V(X₂.G) := by
  rintro x ⟨_, ⟨n, rfl⟩, _, ⟨v, rfl⟩, _, ⟨hv, rfl⟩, hx⟩
  exact (D₂.le_G (φ n)).vertexSet_mono ((hsim n).1.vertex_subset v hv hx)

theorem RVerts_subset_V {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} (P₂ : Fin k → Graph α β) (φ : Fin D₁.r → Fin D₂.r) :
    RVerts D₁ D₂ P₂ φ ⊆ V(X₂.G) := by
  rintro x ⟨_, ⟨p, rfl⟩, _, ⟨j, rfl⟩, _, ⟨_, rfl⟩, hx⟩
  exact (D₂.le_G j).vertexSet_mono hx.2

theorem QEdges_endpoints_in_QVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))
    ⦃e : β⦄ ⦃x y : α⦄
    (he : e ∈ QEdges D₁ D₂ cd₁ cd₂ φ ηv ηe hsim) (hl : X₂.G.IsLink e x y) :
    x ∈ QVerts D₁ ηv ∧ y ∈ QVerts D₁ ηv := by
  simp only [QEdges, mem_iUnion] at he
  obtain ⟨n, v, hv, heK⟩ := he
  have hK_le : simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv ≤ X₂.G :=
    (simSubgraph_le D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv).trans
      (deleteEdges_le.trans (D₂.le_G (φ n)))
  have hlK := (hK_le.isLink_iff heK).mpr hl
  have hx : x ∈ ηv n v := by
    rw [← simSubgraph_vertexSet D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv]
    exact hlK.left_mem
  have hy : y ∈ ηv n v := by
    rw [← simSubgraph_vertexSet D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv]
    exact hlK.right_mem
  exact ⟨mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, hx⟩⟩⟩,
    mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, hy⟩⟩⟩⟩

theorem REdges_endpoints_in_RVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} (P₂ : Fin k → Graph α β) (φ : Fin D₁.r → Fin D₂.r)
    ⦃e : β⦄ ⦃x y : α⦄
    (he : e ∈ REdges D₁ D₂ P₂ φ) (hl : X₂.G.IsLink e x y) :
    x ∈ RVerts D₁ D₂ P₂ φ ∧ y ∈ RVerts D₁ D₂ P₂ φ := by
  simp only [REdges, mem_iUnion, exists_prop] at he
  obtain ⟨p, j, hj, hePJ⟩ := he
  have hPJ_le : P₂ p ⊓ D₂.G j ≤ X₂.G := inf_le_right.trans (D₂.le_G j)
  have hlPJ := (hPJ_le.isLink_iff hePJ).mpr hl
  exact ⟨mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hlPJ.left_mem⟩⟩⟩,
    mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hlPJ.right_mem⟩⟩⟩⟩

/-- The subgraph $G = Q \cup R \le X_2.G$ in the proof of (14.2) (page 277). -/
def unionGraphG {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n)) :
    Graph α β :=
  subgraphOfVertsEdges X₂.G
    (QVerts D₁ ηv ∪ RVerts D₁ D₂ P₂ φ)
    (QEdges D₁ D₂ cd₁ cd₂ φ ηv ηe hsim ∪ REdges D₁ D₂ P₂ φ)
    (union_subset (QVerts_subset_V D₁ D₂ cd₁ cd₂ φ ηv ηe hsim) (RVerts_subset_V D₁ D₂ P₂ φ))
    (fun _ _ _ he hl => by
      rcases he with heQ | heR
      · obtain ⟨hx, hy⟩ := QEdges_endpoints_in_QVerts D₁ D₂ cd₁ cd₂ φ ηv ηe hsim heQ hl
        exact ⟨Or.inl hx, Or.inl hy⟩
      · obtain ⟨hx, hy⟩ := REdges_endpoints_in_RVerts D₁ D₂ P₂ φ heR hl
        exact ⟨Or.inr hx, Or.inr hy⟩)

/-- Vertex assignment relation on $V(G)$: a vertex $z \in V(G)$ is assigned to $u \in V(X_1.G)$ if
either $z \in \eta_{v,m}(u)$ for some $m : \operatorname{Fin} D_1.r$ with $u \in V(D_1.G\ m)$, or
$z \in V(P_2(p) \sqcap D_2.G(j))$ for some $p : \operatorname{Fin} k$ and $j \notin \operatorname{range}(\phi)$,
where $u = y_1(0, p)$ if $j < \phi(0)$ and $u = y_1(m.\text{succ}, p)$ for the greatest $m$ with
$\phi(m) < j$ otherwise. -/
def VertexAssignedTo {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (P₂ : Fin k → Graph α β)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (z u : α) : Prop :=
  (∃ m : Fin D₁.r, u ∈ V(D₁.G m) ∧ z ∈ ηv m u) ∨
  (∃ (p : Fin k) (j : Fin D₂.r), j ∉ range φ ∧ z ∈ V(P₂ p ⊓ D₂.G j) ∧
    ((j < φ ⟨0, D₁.hr⟩ ∧ u = cd₁.y (⟨0, D₁.hr⟩ : Fin D₁.r).castSucc p) ∨
     (∃ m : Fin D₁.r, φ m < j ∧ (∀ l : Fin D₁.r, m < l → j < φ l) ∧ u = cd₁.y m.succ p)))

/-- The vertex simulation map $\sigma(v)$ in the proof of (14.2) (page 278): the vertex set of the
component of $G = Q \cup R$ realizing $v \in V(X_1.G)$. -/
def chainSimVerts {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ X₂ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (D₂ : GraftPathDecomposition 𝒜 X₂)
    {k : ℕ} {P₁ P₂ : Fin k → Graph α β}
    (cd₁ : KChainCutData D₁ k P₁) (cd₂ : KChainCutData D₂ k P₂)
    (φ : Fin D₁.r → Fin D₂.r) (ηv : Fin D₁.r → α → Set α) (ηe : Fin D₁.r → β → β)
    (hsim : ∀ n : Fin D₁.r,
      IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))
    (v : α) : Set α :=
  {z ∈ V(unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim) |
    ∃ m : Fin D₁.r, v ∈ V(D₁.G m) ∧
      ∃ x ∈ ηv m v,
        Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj z x}

open Classical in
/-- The edge simulation map $\sigma(e)$ in the proof of (14.2) (page 278): $\sigma_n(e)$ where
$e \in E(D_1.G\ n)$. -/
noncomputable def chainSimEdges {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {X₁ : Graft α β}
    (D₁ : GraftPathDecomposition 𝒜 X₁) (ηe : Fin D₁.r → β → β) (e : β) : β :=
  if h : ∃ n : Fin D₁.r, e ∈ E(D₁.G n) then ηe (Classical.choose h) e else e

section ChainSimulation

variable {α : Type u} {β : Type v}
  {𝒜 : Set (Graft α β)}
  {X₁ X₂ : Graft α β}
  (D₁ : GraftPathDecomposition 𝒜 X₁)
  (D₂ : GraftPathDecomposition 𝒜 X₂)
  {k : ℕ}
  {P₁ P₂ : Fin k → Graph α β}
  (cd₁ : KChainCutData D₁ k P₁)
  (cd₂ : KChainCutData D₂ k P₂)
  (φ : Fin D₁.r → Fin D₂.r)
  (hφ_mono : StrictMono φ)
  (ηv : Fin D₁.r → α → Set α)
  (ηe : Fin D₁.r → β → β)
  (hsim : ∀ n : Fin D₁.r,
    IsRootedGraphSimulation (cd₁.partRootedGraph n) (cd₂.partRootedGraph (φ n)) (ηv n) (ηe n))

include hsim in
/-- Root condition for the first $k$ roots: `cd₂.y (φ n).castSucc p ∈ ηv n (cd₁.y n.castSucc p)`. -/
theorem root_mem_eta_castSucc (n : Fin D₁.r) (p : Fin k) :
    cd₂.y (φ n).castSucc p ∈ ηv n (cd₁.y n.castSucc p) := by
  obtain ⟨_, hlen, hmem, _⟩ := hsim n
  have hp_len2 : p.1 < (kChainPartRootList cd₂.y (φ n)).length := by
    simp [kChainPartRootList_length]; omega
  have hp_len1 : p.1 < (kChainPartRootList cd₁.y n).length := by
    simp [kChainPartRootList_length]; omega
  have h := hmem ⟨p.1, hp_len2⟩
  change (kChainPartRootList cd₂.y (φ n))[p.1]'hp_len2 ∈
    ηv n ((kChainPartRootList cd₁.y n)[p.1]'hp_len1) at h
  rwa [kChainPartRootList_getElem_left, kChainPartRootList_getElem_left] at h

include hsim in
/-- Root condition for the last $k$ roots: `cd₂.y (φ n).succ p ∈ ηv n (cd₁.y n.succ p)`. -/
theorem root_mem_eta_succ (n : Fin D₁.r) (p : Fin k) :
    cd₂.y (φ n).succ p ∈ ηv n (cd₁.y n.succ p) := by
  obtain ⟨_, hlen, hmem, _⟩ := hsim n
  have hp_len2 : p.1 + k < (kChainPartRootList cd₂.y (φ n)).length := by
    simp [kChainPartRootList_length]; omega
  have hp_len1 : p.1 + k < (kChainPartRootList cd₁.y n).length := by
    simp [kChainPartRootList_length]; omega
  have h := hmem ⟨p.1 + k, hp_len2⟩
  change (kChainPartRootList cd₂.y (φ n))[p.1 + k]'hp_len2 ∈
    ηv n ((kChainPartRootList cd₁.y n)[p.1 + k]'hp_len1) at h
  rwa [kChainPartRootList_getElem_right, kChainPartRootList_getElem_right] at h

include hsim in
/-- If `u ∈ V(D₁.G n)` and `cd₂.y (φ n).castSucc p ∈ ηv n u`, then `u = cd₁.y n.castSucc p`. -/
theorem eq_y_castSucc_of_mem_eta {n : Fin D₁.r} {u : α} (hu : u ∈ V(D₁.G n))
    {p : Fin k} (hx : cd₂.y (φ n).castSucc p ∈ ηv n u) :
    u = cd₁.y n.castSucc p := by
  by_contra hne
  have hdisj := (hsim n).1.vertex_disjoint u hu (cd₁.y n.castSucc p)
    (cd₁.y_mem_G_castSucc n p) hne
  exact hdisj.notMem_of_mem_left hx (root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n p)

include hsim in
/-- If `u ∈ V(D₁.G n)` and `cd₂.y (φ n).succ p ∈ ηv n u`, then `u = cd₁.y n.succ p`. -/
theorem eq_y_succ_of_mem_eta {n : Fin D₁.r} {u : α} (hu : u ∈ V(D₁.G n))
    {p : Fin k} (hx : cd₂.y (φ n).succ p ∈ ηv n u) :
    u = cd₁.y n.succ p := by
  by_contra hne
  have hdisj := (hsim n).1.vertex_disjoint u hu (cd₁.y n.succ p)
    (cd₁.y_mem_G_succ n p) hne
  exact hdisj.notMem_of_mem_left hx (root_mem_eta_succ D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n p)

include hφ_mono hsim in
/-- **Graph Minors VIII, (14.2) Claim (2)** (page 277):
"(2) *If $V(\sigma_m(u)) \cap V(\sigma_n(v)) \ne \emptyset$ then $u = v$.*" -/
theorem lemma_14_2_claim_2
    {m n : Fin D₁.r} {u v : α}
    (hu : u ∈ V(D₁.G m)) (hv : v ∈ V(D₁.G n))
    (hinter : (ηv m u ∩ ηv n v).Nonempty) :
    u = v := by
  have haux : ∀ {m n : Fin D₁.r} {u v : α},
      m ≤ n → u ∈ V(D₁.G m) → v ∈ V(D₁.G n) → (ηv m u ∩ ηv n v).Nonempty → u = v := by
    intro m n u v hmn hu hv ⟨x, hxm, hxn⟩
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · by_contra hne
      exact ((hsim m).1.vertex_disjoint u hu v hv hne).notMem_of_mem_left hxm hxn
    · have hxGm : x ∈ V(D₂.G (φ m)) := (hsim m).1.vertex_subset u hu hxm
      have hxGn : x ∈ V(D₂.G (φ n)) := (hsim n).1.vertex_subset v hv hxn
      have hφ_lt : φ m < φ n := hφ_mono hlt
      have hxYm : x ∈ D₂.Y (φ m).succ :=
        D₂.inter_subset_Y_succ (le_refl (φ m)) hφ_lt
          (by have := (φ n).2; change (φ m).1 + 1 < D₂.r; change (φ m).1 < (φ n).1 at hφ_lt; omega)
          ⟨hxGm, hxGn⟩
      obtain ⟨p, hp⟩ := cd₂.y_surj (φ m).succ x hxYm
      have hxP : x ∈ V(P₂ p) := hp ▸ cd₂.y_mem_P (φ m).succ p
      have hu_eq : u = cd₁.y m.succ p :=
        eq_y_succ_of_mem_eta D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hu (hp.symm ▸ hxm)
      have hv_eq : v = cd₁.y n.castSucc p := by
        have hxYn : x ∈ D₂.Y (φ n).castSucc :=
          D₂.inter_subset_Y_castSucc hφ_lt (le_refl (φ n)) ⟨hxGm, hxGn⟩
        have hx_yn : x = cd₂.y (φ n).castSucc p := cd₂.eq_y_of_mem_Y_inter_P hxYn hxP
        exact eq_y_castSucc_of_mem_eta D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hv (hx_yn ▸ hxn)
      have hmid : ∀ (l : Fin D₁.r), m < l → l < n → cd₁.y l.castSucc p = cd₁.y l.succ p := by
        intro l hml hln
        have hφml : φ m < φ l := hφ_mono hml
        have hφln : φ l < φ n := hφ_mono hln
        have hxYl_left : x ∈ D₂.Y (φ l).castSucc :=
          D₂.inter_subset_Y_castSucc hφml hφln.le ⟨hxGm, hxGn⟩
        have hxYl_right : x ∈ D₂.Y (φ l).succ :=
          D₂.inter_subset_Y_succ hφml.le hφln
            (by have := (φ n).2; change (φ l).1 + 1 < D₂.r; change (φ l).1 < (φ n).1 at hφln; omega)
            ⟨hxGm, hxGn⟩
        have hxl1 : x = cd₂.y (φ l).castSucc p := cd₂.eq_y_of_mem_Y_inter_P hxYl_left hxP
        have hxl2 : x = cd₂.y (φ l).succ p := cd₂.eq_y_of_mem_Y_inter_P hxYl_right hxP
        have hmem1 : x ∈ ηv l (cd₁.y l.castSucc p) :=
          hxl1.symm ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim l p
        exact eq_y_succ_of_mem_eta D₁ D₂ cd₁ cd₂ φ ηv ηe hsim
          (cd₁.y_mem_G_castSucc l p) (hxl2 ▸ hmem1)
      have hchain : ∀ (d : ℕ) (hd : m.1 + 1 + d ≤ n.1),
          cd₁.y m.succ p = cd₁.y ⟨m.1 + 1 + d, by have := n.2; omega⟩ p := by
        intro d
        induction d with
        | zero =>
          intro _
          rfl
        | succ d ih =>
          intro hd
          rw [ih (by omega)]
          let l : Fin D₁.r := ⟨m.1 + 1 + d, by have := n.2; omega⟩
          have hml : m < l := by change m.1 < m.1 + 1 + d; omega
          have hln : l < n := by change m.1 + 1 + d < n.1; omega
          exact hmid l hml hln
      rw [hu_eq, hv_eq]
      have hstep := hchain (n.1 - (m.1 + 1)) (by change m.1 < n.1 at hlt; omega)
      convert hstep using 2
      ext
      change n.1 = m.1 + 1 + (n.1 - (m.1 + 1))
      change m.1 < n.1 at hlt
      omega
  rcases le_or_gt m n with hmn | hnm
  · exact haux hmn hu hv hinter
  · exact (haux hnm.le hv hu (inter_comm (ηv m u) (ηv n v) ▸ hinter)).symm

include hsim in
theorem simSubgraph_le_unionGraphG (n : Fin D₁.r) (v : α) (hv : v ∈ V(D₁.G n)) :
    simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv ≤
      unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [simSubgraph_vertexSet D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv] at hx
    exact Or.inl (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, hx⟩⟩⟩)
  · intro e x y hlK
    have hK_le : simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv ≤ X₂.G :=
      (simSubgraph_le D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv).trans
        (deleteEdges_le.trans (D₂.le_G (φ n)))
    refine ⟨Or.inl ?_, hlK.mono hK_le⟩
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, hlK.edge_mem⟩⟩⟩

include hsim in
theorem reflTransGen_unionGraphG_of_mem_eta {n : Fin D₁.r} {v : α} (hv : v ∈ V(D₁.G n))
    {x y : α} (hx : x ∈ ηv n v) (hy : y ∈ ηv n v) :
    Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x y := by
  have hconn := (simSubgraph_connected D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv).2
  rw [simSubgraph_vertexSet D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv] at hconn
  have hwalk := hconn x hx y hy
  have hle := simSubgraph_le_unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n v hv
  clear hx hy hconn
  induction hwalk with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hadj ih =>
    obtain ⟨e, hl⟩ := hadj
    exact ih.tail ⟨e, hl.mono hle⟩

include hsim in
/-- Along any piece $j \notin \operatorname{range}(\phi)$, every vertex of $P_2(p) \sqcap D_2.G(j)$
is connected in $G = Q \cup R$ to both `cd₂.y j.castSucc p` and `cd₂.y j.succ p`. -/
theorem reflTransGen_unionGraphG_of_notMem_range
    {p : Fin k} {j : Fin D₂.r} (hj : j ∉ range φ)
    {s₁ s₂ : ℕ} (hs₁ : cd₂.c p j.castSucc ≤ s₁) (hs₁₂ : s₁ ≤ s₂)
    (hs₂ : s₂ ≤ cd₂.c p j.succ) :
    Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
      ((cd₂.wp p).verts[s₁]'(by have := cd₂.c_lt p j.succ; omega))
      ((cd₂.wp p).verts[s₂]'(by have := cd₂.c_lt p j.succ; omega)) := by
  have hc_lt := cd₂.c_lt p j.succ
  have hstep : ∀ (s : ℕ) (hs_ge : cd₂.c p j.castSucc ≤ s) (hs_lt : s < cd₂.c p j.succ),
      (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
        ((cd₂.wp p).verts[s]'(by omega)) ((cd₂.wp p).verts[s + 1]'(by omega)) := by
    intro s hs_ge hs_lt
    have hs_edges : s < (cd₂.wp p).edges.length := by
      have := (cd₂.wp p).length_verts; omega
    have hlP : (P₂ p).IsLink ((cd₂.wp p).edges[s]'hs_edges)
        ((cd₂.wp p).verts[s]'(by omega)) ((cd₂.wp p).verts[s + 1]'(by omega)) :=
      (cd₂.wp p).isLink_step s hs_edges
    have hlX : X₂.G.IsLink ((cd₂.wp p).edges[s]'hs_edges)
        ((cd₂.wp p).verts[s]'(by omega)) ((cd₂.wp p).verts[s + 1]'(by omega)) :=
      hlP.mono (cd₂.wp p).le_G
    have heJ : (cd₂.wp p).edges[s]'hs_edges ∈ E(D₂.G j) :=
      (cd₂.edges_mem_iff p j s hs_edges).mpr ⟨hs_ge, hs_lt⟩
    have hlJ : (D₂.G j).IsLink ((cd₂.wp p).edges[s]'hs_edges)
        ((cd₂.wp p).verts[s]'(by omega)) ((cd₂.wp p).verts[s + 1]'(by omega)) :=
      ((D₂.le_G j).isLink_iff heJ).mpr hlX
    have hlPJ : (P₂ p ⊓ D₂.G j).IsLink ((cd₂.wp p).edges[s]'hs_edges)
        ((cd₂.wp p).verts[s]'(by omega)) ((cd₂.wp p).verts[s + 1]'(by omega)) := by
      rw [inf_isLink]
      exact ⟨hlP, hlJ⟩
    refine ⟨(cd₂.wp p).edges[s]'hs_edges, Or.inr ?_, hlX⟩
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hlPJ.edge_mem⟩⟩⟩
  have hind : ∀ (d : ℕ) (hd : s₁ + d ≤ cd₂.c p j.succ),
      Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
        ((cd₂.wp p).verts[s₁]'(by omega))
        ((cd₂.wp p).verts[s₁ + d]'(by omega)) := by
    intro d
    induction d with
    | zero =>
      intro _
      exact Relation.ReflTransGen.refl
    | succ d ih =>
      intro hd
      exact (ih (by omega)).tail (hstep (s₁ + d) (by omega) (by omega))
  have h := hind (s₂ - s₁) (by omega)
  convert h using 2
  omega

include hsim in
/-- If no index $j \in \operatorname{range}(\phi)$ lies in $[a, b)$, then `cd₂.y a p` and
`cd₂.y b p` are connected in $G = Q \cup R$. -/
theorem reflTransGen_unionGraphG_y_range {p : Fin k}
    {a b : Fin (D₂.r + 1)} (hab : a ≤ b)
    (hgap : ∀ j : Fin D₂.r, a.1 ≤ j.1 → j.1 < b.1 → j ∉ range φ) :
    Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
      (cd₂.y a p) (cd₂.y b p) := by
  have hind : ∀ (d : ℕ) (hd : a.1 + d ≤ b.1),
      Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
        (cd₂.y a p) (cd₂.y ⟨a.1 + d, by have := b.2; omega⟩ p) := by
    intro d
    induction d with
    | zero =>
      intro _
      exact Relation.ReflTransGen.refl
    | succ d ih =>
      intro hd
      let j : Fin D₂.r := ⟨a.1 + d, by have := b.2; omega⟩
      have hj : j ∉ range φ := hgap j (by dsimp [j]; omega) (by dsimp [j]; omega)
      have hstep := reflTransGen_unionGraphG_of_notMem_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hj
        (le_refl (cd₂.c p j.castSucc))
        (cd₂.c_mono p (Fin.castSucc_le_succ j))
        (le_refl (cd₂.c p j.succ))
      exact (ih (by omega)).trans hstep
  have h := hind (b.1 - a.1) (by change a.1 ≤ b.1 at hab; omega)
  convert h using 2
  ext
  change b.1 = a.1 + (b.1 - a.1)
  change a.1 ≤ b.1 at hab
  omega

theorem reflTransGen_symm {G : Graph α β} {x y : α}
    (h : Relation.ReflTransGen G.Adj x y) :
    Relation.ReflTransGen G.Adj y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hadj ih => exact (Relation.ReflTransGen.single hadj.symm).trans ih

/-- Every index $j \notin \operatorname{range}(\phi)$ either satisfies $j < \phi(0)$ or has a
greatest index $m : \operatorname{Fin} D_1.r$ such that $\phi(m) < j$. -/
theorem lt_phi_zero_or_exists_max_phi_lt (j : Fin D₂.r) (hj : j ∉ range φ) :
    (j < φ ⟨0, D₁.hr⟩) ∨
      ∃ m : Fin D₁.r, φ m < j ∧ ∀ l : Fin D₁.r, m < l → j < φ l := by
  by_cases hj0 : j < φ ⟨0, D₁.hr⟩
  · exact Or.inl hj0
  · right
    have hj0' : φ ⟨0, D₁.hr⟩ < j :=
      lt_of_le_of_ne (not_lt.mp hj0) (fun heq => hj ⟨⟨0, D₁.hr⟩, heq⟩)
    have haux : ∀ (d : ℕ) (hd : d < D₁.r),
        φ ⟨0, D₁.hr⟩ < j →
        ∃ m : Fin D₁.r, m.1 ≤ d ∧ φ m < j ∧
          ∀ l : Fin D₁.r, l.1 ≤ d → m < l → j < φ l := by
      intro d
      induction d with
      | zero =>
        intro _ h0
        refine ⟨⟨0, D₁.hr⟩, le_refl 0, h0, fun l hl hlt => ?_⟩
        change 0 < l.1 at hlt
        omega
      | succ d ih =>
        intro hd h0
        by_cases hsucc : φ ⟨d + 1, hd⟩ < j
        · refine ⟨⟨d + 1, hd⟩, le_refl _, hsucc, fun l hl hlt => ?_⟩
          change d + 1 < l.1 at hlt
          omega
        · have hsucc' : j < φ ⟨d + 1, hd⟩ :=
            lt_of_le_of_ne (not_lt.mp hsucc) (fun heq => hj ⟨⟨d + 1, hd⟩, heq.symm⟩)
          obtain ⟨m, hmd, hmj, hmax⟩ := ih (by omega) h0
          refine ⟨m, by omega, hmj, fun l hl hlt => ?_⟩
          rcases eq_or_lt_of_le hl with hld | hld
          · have hl_eq : l = ⟨d + 1, hd⟩ := Fin.ext hld
            exact hl_eq ▸ hsucc'
          · exact hmax l (Nat.le_of_lt_succ hld) hlt
    have hhr := D₁.hr
    obtain ⟨m, _, hmj, hmax⟩ := haux (D₁.r - 1) (by omega) hj0'
    exact ⟨m, hmj, fun l hml => hmax l (by have := l.2; omega) hml⟩

include hφ_mono hsim in
/-- **Graph Minors VIII, (14.2) Claim (1)** (page 277):
"(1) *Every component of $G$ realizes some vertex of $V(G^h)$.*" -/
theorem lemma_14_2_claim_1
    {x : α} (hx : x ∈ V(unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim)) :
    ∃ (n : Fin D₁.r) (v : α), v ∈ V(D₁.G n) ∧
      ∃ z ∈ ηv n v, Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x z := by
  rcases hx with hxQ | hxR
  · simp only [QVerts, mem_iUnion] at hxQ
    obtain ⟨n, v, hv, hx_eta⟩ := hxQ
    exact ⟨n, v, hv, x, hx_eta, Relation.ReflTransGen.refl⟩
  · simp only [RVerts, mem_iUnion, exists_prop] at hxR
    obtain ⟨p, j, hj, hxP, hxJ⟩ := hxR
    have hx_verts : x ∈ {w | w ∈ (cd₂.wp p).verts} := by
      rw [← (cd₂.wp p).vertexSet_eq]
      exact hxP
    rw [mem_ofPred_eq, List.mem_iff_getElem] at hx_verts
    obtain ⟨s, hs, rfl⟩ := hx_verts
    obtain ⟨hs_ge, hs_le⟩ := (cd₂.verts_mem_iff p j s hs).mp hxJ
    rcases lt_phi_zero_or_exists_max_phi_lt D₁ D₂ φ j hj with hj0 | ⟨m, hmj, hmax⟩
    · let n₀ : Fin D₁.r := ⟨0, D₁.hr⟩
      have hconn1 : Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
          ((cd₂.wp p).verts[s]'hs) (cd₂.y j.succ p) :=
        reflTransGen_unionGraphG_of_notMem_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hj
          hs_ge hs_le (le_refl _)
      have hconn2 : Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
          (cd₂.y j.succ p) (cd₂.y (φ n₀).castSucc p) := by
        apply reflTransGen_unionGraphG_y_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim (Nat.succ_le_of_lt hj0)
        intro l hlj hl0 ⟨n, hnl⟩
        subst hnl
        have hn0 : n₀ ≤ n := Nat.zero_le n.1
        have hle : (φ n₀).1 ≤ (φ n).1 := hφ_mono.monotone hn0
        change (φ n).1 < (φ n₀).1 at hl0
        omega
      refine ⟨n₀, cd₁.y n₀.castSucc p, cd₁.y_mem_G_castSucc n₀ p,
        cd₂.y (φ n₀).castSucc p,
        root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n₀ p,
        hconn1.trans hconn2⟩
    · have hconn1 : Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
          ((cd₂.wp p).verts[s]'hs) (cd₂.y j.castSucc p) :=
        reflTransGen_symm (reflTransGen_unionGraphG_of_notMem_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hj
          (le_refl _) hs_ge hs_le)
      have hconn2 : Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
          (cd₂.y j.castSucc p) (cd₂.y (φ m).succ p) := by
        apply reflTransGen_symm
        apply reflTransGen_unionGraphG_y_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim (Nat.succ_le_of_lt hmj)
        intro l hml hlj ⟨n, hnl⟩
        subst hnl
        rcases le_or_gt n m with hnm | hmn
        · have hle : (φ n).1 ≤ (φ m).1 := hφ_mono.monotone hnm
          change (φ m).1 + 1 ≤ (φ n).1 at hml
          omega
        · have hgt : j < φ n := hmax n hmn
          change (φ n).1 < j.1 at hlj
          change j.1 < (φ n).1 at hgt
          omega
      refine ⟨m, cd₁.y m.succ p, cd₁.y_mem_G_succ m p,
        cd₂.y (φ m).succ p,
        root_mem_eta_succ D₁ D₂ cd₁ cd₂ φ ηv ηe hsim m p,
        hconn1.trans hconn2⟩

include hφ_mono hsim in
/-- If $z \in V(P_2(p) \sqcap D_2.G(j))$ with $j \notin \operatorname{range}(\phi)$ and
$z \in \eta_{v,m}(u)$ with $u \in V(D_1.G\ m)$, then $u$ equals the gap vertex of $(p, j)$. -/
theorem vertexAssignedTo_Q_R_agree
    {z u₁ u₂ : α} {m : Fin D₁.r} (hu₁ : u₁ ∈ V(D₁.G m)) (hzQ : z ∈ ηv m u₁)
    {p : Fin k} {j : Fin D₂.r} (_hj : j ∉ range φ) (hzR : z ∈ V(P₂ p ⊓ D₂.G j))
    (hu₂ : (j < φ ⟨0, D₁.hr⟩ ∧ u₂ = cd₁.y (⟨0, D₁.hr⟩ : Fin D₁.r).castSucc p) ∨
      (∃ n : Fin D₁.r, φ n < j ∧ (∀ l : Fin D₁.r, n < l → j < φ l) ∧ u₂ = cd₁.y n.succ p)) :
    u₁ = u₂ := by
  have hzGm : z ∈ V(D₂.G (φ m)) := (hsim m).1.vertex_subset u₁ hu₁ hzQ
  have hzP : z ∈ V(P₂ p) := hzR.1
  have hzJ : z ∈ V(D₂.G j) := hzR.2
  rcases hu₂ with ⟨hj0, rfl⟩ | ⟨n, hnj, hmax, rfl⟩
  · let n₀ : Fin D₁.r := ⟨0, D₁.hr⟩
    have hφ0_le : φ n₀ ≤ φ m := hφ_mono.monotone (Nat.zero_le m.1)
    have hzY0 : z ∈ D₂.Y (φ n₀).castSucc :=
      D₂.inter_subset_Y_castSucc hj0 hφ0_le ⟨hzJ, hzGm⟩
    have hz_eq : z = cd₂.y (φ n₀).castSucc p := cd₂.eq_y_of_mem_Y_inter_P hzY0 hzP
    have hz_n0 : z ∈ ηv n₀ (cd₁.y n₀.castSucc p) :=
      hz_eq.symm ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n₀ p
    exact lemma_14_2_claim_2 D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
      hu₁ (cd₁.y_mem_G_castSucc n₀ p) ⟨z, hzQ, hz_n0⟩
  · rcases le_or_gt m n with hmn | hnm
    · have hφ_le : φ m ≤ φ n := hφ_mono.monotone hmn
      have hzYn : z ∈ D₂.Y (φ n).succ :=
        D₂.inter_subset_Y_succ hφ_le hnj
          (by have := j.2; change (φ n).1 + 1 < D₂.r; change (φ n).1 < j.1 at hnj; omega)
          ⟨hzGm, hzJ⟩
      have hz_eq : z = cd₂.y (φ n).succ p := cd₂.eq_y_of_mem_Y_inter_P hzYn hzP
      have hz_n : z ∈ ηv n (cd₁.y n.succ p) :=
        hz_eq.symm ▸ root_mem_eta_succ D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n p
      exact lemma_14_2_claim_2 D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
        hu₁ (cd₁.y_mem_G_succ n p) ⟨z, hzQ, hz_n⟩
    · let n₁ : Fin D₁.r := ⟨n.1 + 1, by have := m.2; change n.1 < m.1 at hnm; omega⟩
      have hn_lt_n1 : n < n₁ := by change n.1 < n.1 + 1; omega
      have hjn1 : j < φ n₁ := hmax n₁ hn_lt_n1
      have hn1_le_m : n₁ ≤ m := by change n.1 + 1 ≤ m.1; exact hnm
      have hφn1_le : φ n₁ ≤ φ m := hφ_mono.monotone hn1_le_m
      have hzYn1 : z ∈ D₂.Y (φ n₁).castSucc :=
        D₂.inter_subset_Y_castSucc hjn1 hφn1_le ⟨hzJ, hzGm⟩
      have hz_eq : z = cd₂.y (φ n₁).castSucc p := cd₂.eq_y_of_mem_Y_inter_P hzYn1 hzP
      have hz_n1 : z ∈ ηv n₁ (cd₁.y n₁.castSucc p) :=
        hz_eq.symm ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n₁ p
      exact lemma_14_2_claim_2 D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
        hu₁ (cd₁.y_mem_G_castSucc n₁ p) ⟨z, hzQ, hz_n1⟩

include cd₂ hφ_mono hsim in
/-- Uniqueness of `VertexAssignedTo`: each vertex $z \in V(G)$ is assigned to at most one
$u \in V(X_1.G)$. -/
theorem vertexAssignedTo_unique {z u₁ u₂ : α}
    (h₁ : VertexAssignedTo D₁ D₂ cd₁ P₂ φ ηv z u₁)
    (h₂ : VertexAssignedTo D₁ D₂ cd₁ P₂ φ ηv z u₂) :
    u₁ = u₂ := by
  rcases h₁ with ⟨m₁, hu₁, hz₁⟩ | ⟨p₁, j₁, hj₁, hz₁, hcase₁⟩
  · rcases h₂ with ⟨m₂, hu₂, hz₂⟩ | ⟨p₂, j₂, hj₂, hz₂, hcase₂⟩
    · exact lemma_14_2_claim_2 D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
        hu₁ hu₂ ⟨z, hz₁, hz₂⟩
    · exact vertexAssignedTo_Q_R_agree D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
        hu₁ hz₁ hj₂ hz₂ hcase₂
  · rcases h₂ with ⟨m₂, hu₂, hz₂⟩ | ⟨p₂, j₂, hj₂, hz₂, hcase₂⟩
    · exact (vertexAssignedTo_Q_R_agree D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
        hu₂ hz₂ hj₁ hz₁ hcase₁).symm
    · have hp : p₁ = p₂ := by
        by_contra hne
        exact (cd₂.P_disj p₁ p₂ hne).notMem_of_mem_left hz₁.1 hz₂.1
      subst hp
      have hcond_unique : ∀ {j : Fin D₂.r} {v₁ v₂ : α},
          ((j < φ ⟨0, D₁.hr⟩ ∧ v₁ = cd₁.y (⟨0, D₁.hr⟩ : Fin D₁.r).castSucc p₁) ∨
           (∃ m : Fin D₁.r, φ m < j ∧ (∀ l : Fin D₁.r, m < l → j < φ l) ∧ v₁ = cd₁.y m.succ p₁)) →
          ((j < φ ⟨0, D₁.hr⟩ ∧ v₂ = cd₁.y (⟨0, D₁.hr⟩ : Fin D₁.r).castSucc p₁) ∨
           (∃ m : Fin D₁.r, φ m < j ∧ (∀ l : Fin D₁.r, m < l → j < φ l) ∧ v₂ = cd₁.y m.succ p₁)) →
          v₁ = v₂ := by
        rintro j v₁ v₂ (⟨hj0, rfl⟩ | ⟨m₁, hm₁, hmax₁, rfl⟩) (⟨hj0', rfl⟩ | ⟨m₂, hm₂, hmax₂, rfl⟩)
        · rfl
        · exfalso
          have hle : φ ⟨0, D₁.hr⟩ ≤ φ m₂ := hφ_mono.monotone (Nat.zero_le m₂.1)
          exact not_lt_of_ge hle (lt_trans hm₂ hj0)
        · exfalso
          have hle : φ ⟨0, D₁.hr⟩ ≤ φ m₁ := hφ_mono.monotone (Nat.zero_le m₁.1)
          exact not_lt_of_ge hle (lt_trans hm₁ hj0')
        · have hm_eq : m₁ = m₂ := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · exact lt_irrefl j (lt_trans (hmax₁ m₂ hlt) hm₂)
            · exact lt_irrefl j (lt_trans (hmax₂ m₁ hgt) hm₁)
          rw [hm_eq]
      by_cases hgap : ∃ l : Fin D₁.r, (j₁ < φ l ∧ φ l < j₂) ∨ (j₂ < φ l ∧ φ l < j₁)
      · obtain ⟨l, ⟨hl1, hl2⟩ | ⟨hl1, hl2⟩⟩ := hgap
        · have hzYl : z ∈ D₂.Y (φ l).castSucc :=
            D₂.inter_subset_Y_castSucc hl1 hl2.le ⟨hz₁.2, hz₂.2⟩
          have hz_eq : z = cd₂.y (φ l).castSucc p₁ := cd₂.eq_y_of_mem_Y_inter_P hzYl hz₁.1
          have hzQ : z ∈ ηv l (cd₁.y l.castSucc p₁) :=
            hz_eq.symm ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim l p₁
          have h1 := vertexAssignedTo_Q_R_agree D₁ D₂ cd₁ cd₂ φ hφ_mono
            ηv ηe hsim (cd₁.y_mem_G_castSucc l p₁) hzQ hj₁ hz₁ hcase₁
          have h2 := vertexAssignedTo_Q_R_agree D₁ D₂ cd₁ cd₂ φ hφ_mono
            ηv ηe hsim (cd₁.y_mem_G_castSucc l p₁) hzQ hj₂ hz₂ hcase₂
          exact h1.symm.trans h2
        · have hzYl : z ∈ D₂.Y (φ l).castSucc :=
            D₂.inter_subset_Y_castSucc hl1 hl2.le ⟨hz₂.2, hz₁.2⟩
          have hz_eq : z = cd₂.y (φ l).castSucc p₁ := cd₂.eq_y_of_mem_Y_inter_P hzYl hz₁.1
          have hzQ : z ∈ ηv l (cd₁.y l.castSucc p₁) :=
            hz_eq.symm ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim l p₁
          have h1 := vertexAssignedTo_Q_R_agree D₁ D₂ cd₁ cd₂ φ hφ_mono
            ηv ηe hsim (cd₁.y_mem_G_castSucc l p₁) hzQ hj₁ hz₁ hcase₁
          have h2 := vertexAssignedTo_Q_R_agree D₁ D₂ cd₁ cd₂ φ hφ_mono
            ηv ηe hsim (cd₁.y_mem_G_castSucc l p₁) hzQ hj₂ hz₂ hcase₂
          exact h1.symm.trans h2
      · have hsame : ∀ l : Fin D₁.r, φ l < j₁ ↔ φ l < j₂ := by
          intro l
          constructor
          · intro hl1
            by_contra hnot
            have hl2 : j₂ < φ l := lt_of_le_of_ne (not_lt.mp hnot) (fun heq => hj₂ ⟨l, heq.symm⟩)
            exact hgap ⟨l, Or.inr ⟨hl2, hl1⟩⟩
          · intro hl2
            by_contra hnot
            have hl1 : j₁ < φ l := lt_of_le_of_ne (not_lt.mp hnot) (fun heq => hj₁ ⟨l, heq.symm⟩)
            exact hgap ⟨l, Or.inl ⟨hl1, hl2⟩⟩
        have hcase₂' : (j₁ < φ ⟨0, D₁.hr⟩ ∧ u₂ = cd₁.y (⟨0, D₁.hr⟩ : Fin D₁.r).castSucc p₁) ∨
            (∃ m : Fin D₁.r, φ m < j₁ ∧ (∀ l : Fin D₁.r, m < l → j₁ < φ l) ∧ u₂ = cd₁.y m.succ p₁) := by
          rcases hcase₂ with ⟨hj0, hu₂⟩ | ⟨m, hm, hmax, hu₂⟩
          · left
            refine ⟨?_, hu₂⟩
            by_contra hnot
            have hlt : φ ⟨0, D₁.hr⟩ < j₁ :=
              lt_of_le_of_ne (not_lt.mp hnot) (fun heq => hj₁ ⟨⟨0, D₁.hr⟩, heq⟩)
            exact lt_irrefl j₂ (lt_trans hj0 ((hsame ⟨0, D₁.hr⟩).mp hlt))
          · right
            refine ⟨m, (hsame m).mpr hm, fun l hml => ?_, hu₂⟩
            by_contra hnot
            have hlt : φ l < j₁ :=
              lt_of_le_of_ne (not_lt.mp hnot) (fun heq => hj₁ ⟨l, heq⟩)
            exact lt_irrefl j₂ (lt_trans (hmax l hml) ((hsame l).mp hlt))
        exact hcond_unique hcase₁ hcase₂'

include hsim in
/-- Every edge of $G = Q \cup R$ preserves `VertexAssignedTo`. -/
theorem vertexAssignedTo_of_adj {x y : α}
    (hadj : (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x y) :
    ∃ u : α,
      VertexAssignedTo D₁ D₂ cd₁ P₂ φ ηv x u ∧
      VertexAssignedTo D₁ D₂ cd₁ P₂ φ ηv y u := by
  obtain ⟨e, he, hlX⟩ := hadj
  rcases he with heQ | heR
  · simp only [QEdges, mem_iUnion] at heQ
    obtain ⟨m, u, hu, heK⟩ := heQ
    have hK_le : simSubgraph D₁ D₂ cd₁ cd₂ φ ηv ηe hsim m u hu ≤ X₂.G :=
      (simSubgraph_le D₁ D₂ cd₁ cd₂ φ ηv ηe hsim m u hu).trans
        (deleteEdges_le.trans (D₂.le_G (φ m)))
    have hlK := (hK_le.isLink_iff heK).mpr hlX
    have hx : x ∈ ηv m u := by
      rw [← simSubgraph_vertexSet D₁ D₂ cd₁ cd₂ φ ηv ηe hsim m u hu]
      exact hlK.left_mem
    have hy : y ∈ ηv m u := by
      rw [← simSubgraph_vertexSet D₁ D₂ cd₁ cd₂ φ ηv ηe hsim m u hu]
      exact hlK.right_mem
    exact ⟨u, Or.inl ⟨m, hu, hx⟩, Or.inl ⟨m, hu, hy⟩⟩
  · simp only [REdges, mem_iUnion, exists_prop] at heR
    obtain ⟨p, j, hj, hePJ⟩ := heR
    have hPJ_le : P₂ p ⊓ D₂.G j ≤ X₂.G := inf_le_right.trans (D₂.le_G j)
    have hlPJ := (hPJ_le.isLink_iff hePJ).mpr hlX
    rcases lt_phi_zero_or_exists_max_phi_lt D₁ D₂ φ j hj with hj0 | ⟨m, hmj, hmax⟩
    · refine ⟨cd₁.y (⟨0, D₁.hr⟩ : Fin D₁.r).castSucc p,
        Or.inr ⟨p, j, hj, hlPJ.left_mem, Or.inl ⟨hj0, rfl⟩⟩,
        Or.inr ⟨p, j, hj, hlPJ.right_mem, Or.inl ⟨hj0, rfl⟩⟩⟩
    · refine ⟨cd₁.y m.succ p,
        Or.inr ⟨p, j, hj, hlPJ.left_mem, Or.inr ⟨m, hmj, hmax, rfl⟩⟩,
        Or.inr ⟨p, j, hj, hlPJ.right_mem, Or.inr ⟨m, hmj, hmax, rfl⟩⟩⟩

include hφ_mono hsim in
/-- **Graph Minors VIII, (14.2) Claim (3)** (page 278):
"(3) *Every component of $G$ realizes a unique vertex of $V(G^h)$.*" -/
theorem lemma_14_2_claim_3
    {m n : Fin D₁.r} {u v : α}
    (hu : u ∈ V(D₁.G m)) (hv : v ∈ V(D₁.G n))
    {x y : α} (hx : x ∈ ηv m u) (hy : y ∈ ηv n v)
    (hconn : Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x y) :
    u = v := by
  have hwalk : ∀ {z : α},
      Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x z →
      VertexAssignedTo D₁ D₂ cd₁ P₂ φ ηv z u := by
    intro z hxz
    induction hxz with
    | refl => exact Or.inl ⟨m, hu, hx⟩
    | tail _ hadj ih =>
      obtain ⟨w, hwu, hwz⟩ := vertexAssignedTo_of_adj D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hadj
      have hweq : w = u :=
        vertexAssignedTo_unique D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim hwu ih
      exact hweq ▸ hwz
  exact vertexAssignedTo_unique D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim
    (hwalk hconn) (Or.inl ⟨n, hv, hy⟩)

include hφ_mono hsim in
/-- **Graph Minors VIII, (14.2) Claim (4)** (page 278):
"(4) *Every vertex of $V(G^h)$ is realized by a unique component of $G$.*" -/
theorem lemma_14_2_claim_4
    {m n : Fin D₁.r} {v : α}
    (hvm : v ∈ V(D₁.G m)) (hvn : v ∈ V(D₁.G n))
    {x y : α} (hx : x ∈ ηv m v) (hy : y ∈ ηv n v) :
    Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x y := by
  have hstep : ∀ (l : Fin D₁.r) (hl : l.1 + 1 < D₁.r),
      v ∈ V(D₁.G l) → v ∈ V(D₁.G ⟨l.1 + 1, hl⟩) →
      ∀ {x₁ y₁ : α}, x₁ ∈ ηv l v → y₁ ∈ ηv ⟨l.1 + 1, hl⟩ v →
      Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x₁ y₁ := by
    intro l hl hvl hvl₁ x₁ y₁ hx₁ hy₁
    let l₁ : Fin D₁.r := ⟨l.1 + 1, hl⟩
    have hvY : v ∈ D₁.Y l.succ := by
      rw [← D₁.adj_vertex_inter l hl]
      exact ⟨hvl, hvl₁⟩
    obtain ⟨p, hp⟩ := cd₁.y_surj l.succ v hvY
    have hp' : cd₁.y l₁.castSucc p = v := hp
    have hroot_l : cd₂.y (φ l).succ p ∈ ηv l v :=
      hp ▸ root_mem_eta_succ D₁ D₂ cd₁ cd₂ φ ηv ηe hsim l p
    have hroot_l1 : cd₂.y (φ l₁).castSucc p ∈ ηv l₁ v :=
      hp' ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim l₁ p
    have hconn_left :=
      reflTransGen_unionGraphG_of_mem_eta D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hvl hx₁ hroot_l
    have hconn_right :=
      reflTransGen_unionGraphG_of_mem_eta D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hvl₁ hroot_l1 hy₁
    have hφ_lt : φ l < φ l₁ := hφ_mono (by change l.1 < l.1 + 1; omega)
    have hconn_mid : Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj
        (cd₂.y (φ l).succ p) (cd₂.y (φ l₁).castSucc p) := by
      apply reflTransGen_unionGraphG_y_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim (Nat.succ_le_of_lt hφ_lt)
      intro j hjl hjl₁ ⟨q, hqj⟩
      subst hqj
      rcases le_or_gt q l with hql | hlq
      · have hle : (φ q).1 ≤ (φ l).1 := hφ_mono.monotone hql
        change (φ l).1 + 1 ≤ (φ q).1 at hjl
        omega
      · have hge : l₁ ≤ q := Nat.succ_le_of_lt hlq
        have hle : (φ l₁).1 ≤ (φ q).1 := hφ_mono.monotone hge
        change (φ q).1 < (φ l₁).1 at hjl₁
        omega
    exact (hconn_left.trans hconn_mid).trans hconn_right
  have haux : ∀ {a b : Fin D₁.r}, a ≤ b →
      v ∈ V(D₁.G a) → v ∈ V(D₁.G b) →
      ∀ {x₁ y₁ : α}, x₁ ∈ ηv a v → y₁ ∈ ηv b v →
      Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x₁ y₁ := by
    intro a b hab hva hvb x₁ y₁ hx₁ hy₁
    have hind : ∀ (d : ℕ) (hd : a.1 + d ≤ b.1),
        ∀ {y_d : α}, y_d ∈ ηv ⟨a.1 + d, by have := b.2; omega⟩ v →
        Relation.ReflTransGen (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj x₁ y_d := by
      intro d
      induction d with
      | zero =>
        intro _ y_d hy_d
        exact reflTransGen_unionGraphG_of_mem_eta D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hva hx₁ hy_d
      | succ d ih =>
        intro hd y_d hy_d
        let l : Fin D₁.r := ⟨a.1 + d, by have := b.2; omega⟩
        let l₁ : Fin D₁.r := ⟨a.1 + (d + 1), by have := b.2; omega⟩
        have hvl : v ∈ V(D₁.G l) :=
          D₁.vertex_inter_subset a l b (by change a.1 ≤ a.1 + d; omega) (by change a.1 + d ≤ b.1; omega)
            ⟨hva, hvb⟩
        have hvl₁ : v ∈ V(D₁.G l₁) :=
          D₁.vertex_inter_subset a l₁ b (by change a.1 ≤ a.1 + (d + 1); omega) hd ⟨hva, hvb⟩
        obtain ⟨z_l, hz_l⟩ := (hsim l).1.vertex_nonempty v hvl
        have h1 := ih (by omega) hz_l
        have h2 := hstep l (by have := b.2; change a.1 + d + 1 < D₁.r; omega) hvl hvl₁ hz_l hy_d
        exact h1.trans h2
    have hb_eq : (⟨a.1 + (b.1 - a.1), by have := b.2; change a.1 ≤ b.1 at hab; omega⟩ : Fin D₁.r) = b := by
      ext
      change a.1 + (b.1 - a.1) = b.1
      change a.1 ≤ b.1 at hab
      omega
    exact hind (b.1 - a.1) (by change a.1 ≤ b.1 at hab; omega) (hb_eq.symm ▸ hy₁)
  rcases le_or_gt m n with hmn | hnm
  · exact haux hmn hvm hvn hx hy
  · exact reflTransGen_symm (haux hnm.le hvn hvm hy hx)

/-! ## Assembling the simulation $\sigma$ of $(G^h, T^h)$ in $(G^i, T^i)$ -/

theorem chainSimEdges_eq_of_mem {n : Fin D₁.r} {e : β} (he : e ∈ E(D₁.G n)) :
    chainSimEdges D₁ ηe e = ηe n e := by
  have hex : ∃ m : Fin D₁.r, e ∈ E(D₁.G m) := ⟨n, he⟩
  unfold chainSimEdges
  simp only [hex, ↓reduceDIte]
  have hm : e ∈ E(D₁.G (Classical.choose hex)) := Classical.choose_spec hex
  have hmn : Classical.choose hex = n := by
    by_contra hne
    exact (D₁.edge_disjoint _ _ hne).notMem_of_mem_left hm he
  rw [hmn]

include hsim in
theorem subset_chainSimVerts_of_mem {n : Fin D₁.r} {v : α} (hv : v ∈ V(D₁.G n)) :
    ηv n v ⊆ chainSimVerts D₁ D₂ cd₁ cd₂ φ ηv ηe hsim v := by
  intro x hx
  have hxG : x ∈ V(unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim) :=
    Or.inl (mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, hx⟩⟩⟩)
  exact ⟨hxG, n, hv, x, hx, Relation.ReflTransGen.refl⟩

include hsim in
theorem chainSimVerts_closed_adj {v z w : α}
    (hz : z ∈ chainSimVerts D₁ D₂ cd₁ cd₂ φ ηv ηe hsim v)
    (hadj : (unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim).Adj z w) :
    w ∈ chainSimVerts D₁ D₂ cd₁ cd₂ φ ηv ηe hsim v := by
  obtain ⟨_, m, hvm, x, hx, hzx⟩ := hz
  obtain ⟨e, hlG⟩ := hadj
  exact ⟨hlG.right_mem, m, hvm, x, hx,
    (Relation.ReflTransGen.single ⟨e, hlG.symm⟩).trans hzx⟩

include hφ_mono hsim in
theorem unionGraphG_le_deleteEdges :
    unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim ≤
      X₂.G.deleteEdges (chainSimEdges D₁ ηe '' E(X₁.G)) := by
  refine ⟨(subgraphOfVertsEdges_le _ _ _ _ _).vertexSet_mono, ?_⟩
  intro e x y ⟨he, hlX⟩
  rw [deleteEdges_isLink]
  refine ⟨hlX, ?_⟩
  rintro ⟨e₀, he₀, rfl⟩
  obtain ⟨n, he₀_n⟩ := D₁.exists_mem_edgeSet he₀
  rw [chainSimEdges_eq_of_mem D₁ ηe he₀_n] at he
  have he_n : ηe n e₀ ∈ E(D₂.G (φ n)) := (hsim n).1.edge_mem e₀ he₀_n
  rcases he with heQ | heR
  · simp only [QEdges, mem_iUnion] at heQ
    obtain ⟨m, v, hv, heK⟩ := heQ
    have hK_le := simSubgraph_le D₁ D₂ cd₁ cd₂ φ ηv ηe hsim m v hv
    obtain ⟨xk, yk, hlK⟩ := exists_isLink_of_mem_edgeSet heK
    have hl_del := hlK.mono hK_le
    rw [deleteEdges_isLink] at hl_del
    have hmn : m = n := by
      by_contra hne
      have hφ_ne : φ m ≠ φ n := fun h => hne (hφ_mono.injective h)
      exact (D₂.edge_disjoint (φ m) (φ n) hφ_ne).notMem_of_mem_left hl_del.1.edge_mem he_n
    subst hmn
    exact hl_del.2 ⟨e₀, he₀_n, rfl⟩
  · simp only [REdges, mem_iUnion, exists_prop] at heR
    obtain ⟨p, j, hj, hePJ⟩ := heR
    have heJ : ηe n e₀ ∈ E(D₂.G j) := (inf_le_right : P₂ p ⊓ D₂.G j ≤ D₂.G j).edgeSet_mono hePJ
    have hjn : j ≠ φ n := fun h => hj ⟨n, h.symm⟩
    exact (D₂.edge_disjoint j (φ n) hjn).notMem_of_mem_left heJ he_n

private theorem left_mem_of_reflTransGen {G : Graph α β} {z w : α}
    (h : Relation.ReflTransGen G.Adj z w) (hw : w ∈ V(G)) : z ∈ V(G) := by
  induction h with
  | refl => exact hw
  | tail _ hadj ih => exact ih hadj.left_mem

include hφ_mono hsim in
/-- Given the setup of (14.2) with $|T^h| = |T^i|$, $(\sigma(v), \sigma(e))$ is a graft simulation
of $X_1$ in $X_2$. -/
theorem isGraftSimulatedIn_of_kChain_subseq
    (hT_card : X₂.T.ncard = X₁.T.ncard) :
    IsGraftSimulatedIn X₁ X₂ := by
  let G := unionGraphG D₁ D₂ cd₁ cd₂ φ ηv ηe hsim
  let ηv' := chainSimVerts D₁ D₂ cd₁ cd₂ φ ηv ηe hsim
  let ηe' := chainSimEdges D₁ ηe
  have hdisj_ηv' : ∀ v₁ ∈ V(X₁.G), ∀ v₂ ∈ V(X₁.G), v₁ ≠ v₂ → Disjoint (ηv' v₁) (ηv' v₂) := by
    intro v₁ _ v₂ _ hne
    rw [disjoint_left]
    rintro z ⟨_, m₁, hv₁m, x₁, hx₁, hzx₁⟩ ⟨_, m₂, hv₂m, x₂, hx₂, hzx₂⟩
    have hx₁x₂ : Relation.ReflTransGen G.Adj x₁ x₂ :=
      (reflTransGen_symm hzx₁).trans hzx₂
    exact hne (lemma_14_2_claim_3 D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim hv₁m hv₂m hx₁ hx₂ hx₁x₂)
  refine ⟨ηv', ηe', ?_, hT_card, ?_⟩
  · refine {
      vertex_nonempty := fun v hv => by
        obtain ⟨m, hvm⟩ := D₁.exists_mem_vertexSet hv
        obtain ⟨x, hx⟩ := (hsim m).1.vertex_nonempty v hvm
        exact ⟨x, subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hvm hx⟩
      vertex_subset := fun v _ z hz =>
        (subgraphOfVertsEdges_le _ _ _ _ _).vertexSet_mono hz.1
      edge_mem := fun e he => by
        obtain ⟨n, hen⟩ := D₁.exists_mem_edgeSet he
        dsimp only [ηe']
        rw [chainSimEdges_eq_of_mem D₁ ηe hen]
        exact (D₂.le_G (φ n)).edgeSet_mono ((hsim n).1.edge_mem e hen)
      vertex_disjoint := hdisj_ηv'
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        obtain ⟨n₁, hen₁⟩ := D₁.exists_mem_edgeSet he₁
        obtain ⟨n₂, hen₂⟩ := D₁.exists_mem_edgeSet he₂
        dsimp only [ηe'] at heq
        rw [chainSimEdges_eq_of_mem D₁ ηe hen₁, chainSimEdges_eq_of_mem D₁ ηe hen₂] at heq
        have hm₁ := (hsim n₁).1.edge_mem e₁ hen₁
        have hm₂ := (hsim n₂).1.edge_mem e₂ hen₂
        have hn : n₁ = n₂ := by
          by_contra hne
          have hφ_ne : φ n₁ ≠ φ n₂ := fun h => hne (hφ_mono.injective h)
          exact (D₂.edge_disjoint (φ n₁) (φ n₂) hφ_ne).notMem_of_mem_left hm₁ (heq ▸ hm₂)
        subst hn
        exact (hsim n₁).1.edge_injOn hen₁ hen₂ heq
      inc_iff := fun v hv e he => by
        obtain ⟨n, hen⟩ := D₁.exists_mem_edgeSet he
        dsimp only [ηe']
        rw [chainSimEdges_eq_of_mem D₁ ηe hen]
        have he_φn := (hsim n).1.edge_mem e hen
        constructor
        · intro hinc
          have hinc_n : (D₁.G n).Inc e v := ((D₁.le_G n).inc_congr hen).mpr hinc
          obtain ⟨x, hx, hinc_x⟩ :=
            ((hsim n).1.inc_iff v hinc_n.vertex_mem e hen).1 hinc_n
          exact ⟨x, subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hinc_n.vertex_mem hx,
            hinc_x.mono (D₂.le_G (φ n))⟩
        · rintro ⟨x, hx_v, hinc_x⟩
          have hinc_φn : (D₂.G (φ n)).Inc (ηe n e) x :=
            ((D₂.le_G (φ n)).inc_congr he_φn).mpr hinc_x
          obtain ⟨u, hu_n, hinc_u, hx_u⟩ :=
            exists_inc_and_mem_eta_of_inc (hsim n).1 hen hinc_φn
          have hx_u' : x ∈ ηv' u :=
            subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hu_n hx_u
          have huv : u = v := by
            by_contra hne
            exact (hdisj_ηv' u ((D₁.le_G n).vertexSet_mono hu_n) v hv hne).notMem_of_mem_left
              hx_u' hx_v
          exact (huv ▸ hinc_u).mono (D₁.le_G n)
      isLoopAt_iff := fun v hv e he => by
        obtain ⟨n, hen⟩ := D₁.exists_mem_edgeSet he
        dsimp only [ηe']
        rw [chainSimEdges_eq_of_mem D₁ ηe hen]
        have he_φn := (hsim n).1.edge_mem e hen
        constructor
        · intro hloop x hinc_x
          have hloop_n : (D₁.G n).IsLoopAt e v :=
            ((D₁.le_G n).isLoopAt_congr hen).mpr hloop
          have hinc_φn : (D₂.G (φ n)).Inc (ηe n e) x :=
            ((D₂.le_G (φ n)).inc_congr he_φn).mpr hinc_x
          have hx_n : x ∈ ηv n v :=
            ((hsim n).1.isLoopAt_iff v hloop_n.left_mem e hen).1 hloop_n x hinc_φn
          exact subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hloop_n.left_mem hx_n
        · intro hall
          obtain ⟨a, b, hl_n⟩ := exists_isLink_of_mem_edgeSet hen
          have hvn : v ∈ V(D₁.G n) := by
            obtain ⟨x, hx, hinc_x⟩ :=
              ((hsim n).1.inc_iff a hl_n.left_mem e hen).1 hl_n.inc_left
            have hx_v : x ∈ ηv' v := hall x (hinc_x.mono (D₂.le_G (φ n)))
            have hx_a : x ∈ ηv' a :=
              subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hl_n.left_mem hx
            have hav : a = v := by
              by_contra hne
              exact (hdisj_ηv' a ((D₁.le_G n).vertexSet_mono hl_n.left_mem) v hv hne).notMem_of_mem_left
                hx_a hx_v
            exact hav ▸ hl_n.left_mem
          have hloop_n : (D₁.G n).IsLoopAt e v := by
            change ((cd₁.partRootedGraph n).G).IsLoopAt e v
            rw [(hsim n).1.isLoopAt_iff v hvn e hen]
            intro x hinc_φn
            obtain ⟨u, hu_n, _, hx_u⟩ :=
              exists_inc_and_mem_eta_of_inc (hsim n).1 hen hinc_φn
            have hx_v : x ∈ ηv' v := hall x (hinc_φn.mono (D₂.le_G (φ n)))
            have hx_u' : x ∈ ηv' u :=
              subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hu_n hx_u
            have huv : u = v := by
              by_contra hne
              exact (hdisj_ηv' u ((D₁.le_G n).vertexSet_mono hu_n) v hv hne).notMem_of_mem_left
                hx_u' hx_v
            exact huv ▸ hx_u
          exact hloop_n.mono (D₁.le_G n)
      connected := fun v hv => by
        let Kv : Graph α β :=
          subgraphOfVertsEdges G (ηv' v) {e ∈ E(G) | ∃ x y, x ∈ ηv' v ∧ y ∈ ηv' v ∧ G.IsLink e x y}
            (fun _ hz => hz.1)
            (fun e x y ⟨_, x₀, y₀, hx₀, _, hl₀⟩ hl => by
              have hxy_eq := G.eq_or_eq_of_isLink_of_isLink hl hl₀
              have hx_mem : x ∈ ηv' v := by
                rcases hxy_eq with ⟨rfl, _⟩ | ⟨rfl, _⟩
                · exact hx₀
                · exact chainSimVerts_closed_adj D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hx₀ ⟨e, hl₀⟩
              exact ⟨hx_mem, chainSimVerts_closed_adj D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hx_mem ⟨e, hl⟩⟩)
        have hKv_le_G : Kv ≤ G := subgraphOfVertsEdges_le _ _ _ _ _
        have hwalk_Kv : ∀ {z w : α}, z ∈ ηv' v →
            Relation.ReflTransGen G.Adj z w → Relation.ReflTransGen Kv.Adj z w := by
          intro z w hz hzw
          induction hzw with
          | refl => exact Relation.ReflTransGen.refl
          | @tail b c hzb hadj ih =>
            have hb : b ∈ ηv' v := by
              clear hadj ih
              induction hzb with
              | refl => exact hz
              | tail _ hadj' ih' =>
                exact chainSimVerts_closed_adj D₁ D₂ cd₁ cd₂ φ ηv ηe hsim ih' hadj'
            have hc : c ∈ ηv' v :=
              chainSimVerts_closed_adj D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hb hadj
            obtain ⟨e, hlG⟩ := hadj
            have hadj_Kv : Kv.Adj b c :=
              ⟨e, ⟨hlG.edge_mem, b, c, hb, hc, hlG⟩, hlG⟩
            exact ih.tail hadj_Kv
        refine ⟨Kv, hKv_le_G.trans (unionGraphG_le_deleteEdges D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim),
          rfl, ?_⟩
        obtain ⟨m₀, hvm₀⟩ := D₁.exists_mem_vertexSet hv
        obtain ⟨x₀, hx₀⟩ := (hsim m₀).1.vertex_nonempty v hvm₀
        refine ⟨⟨x₀, subset_chainSimVerts_of_mem D₁ D₂ cd₁ cd₂ φ ηv ηe hsim hvm₀ hx₀⟩, ?_⟩
        intro z₁ hz₁ z₂ hz₂
        rcases hz₁ with ⟨hz₁G, m₁, hvm₁, x₁, hx₁, hz₁x₁⟩
        rcases hz₂ with ⟨_, m₂, hvm₂, x₂, hx₂, hz₂x₂⟩
        have hx₁x₂ := lemma_14_2_claim_4 D₁ D₂ cd₁ cd₂ φ hφ_mono ηv ηe hsim hvm₁ hvm₂ hx₁ hx₂
        have hz₁z₂ : Relation.ReflTransGen G.Adj z₁ z₂ :=
          (hz₁x₁.trans hx₁x₂).trans (reflTransGen_symm hz₂x₂)
        exact hwalk_Kv ⟨hz₁G, m₁, hvm₁, x₁, hx₁, hz₁x₁⟩ hz₁z₂ }
  · intro u hu
    rw [D₁.T_eq] at hu
    rcases hu with hu0 | hur
    · obtain ⟨p, hp⟩ := cd₁.y_surj ⟨0, Nat.zero_lt_succ D₁.r⟩ u hu0
      let n₀ : Fin D₁.r := ⟨0, D₁.hr⟩
      have hp' : cd₁.y n₀.castSucc p = u := hp
      let z := cd₂.y ⟨0, Nat.zero_lt_succ D₂.r⟩ p
      have hz_T : z ∈ X₂.T := by
        rw [D₂.T_eq]
        exact Or.inl (cd₂.y_mem_Y ⟨0, Nat.zero_lt_succ D₂.r⟩ p)
      have hroot : cd₂.y (φ n₀).castSucc p ∈ ηv n₀ u :=
        hp' ▸ root_mem_eta_castSucc D₁ D₂ cd₁ cd₂ φ ηv ηe hsim n₀ p
      have hconn : Relation.ReflTransGen G.Adj z (cd₂.y (φ n₀).castSucc p) := by
        apply reflTransGen_unionGraphG_y_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim
          (Nat.zero_le (φ n₀).1)
        intro j _ hj0 ⟨n, hnj⟩
        subst hnj
        have hle : (φ n₀).1 ≤ (φ n).1 := hφ_mono.monotone (Nat.zero_le n.1)
        change (φ n).1 < (φ n₀).1 at hj0
        omega
      have hz_G : z ∈ V(G) :=
        left_mem_of_reflTransGen hconn
          (Or.inl (mem_iUnion.mpr ⟨n₀, mem_iUnion.mpr ⟨u, mem_iUnion.mpr
            ⟨hp' ▸ cd₁.y_mem_G_castSucc n₀ p, hroot⟩⟩⟩))
      exact ⟨z, ⟨hz_G, n₀, hp' ▸ cd₁.y_mem_G_castSucc n₀ p,
        cd₂.y (φ n₀).castSucc p, hroot, hconn⟩, hz_T⟩
    · obtain ⟨p, hp⟩ := cd₁.y_surj (Fin.last D₁.r) u hur
      have hhr := D₁.hr
      let nL : Fin D₁.r := ⟨D₁.r - 1, by omega⟩
      have hnL_succ : nL.succ = Fin.last D₁.r := Fin.ext (by dsimp [nL]; omega)
      have hp' : cd₁.y nL.succ p = u := by rw [hnL_succ]; exact hp
      let z := cd₂.y (Fin.last D₂.r) p
      have hz_T : z ∈ X₂.T := by
        rw [D₂.T_eq]
        exact Or.inr (cd₂.y_mem_Y (Fin.last D₂.r) p)
      have hroot : cd₂.y (φ nL).succ p ∈ ηv nL u :=
        hp' ▸ root_mem_eta_succ D₁ D₂ cd₁ cd₂ φ ηv ηe hsim nL p
      have hconn : Relation.ReflTransGen G.Adj (cd₂.y (φ nL).succ p) z := by
        apply reflTransGen_unionGraphG_y_range D₁ D₂ cd₁ cd₂ φ ηv ηe hsim
          (Fin.le_last (φ nL).succ)
        intro j hjl _ ⟨n, hnj⟩
        subst hnj
        have hn_le : n ≤ nL := by change n.1 ≤ D₁.r - 1; have := n.2; omega
        have hle : (φ n).1 ≤ (φ nL).1 := hφ_mono.monotone hn_le
        change (φ nL).1 + 1 ≤ (φ n).1 at hjl
        omega
      have hconn' := reflTransGen_symm hconn
      have hz_G : z ∈ V(G) :=
        left_mem_of_reflTransGen hconn'
          (Or.inl (mem_iUnion.mpr ⟨nL, mem_iUnion.mpr ⟨u, mem_iUnion.mpr
            ⟨hp' ▸ cd₁.y_mem_G_succ nL p, hroot⟩⟩⟩))
      exact ⟨z, ⟨hz_G, nL, hp' ▸ cd₁.y_mem_G_succ nL p,
        cd₂.y (φ nL).succ p, hroot, hconn'⟩, hz_T⟩

end ChainSimulation

/-! ## Proof of (14.2) -/

/-- Every $k$-chain $X \in \text{kChainClass }\mathscr{A}\ k$ has index $|X.T| \le 2k$. -/
theorem index_le_two_mul_of_mem_kChainClass {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} {k : ℕ} {X : Graft α β} (hX : X ∈ kChainClass 𝒜 k) :
    X.index ≤ 2 * k := by
  obtain ⟨D, hY_card, _⟩ := hX
  change X.T.ncard ≤ 2 * k
  rw [D.T_eq]
  have hle := ncard_union_le (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r))
  rw [hY_card ⟨0, Nat.zero_lt_succ D.r⟩, hY_card (Fin.last D.r)] at hle
  omega

/-- **Graph Minors VIII, (14.2)** (pages 276–278):
"(14.2) *If $\mathscr{A}$ is well-rooted and $k \ge 0$ is an integer, the class of all $k$-chains
over $\mathscr{A}$ is well-rooted.*" -/
theorem theorem_14_2_proof {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) (k : ℕ) :
    IsWellRootedGraftClass (kChainClass 𝒜 k) := by
  intro X₀ hX₀
  let idxFin : ℕ → Fin (2 * k + 1) :=
    fun n => ⟨(X₀ n).index, Nat.lt_succ_of_le (index_le_two_mul_of_mem_kChainClass (hX₀ n))⟩
  obtain ⟨kFin, hkInf⟩ := Finite.exists_infinite_fiber idxFin
  have hkInf' : {n : ℕ | (X₀ n).index = kFin.1}.Infinite := by
    have heq : (idxFin ⁻¹' {kFin}) = {n : ℕ | (X₀ n).index = kFin.1} := by
      ext n
      exact Fin.ext_iff
    rw [← heq]
    exact Set.infinite_coe_iff.mp hkInf
  let ψ : ℕ → ℕ := Nat.nth (· ∈ {n : ℕ | (X₀ n).index = kFin.1})
  have hψ_mono : StrictMono ψ := Nat.nth_strictMono hkInf'
  have hψ_mem : ∀ n, (X₀ (ψ n)).index = kFin.1 := fun n => Nat.nth_mem_of_infinite hkInf' n
  let X : ℕ → Graft α β := fun n => X₀ (ψ n)
  have hX : ∀ n, X n ∈ kChainClass 𝒜 k := fun n => hX₀ (ψ n)
  have hX_idx : ∀ n, (X n).T.ncard = kFin.1 := hψ_mem
  have hD_ex : ∀ n, ∃ D : GraftPathDecomposition 𝒜 (X n),
      (∀ l : Fin (D.r + 1), (D.Y l).ncard = k) ∧
      HasDisjointGraphPathsFromTo (X n).G
        (D.Y ⟨0, Nat.zero_lt_succ D.r⟩) (D.Y (Fin.last D.r)) k :=
    fun n => (hX n)
  choose D hY_card hpaths using hD_ex
  choose P hP_path hP_disj using hpaths
  let cd := fun n => (D n).mkKChainCutData (hY_card n) (hP_path n) (hP_disj n)
  let ℬ : Set (RootedGraph α β) :=
    {M : RootedGraph α β | M.index = 2 * k ∧ M.toGraft ∈ 𝒜}
  have hℬ_wr : IsWellRootedRootedGraphClass ℬ :=
    theorem_4_3_proof h𝒜 ⟨2 * k, fun M hM => le_of_eq hM.1⟩ (fun M hM => hM.2)
  let B_sub := {M : RootedGraph α β | M ∈ ℬ}
  have hWQO_B : IsWellQuasiOrder (fun (M₁ M₂ : B_sub) => IsRootedGraphSimulatedIn M₁.1 M₂.1) := by
    refine ⟨⟨fun M => IsRootedGraphSimulatedIn.refl M.1,
      fun _ _ _ => IsRootedGraphSimulatedIn.trans⟩, ?_⟩
    intro q
    exact hℬ_wr (fun n => (q n).1) (fun n => (q n).2)
  have hWQO_seq := theorem_3_3_proof hWQO_B
  let partSub (n : ℕ) (j : Fin (D n).r) : B_sub :=
    ⟨(cd n).partRootedGraph j, by
      refine ⟨?_, ?_⟩
      · simp [RootedGraph.index, KChainCutData.partRootedGraph, kChainPartRootedGraph]
      · rw [(cd n).partRootedGraph_toGraft_eq j]
        exact (D n).mem_𝒜 j⟩
  obtain ⟨h, i, hhi, hsubseq⟩ := hWQO_seq.2 (fun n => List.ofFn (partSub n))
  obtain ⟨φ, hφ_mono, hφ_sim⟩ :=
    exists_strictMono_of_sublistForall₂_ofFn (partSub h) (partSub i) hsubseq
  have hφ_sim' : ∀ n : Fin (D h).r,
      IsRootedGraphSimulatedIn ((cd h).partRootedGraph n) ((cd i).partRootedGraph (φ n)) :=
    hφ_sim
  choose ηv ηe hsim using hφ_sim'
  have hT_card : (X i).T.ncard = (X h).T.ncard := by rw [hX_idx i, hX_idx h]
  have hsim_hi : IsGraftSimulatedIn (X h) (X i) :=
    isGraftSimulatedIn_of_kChain_subseq (D h) (D i) (cd h) (cd i) φ hφ_mono ηv ηe hsim hT_card
  exact ⟨ψ h, ψ i, hψ_mono hhi, hsim_hi⟩

end GraphMinor.GM08
