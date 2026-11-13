module

public import GraphMinor.GM08.Section7Grid
public import GraphMinor.GM01.Defs
import GraphMinor.GM01.Basic
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.Separate
import GraphMinor.GM12.Section3OneDiscComplement
import GraphMinor.Surface.CrossingProved

@[expose] public section

/-!
# Concentric Grid Frames and Separation from a Grid Minor Model (for GM VIII (7.1))

Given a minor model `IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe` of a `θ`-grid in a drawing
`D₀` on `SphereSurf = OnePoint EuclideanPlane`, this file lifts:
- arbitrary injective grid walks to simple walks of `D₀` (`liftGridSteps`),
- the concentric square perimeter frames `Q_k` (`2 * k + 4 ≤ θ`) to circuit subdrawings
  `frameCircuit hm k` satisfying `PairsCrossOn` on the four sides (`frameCircuit_pairsCrossOn`),
- and proves `not_same_disc_of_three_frames`: for `1 ≤ k` with `2 * (k + 1) + 4 ≤ θ`, the adjacent
  frames `frameCircuit hm (k - 1)` and `frameCircuit hm (k + 1)` cannot both lie in `discInt D`
  for any closed disc `D ⊆ SphereSurf` bounded by `(frameCircuit hm k).U`.
-/

namespace GraphMinor
namespace GM08

open Set Function Topology Graph SimpleGraph Surface GM11

/-!
## 1. Branch Walks and Model Edges of a Grid Minor Model
-/

theorem mem_gridGraph_V {θ : ℕ} (p : Fin θ × Fin θ) : p ∈ V(GM01.gridGraph θ) := by
  simp [GM01.gridGraph]

theorem gridGraph_isLink_of_adj {θ : ℕ} {p q : Fin θ × Fin θ}
    (hadj : (pathGraph θ □ pathGraph θ).Adj p q) :
    (GM01.gridGraph θ).IsLink s(p, q) p q := by
  rw [GM01.gridGraph, Graph.ofSimpleGraph_isLink]
  exact ⟨rfl, hadj⟩

/-- Any two vertices in the same branch set `ηv p` are joined by a simple walk of `D₀` whose
vertices all lie in `ηv p`. -/
theorem exists_branch_walk {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    (p : Fin θ × Fin θ) {x y : SphereSurf} (hx : x ∈ ηv p) (hy : y ∈ ηv p) :
    ∃ W : GraphWalk D₀.toGraph x y, W.IsSimple ∧ ∀ z ∈ W.support, z ∈ ηv p := by
  classical
  have hpV := mem_gridGraph_V p
  obtain ⟨K, hKle, hVK, hKconn⟩ := hm.connected p hpV
  have hxy : Relation.ReflTransGen K.Adj x y := hKconn.2 x (hVK ▸ hx) y (hVK ▸ hy)
  have hraw : ∀ {w : SphereSurf}, w ∈ V(K) → Relation.ReflTransGen K.Adj x w →
      ∃ W₀ : GraphWalk D₀.toGraph x w, ∀ z ∈ W₀.support, z ∈ V(K) := by
    intro w _ hrt
    induction hrt with
    | refl =>
      refine ⟨.nil (hm.vertex_subset p hpV hx), ?_⟩
      intro z hz
      simp only [GraphWalk.support_nil, List.mem_singleton] at hz
      exact hz ▸ hVK ▸ hx
    | @tail a b _ hab ih =>
      obtain ⟨e, hlK⟩ := hab
      obtain ⟨W₁, hW₁⟩ := ih hlK.left_mem
      have hlD : D₀.toGraph.IsLink e a b := ((deleteEdges_isLink _ _ _ _ _).mp (hlK.mono hKle)).1
      have hbD : b ∈ V(D₀.toGraph) := hlD.right_mem
      refine ⟨W₁.append (.cons hlD (.nil hbD)), ?_⟩
      intro z hz
      rcases (GraphWalk.mem_support_append _ _).mp hz with hz₁ | hz₂
      · exact hW₁ z hz₁
      · rcases List.mem_cons.mp hz₂ with rfl | hz₂
        · exact hlK.left_mem
        · simp only [GraphWalk.support_nil, List.mem_singleton] at hz₂
          exact hz₂ ▸ hlK.right_mem
  obtain ⟨W₀, hW₀⟩ := hraw (hVK ▸ hy) hxy
  obtain ⟨W, hWs, hWsup, -⟩ := GraphWalk.exists_isSimple W₀
  exact ⟨W, hWs, fun z hz => hVK ▸ hW₀ z (hWsup z hz)⟩

/-- Each grid adjacency `(p, q)` lifts to a link `D₀.toGraph.IsLink (ηe s(p, q)) x y` with
`x ∈ ηv p` and `y ∈ ηv q`. -/
theorem exists_modelEdge_link {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q) :
    ∃ x ∈ ηv p, ∃ y ∈ ηv q, D₀.toGraph.IsLink (ηe s(p, q)) x y := by
  have hpq : p ≠ q := (pathGraph θ □ pathGraph θ).ne_of_adj hadj
  have hl := gridGraph_isLink_of_adj hadj
  have he : s(p, q) ∈ E(GM01.gridGraph θ) := hl.edge_mem
  have hpV := mem_gridGraph_V p
  have hqV := mem_gridGraph_V q
  obtain ⟨x, hxp, y', hxy'⟩ := (hm.inc_iff p hpV _ he).mp hl.inc_left
  obtain ⟨z, hzq, w', hzw'⟩ := (hm.inc_iff q hqV _ he).mp hl.inc_right
  have hxz : z ≠ x := fun h => Set.disjoint_left.mp (hm.vertex_disjoint p hpV q hqV hpq) hxp (h ▸ hzq)
  have hz_mem : z ∈ ({x, y'} : Set SphereSurf) := by
    rw [← hxy'.2.2.2, hzw'.2.2.2]
    simp
  rcases hz_mem with hzx | hzy'
  · exact absurd hzx hxz
  · have hzy : z = y' := Set.mem_singleton_iff.mp hzy'
    exact ⟨x, hxp, z, hzq, hzy ▸ hxy'⟩

noncomputable def edgeLeft {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q) : SphereSurf :=
  (exists_modelEdge_link hm hadj).choose

noncomputable def edgeRight {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q) : SphereSurf :=
  (exists_modelEdge_link hm hadj).choose_spec.2.choose

theorem edgeLeft_mem {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q) :
    edgeLeft hm hadj ∈ ηv p :=
  (exists_modelEdge_link hm hadj).choose_spec.1

theorem edgeRight_mem {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q) :
    edgeRight hm hadj ∈ ηv q :=
  (exists_modelEdge_link hm hadj).choose_spec.2.choose_spec.1

theorem isLink_modelEdge {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q) :
    D₀.toGraph.IsLink (ηe s(p, q)) (edgeLeft hm hadj) (edgeRight hm hadj) :=
  (exists_modelEdge_link hm hadj).choose_spec.2.choose_spec.2

/-!
## 2. Lifting Injective Grid Walks to Simple Walks
-/

theorem isSimple_append {α β : Type*} {G : Graph α β} {a b c : α}
    {W₁ : GraphWalk G a b} {W₂ : GraphWalk G b c}
    (h₁ : W₁.IsSimple) (h₂ : W₂.IsSimple)
    (hdis : ∀ z, z ∈ W₁.support → z ∈ W₂.support → z = b) :
    (W₁.append W₂).IsSimple := by
  unfold GraphWalk.IsSimple
  rw [GraphWalk.support_append]
  refine List.nodup_append.mpr ⟨h₁, h₂.tail, fun x hx y hy hxy => ?_⟩
  subst hxy
  have hxb : x = b := hdis x hx (by rw [W₂.support_eq_cons]; exact List.mem_cons_of_mem _ hy)
  subst hxb
  have h₂' : W₂.support.Nodup := h₂
  rw [W₂.support_eq_cons] at h₂'
  exact (List.nodup_cons.mp h₂').1 hy

/-- Lift an `(n + 1)`-step injective grid path `p 0, p 1, ..., p (n + 1)` starting at a prescribed
vertex `x₀ ∈ ηv (p 0)` and ending at `edgeRight hm (hadj n le_rfl) ∈ ηv (p (n + 1))`. -/
noncomputable def liftGridSteps {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe) :
    ∀ (n : ℕ) (p : ℕ → Fin θ × Fin θ)
      (hadj : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p t) (p (t + 1)))
      {x₀ : SphereSurf} (_hx₀ : x₀ ∈ ηv (p 0)),
      GraphWalk D₀.toGraph x₀ (edgeRight hm (hadj n le_rfl))
  | 0, p, hadj, _, hx₀ =>
    let hl := isLink_modelEdge hm (hadj 0 le_rfl)
    let B₀ := (exists_branch_walk hm (p 0) hx₀ (edgeLeft_mem hm (hadj 0 le_rfl))).choose
    B₀.append (.cons hl (.nil hl.right_mem))
  | n + 1, p, hadj, _, hx₀ =>
    let hadj' : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p t) (p (t + 1)) :=
      fun t ht => hadj t (Nat.le_succ_of_le ht)
    let W_prev := liftGridSteps hm n p hadj' hx₀
    let hl_last := isLink_modelEdge hm (hadj (n + 1) le_rfl)
    let B_last := (exists_branch_walk hm (p (n + 1))
      (edgeRight_mem hm (hadj' n le_rfl)) (edgeLeft_mem hm (hadj (n + 1) le_rfl))).choose
    W_prev.append (B_last.append (.cons hl_last (.nil hl_last.right_mem)))

theorem liftGridSteps_props {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    (n : ℕ) (p : ℕ → Fin θ × Fin θ)
    (hadj : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p t) (p (t + 1)))
    (hinj : ∀ i ≤ n + 1, ∀ j ≤ n + 1, p i = p j → i = j)
    {x₀ : SphereSurf} (hx₀ : x₀ ∈ ηv (p 0)) :
    let W := liftGridSteps hm n p hadj hx₀
    W.IsSimple ∧
    (∀ t (ht : t ≤ n), edgeLeft hm (hadj t ht) ∈ W.support) ∧
    (∀ z ∈ W.support, z = edgeRight hm (hadj n le_rfl) ∨ ∃ t ≤ n, z ∈ ηv (p t)) ∧
    (∀ e ∈ W.edges, ∃ x y, D₀.toGraph.IsLink e x y ∧
      (∃ t ≤ n, x ∈ ηv (p t)) ∧ (y = edgeRight hm (hadj n le_rfl) ∨ ∃ t ≤ n, y ∈ ηv (p t))) := by
  induction n with
  | zero =>
    dsimp [liftGridSteps]
    set hl := isLink_modelEdge hm (hadj 0 le_rfl)
    have hBspec := (exists_branch_walk hm (p 0) hx₀ (edgeLeft_mem hm (hadj 0 le_rfl))).choose_spec
    set B₀ := (exists_branch_walk hm (p 0) hx₀ (edgeLeft_mem hm (hadj 0 le_rfl))).choose
    have hp01 : p 0 ≠ p 1 := fun h => by have := hinj 0 (by omega) 1 (by omega) h; omega
    have hdis01 := hm.vertex_disjoint (p 0) (mem_gridGraph_V _) (p 1) (mem_gridGraph_V _) hp01
    have hstep_s : (GraphWalk.cons hl (.nil hl.right_mem)).IsSimple := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro h
      exact Set.disjoint_left.mp hdis01
        (edgeLeft_mem hm (hadj 0 le_rfl))
        (List.mem_singleton.mp h ▸ edgeRight_mem hm (hadj 0 le_rfl))
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine isSimple_append hBspec.1 hstep_s fun z hz₁ hz₂ => ?_
      rcases List.mem_cons.mp hz₂ with rfl | hz₂
      · rfl
      · exact (Set.disjoint_left.mp hdis01
          (hBspec.2 _ hz₁) (List.mem_singleton.mp hz₂ ▸ edgeRight_mem hm (hadj 0 le_rfl))).elim
    · intro t ht
      have ht0 : t = 0 := Nat.eq_zero_of_le_zero ht
      subst ht0
      exact (GraphWalk.mem_support_append _ _).mpr (Or.inl B₀.end_mem_support)
    · intro z hz
      rcases (GraphWalk.mem_support_append _ _).mp hz with hz₁ | hz₂
      · exact Or.inr ⟨0, le_rfl, hBspec.2 z hz₁⟩
      · rcases List.mem_cons.mp hz₂ with rfl | hz₂
        · exact Or.inr ⟨0, le_rfl, edgeLeft_mem hm (hadj 0 le_rfl)⟩
        · exact Or.inl (List.mem_singleton.mp hz₂)
    · intro e he
      rw [GraphWalk.edges_append, List.mem_append] at he
      rcases he with he₁ | he₂
      · obtain ⟨a, b, hab⟩ := (D₀.toGraph.edge_mem_iff_exists_isLink e).mp
          (GM11.mem_E_of_mem_edges B₀ he₁)
        have ha : a ∈ ηv (p 0) := hBspec.2 a (B₀.left_mem_support_of_mem_edges he₁ hab)
        have hb : b ∈ ηv (p 0) := hBspec.2 b (B₀.left_mem_support_of_mem_edges he₁ hab.symm)
        exact ⟨a, b, hab, ⟨0, le_rfl, ha⟩, Or.inr ⟨0, le_rfl, hb⟩⟩
      · simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at he₂
        subst he₂
        exact ⟨_, _, hl, ⟨0, le_rfl, edgeLeft_mem hm (hadj 0 le_rfl)⟩, Or.inl rfl⟩
  | succ m ih =>
    dsimp [liftGridSteps]
    let hadj' : ∀ t ≤ m, (pathGraph θ □ pathGraph θ).Adj (p t) (p (t + 1)) :=
      fun t ht => hadj t (Nat.le_succ_of_le ht)
    have hinj' : ∀ i ≤ m + 1, ∀ j ≤ m + 1, p i = p j → i = j :=
      fun i hi j hj h => hinj i (by omega) j (by omega) h
    obtain ⟨hW_s, hW_el, hW_sup, hW_ed⟩ := ih hadj' hinj'
    set W_prev := liftGridSteps hm m p hadj' hx₀
    set hl_last := isLink_modelEdge hm (hadj (m + 1) le_rfl)
    have hBspec := (exists_branch_walk hm (p (m + 1))
      (edgeRight_mem hm (hadj' m le_rfl)) (edgeLeft_mem hm (hadj (m + 1) le_rfl))).choose_spec
    set B_last := (exists_branch_walk hm (p (m + 1))
      (edgeRight_mem hm (hadj' m le_rfl)) (edgeLeft_mem hm (hadj (m + 1) le_rfl))).choose
    have hp_end : p (m + 1) ≠ p (m + 2) := fun h => by
      have := hinj (m + 1) (by omega) (m + 2) (by omega) h; omega
    have hdis_end := hm.vertex_disjoint (p (m + 1)) (mem_gridGraph_V _)
      (p (m + 2)) (mem_gridGraph_V _) hp_end
    have hstep_s : (GraphWalk.cons hl_last (.nil hl_last.right_mem)).IsSimple := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      intro h
      exact Set.disjoint_left.mp hdis_end
        (edgeLeft_mem hm (hadj (m + 1) le_rfl))
        (List.mem_singleton.mp h ▸ edgeRight_mem hm (hadj (m + 1) le_rfl))
    have htail_s : (B_last.append (.cons hl_last (.nil hl_last.right_mem))).IsSimple := by
      refine isSimple_append hBspec.1 hstep_s fun z hz₁ hz₂ => ?_
      rcases List.mem_cons.mp hz₂ with rfl | hz₂
      · rfl
      · exact (Set.disjoint_left.mp hdis_end
          (hBspec.2 _ hz₁) (List.mem_singleton.mp hz₂ ▸ edgeRight_mem hm (hadj (m + 1) le_rfl))).elim
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine isSimple_append hW_s htail_s fun z hz₁ hz₂ => ?_
      rcases hW_sup z hz₁ with rfl | ⟨t, ht, hzt⟩
      · rfl
      · rcases (GraphWalk.mem_support_append _ _).mp hz₂ with hzB | hzC
        · have hne : p t ≠ p (m + 1) := fun h => by
            have := hinj t (by omega) (m + 1) (by omega) h; omega
          exact (Set.disjoint_left.mp
            (hm.vertex_disjoint _ (mem_gridGraph_V _) _ (mem_gridGraph_V _) hne)
            hzt (hBspec.2 z hzB)).elim
        · rcases List.mem_cons.mp hzC with rfl | hzC
          · have hne : p t ≠ p (m + 1) := fun h => by
              have := hinj t (by omega) (m + 1) (by omega) h; omega
            exact (Set.disjoint_left.mp
              (hm.vertex_disjoint _ (mem_gridGraph_V _) _ (mem_gridGraph_V _) hne)
              hzt (edgeLeft_mem hm (hadj (m + 1) le_rfl))).elim
          · have hne : p t ≠ p (m + 2) := fun h => by
              have := hinj t (by omega) (m + 2) (by omega) h; omega
            exact (Set.disjoint_left.mp
              (hm.vertex_disjoint _ (mem_gridGraph_V _) _ (mem_gridGraph_V _) hne)
              hzt (List.mem_singleton.mp hzC ▸ edgeRight_mem hm (hadj (m + 1) le_rfl))).elim
    · intro t ht
      rcases Nat.of_le_succ ht with htm | rfl
      · exact (GraphWalk.mem_support_append _ _).mpr (Or.inl (hW_el t htm))
      · exact (GraphWalk.mem_support_append _ _).mpr
          (Or.inr ((GraphWalk.mem_support_append _ _).mpr (Or.inl B_last.end_mem_support)))
    · intro z hz
      rcases (GraphWalk.mem_support_append _ _).mp hz with hz₁ | hz₂
      · rcases hW_sup z hz₁ with rfl | ⟨t, ht, hzt⟩
        · exact Or.inr ⟨m + 1, le_rfl, edgeRight_mem hm (hadj' m le_rfl)⟩
        · exact Or.inr ⟨t, Nat.le_succ_of_le ht, hzt⟩
      · rcases (GraphWalk.mem_support_append _ _).mp hz₂ with hzB | hzC
        · exact Or.inr ⟨m + 1, le_rfl, hBspec.2 z hzB⟩
        · rcases List.mem_cons.mp hzC with rfl | hzC
          · exact Or.inr ⟨m + 1, le_rfl, edgeLeft_mem hm (hadj (m + 1) le_rfl)⟩
          · exact Or.inl (List.mem_singleton.mp hzC)
    · intro e he
      rw [GraphWalk.edges_append, List.mem_append] at he
      rcases he with he₁ | he₂
      · obtain ⟨x, y, hxy, ⟨t, ht, hxt⟩, hy⟩ := hW_ed e he₁
        refine ⟨x, y, hxy, ⟨t, Nat.le_succ_of_le ht, hxt⟩, ?_⟩
        rcases hy with rfl | ⟨t', ht', hyt'⟩
        · exact Or.inr ⟨m + 1, le_rfl, edgeRight_mem hm (hadj' m le_rfl)⟩
        · exact Or.inr ⟨t', Nat.le_succ_of_le ht', hyt'⟩
      · rw [GraphWalk.edges_append, List.mem_append] at he₂
        rcases he₂ with heB | heC
        · obtain ⟨a, b, hab⟩ := (D₀.toGraph.edge_mem_iff_exists_isLink e).mp
            (GM11.mem_E_of_mem_edges B_last heB)
          have ha := hBspec.2 a (B_last.left_mem_support_of_mem_edges heB hab)
          have hb := hBspec.2 b (B_last.left_mem_support_of_mem_edges heB hab.symm)
          exact ⟨a, b, hab, ⟨m + 1, le_rfl, ha⟩, Or.inr ⟨m + 1, le_rfl, hb⟩⟩
        · simp only [GraphWalk.edges_cons, GraphWalk.edges_nil, List.mem_singleton] at heC
          subst heC
          exact ⟨_, _, hl_last, ⟨m + 1, le_rfl, edgeLeft_mem hm (hadj (m + 1) le_rfl)⟩, Or.inl rfl⟩

/-!
## 3. Concentric Square Frames `Q_k` and Their Properties
-/

/-- The four side grid-vertex sets `(top, right, bottom, left)` of the `k`-th concentric square
frame in `Fin θ × Fin θ` (with `b = θ - 1 - k`). -/
def sideGridSet (θ k : ℕ) : Fin 4 → Set (Fin θ × Fin θ)
  | 0 => {p | p.1.1 = k ∧ k ≤ p.2.1 ∧ p.2.1 < θ - 1 - k}
  | 1 => {p | p.2.1 = θ - 1 - k ∧ k ≤ p.1.1 ∧ p.1.1 < θ - 1 - k}
  | 2 => {p | p.1.1 = θ - 1 - k ∧ k < p.2.1 ∧ p.2.1 ≤ θ - 1 - k}
  | 3 => {p | p.2.1 = k ∧ k < p.1.1 ∧ p.1.1 ≤ θ - 1 - k}

/-- All grid vertices belonging to the `k`-th square frame `Q_k`. -/
def frameGridSet (θ k : ℕ) : Set (Fin θ × Fin θ) :=
  ⋃ i : Fin 4, sideGridSet θ k i

theorem sideGridSet_pairwise_disjoint {θ k : ℕ} (_hk : 2 * k + 4 ≤ θ) :
    Pairwise fun i j : Fin 4 => Disjoint (sideGridSet θ k i) (sideGridSet θ k j) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun p hpi hpj => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact absurd rfl hij | (simp only [sideGridSet, Set.mem_ofPred_eq] at hpi hpj; omega)

theorem frameGridSet_disjoint {θ k₁ k₂ : ℕ} (_hk₁ : 2 * k₁ + 4 ≤ θ) (_hk₂ : 2 * k₂ + 4 ≤ θ)
    (hne : k₁ ≠ k₂) : Disjoint (frameGridSet θ k₁) (frameGridSet θ k₂) := by
  refine Set.disjoint_left.mpr fun p hp₁ hp₂ => ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp₁
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp₂
  fin_cases i <;> fin_cases j <;> simp only [sideGridSet, Set.mem_ofPred_eq] at hi hj <;> omega

/-- Branch-set union `S_i(k) = ⋃_{p ∈ sideGridSet θ k i} ηv p` for each side `i : Fin 4`. -/
def sideBranchSet {θ : ℕ} (ηv : (Fin θ × Fin θ) → Set SphereSurf) (k : ℕ) (i : Fin 4) :
    Set SphereSurf :=
  ⋃ p ∈ sideGridSet θ k i, ηv p

theorem sideBranchSet_pairwise_disjoint {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe) {k : ℕ} (hk : 2 * k + 4 ≤ θ) :
    Pairwise fun i j : Fin 4 => Disjoint (sideBranchSet ηv k i) (sideBranchSet ηv k j) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hx₁ hx₂ => ?_
  obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx₁
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hx₂
  have hpq : p ≠ q := fun h =>
    Set.disjoint_left.mp (sideGridSet_pairwise_disjoint hk hij) hp (h ▸ hq)
  exact Set.disjoint_left.mp
    (hm.vertex_disjoint p (mem_gridGraph_V p) q (mem_gridGraph_V q) hpq) hxp hxq

/-- Bundled construction of the `k`-th concentric frame circuit `C'_k` of `D₀` (`2 * k + 4 ≤ θ`). -/
theorem exists_frame_circuit {θ : ℕ} {D₀ : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe) (k : ℕ) (hk : 2 * k + 4 ≤ θ) :
    ∃ C : Drawing SphereSurf,
      C.IsCircuit ∧
      C.IsSubdrawing D₀ ∧
      (∀ x ∈ C.V, ∃ p ∈ frameGridSet θ k, x ∈ ηv p) ∧
      (∀ p ∈ frameGridSet θ k, (C.V ∩ ηv p).Nonempty) ∧
      (∀ {a b c d : SphereSurf},
        a ∈ C.V ∩ sideBranchSet ηv k 0 →
        b ∈ C.V ∩ sideBranchSet ηv k 1 →
        c ∈ C.V ∩ sideBranchSet ηv k 2 →
        d ∈ C.V ∩ sideBranchSet ηv k 3 →
        PairsCrossOn C.U a c b d) := by
  set b := θ - 1 - k
  set n := b - k - 1
  have hbk : k + 2 ≤ b := by omega
  have hn_eq : k + (n + 1) = b := by omega
  let p₀ : ℕ → Fin θ × Fin θ := fun t =>
    (⟨k, by omega⟩, ⟨min (k + t) (θ - 1), by omega⟩)
  let p₁ : ℕ → Fin θ × Fin θ := fun t =>
    (⟨min (k + t) (θ - 1), by omega⟩, ⟨b, by omega⟩)
  let p₂ : ℕ → Fin θ × Fin θ := fun t =>
    (⟨b, by omega⟩, ⟨b - min t b, by omega⟩)
  let p₃ : ℕ → Fin θ × Fin θ := fun t =>
    (⟨b - min t b, by omega⟩, ⟨k, by omega⟩)
  have hadj₀ : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p₀ t) (p₀ (t + 1)) := by
    intro t ht; simp only [p₀, boxProd_adj, pathGraph_adj]; right
    exact ⟨Or.inl (by dsimp [b, n] at *; omega), trivial⟩
  have hadj₁ : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p₁ t) (p₁ (t + 1)) := by
    intro t ht; simp only [p₁, boxProd_adj, pathGraph_adj]; left
    exact ⟨Or.inl (by dsimp [b, n] at *; omega), trivial⟩
  have hadj₂ : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p₂ t) (p₂ (t + 1)) := by
    intro t ht; simp only [p₂, boxProd_adj, pathGraph_adj]; right
    exact ⟨Or.inr (by dsimp [b, n] at *; omega), trivial⟩
  have hadj₃ : ∀ t ≤ n, (pathGraph θ □ pathGraph θ).Adj (p₃ t) (p₃ (t + 1)) := by
    intro t ht; simp only [p₃, boxProd_adj, pathGraph_adj]; left
    exact ⟨Or.inr (by dsimp [b, n] at *; omega), trivial⟩
  have hinj₀ : ∀ i ≤ n + 1, ∀ j ≤ n + 1, p₀ i = p₀ j → i = j := by
    intro i hi j hj h; have := congrArg (fun x => x.2.1) h; dsimp [p₀] at this; omega
  have hinj₁ : ∀ i ≤ n + 1, ∀ j ≤ n + 1, p₁ i = p₁ j → i = j := by
    intro i hi j hj h; have := congrArg (fun x => x.1.1) h; dsimp [p₁] at this; omega
  have hinj₂ : ∀ i ≤ n + 1, ∀ j ≤ n + 1, p₂ i = p₂ j → i = j := by
    intro i hi j hj h; have := congrArg (fun x => x.2.1) h; dsimp [p₂] at this; omega
  have hinj₃ : ∀ i ≤ n + 1, ∀ j ≤ n + 1, p₃ i = p₃ j → i = j := by
    intro i hi j hj h; have := congrArg (fun x => x.1.1) h; dsimp [p₃] at this; omega
  have hp₀_end : p₀ (n + 1) = p₁ 0 := by ext <;> dsimp [p₀, p₁] <;> omega
  have hp₁_end : p₁ (n + 1) = p₂ 0 := by ext <;> dsimp [p₁, p₂] <;> omega
  have hp₂_end : p₂ (n + 1) = p₃ 0 := by ext <;> dsimp [p₂, p₃] <;> omega
  have hp₃_end : p₃ (n + 1) = p₀ 0 := by ext <;> dsimp [p₃, p₀] <;> omega
  let q₁ : SphereSurf := edgeRight hm (hadj₀ n le_rfl)
  let q₂ : SphereSurf := edgeRight hm (hadj₁ n le_rfl)
  let q₃ : SphereSurf := edgeRight hm (hadj₂ n le_rfl)
  let q₀ : SphereSurf := edgeRight hm (hadj₃ n le_rfl)
  have hq₀_p₀ : q₀ ∈ ηv (p₀ 0) := hp₃_end ▸ edgeRight_mem hm (hadj₃ n le_rfl)
  have hq₁_p₁ : q₁ ∈ ηv (p₁ 0) := hp₀_end ▸ edgeRight_mem hm (hadj₀ n le_rfl)
  have hq₂_p₂ : q₂ ∈ ηv (p₂ 0) := hp₁_end ▸ edgeRight_mem hm (hadj₁ n le_rfl)
  have hq₃_p₃ : q₃ ∈ ηv (p₃ 0) := hp₂_end ▸ edgeRight_mem hm (hadj₂ n le_rfl)
  let W₀ := liftGridSteps hm n p₀ hadj₀ hq₀_p₀
  let W₁ := liftGridSteps hm n p₁ hadj₁ hq₁_p₁
  let W₂ := liftGridSteps hm n p₂ hadj₂ hq₂_p₂
  let W₃ := liftGridSteps hm n p₃ hadj₃ hq₃_p₃
  obtain ⟨hW₀s, hW₀el, hW₀sup, hW₀ed⟩ := liftGridSteps_props hm n p₀ hadj₀ hinj₀ hq₀_p₀
  obtain ⟨hW₁s, hW₁el, hW₁sup, hW₁ed⟩ := liftGridSteps_props hm n p₁ hadj₁ hinj₁ hq₁_p₁
  obtain ⟨hW₂s, hW₂el, hW₂sup, hW₂ed⟩ := liftGridSteps_props hm n p₂ hadj₂ hinj₂ hq₂_p₂
  obtain ⟨hW₃s, hW₃el, hW₃sup, hW₃ed⟩ := liftGridSteps_props hm n p₃ hadj₃ hinj₃ hq₃_p₃
  let S := sideBranchSet ηv k
  have hSdisj := sideBranchSet_pairwise_disjoint hm hk
  have hp₀_S : ∀ t ≤ n, p₀ t ∈ sideGridSet θ k 0 := fun t ht => by
    dsimp [sideGridSet, p₀, b, n] at *; omega
  have hp₁_S : ∀ t ≤ n, p₁ t ∈ sideGridSet θ k 1 := fun t ht => by
    dsimp [sideGridSet, p₁, b, n] at *; omega
  have hp₂_S : ∀ t ≤ n, p₂ t ∈ sideGridSet θ k 2 := fun t ht => by
    dsimp [sideGridSet, p₂, b, n] at *; omega
  have hp₃_S : ∀ t ≤ n, p₃ t ∈ sideGridSet θ k 3 := fun t ht => by
    dsimp [sideGridSet, p₃, b, n] at *; omega
  have hq₀ : q₀ ∈ S 0 := Set.mem_iUnion₂.mpr ⟨p₀ 0, hp₀_S 0 (Nat.zero_le _), hq₀_p₀⟩
  have hq₁ : q₁ ∈ S 1 := Set.mem_iUnion₂.mpr ⟨p₁ 0, hp₁_S 0 (Nat.zero_le _), hq₁_p₁⟩
  have hq₂ : q₂ ∈ S 2 := Set.mem_iUnion₂.mpr ⟨p₂ 0, hp₂_S 0 (Nat.zero_le _), hq₂_p₂⟩
  have hq₃ : q₃ ∈ S 3 := Set.mem_iUnion₂.mpr ⟨p₃ 0, hp₃_S 0 (Nat.zero_le _), hq₃_p₃⟩
  have hW₀_S : ∀ x ∈ W₀.support, x = q₁ ∨ x ∈ S 0 := fun x hx =>
    (hW₀sup x hx).imp_right fun ⟨t, ht, hxt⟩ => Set.mem_iUnion₂.mpr ⟨p₀ t, hp₀_S t ht, hxt⟩
  have hW₁_S : ∀ x ∈ W₁.support, x = q₂ ∨ x ∈ S 1 := fun x hx =>
    (hW₁sup x hx).imp_right fun ⟨t, ht, hxt⟩ => Set.mem_iUnion₂.mpr ⟨p₁ t, hp₁_S t ht, hxt⟩
  have hW₂_S : ∀ x ∈ W₂.support, x = q₃ ∨ x ∈ S 2 := fun x hx =>
    (hW₂sup x hx).imp_right fun ⟨t, ht, hxt⟩ => Set.mem_iUnion₂.mpr ⟨p₂ t, hp₂_S t ht, hxt⟩
  have hW₃_S : ∀ x ∈ W₃.support, x = q₀ ∨ x ∈ S 3 := fun x hx =>
    (hW₃sup x hx).imp_right fun ⟨t, ht, hxt⟩ => Set.mem_iUnion₂.mpr ⟨p₃ t, hp₃_S t ht, hxt⟩
  have hed_ends : ∀ i : Fin 4, ∀ e ∈ ([W₀.edges, W₁.edges, W₂.edges, W₃.edges].get i),
      ∃ x y, D₀.toGraph.IsLink e x y ∧ x ∈ S i ∧ (y ∈ S i ∨ y ∈ S (i + 1)) := by
    intro i e he
    fin_cases i
    · obtain ⟨x, y, hl, ⟨t, ht, hxt⟩, hy⟩ := hW₀ed e he
      refine ⟨x, y, hl, Set.mem_iUnion₂.mpr ⟨p₀ t, hp₀_S t ht, hxt⟩, ?_⟩
      rcases hy with rfl | ⟨t', ht', hyt'⟩
      · exact Or.inr hq₁
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨p₀ t', hp₀_S t' ht', hyt'⟩)
    · obtain ⟨x, y, hl, ⟨t, ht, hxt⟩, hy⟩ := hW₁ed e he
      refine ⟨x, y, hl, Set.mem_iUnion₂.mpr ⟨p₁ t, hp₁_S t ht, hxt⟩, ?_⟩
      rcases hy with rfl | ⟨t', ht', hyt'⟩
      · exact Or.inr hq₂
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨p₁ t', hp₁_S t' ht', hyt'⟩)
    · obtain ⟨x, y, hl, ⟨t, ht, hxt⟩, hy⟩ := hW₂ed e he
      refine ⟨x, y, hl, Set.mem_iUnion₂.mpr ⟨p₂ t, hp₂_S t ht, hxt⟩, ?_⟩
      rcases hy with rfl | ⟨t', ht', hyt'⟩
      · exact Or.inr hq₃
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨p₂ t', hp₂_S t' ht', hyt'⟩)
    · obtain ⟨x, y, hl, ⟨t, ht, hxt⟩, hy⟩ := hW₃ed e he
      refine ⟨x, y, hl, Set.mem_iUnion₂.mpr ⟨p₃ t, hp₃_S t ht, hxt⟩, ?_⟩
      rcases hy with rfl | ⟨t', ht', hyt'⟩
      · exact Or.inr hq₀
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨p₃ t', hp₃_S t' ht', hyt'⟩)
  have hE_disj : Pairwise fun i j : Fin 4 =>
      Disjoint {e | e ∈ ([W₀.edges, W₁.edges, W₂.edges, W₃.edges].get i)}
               {e | e ∈ ([W₀.edges, W₁.edges, W₂.edges, W₃.edges].get j)} := by
    intro i j hij
    refine Set.disjoint_left.mpr fun e hei hej => ?_
    obtain ⟨x₁, y₁, hl₁, hx₁, hy₁⟩ := hed_ends i e hei
    obtain ⟨x₂, y₂, hl₂, hx₂, hy₂⟩ := hed_ends j e hej
    have hcap : ({x₁, y₁} : Set SphereSurf) = {x₂, y₂} := hl₁.2.2.2.symm.trans hl₂.2.2.2
    by_cases hji1 : j = i + 1
    · have hij' : i ≠ j + 1 := by subst hji1; fin_cases i <;> decide
      have hx₁_in : x₁ ∈ ({x₂, y₂} : Set SphereSurf) := hcap ▸ by simp
      rcases hx₁_in with rfl | hxy
      · exact Set.disjoint_left.mp (hSdisj hij) hx₁ hx₂
      · have hx₁' : x₁ = y₂ := Set.mem_singleton_iff.mp hxy
        rcases hy₂ with hy₂' | hy₂'
        · exact Set.disjoint_left.mp (hSdisj hij) hx₁ (hx₁' ▸ hy₂')
        · exact Set.disjoint_left.mp (hSdisj hij') hx₁ (hx₁' ▸ hy₂')
    · have hx₂_in : x₂ ∈ ({x₁, y₁} : Set SphereSurf) := hcap.symm ▸ by simp
      rcases hx₂_in with rfl | hxy
      · exact Set.disjoint_left.mp (hSdisj hij.symm) hx₂ hx₁
      · have hx₂' : x₂ = y₁ := Set.mem_singleton_iff.mp hxy
        rcases hy₁ with hy₁' | hy₁'
        · exact Set.disjoint_left.mp (hSdisj hij.symm) hx₂ (hx₂' ▸ hy₁')
        · exact Set.disjoint_left.mp (hSdisj hji1) hx₂ (hx₂' ▸ hy₁')
  set W := (W₀.append W₁).append (W₂.append W₃)
  have hW₀₁_s : (W₀.append W₁).IsSimple := by
    refine isSimple_append hW₀s hW₁s fun z hz₀ hz₁ => ?_
    rcases hW₀_S z hz₀ with rfl | h0
    · rfl
    · rcases hW₁_S z hz₁ with eq₂ | h1
      · exact (Set.disjoint_left.mp (hSdisj (by decide : (0 : Fin 4) ≠ 2)) h0 (eq₂ ▸ hq₂)).elim
      · exact (Set.disjoint_left.mp (hSdisj (by decide : (0 : Fin 4) ≠ 1)) h0 h1).elim
  have hW₂₃_s : (W₂.append W₃).IsSimple := by
    refine isSimple_append hW₂s hW₃s fun z hz₂ hz₃ => ?_
    rcases hW₂_S z hz₂ with rfl | h2
    · rfl
    · rcases hW₃_S z hz₃ with eq₀ | h3
      · exact (Set.disjoint_left.mp (hSdisj (by decide : (2 : Fin 4) ≠ 0)) h2 (eq₀ ▸ hq₀)).elim
      · exact (Set.disjoint_left.mp (hSdisj (by decide : (2 : Fin 4) ≠ 3)) h2 h3).elim
  have hW_sc : W.IsSimpleClosed := by
    refine GraphWalk.isSimpleClosed_append hW₀₁_s hW₂₃_s ?_ ?_
    · intro z hz₁ hz₂
      rcases (GraphWalk.mem_support_append _ _).mp hz₁ with h0 | h1 <;>
        rcases (GraphWalk.mem_support_append _ _).mp hz₂ with h2 | h3
      · rcases hW₀_S z h0 with eq1 | hs0 <;> rcases hW₂_S z h2 with eq3 | hs2
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 3)) (eq1 ▸ hq₁) (eq3 ▸ hq₃)).elim
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 2)) (eq1 ▸ hq₁) hs2).elim
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (0 : Fin 4) ≠ 3)) hs0 (eq3 ▸ hq₃)).elim
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (0 : Fin 4) ≠ 2)) hs0 hs2).elim
      · rcases hW₀_S z h0 with eq1 | hs0 <;> rcases hW₃_S z h3 with eq0 | hs3
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 0)) (eq1 ▸ hq₁) (eq0 ▸ hq₀)).elim
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 3)) (eq1 ▸ hq₁) hs3).elim
        · exact Or.inl eq0
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (0 : Fin 4) ≠ 3)) hs0 hs3).elim
      · rcases hW₁_S z h1 with eq2 | hs1 <;> rcases hW₂_S z h2 with eq3 | hs2
        · exact Or.inr eq2
        · exact Or.inr eq2
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 3)) hs1 (eq3 ▸ hq₃)).elim
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 2)) hs1 hs2).elim
      · rcases hW₁_S z h1 with eq2 | hs1 <;> rcases hW₃_S z h3 with eq0 | hs3
        · exact Or.inr eq2
        · exact Or.inr eq2
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 0)) hs1 (eq0 ▸ hq₀)).elim
        · exact (Set.disjoint_left.mp (hSdisj (by decide : (1 : Fin 4) ≠ 3)) hs1 hs3).elim
    · intro e he₁ he₂
      rw [GraphWalk.edges_append, List.mem_append] at he₁ he₂
      rcases he₁ with h0 | h1 <;> rcases he₂ with h2 | h3
      · exact Set.disjoint_left.mp (hE_disj (by decide : (0 : Fin 4) ≠ 2)) h0 h2
      · exact Set.disjoint_left.mp (hE_disj (by decide : (0 : Fin 4) ≠ 3)) h0 h3
      · exact Set.disjoint_left.mp (hE_disj (by decide : (1 : Fin 4) ≠ 2)) h1 h2
      · exact Set.disjoint_left.mp (hE_disj (by decide : (1 : Fin 4) ≠ 3)) h1 h3
  have hW_pos : 0 < W.length := by
    have hq01 : q₀ ≠ q₁ := fun h =>
      Set.disjoint_left.mp (hSdisj (by decide : (0 : Fin 4) ≠ 1)) hq₀ (h ▸ hq₁)
    have hpos₀ : W₀.length ≠ 0 := fun h => hq01 (GraphWalk.eq_of_length_eq_zero h)
    rw [GraphWalk.length_append, GraphWalk.length_append]
    omega
  refine ⟨walkDrawing D₀ W, GM11.isCircuit_walkDrawing D₀ hW_sc hW_pos,
    GM11.walkDrawing_isSubdrawing D₀ W, ?_, ?_, ?_⟩
  · intro x hx
    rw [GM11.walkDrawing_V, Set.mem_ofPred_eq, GraphWalk.mem_support_append,
      GraphWalk.mem_support_append, GraphWalk.mem_support_append] at hx
    have hsub : ∀ i : Fin 4, S i ⊆ ⋃ j : Fin 4, S j := fun i z hz => Set.mem_iUnion.mpr ⟨i, hz⟩
    have hxU : x ∈ ⋃ j : Fin 4, S j := by
      rcases hx with (h0 | h1) | (h2 | h3)
      · rcases hW₀_S x h0 with eq1 | hs
        · exact hsub 1 (eq1 ▸ hq₁)
        · exact hsub 0 hs
      · rcases hW₁_S x h1 with eq2 | hs
        · exact hsub 2 (eq2 ▸ hq₂)
        · exact hsub 1 hs
      · rcases hW₂_S x h2 with eq3 | hs
        · exact hsub 3 (eq3 ▸ hq₃)
        · exact hsub 2 hs
      · rcases hW₃_S x h3 with eq0 | hs
        · exact hsub 0 (eq0 ▸ hq₀)
        · exact hsub 3 hs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hj
    exact ⟨p, Set.mem_iUnion.mpr ⟨j, hp⟩, hxp⟩
  · intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    fin_cases i
    · simp only [sideGridSet, Set.mem_ofPred_eq] at hi
      let t := p.2.1 - k
      have ht : t ≤ n := by omega
      have hpt : p₀ t = p := by ext <;> dsimp [p₀] <;> omega
      refine ⟨edgeLeft hm (hadj₀ t ht), ?_, hpt ▸ edgeLeft_mem hm (hadj₀ t ht)⟩
      rw [GM11.walkDrawing_V, Set.mem_ofPred_eq]
      exact (GraphWalk.mem_support_append _ _).mpr
        (Or.inl ((GraphWalk.mem_support_append _ _).mpr (Or.inl (hW₀el t ht))))
    · simp only [sideGridSet, Set.mem_ofPred_eq] at hi
      let t := p.1.1 - k
      have ht : t ≤ n := by omega
      have hpt : p₁ t = p := by ext <;> dsimp [p₁] <;> omega
      refine ⟨edgeLeft hm (hadj₁ t ht), ?_, hpt ▸ edgeLeft_mem hm (hadj₁ t ht)⟩
      rw [GM11.walkDrawing_V, Set.mem_ofPred_eq]
      exact (GraphWalk.mem_support_append _ _).mpr
        (Or.inl ((GraphWalk.mem_support_append _ _).mpr (Or.inr (hW₁el t ht))))
    · simp only [sideGridSet, Set.mem_ofPred_eq] at hi
      let t := b - p.2.1
      have ht : t ≤ n := by omega
      have hpt : p₂ t = p := by ext <;> dsimp [p₂] <;> omega
      refine ⟨edgeLeft hm (hadj₂ t ht), ?_, hpt ▸ edgeLeft_mem hm (hadj₂ t ht)⟩
      rw [GM11.walkDrawing_V, Set.mem_ofPred_eq]
      exact (GraphWalk.mem_support_append _ _).mpr
        (Or.inr ((GraphWalk.mem_support_append _ _).mpr (Or.inl (hW₂el t ht))))
    · simp only [sideGridSet, Set.mem_ofPred_eq] at hi
      let t := b - p.1.1
      have ht : t ≤ n := by omega
      have hpt : p₃ t = p := by ext <;> dsimp [p₃] <;> omega
      refine ⟨edgeLeft hm (hadj₃ t ht), ?_, hpt ▸ edgeLeft_mem hm (hadj₃ t ht)⟩
      rw [GM11.walkDrawing_V, Set.mem_ofPred_eq]
      exact (GraphWalk.mem_support_append _ _).mpr
        (Or.inr ((GraphWalk.mem_support_append _ _).mpr (Or.inr (hW₃el t ht))))
  · intro a b_pt c d ha hb hc hd
    exact pairsCrossOn_of_four_arcs D₀ W₀ W₁ W₂ W₃
      (hSdisj (by decide : (0 : Fin 4) ≠ 1))
      (hSdisj (by decide : (0 : Fin 4) ≠ 2))
      (hSdisj (by decide : (0 : Fin 4) ≠ 3))
      (hSdisj (by decide : (1 : Fin 4) ≠ 2))
      (hSdisj (by decide : (1 : Fin 4) ≠ 3))
      (hSdisj (by decide : (2 : Fin 4) ≠ 3))
      hW₀_S hW₁_S hW₂_S hW₃_S hq₀ hq₁ hq₂ hq₃
      hW₀s hW₁s hW₂s hW₃s hE_disj ha hb hc hd

/-!
## 4. Single-Step Spoke Trimming and Three-Frame Separation
-/

/-- Given a single grid adjacency `(p, q)` with `p ∉ frameGridSet θ k` and `q ∈ sideGridSet θ k i`,
if `u ∈ C'.V ∩ ηv p` with `C'.U ⊆ discInt D` (where `discBd D = C.U`), there is a trimmed spoke
subdrawing `P` of `D₀` with `P.U ⊆ D`, `IsPathConnected P.U`, `u ∈ P.U`, `P.V ⊆ ηv p ∪ ηv q`,
and an endpoint `z ∈ P.U ∩ (C.V ∩ sideBranchSet ηv k i)`. -/
theorem exists_trimmed_spoke {θ : ℕ} {D₀ C C' : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {k : ℕ} (i : Fin 4)
    (hCs : C.IsSubdrawing D₀)
    (hCV : ∀ x ∈ C.V, ∃ r ∈ frameGridSet θ k, x ∈ ηv r)
    {D : Set SphereSurf} (hD : IsClosedDisc D) (hbd : discBd D = C.U)
    {p q : Fin θ × Fin θ} (hadj : (pathGraph θ □ pathGraph θ).Adj p q)
    (hp_out : p ∉ frameGridSet θ k) (hq_side : q ∈ sideGridSet θ k i)
    {u : SphereSurf} (huC' : u ∈ C'.V) (hup : u ∈ ηv p) (hC'_in : C'.U ⊆ discInt D)
    {w₀ : SphereSurf} (hw₀C : w₀ ∈ C.V) (hw₀q : w₀ ∈ ηv q) :
    ∃ (P : Drawing SphereSurf) (z : SphereSurf),
      P.IsSubdrawing D₀ ∧
      P.U ⊆ D ∧
      IsPathConnected P.U ∧
      u ∈ P.U ∧
      z ∈ P.U ∧
      z ∈ C.V ∩ sideBranchSet ηv k i ∧
      P.V ⊆ ηv p ∪ ηv q := by
  classical
  obtain ⟨B₁, _, hB₁⟩ := exists_branch_walk hm p hup (edgeLeft_mem hm hadj)
  obtain ⟨B₂, _, hB₂⟩ := exists_branch_walk hm q (edgeRight_mem hm hadj) hw₀q
  let hl := isLink_modelEdge hm hadj
  let W_raw := (B₁.append (.cons hl (.nil hl.right_mem))).append B₂
  have hW_raw_sup : ∀ x ∈ W_raw.support, x ∈ ηv p ∪ ηv q := by
    intro x hx
    rcases (GraphWalk.mem_support_append _ _).mp hx with hx₁ | hx₂
    · rcases (GraphWalk.mem_support_append _ _).mp hx₁ with hB₁' | hstep
      · exact Or.inl (hB₁ x hB₁')
      · rcases List.mem_cons.mp hstep with rfl | hstep'
        · exact Or.inl (edgeLeft_mem hm hadj)
        · simp only [GraphWalk.support_nil, List.mem_singleton] at hstep'
          exact Or.inr (hstep' ▸ edgeRight_mem hm hadj)
    · exact Or.inr (hB₂ x hx₂)
  obtain ⟨W₁, hW₁s, hW₁sup, -⟩ := GraphWalk.exists_isSimple W_raw
  obtain ⟨z, W₂, hzCV, hfirst, hW₂sup, -, hW₂s_imp⟩ := GraphWalk.exists_prefix W₁ C.V hw₀C
  have hW₂s : W₂.IsSimple := hW₂s_imp hW₁s
  have hu_int : u ∈ discInt D := hC'_in (C'.V_subset_U huC')
  have hsubD : (walkDrawing D₀ W₂).U ⊆ D :=
    walkDrawing_subset_disc_of_first_hit D₀ C hD hCs hbd W₂ hW₂s hu_int hzCV hfirst
  have hzq : z ∈ ηv q := by
    rcases hW_raw_sup z (hW₁sup z (hW₂sup z W₂.end_mem_support)) with hzp | hzq
    · obtain ⟨r, hr, hzr⟩ := hCV z hzCV
      have hpr : p ≠ r := fun h => hp_out (h ▸ hr)
      exact (Set.disjoint_left.mp
        (hm.vertex_disjoint p (mem_gridGraph_V p) r (mem_gridGraph_V r) hpr) hzp hzr).elim
    · exact hzq
  refine ⟨walkDrawing D₀ W₂, z, GM11.walkDrawing_isSubdrawing D₀ W₂, hsubD,
    isPathConnected_walkDrawing_U D₀ W₂,
    (walkDrawing D₀ W₂).V_subset_U (by rw [GM11.walkDrawing_V]; exact W₂.start_mem_support),
    (walkDrawing D₀ W₂).V_subset_U (by rw [GM11.walkDrawing_V]; exact W₂.end_mem_support),
    ⟨hzCV, Set.mem_iUnion₂.mpr ⟨q, hq_side, hzq⟩⟩, ?_⟩
  intro x hx
  rw [GM11.walkDrawing_V, Set.mem_ofPred_eq] at hx
  exact hW_raw_sup x (hW₁sup x (hW₂sup x hx))

/-- Three consecutive concentric square frames `C'_{k-1}, C'_k, C'_{k+1}` cannot have both
`C'_{k-1}` and `C'_{k+1}` inside the open interior `discInt D` of the same closed disc `D`
bounded by `C'_k.U`. -/
theorem not_same_disc_of_three_frames {θ : ℕ} {D₀ C_prev C_mid C_next : Drawing SphereSurf}
    {ηv : (Fin θ × Fin θ) → Set SphereSurf} {ηe : Sym2 (Fin θ × Fin θ) → Set SphereSurf}
    (hm : IsMinorModel (GM01.gridGraph θ) D₀.toGraph ηv ηe)
    {k c₀ : ℕ} (hk1 : 1 ≤ k) (hk_bd : 2 * (k + 1) + 4 ≤ θ)
    (hc₀_lo : k + 1 < c₀) (hc₀_hi : c₀ < θ - 1 - (k + 1))
    (hprev_s : C_prev.IsSubdrawing D₀) (hmid_s : C_mid.IsSubdrawing D₀)
    (hnext_s : C_next.IsSubdrawing D₀)
    (hprev_c : C_prev.IsCircuit) (hnext_c : C_next.IsCircuit)
    (hprev_V : ∀ x ∈ C_prev.V, ∃ p ∈ frameGridSet θ (k - 1), x ∈ ηv p)
    (hmid_V : ∀ x ∈ C_mid.V, ∃ p ∈ frameGridSet θ k, x ∈ ηv p)
    (hnext_V : ∀ x ∈ C_next.V, ∃ p ∈ frameGridSet θ (k + 1), x ∈ ηv p)
    (hprev_hit : ∀ p ∈ frameGridSet θ (k - 1), (C_prev.V ∩ ηv p).Nonempty)
    (hmid_hit : ∀ p ∈ frameGridSet θ k, (C_mid.V ∩ ηv p).Nonempty)
    (hnext_hit : ∀ p ∈ frameGridSet θ (k + 1), (C_next.V ∩ ηv p).Nonempty)
    (hmid_cross : ∀ {a b c d : SphereSurf},
      a ∈ C_mid.V ∩ sideBranchSet ηv k 0 →
      b ∈ C_mid.V ∩ sideBranchSet ηv k 1 →
      c ∈ C_mid.V ∩ sideBranchSet ηv k 2 →
      d ∈ C_mid.V ∩ sideBranchSet ηv k 3 →
      PairsCrossOn C_mid.U a c b d)
    {D : Set SphereSurf} (hD : IsClosedDisc D) (hbd : discBd D = C_mid.U)
    (hin_prev : C_prev.U ⊆ discInt D) (hin_next : C_next.U ⊆ discInt D) : False := by
  set b := θ - 1 - k
  have hp_top : (⟨k - 1, by omega⟩, ⟨c₀, by omega⟩) ∈ frameGridSet θ (k - 1) :=
    Set.mem_iUnion.mpr ⟨0, by dsimp [sideGridSet, b]; omega⟩
  have hp_bot : (⟨b + 1, by omega⟩, ⟨c₀, by omega⟩) ∈ frameGridSet θ (k - 1) :=
    Set.mem_iUnion.mpr ⟨2, by dsimp [sideGridSet, b]; omega⟩
  have hp_right : (⟨c₀, by omega⟩, ⟨b - 1, by omega⟩) ∈ frameGridSet θ (k + 1) :=
    Set.mem_iUnion.mpr ⟨1, by dsimp [sideGridSet, b]; omega⟩
  have hp_left : (⟨c₀, by omega⟩, ⟨k + 1, by omega⟩) ∈ frameGridSet θ (k + 1) :=
    Set.mem_iUnion.mpr ⟨3, by dsimp [sideGridSet, b]; omega⟩
  have hq_top : (⟨k, by omega⟩, ⟨c₀, by omega⟩) ∈ sideGridSet θ k 0 := by
    dsimp [sideGridSet, b]; omega
  have hq_right : (⟨c₀, by omega⟩, ⟨b, by omega⟩) ∈ sideGridSet θ k 1 := by
    dsimp [sideGridSet, b]; omega
  have hq_bot : (⟨b, by omega⟩, ⟨c₀, by omega⟩) ∈ sideGridSet θ k 2 := by
    dsimp [sideGridSet, b]; omega
  have hq_left : (⟨c₀, by omega⟩, ⟨k, by omega⟩) ∈ sideGridSet θ k 3 := by
    dsimp [sideGridSet, b]; omega
  obtain ⟨u_top, hu_topC, hu_top⟩ := hprev_hit _ hp_top
  obtain ⟨u_bot, hu_botC, hu_bot⟩ := hprev_hit _ hp_bot
  obtain ⟨u_right, hu_rightC, hu_right⟩ := hnext_hit _ hp_right
  obtain ⟨u_left, hu_leftC, hu_left⟩ := hnext_hit _ hp_left
  obtain ⟨w_top, hw_topC, hw_top⟩ := hmid_hit _ (Set.mem_iUnion.mpr ⟨0, hq_top⟩)
  obtain ⟨w_right, hw_rightC, hw_right⟩ := hmid_hit _ (Set.mem_iUnion.mpr ⟨1, hq_right⟩)
  obtain ⟨w_bot, hw_botC, hw_bot⟩ := hmid_hit _ (Set.mem_iUnion.mpr ⟨2, hq_bot⟩)
  obtain ⟨w_left, hw_leftC, hw_left⟩ := hmid_hit _ (Set.mem_iUnion.mpr ⟨3, hq_left⟩)
  have hk_mid : 2 * k + 4 ≤ θ := by omega
  have hk_prev : 2 * (k - 1) + 4 ≤ θ := by omega
  obtain ⟨P_top, a, hP_top_s, hP_top_D, hP_top_pc, hu_topP, haP, ha_side, hP_top_V⟩ :=
    exists_trimmed_spoke hm 0 hmid_s hmid_V hD hbd
      (by simp only [boxProd_adj, pathGraph_adj]; left; exact ⟨Or.inl (by omega), trivial⟩)
      (fun h => Set.disjoint_left.mp (frameGridSet_disjoint hk_prev hk_mid (by omega)) hp_top h)
      hq_top hu_topC hu_top hin_prev hw_topC hw_top
  obtain ⟨P_bot, c, hP_bot_s, hP_bot_D, hP_bot_pc, hu_botP, hcP, hc_side, hP_bot_V⟩ :=
    exists_trimmed_spoke hm 2 hmid_s hmid_V hD hbd
      (by simp only [boxProd_adj, pathGraph_adj]; left; exact ⟨Or.inr trivial, trivial⟩)
      (fun h => Set.disjoint_left.mp (frameGridSet_disjoint hk_prev hk_mid (by omega)) hp_bot h)
      hq_bot hu_botC hu_bot hin_prev hw_botC hw_bot
  obtain ⟨P_right, b_pt, hP_right_s, hP_right_D, hP_right_pc, hu_rightP, hbP, hb_side, hP_right_V⟩ :=
    exists_trimmed_spoke hm 1 hmid_s hmid_V hD hbd
      (by simp only [boxProd_adj, pathGraph_adj]; right; exact ⟨Or.inl (by dsimp [b]; omega), trivial⟩)
      (fun h => Set.disjoint_left.mp (frameGridSet_disjoint hk_bd hk_mid (by omega)) hp_right h)
      hq_right hu_rightC hu_right hin_next hw_rightC hw_right
  obtain ⟨P_left, d, hP_left_s, hP_left_D, hP_left_pc, hu_leftP, hdP, hd_side, hP_left_V⟩ :=
    exists_trimmed_spoke hm 3 hmid_s hmid_V hD hbd
      (by simp only [boxProd_adj, pathGraph_adj]; right; exact ⟨Or.inr trivial, trivial⟩)
      (fun h => Set.disjoint_left.mp (frameGridSet_disjoint hk_bd hk_mid (by omega)) hp_left h)
      hq_left hu_leftC hu_left hin_next hw_leftC hw_left
  let A := (C_prev.U ∪ P_top.U) ∪ P_bot.U
  let B := (C_next.U ∪ P_right.U) ∪ P_left.U
  have hcirc_pc : ∀ {C : Drawing SphereSurf}, C.IsSubdrawing D₀ → C.IsCircuit →
      IsPathConnected C.U := by
    intro C hCs hCc
    obtain ⟨u, W, -, -, hV, hE⟩ := hCc
    obtain ⟨W', hs, he⟩ := hCs.exists_walk_up W
    have hEq : C = walkDrawing D₀ W' := Drawing.ext_of_V_E
      (by rw [hV, GM11.walkDrawing_V, hs]) (by rw [hE, GM11.walkDrawing_E, he])
    rw [hEq]
    exact isPathConnected_walkDrawing_U D₀ W'
  have hCprev_pc : IsPathConnected C_prev.U := hcirc_pc hprev_s hprev_c
  have hCnext_pc : IsPathConnected C_next.U := hcirc_pc hnext_s hnext_c
  have hA_pc : IsPathConnected A :=
    (hCprev_pc.union hP_top_pc ⟨u_top, C_prev.V_subset_U hu_topC, hu_topP⟩).union
      hP_bot_pc ⟨u_bot, Or.inl (C_prev.V_subset_U hu_botC), hu_botP⟩
  have hB_pc : IsPathConnected B :=
    (hCnext_pc.union hP_right_pc ⟨u_right, C_next.V_subset_U hu_rightC, hu_rightP⟩).union
      hP_left_pc ⟨u_left, Or.inl (C_next.V_subset_U hu_leftC), hu_leftP⟩
  have hA_D : A ⊆ D := union_subset
    (union_subset (hin_prev.trans (discInt_subset D)) hP_top_D) hP_bot_D
  have hB_D : B ⊆ D := union_subset
    (union_subset (hin_next.trans (discInt_subset D)) hP_right_D) hP_left_D
  have hcross : PairsCrossOn (discBd D) a c b_pt d :=
    hbd ▸ hmid_cross ha_side hb_side hc_side hd_side
  obtain ⟨z, hzA, hzB⟩ := DiscCrossingStatement.of_isPathConnected_proved D A B a c b_pt d hD
    hA_D hB_D hA_pc hB_pc (Or.inl (Or.inr haP)) (Or.inr hcP) (Or.inl (Or.inr hbP)) (Or.inr hdP) hcross
  let GA : Set (Fin θ × Fin θ) :=
    frameGridSet θ (k - 1) ∪ {(⟨k, by omega⟩, ⟨c₀, by omega⟩), (⟨b, by omega⟩, ⟨c₀, by omega⟩)}
  let GB : Set (Fin θ × Fin θ) :=
    frameGridSet θ (k + 1) ∪ {(⟨c₀, by omega⟩, ⟨b, by omega⟩), (⟨c₀, by omega⟩, ⟨k, by omega⟩)}
  have hGAB_disj : Disjoint GA GB := by
    refine Disjoint.union_left ?_ ?_
    · refine Disjoint.union_right (frameGridSet_disjoint hk_prev hk_bd (by omega)) ?_
      refine Set.disjoint_left.mpr fun p hp₁ hp₂ => ?_
      have hp_mid : p ∈ frameGridSet θ k := by
        rcases hp₂ with rfl | hp₂
        · exact Set.mem_iUnion.mpr ⟨1, hq_right⟩
        · rw [Set.mem_singleton_iff] at hp₂; subst hp₂; exact Set.mem_iUnion.mpr ⟨3, hq_left⟩
      exact Set.disjoint_left.mp (frameGridSet_disjoint hk_prev hk_mid (by omega)) hp₁ hp_mid
    · refine Disjoint.union_right ?_ ?_
      · refine Set.disjoint_left.mpr fun p hp₁ hp₂ => ?_
        have hp_mid : p ∈ frameGridSet θ k := by
          rcases hp₁ with rfl | hp₁
          · exact Set.mem_iUnion.mpr ⟨0, hq_top⟩
          · rw [Set.mem_singleton_iff] at hp₁; subst hp₁; exact Set.mem_iUnion.mpr ⟨2, hq_bot⟩
        exact Set.disjoint_left.mp (frameGridSet_disjoint hk_mid hk_bd (by omega)) hp_mid hp₂
      · refine Set.disjoint_left.mpr fun p hp₁ hp₂ => ?_
        rcases hp₁ with hp₁ | hp₁ <;> rcases hp₂ with hp₂ | hp₂
        · have := congrArg (fun x => x.1.1) (hp₁.symm.trans hp₂); dsimp [b] at this; omega
        · rw [Set.mem_singleton_iff] at hp₂
          have := congrArg (fun x => x.2.1) (hp₁.symm.trans hp₂); dsimp [b] at this; omega
        · rw [Set.mem_singleton_iff] at hp₁
          have := congrArg (fun x => x.1.1) (hp₁.symm.trans hp₂); dsimp [b] at this; omega
        · rw [Set.mem_singleton_iff] at hp₁ hp₂
          have := congrArg (fun x => x.2.1) (hp₁.symm.trans hp₂); dsimp [b] at this; omega
  have hdisj_sub : ∀ {X Y : Drawing SphereSurf}, X.IsSubdrawing D₀ → Y.IsSubdrawing D₀ →
      (∀ x ∈ X.V, ∃ p ∈ GA, x ∈ ηv p) → (∀ y ∈ Y.V, ∃ q ∈ GB, y ∈ ηv q) →
      Disjoint X.U Y.U := by
    intro X Y hXs hYs hXV hYV
    refine disjoint_U_of_disjoint_V hXs hYs (Set.disjoint_left.mpr fun x hxX hxY => ?_)
    obtain ⟨p, hp, hxp⟩ := hXV x hxX
    obtain ⟨q, hq, hxq⟩ := hYV x hxY
    have hpq : p ≠ q := fun h => Set.disjoint_left.mp hGAB_disj hp (h ▸ hq)
    exact Set.disjoint_left.mp
      (hm.vertex_disjoint p (mem_gridGraph_V p) q (mem_gridGraph_V q) hpq) hxp hxq
  have hV_prev : ∀ x ∈ C_prev.V, ∃ p ∈ GA, x ∈ ηv p := fun x hx =>
    let ⟨p, hp, hxp⟩ := hprev_V x hx; ⟨p, Or.inl hp, hxp⟩
  have hV_top : ∀ x ∈ P_top.V, ∃ p ∈ GA, x ∈ ηv p := fun x hx => by
    rcases hP_top_V hx with hxp | hxq
    · exact ⟨_, Or.inl hp_top, hxp⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hxq⟩
  have hV_bot : ∀ x ∈ P_bot.V, ∃ p ∈ GA, x ∈ ηv p := fun x hx => by
    rcases hP_bot_V hx with hxp | hxq
    · exact ⟨_, Or.inl hp_bot, hxp⟩
    · exact ⟨_, Or.inr (Or.inr (Set.mem_singleton _)), hxq⟩
  have hV_next : ∀ x ∈ C_next.V, ∃ p ∈ GB, x ∈ ηv p := fun x hx =>
    let ⟨p, hp, hxp⟩ := hnext_V x hx; ⟨p, Or.inl hp, hxp⟩
  have hV_right : ∀ x ∈ P_right.V, ∃ p ∈ GB, x ∈ ηv p := fun x hx => by
    rcases hP_right_V hx with hxp | hxq
    · exact ⟨_, Or.inl hp_right, hxp⟩
    · exact ⟨_, Or.inr (Or.inl rfl), hxq⟩
  have hV_left : ∀ x ∈ P_left.V, ∃ p ∈ GB, x ∈ ηv p := fun x hx => by
    rcases hP_left_V hx with hxp | hxq
    · exact ⟨_, Or.inl hp_left, hxp⟩
    · exact ⟨_, Or.inr (Or.inr (Set.mem_singleton _)), hxq⟩
  have hAB_disj : Disjoint A B := by
    refine Disjoint.union_left (Disjoint.union_left ?_ ?_) ?_
    · exact Disjoint.union_right (Disjoint.union_right
        (hdisj_sub hprev_s hnext_s hV_prev hV_next)
        (hdisj_sub hprev_s hP_right_s hV_prev hV_right))
        (hdisj_sub hprev_s hP_left_s hV_prev hV_left)
    · exact Disjoint.union_right (Disjoint.union_right
        (hdisj_sub hP_top_s hnext_s hV_top hV_next)
        (hdisj_sub hP_top_s hP_right_s hV_top hV_right))
        (hdisj_sub hP_top_s hP_left_s hV_top hV_left)
    · exact Disjoint.union_right (Disjoint.union_right
        (hdisj_sub hP_bot_s hnext_s hV_bot hV_next)
        (hdisj_sub hP_bot_s hP_right_s hV_bot hV_right))
        (hdisj_sub hP_bot_s hP_left_s hV_bot hV_left)
  exact Set.disjoint_left.mp hAB_disj hzA hzB

end GM08
end GraphMinor
