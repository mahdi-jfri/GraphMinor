module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2g
public import GraphMinor.Surface.Defs

/-!
# Graph Minors III, Section 2h: Binary-Word Tour Models and Spoke Placement (for (2.3))

This file proves the combinatorial tree-tour and spoke-placement lemmas for `(2.3)` (page 55) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B
**36** (1984), 49–64: `exists_binWord_tour_model`, `exists_monotone_dividers_and_spokes`, and
`cone_extend_binWord_tour`.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Classical
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v u₁ v₁

/-! ## 1. Binary-Word Arithmetic and Cone Extension -/

/-- Extract representative endpoints in `ηv u` and `ηv v` linked by `ηe e` from any minor model of a
non-loop link `H.IsLink e u v` (`u ≠ v`). -/
theorem exists_isLink_of_isMinorModel {α₁ : Type u} {β₁ : Type v} {α₂ : Type u₁} {β₂ : Type v₁}
    {H : Graph α₁ β₁} {G : Graph α₂ β₂} {ηv : α₁ → Set α₂} {ηe : β₁ → β₂}
    (hm : IsMinorModel H G ηv ηe) {e : β₁} {u v : α₁} (hl : H.IsLink e u v) (huv : u ≠ v) :
    ∃ x ∈ ηv u, ∃ y ∈ ηv v, G.IsLink (ηe e) x y := by
  obtain ⟨x, hxu, _, hl₁⟩ := (hm.inc_iff u hl.left_mem e hl.edge_mem).mp ⟨v, hl⟩
  obtain ⟨y, hyv, _, hl₂⟩ := (hm.inc_iff v hl.right_mem e hl.edge_mem).mp ⟨u, hl.symm⟩
  have hxy : x ≠ y := fun h =>
    Set.disjoint_left.mp (hm.vertex_disjoint u hl.left_mem v hl.right_mem huv) hxu (h ▸ hyv)
  exact ⟨x, hxu, y, hyv,
    (hl₁.left_eq_or_eq hl₂).elim (fun h1 => absurd h1 hxy) (fun h1 => h1 ▸ hl₂.symm)⟩

theorem subVal_append (w u : List Bool) :
    subVal (w ++ u) = 2 ^ u.length * subVal w + subVal u := by
  induction u generalizing w with
  | nil => simp [subVal]
  | cons b t ih =>
    have hcons : w ++ (b :: t) = (w ++ [b]) ++ t := by simp
    rw [hcons, ih (w ++ [b]), subVal_snoc]
    cases b <;>
      (simp [subVal, pow_succ']
       ring)

/-- Fixed-length MSB-first binary representation of `r < 2 ^ m` as a `List Bool` of length `m`. -/
def wordOfNat : ℕ → ℕ → List Bool
  | 0, _ => []
  | m + 1, r => decide (2 ^ m ≤ r % 2 ^ (m + 1)) :: wordOfNat m (r % 2 ^ m)

theorem length_wordOfNat (m r : ℕ) : (wordOfNat m r).length = m := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih => simp [wordOfNat, ih]

theorem subVal_wordOfNat (m : ℕ) {r : ℕ} (hr : r < 2 ^ m) :
    subVal (wordOfNat m r) = r := by
  induction m generalizing r with
  | zero =>
    have hr0 : r = 0 := by simpa using hr
    subst hr0; rfl
  | succ m ih =>
    have hrm : r % 2 ^ (m + 1) = r := Nat.mod_eq_of_lt hr
    have hlt_m : r % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
    simp only [wordOfNat, hrm]
    by_cases hge : 2 ^ m ≤ r
    · have hlt2 : r - 2 ^ m < 2 ^ m := by rw [pow_succ'] at hr; omega
      have hmod : r % 2 ^ m = r - 2 ^ m := by
        have heq : r = 2 ^ m * 1 + (r - 2 ^ m) := by omega
        conv_lhs => rw [heq]
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt2]
      simp only [hge, decide_true, subVal, length_wordOfNat, hmod, ih hlt2]
      omega
    · have hlt' : r < 2 ^ m := by omega
      simp only [hge, decide_false, subVal, Nat.mod_eq_of_lt hlt', ih hlt']

/-- Walk upward in `binWordTree h'` from `l ++ u` (`u.length ≤ κ`) to `l` using `.dropLast` steps of
length `≥ l.length + 1`, avoiding any deleted edge set `D` whose elements have length `≤ l.length`. -/
theorem reflTransGen_cone_to_base {h' : ℕ} {S D : Set (List Bool)}
    (l u : List Bool)
    (hl_mem : l ∈ S)
    (hu_all : ∀ p : List Bool, p ≠ [] → p.length ≤ u.length → (l ++ p).length < h' ∧ l ++ p ∈ S)
    (hD_len : ∀ d ∈ D, d.length ≤ l.length) :
    Relation.ReflTransGen (((binWordTree h').deleteEdges D).induce S).Adj l (l ++ u) := by
  induction u using List.reverseRecOn with
  | nil => simpa using Relation.ReflTransGen.refl
  | append_singleton p b ih =>
    have hp_len : p.length ≤ (p ++ [b]).length := by simp
    have hprev := ih (fun q hq hql => hu_all q hq (hql.trans hp_len))
    refine Relation.ReflTransGen.tail hprev ?_
    have hne : p ++ [b] ≠ [] := List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil b [])
    obtain ⟨hlt, hmem_cur⟩ := hu_all (p ++ [b]) hne le_rfl
    have hmem_prev : l ++ p ∈ S := by
      by_cases hp0 : p = []
      · subst hp0; simpa using hl_mem
      · exact (hu_all p hp0 hp_len).2
    have hdrop : (l ++ (p ++ [b])).dropLast = l ++ p := by
      have hsnoc : ∀ q : List Bool, (q ++ [b]).dropLast = q := by
        intro q
        induction q with
        | nil => rfl
        | cons c cs ihq =>
          have hne_q : cs ++ [b] ≠ [] := List.append_ne_nil_of_right_ne_nil cs (List.cons_ne_nil b [])
          simp only [List.cons_append, dropLast_cons_ne_nil c hne_q, ihq]
      rw [← List.append_assoc, hsnoc]
    have hne_full : l ++ (p ++ [b]) ≠ [] := List.append_ne_nil_of_right_ne_nil l hne
    refine ⟨l ++ (p ++ [b]), ?_⟩
    rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
    refine ⟨⟨⟨hne_full, hlt, Or.inr ⟨rfl, hdrop.symm⟩⟩, ?_⟩, hmem_prev, hmem_cur⟩
    intro hdD
    have hle := hD_len _ hdD
    rw [List.length_append, List.length_append, List.length_singleton] at hle
    omega

/-! ## 2. Splitting Closed Walks on Trees and Tour Minor Models in `binWordTree` -/

private theorem walk_support_length {α : Type u} {β : Type v} {G : Graph α β} {x y : α}
    (W : GraphWalk G x y) : W.support.length = W.length + 1 := by
  induction W with
  | nil _ => rfl
  | cons _ rest ih =>
    simp only [GraphWalk.support, List.length_cons, ih, GraphWalk.length, GraphWalk.edges]

private theorem walk_support_append_cons {α : Type u} {β : Type v} {G : Graph α β}
    {a b c d : α} {e : β} (Q₁ : GraphWalk G a b) (hl : G.IsLink e b c) (Q₂ : GraphWalk G c d) :
    (Q₁.append (.cons hl Q₂)).support = Q₁.support ++ Q₂.support := by
  induction Q₁ with
  | nil _ => rfl
  | cons _ rest ih =>
    change _ :: (rest.append (.cons hl Q₂)).support = (_ :: rest.support) ++ Q₂.support
    rw [ih, List.cons_append]

private theorem walk_end_eq_of_nil_edges {α : Type u} {β : Type v} {G : Graph α β} {x y : α}
    (W : GraphWalk G x y) (h : W.edges = []) : x = y ∧ W.support = [x] := by
  cases W with
  | nil _ => exact ⟨rfl, rfl⟩
  | cons _ _ => simp [GraphWalk.edges] at h

/-- Split a walk `W : GraphWalk G a b` at the unique occurrence of an edge `g` (`g ∈ W.edges`). -/
private theorem split_walk_first_edge {α : Type u} {β : Type v} {G : Graph α β}
    {a b : α} (W : GraphWalk G a b) (g : β) (hg : g ∈ W.edges) :
    ∃ (p q : α) (Q₁ : GraphWalk G a p) (_hl : G.IsLink g p q) (Q₂ : GraphWalk G q b),
      g ∉ Q₁.edges ∧ W.edges = Q₁.edges ++ g :: Q₂.edges ∧ W.support = Q₁.support ++ Q₂.support := by
  induction W with
  | nil _ => cases hg
  | @cons u v w e hl rest ih =>
    by_cases heg : e = g
    · subst heg
      exact ⟨u, v, .nil hl.left_mem, hl, rest, by simp [GraphWalk.edges], rfl, rfl⟩
    · have hg_rest : g ∈ rest.edges := (List.mem_cons.mp hg).resolve_left (Ne.symm heg)
      obtain ⟨p, q, Q₁, hlg, Q₂, hnot₁, hedg, hsup⟩ := ih hg_rest
      refine ⟨p, q, .cons hl Q₁, hlg, Q₂, ?_, ?_, ?_⟩
      · simp only [GraphWalk.edges, List.mem_cons, not_or]
        exact ⟨Ne.symm heg, hnot₁⟩
      · simp only [GraphWalk.edges, hedg, List.cons_append]
      · simp only [GraphWalk.support, hsup, List.cons_append]

/-- Lift a walk `Q : GraphWalk T a b` avoiding `g` whose start `a` lies in `S` (closed under
`(T.deleteEdges {g})`-links) to a walk on `(T.deleteEdges {g}).induce S`. -/
private def liftWalkToComponent {α : Type u} {β : Type v} {T : Graph α β}
    {g : β} {S : Set α}
    (hclosed : ∀ ⦃e u v⦄, (T.deleteEdges {g}).IsLink e u v → u ∈ S → v ∈ S)
    {a b : α} (Q : GraphWalk T a b) (ha : a ∈ S) (hg_not : g ∉ Q.edges) :
    GraphWalk ((T.deleteEdges {g}).induce S) a b :=
  match Q with
  | .nil _ => .nil ha
  | .cons (v := m) (e := e) hl rest =>
    have heg : e ≠ g := fun h => hg_not (by simp [GraphWalk.edges, h])
    have hdel : (T.deleteEdges {g}).IsLink e a m := by
      rw [Graph.deleteEdges_isLink]
      exact ⟨hl, fun h => heg (mem_singleton_iff.mp h)⟩
    have hm : m ∈ S := hclosed hdel ha
    have hl' : ((T.deleteEdges {g}).induce S).IsLink e a m := by
      rw [Graph.induce_isLink]
      exact ⟨hdel, ha, hm⟩
    .cons hl' (liftWalkToComponent hclosed rest hm
      (fun h => hg_not (List.mem_cons_of_mem _ h)))

private theorem liftWalkToComponent_support {α : Type u} {β : Type v} {T : Graph α β}
    {g : β} {S : Set α}
    (hclosed : ∀ ⦃e u v⦄, (T.deleteEdges {g}).IsLink e u v → u ∈ S → v ∈ S)
    {a b : α} (Q : GraphWalk T a b) (ha : a ∈ S) (hg_not : g ∉ Q.edges) :
    (liftWalkToComponent hclosed Q ha hg_not).support = Q.support := by
  induction Q with
  | nil _ => rfl
  | cons _ _ ih => exact congrArg (_ :: ·) (ih _ _)

private theorem liftWalkToComponent_edges {α : Type u} {β : Type v} {T : Graph α β}
    {g : β} {S : Set α}
    (hclosed : ∀ ⦃e u v⦄, (T.deleteEdges {g}).IsLink e u v → u ∈ S → v ∈ S)
    {a b : α} (Q : GraphWalk T a b) (ha : a ∈ S) (hg_not : g ∉ Q.edges) :
    (liftWalkToComponent hclosed Q ha hg_not).edges = Q.edges := by
  induction Q with
  | nil _ => rfl
  | cons _ _ ih => exact congrArg (_ :: ·) (ih _ _)

private theorem end_mem_of_walk {α : Type u} {β : Type v} {G : Graph α β} {a b : α}
    (Q : GraphWalk G a b) : b ∈ V(G) := by
  induction Q with
  | nil ha => exact ha
  | cons _ _ ih => exact ih

/-- Pad a tour minor model of `T` in `binWordTree h₀` (`1 ≤ h₀`) to height `h₀ + 1` via `false :: ·`
(plus `[]` for `v₀`), preserving `subVal` on all leaf-parent words. -/
theorem pad_binWord_tour_model {α : Type u} {β : Type v}
    {T : Graph α β} (hSimple : T.Simple) {v₀ : α} (_hv₀ : v₀ ∈ V(T))
    {L : List α} (_hL_mem : ∀ k : Fin L.length, L[k] ∈ V(T))
    {h₀ : ℕ} (hh₀ : 1 ≤ h₀)
    {ηv : α → Set (List Bool)} {ηe : β → List Bool}
    (hm : IsMinorModel T (binWordTree h₀) ηv ηe)
    (hroot : [] ∈ ηv v₀)
    {l : Fin L.length → List Bool}
    (hl_spec : ∀ k : Fin L.length, (l k).length = h₀ - 1 ∧ l k ∈ ηv L[k])
    (hl_mono : StrictMono (fun k : Fin L.length => subVal (l k))) :
    ∃ (ηv' : α → Set (List Bool)) (ηe' : β → List Bool) (l' : Fin L.length → List Bool),
      IsMinorModel T (binWordTree (h₀ + 1)) ηv' ηe' ∧
      [] ∈ ηv' v₀ ∧
      (∀ k : Fin L.length, (l' k).length = h₀ ∧ l' k ∈ ηv' L[k]) ∧
      (∀ k : Fin L.length, subVal (l' k) = subVal (l k)) ∧
      StrictMono (fun k : Fin L.length => subVal (l' k)) := by
  let ηv' : α → Set (List Bool) := fun u =>
    if u = v₀ then insert [] ((List.cons false) '' ηv u) else (List.cons false) '' ηv u
  let ηe' : β → List Bool := fun e => false :: ηe e
  let l' : Fin L.length → List Bool := fun k => false :: l k
  refine ⟨ηv', ηe', l', ?_, ?_, ?_, ?_, ?_⟩
  · refine isMinorModel_of_loopless_link
      (fun e _ u hl => hSimple.not_isLoopAt e u hl)
      (fun u hu => by
        dsimp only [ηv']
        split_ifs
        · exact ⟨[], mem_insert _ _⟩
        · obtain ⟨w, hw⟩ := hm.vertex_nonempty u hu
          exact ⟨false :: w, mem_image_of_mem _ hw⟩)
      (fun u hu w hw => by
        change w.length < h₀ + 1
        dsimp only [ηv'] at hw
        split_ifs at hw with huv
        · rcases mem_insert_iff.mp hw with rfl | ⟨w₀, hw₀, rfl⟩
          · simp
          · have hlt : w₀.length < h₀ := hm.vertex_subset u hu hw₀
            simp only [List.length_cons]; omega
        · obtain ⟨w₀, hw₀, rfl⟩ := hw
          have hlt : w₀.length < h₀ := hm.vertex_subset u hu hw₀
          simp only [List.length_cons]; omega)
      (fun u₁ hu₁ u₂ hu₂ hne => by
        rw [Set.disjoint_left]
        intro w hw₁ hw₂
        have hdisj := hm.vertex_disjoint u₁ hu₁ u₂ hu₂ hne
        dsimp only [ηv'] at hw₁ hw₂
        split_ifs at hw₁ with h1 <;> split_ifs at hw₂ with h2
        · exact hne (h1.trans h2.symm)
        · obtain ⟨y₂, hy₂, rfl⟩ := hw₂
          rcases mem_insert_iff.mp hw₁ with hnil | ⟨y₁, hy₁, heq⟩
          · cases hnil
          · injection heq with _ hy; subst hy
            exact Set.disjoint_left.mp hdisj hy₁ hy₂
        · obtain ⟨y₁, hy₁, rfl⟩ := hw₁
          rcases mem_insert_iff.mp hw₂ with hnil | ⟨y₂, hy₂, heq⟩
          · cases hnil
          · injection heq with _ hy; subst hy
            exact Set.disjoint_left.mp hdisj hy₁ hy₂
        · obtain ⟨y₁, hy₁, rfl⟩ := hw₁
          obtain ⟨y₂, hy₂, heq⟩ := hw₂
          injection heq with _ hy; subst hy
          exact Set.disjoint_left.mp hdisj hy₁ hy₂)
      (fun e₁ he₁ e₂ he₂ heq => by
        dsimp only [ηe'] at heq
        injection heq with _ heq'
        exact hm.edge_injOn he₁ he₂ heq')
      (fun e u v hl => by
        have hne : u ≠ v := fun h => hSimple.not_isLoopAt e u (h ▸ hl)
        obtain ⟨x, hx, y, hy, hl_bw⟩ := exists_isLink_of_isMinorModel hm hl hne
        obtain ⟨h_ne, h_lt, h_ends⟩ := hl_bw
        have hx' : false :: x ∈ ηv' u := by
          dsimp only [ηv']
          split_ifs
          · exact mem_insert_of_mem _ (mem_image_of_mem _ hx)
          · exact mem_image_of_mem _ hx
        have hy' : false :: y ∈ ηv' v := by
          dsimp only [ηv']
          split_ifs
          · exact mem_insert_of_mem _ (mem_image_of_mem _ hy)
          · exact mem_image_of_mem _ hy
        refine ⟨false :: x, hx', false :: y, hy', List.cons_ne_nil _ _,
          by simp only [ηe', List.length_cons]; omega, ?_⟩
        dsimp only [ηe']
        rw [dropLast_cons_ne_nil false h_ne]
        rcases h_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩)
      (fun u hu x hx y hy => ?_)
    obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm.connected u hu
    have himg : ∀ z₁ z₂, Relation.ReflTransGen K.Adj z₁ z₂ → z₁ ∈ ηv u → z₂ ∈ ηv u →
        Relation.ReflTransGen
          (((binWordTree (h₀ + 1)).deleteEdges (ηe' '' E(T))).induce (ηv' u)).Adj
          (false :: z₁) (false :: z₂) := by
      intro z₁ z₂ hrel hz₁ hz₂
      clear hz₂
      have hstep : ∀ a b, K.Adj a b →
          (((binWordTree (h₀ + 1)).deleteEdges (ηe' '' E(T))).induce (ηv' u)).Adj
            (false :: a) (false :: b) := by
        rintro a b ⟨f, hlf⟩
        have hlf_del : ((binWordTree h₀).deleteEdges (ηe '' E(T))).IsLink f a b := hlf.mono hK_le
        rw [Graph.deleteEdges_isLink] at hlf_del
        obtain ⟨⟨hf_ne, hf_lt, hf_ends⟩, hf_not_img⟩ := hlf_del
        have ha_u : a ∈ ηv u := hVK ▸ hlf.left_mem
        have hb_u : b ∈ ηv u := hVK ▸ hlf.right_mem
        have ha' : false :: a ∈ ηv' u := by
          dsimp only [ηv']; split_ifs
          · exact mem_insert_of_mem _ (mem_image_of_mem _ ha_u)
          · exact mem_image_of_mem _ ha_u
        have hb' : false :: b ∈ ηv' u := by
          dsimp only [ηv']; split_ifs
          · exact mem_insert_of_mem _ (mem_image_of_mem _ hb_u)
          · exact mem_image_of_mem _ hb_u
        refine ⟨false :: f, ?_⟩
        rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
        refine ⟨⟨⟨List.cons_ne_nil _ _, by simp only [List.length_cons]; omega, ?_⟩, ?_⟩, ha', hb'⟩
        · rw [dropLast_cons_ne_nil false hf_ne]
          rcases hf_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨rfl, rfl⟩
          · exact Or.inr ⟨rfl, rfl⟩
        · rintro ⟨e, he, heq⟩
          dsimp only [ηe'] at heq
          injection heq with _ hf_eq
          exact hf_not_img ⟨e, he, hf_eq⟩
      induction hrel with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a b _ hab ih_r => exact Relation.ReflTransGen.tail ih_r (hstep a b hab)
    have hnil_edge : u = v₀ →
        (((binWordTree (h₀ + 1)).deleteEdges (ηe' '' E(T))).induce (ηv' u)).Adj [] [false] := by
      intro huv
      have h0_mem : [] ∈ ηv' u := by dsimp only [ηv']; simp [huv]
      have h1_mem : [false] ∈ ηv' u := by
        dsimp only [ηv']; simp only [huv, ↓reduceIte]
        exact mem_insert_of_mem _ ⟨[], hroot, rfl⟩
      refine ⟨[false], ?_⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
      refine ⟨⟨⟨List.cons_ne_nil _ _, by simp; omega, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩, h0_mem, h1_mem⟩
      rintro ⟨e, he, heq⟩
      have hne_e : ηe e ≠ [] := (hm.edge_mem e he).1
      dsimp only [ηe'] at heq
      injection heq with _ hnil
      exact hne_e hnil
    dsimp only [ηv'] at hx hy
    by_cases huv : u = v₀
    · simp only [huv, ↓reduceIte] at hx hy
      have hto_f : ∀ z ∈ insert [] ((List.cons false) '' ηv v₀),
          Relation.ReflTransGen
            (((binWordTree (h₀ + 1)).deleteEdges (ηe' '' E(T))).induce (ηv' u)).Adj [false] z := by
        intro z hz
        rcases mem_insert_iff.mp hz with rfl | ⟨w, hw, rfl⟩
        · exact Relation.ReflTransGen.single (hnil_edge huv).symm
        · exact himg [] w (hK_conn.2 [] (hVK.symm ▸ huv ▸ hroot) w (hVK.symm ▸ huv ▸ hw))
            (huv ▸ hroot) (huv ▸ hw)
      exact Relation.ReflTransGen.trans
        (reflTransGen_symm_of (fun _ _ h => h.symm) (hto_f x hx)) (hto_f y hy)
    · simp only [huv, ↓reduceIte] at hx hy
      obtain ⟨wx, hwx, rfl⟩ := hx
      obtain ⟨wy, hwy, rfl⟩ := hy
      exact himg wx wy (hK_conn.2 wx (hVK.symm ▸ hwx) wy (hVK.symm ▸ hwy)) hwx hwy
  · dsimp only [ηv']; simp
  · intro k
    refine ⟨?_, ?_⟩
    · dsimp only [l']
      have hk := (hl_spec k).1
      simp only [List.length_cons]; omega
    · dsimp only [ηv', l']
      split_ifs
      · exact mem_insert_of_mem _ (mem_image_of_mem _ (hl_spec k).2)
      · exact mem_image_of_mem _ (hl_spec k).2
  · intro k; rfl
  · exact hl_mono

/-- Pad a tour minor model of `T` in `binWordTree h₀` to any target height `h₁ ≥ h₀`. -/
theorem pad_binWord_tour_model_to {α : Type u} {β : Type v}
    {T : Graph α β} (hSimple : T.Simple) {v₀ : α} (hv₀ : v₀ ∈ V(T))
    {L : List α} (hL_mem : ∀ k : Fin L.length, L[k] ∈ V(T))
    {h₀ h₁ : ℕ} (hh₀ : 1 ≤ h₀) (hh : h₀ ≤ h₁)
    {ηv : α → Set (List Bool)} {ηe : β → List Bool}
    (hm : IsMinorModel T (binWordTree h₀) ηv ηe)
    (hroot : [] ∈ ηv v₀)
    {l : Fin L.length → List Bool}
    (hl_spec : ∀ k : Fin L.length, (l k).length = h₀ - 1 ∧ l k ∈ ηv L[k])
    (hl_mono : StrictMono (fun k : Fin L.length => subVal (l k))) :
    ∃ (ηv' : α → Set (List Bool)) (ηe' : β → List Bool) (l' : Fin L.length → List Bool),
      IsMinorModel T (binWordTree h₁) ηv' ηe' ∧
      [] ∈ ηv' v₀ ∧
      (∀ k : Fin L.length, (l' k).length = h₁ - 1 ∧ l' k ∈ ηv' L[k]) ∧
      StrictMono (fun k : Fin L.length => subVal (l' k)) := by
  rcases Nat.exists_eq_add_of_le hh with ⟨d, hd⟩
  rw [hd]
  clear hh hd
  induction d with
  | zero => exact ⟨ηv, ηe, l, hm, hroot, hl_spec, hl_mono⟩
  | succ d ih =>
    obtain ⟨ηv₁, ηe₁, l₁, hm₁, hroot₁, hl₁, hmono₁⟩ := ih
    obtain ⟨ηv₂, ηe₂, l₂, hm₂, hroot₂, hl₂, _, hmono₂⟩ :=
      pad_binWord_tour_model hSimple hv₀ hL_mem (by omega) hm₁ hroot₁ hl₁ hmono₁
    refine ⟨ηv₂, ηe₂, l₂, hm₂, hroot₂, ?_, hmono₂⟩
    intro k
    exact ⟨by have := (hl₂ k).1; omega, (hl₂ k).2⟩

/-- **Tree Tour Minor Model Theorem**: Every finite simple connected acyclic graph `T` with a closed
walk `W : GraphWalk T v₀ v₀` using every edge `e ∈ E(T)` exactly twice (`W.edges.count e = 2`) admits
a minor model `(ηv, ηe)` in `binWordTree h` (`1 ≤ h`) with `[] ∈ ηv v₀` and strictly increasing
leaf-parent words `l k ∈ ηv(W.support[k])` of length `h - 1`. -/
theorem exists_binWord_tour_model {α : Type u} {β : Type v} [DecidableEq β]
    (T : Graph α β) (hSimple : T.Simple) (hVT : V(T).Finite) (hET : E(T).Finite)
    (hNoCirc : ∀ C' ≤ T, ¬ GM09.IsGraphCircuit T C')
    {v₀ : α} (hv₀ : v₀ ∈ V(T))
    (hConn : ∀ z ∈ V(T), Relation.ReflTransGen T.Adj v₀ z)
    (W : GraphWalk T v₀ v₀)
    (hCount : ∀ e ∈ E(T), W.edges.count e = 2) :
    ∃ (h : ℕ) (ηv : α → Set (List Bool)) (ηe : β → List Bool)
      (l : Fin W.support.length → List Bool),
      1 ≤ h ∧
      IsMinorModel T (binWordTree h) ηv ηe ∧
      [] ∈ ηv v₀ ∧
      (∀ k : Fin W.support.length, (l k).length = h - 1 ∧ l k ∈ ηv W.support[k]) ∧
      StrictMono (fun k : Fin W.support.length => subVal (l k)) := by
  suffices hind : ∀ m : ℕ, ∀ (T₀ : Graph α β),
      T₀.Simple → V(T₀).Finite → E(T₀).Finite → E(T₀).ncard = m →
      (∀ C' ≤ T₀, ¬ GM09.IsGraphCircuit T₀ C') →
      ∀ {r₀ : α} (hr₀ : r₀ ∈ V(T₀)),
      (∀ z ∈ V(T₀), Relation.ReflTransGen T₀.Adj r₀ z) →
      ∀ (W₀ : GraphWalk T₀ r₀ r₀),
      (∀ e ∈ E(T₀), W₀.edges.count e = 2) →
      ∃ (h : ℕ) (ηv : α → Set (List Bool)) (ηe : β → List Bool)
        (l : Fin W₀.support.length → List Bool),
        1 ≤ h ∧
        IsMinorModel T₀ (binWordTree h) ηv ηe ∧
        [] ∈ ηv r₀ ∧
        (∀ k : Fin W₀.support.length, (l k).length = h - 1 ∧ l k ∈ ηv W₀.support[k]) ∧
        StrictMono (fun k : Fin W₀.support.length => subVal (l k)) from
    hind E(T).ncard T hSimple hVT hET rfl hNoCirc hv₀ hConn W hCount
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro T₀ hS₀ hVT₀ hET₀ hm hNoCirc₀ x hr₀ hConn₀ W₀ hCount₀
    cases W₀ with
    | nil _ =>
      have hE_emp : E(T₀) = ∅ := by
        ext e
        simp only [mem_empty_iff_false, iff_false]
        intro he
        have hc := hCount₀ e he
        simp [GraphWalk.edges] at hc
      have hV_sing : ∀ z ∈ V(T₀), z = x := by
        intro z hz
        cases hConn₀ z hz with
        | refl => rfl
        | @tail b _ _ hab =>
          obtain ⟨e, hl⟩ := hab
          exact (notMem_empty e (hE_emp ▸ hl.edge_mem)).elim
      refine ⟨1, fun u => if u = x then {[]} else ∅, fun _ => [], fun _ => [], le_rfl,
        ?_, by simp, ?_, ?_⟩
      · exact isMinorModel_of_loopless_link
          (fun e he => (notMem_empty e (hE_emp ▸ he)).elim)
          (fun u hu => by rw [hV_sing u hu]; simp)
          (fun u hu w hw => by rw [hV_sing u hu] at hw; simp at hw; subst hw; simp [binWordTree])
          (fun u₁ hu₁ u₂ hu₂ hne => (hne ((hV_sing u₁ hu₁).trans (hV_sing u₂ hu₂).symm)).elim)
          (fun e₁ he₁ => (notMem_empty e₁ (hE_emp ▸ he₁)).elim)
          (fun e _ _ hl => (notMem_empty e (hE_emp ▸ hl.edge_mem)).elim)
          (fun u hu wx hwx wy hwy => by
            rw [hV_sing u hu] at hwx hwy
            simp only [↓reduceIte, mem_singleton_iff] at hwx hwy
            subst hwx hwy
            exact Relation.ReflTransGen.refl)
      · intro k
        have hk_lt : k.1 < 1 := by simpa [GraphWalk.support] using k.2
        have hk0 : k.1 = 0 := by omega
        refine ⟨rfl, ?_⟩
        change [] ∈ (if [x][k.1] = x then ({[]} : Set (List Bool)) else ∅)
        simp [hk0]
      · intro k₁ k₂ hlt
        have h1 : k₁.1 < 1 := by simpa [GraphWalk.support] using k₁.2
        have h2 : k₂.1 < 1 := by simpa [GraphWalk.support] using k₂.2
        simp only [Fin.lt_def] at hlt
        omega
    | @cons _ y _ g hl_xy W_rest =>
      have hg_E : g ∈ E(T₀) := hl_xy.edge_mem
      have hxy : x ≠ y := fun h => hS₀.not_isLoopAt g x (by rw [← h] at hl_xy; exact hl_xy)
      have hg_count_all : (GraphWalk.cons hl_xy W_rest).edges.count g = 2 := hCount₀ g hg_E
      have hg_count_rest : W_rest.edges.count g = 1 := by
        simp only [GraphWalk.edges, List.count_cons_self] at hg_count_all
        omega
      have hg_mem_rest : g ∈ W_rest.edges := List.count_pos_iff.mp (by omega)
      obtain ⟨p, q, Q_y, hl_pq, Q_x, hg_not_Qy, hrest_edg, hrest_sup⟩ :=
        split_walk_first_edge W_rest g hg_mem_rest
      have hg_not_Qx : g ∉ Q_x.edges := by
        have hc := hg_count_rest
        rw [hrest_edg, List.count_append, List.count_cons_self,
          List.count_eq_zero.mpr hg_not_Qy] at hc
        exact List.count_eq_zero.mp (by omega)
      let T' := T₀.deleteEdges {g}
      have hT'_le : T' ≤ T₀ := Graph.deleteEdges_le
      have hnot_conn : ¬ Relation.ReflTransGen T'.Adj x y :=
        not_reflTransGen_deleteEdge_of_no_circuit hS₀ hNoCirc₀ hl_xy
      let V_x : Set α := {z ∈ V(T₀) | Relation.ReflTransGen T'.Adj x z}
      let V_y : Set α := {z ∈ V(T₀) | Relation.ReflTransGen T'.Adj y z}
      have hx_Vx : x ∈ V_x := ⟨hr₀, Relation.ReflTransGen.refl⟩
      have hy_Vy : y ∈ V_y := ⟨hl_xy.right_mem, Relation.ReflTransGen.refl⟩
      have hVx_closed : ∀ ⦃e u v⦄, T'.IsLink e u v → u ∈ V_x → v ∈ V_x := by
        intro e u v hl hu
        exact ⟨((Graph.deleteEdges_isLink T₀ {g} e u v) ▸ hl).1.right_mem,
          Relation.ReflTransGen.tail hu.2 ⟨e, hl⟩⟩
      have hVy_closed : ∀ ⦃e u v⦄, T'.IsLink e u v → u ∈ V_y → v ∈ V_y := by
        intro e u v hl hu
        exact ⟨((Graph.deleteEdges_isLink T₀ {g} e u v) ▸ hl).1.right_mem,
          Relation.ReflTransGen.tail hu.2 ⟨e, hl⟩⟩
      have hVx_Vy_disj : Disjoint V_x V_y := by
        rw [Set.disjoint_left]
        intro z hzx hzy
        exact hnot_conn (Relation.ReflTransGen.trans hzx.2
          (reflTransGen_symm_of (fun _ _ h => h.symm) hzy.2))
      have hVx_Vy_cover : ∀ z ∈ V(T₀), z ∈ V_x ∨ z ∈ V_y := by
        intro z hz
        have hconn_z := hConn₀ z hz
        induction hconn_z with
        | refl => exact Or.inl hx_Vx
        | @tail a b _ hab ih_z =>
          obtain ⟨e, hl_ab⟩ := hab
          by_cases heg : e = g
          · subst heg
            rcases hl_ab.left_eq_or_eq hl_xy with rfl | rfl
            · rw [hl_ab.right_unique hl_xy]
              exact Or.inr hy_Vy
            · rw [hl_ab.right_unique hl_xy.symm]
              exact Or.inl hx_Vx
          · have hdel : T'.IsLink e a b := by
              rw [Graph.deleteEdges_isLink]
              exact ⟨hl_ab, fun h => heg (mem_singleton_iff.mp h)⟩
            rcases ih_z hl_ab.left_mem with ha_x | ha_y
            · exact Or.inl (hVx_closed hdel ha_x)
            · exact Or.inr (hVy_closed hdel ha_y)
      let T_x := T'.induce V_x
      let T_y := T'.induce V_y
      have hTx_le' : T_x ≤ T' := Graph.induce_le (fun _ hz => hz.1)
      have hTy_le' : T_y ≤ T' := Graph.induce_le (fun _ hz => hz.1)
      have hTx_le : T_x ≤ T₀ := hTx_le'.trans hT'_le
      have hTy_le : T_y ≤ T₀ := hTy_le'.trans hT'_le
      let W_y_raw : GraphWalk T_y y p := liftWalkToComponent hVy_closed Q_y hy_Vy hg_not_Qy
      have hp_Vy : p ∈ V_y := end_mem_of_walk W_y_raw
      -- `Q_x` runs from `q` to `x`; reverse or check `q ∈ V_x`
      have hq_Vx : q ∈ V_x := by
        have hrev : ∀ {a b : α} (Q : GraphWalk T₀ a b), g ∉ Q.edges → b ∈ V_x → a ∈ V_x := by
          intro a b Q
          induction Q with
          | nil _ => exact fun _ hb => hb
          | @cons u v w e hl rest ih_q =>
            intro hg_n hw_x
            have heg : e ≠ g := fun h => hg_n (by simp [GraphWalk.edges, h])
            have hv_x : v ∈ V_x := ih_q (fun h => hg_n (List.mem_cons_of_mem _ h)) hw_x
            have hdel : T'.IsLink e v u := by
              rw [Graph.deleteEdges_isLink]
              exact ⟨hl.symm, fun h => heg (mem_singleton_iff.mp h)⟩
            exact hVx_closed hdel hv_x
        exact hrev Q_x hg_not_Qx hx_Vx
      have hp_eq_y : p = y := by
        rcases hl_pq.left_eq_or_eq hl_xy with hp_x | hp_y
        · exact (Set.disjoint_left.mp hVx_Vy_disj (hp_x ▸ hx_Vx) hp_Vy).elim
        · exact hp_y
      have hq_eq_x : q = x := by
        rw [hp_eq_y] at hl_pq
        exact hl_pq.right_unique hl_xy.symm
      subst p
      subst q
      let W_y : GraphWalk T_y y y := W_y_raw
      let W_x : GraphWalk T_x x x := liftWalkToComponent hVx_closed Q_x hx_Vx hg_not_Qx
      have hWy_sup : W_y.support = Q_y.support := liftWalkToComponent_support _ _ _ _
      have hWy_edg : W_y.edges = Q_y.edges := liftWalkToComponent_edges _ _ _ _
      have hWx_sup : W_x.support = Q_x.support := liftWalkToComponent_support _ _ _ _
      have hWx_edg : W_x.edges = Q_x.edges := liftWalkToComponent_edges _ _ _ _
      have hW_sup_eq :
          (GraphWalk.cons hl_xy W_rest).support = [x] ++ W_y.support ++ W_x.support := by
        simp only [GraphWalk.support, hrest_sup, hWy_sup, hWx_sup, List.cons_append, List.nil_append]
      have hE_part : ∀ e ∈ E(T₀), e = g ∨ e ∈ E(T_x) ∨ e ∈ E(T_y) := by
        intro e he
        by_cases heg : e = g
        · exact Or.inl heg
        · obtain ⟨u, v, hl⟩ := T₀.exists_isLink_of_mem_edgeSet he
          have hdel : T'.IsLink e u v := by
            rw [Graph.deleteEdges_isLink]
            exact ⟨hl, fun h => heg (mem_singleton_iff.mp h)⟩
          rcases hVx_Vy_cover u hl.left_mem with hu_x | hu_y
          · exact Or.inr (Or.inl (Graph.IsLink.edge_mem (by
              change T'.IsLink e u v ∧ u ∈ V_x ∧ v ∈ V_x
              exact ⟨hdel, hu_x, hVx_closed hdel hu_x⟩)))
          · exact Or.inr (Or.inr (Graph.IsLink.edge_mem (by
              change T'.IsLink e u v ∧ u ∈ V_y ∧ v ∈ V_y
              exact ⟨hdel, hu_y, hVy_closed hdel hu_y⟩)))
      have hETx_disj_g : g ∉ E(T_x) := by
        intro hg_in
        obtain ⟨u, v, hl⟩ := T_x.exists_isLink_of_mem_edgeSet hg_in
        have hdel : T'.IsLink g u v := hl.mono hTx_le'
        exact ((Graph.deleteEdges_isLink T₀ {g} g u v) ▸ hdel).2 (mem_singleton g)
      have hETy_disj_g : g ∉ E(T_y) := by
        intro hg_in
        obtain ⟨u, v, hl⟩ := T_y.exists_isLink_of_mem_edgeSet hg_in
        have hdel : T'.IsLink g u v := hl.mono hTy_le'
        exact ((Graph.deleteEdges_isLink T₀ {g} g u v) ▸ hdel).2 (mem_singleton g)
      have hETx_ETy_disj : Disjoint E(T_x) E(T_y) := by
        rw [Set.disjoint_left]
        intro e hex hey
        obtain ⟨u₁, v₁, hl₁⟩ := T_x.exists_isLink_of_mem_edgeSet hex
        obtain ⟨u₂, v₂, hl₂⟩ := T_y.exists_isLink_of_mem_edgeSet hey
        have h1 : T₀.IsLink e u₁ v₁ := hl₁.mono hTx_le
        have h2 : T₀.IsLink e u₂ v₂ := hl₂.mono hTy_le
        have hu₁_x : u₁ ∈ V_x := hl₁.left_mem
        rcases h1.left_eq_or_eq h2 with rfl | rfl
        · exact Set.disjoint_left.mp hVx_Vy_disj hu₁_x hl₂.left_mem
        · exact Set.disjoint_left.mp hVx_Vy_disj hu₁_x hl₂.right_mem
      have hmem_edges_sub : ∀ {H : Graph α β} {a b : α} (Q : GraphWalk H a b) {f : β},
          f ∈ Q.edges → f ∈ E(H) := by
        intro H a b Q f hf
        induction Q with
        | nil _ => cases hf
        | cons hl _ ih_e =>
          rcases List.mem_cons.mp hf with rfl | hr
          · exact hl.edge_mem
          · exact ih_e hr
      have hCount_x : ∀ e ∈ E(T_x), W_x.edges.count e = 2 := by
        intro e he
        have heg : e ≠ g := fun h => hETx_disj_g (h ▸ he)
        have hnot_y : e ∉ W_y.edges := fun hy =>
          Set.disjoint_left.mp hETx_ETy_disj he (hmem_edges_sub W_y hy)
        have hall := hCount₀ e (hTx_le.edgeSet_mono he)
        simp only [GraphWalk.edges, hrest_edg, ← hWy_edg, ← hWx_edg] at hall
        rw [List.count_cons_of_ne (Ne.symm heg), List.count_append,
          List.count_cons_of_ne (Ne.symm heg), List.count_eq_zero.mpr hnot_y] at hall
        omega
      have hCount_y : ∀ e ∈ E(T_y), W_y.edges.count e = 2 := by
        intro e he
        have heg : e ≠ g := fun h => hETy_disj_g (h ▸ he)
        have hnot_x : e ∉ W_x.edges := fun hx =>
          Set.disjoint_left.mp hETx_ETy_disj (hmem_edges_sub W_x hx) he
        have hall := hCount₀ e (hTy_le.edgeSet_mono he)
        simp only [GraphWalk.edges, hrest_edg, ← hWy_edg, ← hWx_edg] at hall
        rw [List.count_cons_of_ne (Ne.symm heg), List.count_append,
          List.count_cons_of_ne (Ne.symm heg), List.count_eq_zero.mpr hnot_x] at hall
        omega
      have hConn_x : ∀ z ∈ V(T_x), Relation.ReflTransGen T_x.Adj x z := by
        intro z hz; have hz' : Relation.ReflTransGen T'.Adj x z := hz.2; clear hz
        have hstep : ∀ a b, Relation.ReflTransGen T'.Adj x a → T'.Adj a b → T_x.Adj a b := by
          rintro a b hxa ⟨e, hl⟩
          have ha : a ∈ V_x := ⟨((Graph.deleteEdges_isLink T₀ {g} e a b) ▸ hl).1.left_mem, hxa⟩
          exact ⟨e, by change T'.IsLink e a b ∧ a ∈ V_x ∧ b ∈ V_x; exact ⟨hl, ha, hVx_closed hl ha⟩⟩
        induction hz' with
        | refl => exact Relation.ReflTransGen.refl
        | @tail a b hxa hab ih_c => exact Relation.ReflTransGen.tail ih_c (hstep a b hxa hab)
      have hConn_y : ∀ z ∈ V(T_y), Relation.ReflTransGen T_y.Adj y z := by
        intro z hz; have hz' : Relation.ReflTransGen T'.Adj y z := hz.2; clear hz
        have hstep : ∀ a b, Relation.ReflTransGen T'.Adj y a → T'.Adj a b → T_y.Adj a b := by
          rintro a b hya ⟨e, hl⟩
          have ha : a ∈ V_y := ⟨((Graph.deleteEdges_isLink T₀ {g} e a b) ▸ hl).1.left_mem, hya⟩
          exact ⟨e, by change T'.IsLink e a b ∧ a ∈ V_y ∧ b ∈ V_y; exact ⟨hl, ha, hVy_closed hl ha⟩⟩
        induction hz' with
        | refl => exact Relation.ReflTransGen.refl
        | @tail a b hya hab ih_c => exact Relation.ReflTransGen.tail ih_c (hstep a b hya hab)
      have hm_x : E(T_x).ncard < m := by
        rw [← hm]
        exact ncard_lt_ncard ⟨hTx_le.edgeSet_mono, fun hsub => hETx_disj_g (hsub hg_E)⟩ hET₀
      have hm_y : E(T_y).ncard < m := by
        rw [← hm]
        exact ncard_lt_ncard ⟨hTy_le.edgeSet_mono, fun hsub => hETy_disj_g (hsub hg_E)⟩ hET₀
      obtain ⟨hx0, ηvx0, ηex0, lx0, hhx0, hmx0, hrootx0, hlx0, hmonox0⟩ :=
        ih E(T_x).ncard hm_x T_x (Simple.mono hS₀ hTx_le) (hVT₀.subset hTx_le.vertexSet_mono)
          (hET₀.subset hTx_le.edgeSet_mono) rfl
          (fun C' hC' => by rw [isGraphCircuit_iff_of_le hTx_le hC']; exact hNoCirc₀ C' (hC'.trans hTx_le))
          hx_Vx hConn_x W_x hCount_x
      obtain ⟨hy0, ηvy0, ηey0, ly0, hhy0, hmy0, hrooty0, hly0, hmonoy0⟩ :=
        ih E(T_y).ncard hm_y T_y (Simple.mono hS₀ hTy_le) (hVT₀.subset hTy_le.vertexSet_mono)
          (hET₀.subset hTy_le.edgeSet_mono) rfl
          (fun C' hC' => by rw [isGraphCircuit_iff_of_le hTy_le hC']; exact hNoCirc₀ C' (hC'.trans hTy_le))
          hy_Vy hConn_y W_y hCount_y
      let h₀ := max hx0 hy0
      have hh₀ : 1 ≤ h₀ := le_trans hhx0 (le_max_left _ _)
      have hWx_mem : ∀ k : Fin W_x.support.length, W_x.support[k] ∈ V(T_x) := by
        intro k
        have hmem_s : ∀ {a b : α} (Q : GraphWalk T_x a b), ∀ z ∈ Q.support, z ∈ V(T_x) := by
          intro a b Q z hz
          induction Q with
          | nil ha => rcases List.mem_singleton.mp hz with rfl; exact ha
          | cons hl _ ih_s =>
            rcases List.mem_cons.mp hz with rfl | hr
            · exact hl.left_mem
            · exact ih_s hr
        exact hmem_s W_x _ (List.getElem_mem _)
      have hWy_mem : ∀ k : Fin W_y.support.length, W_y.support[k] ∈ V(T_y) := by
        intro k
        have hmem_s : ∀ {a b : α} (Q : GraphWalk T_y a b), ∀ z ∈ Q.support, z ∈ V(T_y) := by
          intro a b Q z hz
          induction Q with
          | nil ha => rcases List.mem_singleton.mp hz with rfl; exact ha
          | cons hl _ ih_s =>
            rcases List.mem_cons.mp hz with rfl | hr
            · exact hl.left_mem
            · exact ih_s hr
        exact hmem_s W_y _ (List.getElem_mem _)
      obtain ⟨ηvx, ηex, lx, hmx, hrootx, hlx, hmonox⟩ :=
        pad_binWord_tour_model_to (Simple.mono hS₀ hTx_le) hx_Vx hWx_mem hhx0 (le_max_left hx0 hy0)
          hmx0 hrootx0 hlx0 hmonox0
      obtain ⟨ηvy, ηey, ly, hmy, hrooty, hly, hmonoy⟩ :=
        pad_binWord_tour_model_to (Simple.mono hS₀ hTy_le) hy_Vy hWy_mem hhy0 (le_max_right hx0 hy0)
          hmy0 hrooty0 hly0 hmonoy0
      let h := h₀ + 2
      let pLR : List Bool → List Bool := fun w => false :: true :: w
      let pRL : List Bool → List Bool := fun w => true :: false :: w
      let spineLL : Set (List Bool) := {w | ∃ d < h₀, w = false :: false :: List.replicate d false}
      let ηv : α → Set (List Bool) := fun u =>
        if u = x then ({[], [false], [true]} : Set (List Bool)) ∪ spineLL ∪ (pRL '' ηvx u)
        else if u ∈ V_x then pRL '' ηvx u
        else pLR '' ηvy u
      let ηe : β → List Bool := fun e =>
        if e = g then [false, true]
        else if e ∈ E(T_x) then pRL (ηex e)
        else pLR (ηey e)
      let W₀_full := GraphWalk.cons hl_xy W_rest
      have hlen_full : W₀_full.support.length = 1 + W_y.support.length + W_x.support.length := by
        change (GraphWalk.cons hl_xy W_rest).support.length = _
        rw [hW_sup_eq, List.length_append, List.length_append, List.length_singleton]
      let l : Fin W₀_full.support.length → List Bool := fun k =>
        if hk0 : k.1 = 0 then
          false :: false :: List.replicate (h₀ - 1) false
        else if hky : k.1 - 1 < W_y.support.length then
          pLR (ly ⟨k.1 - 1, hky⟩)
        else
          pRL (lx ⟨k.1 - 1 - W_y.support.length, by omega⟩)
      refine ⟨h, ηv, ηe, l, by omega, ?_, ?_, ?_, ?_⟩
      · refine isMinorModel_of_loopless_link
          (fun e _ u hloop => hS₀.not_isLoopAt e u hloop)
          (fun u hu => by
            dsimp only [ηv]
            split_ifs with hux huVx
            · exact ⟨[], Or.inl (Or.inl (mem_insert _ _))⟩
            · obtain ⟨w, hw⟩ := hmx.vertex_nonempty u huVx
              exact ⟨pRL w, mem_image_of_mem _ hw⟩
            · have huVy : u ∈ V_y := (hVx_Vy_cover u hu).resolve_left huVx
              obtain ⟨w, hw⟩ := hmy.vertex_nonempty u huVy
              exact ⟨pLR w, mem_image_of_mem _ hw⟩)
          (fun u hu w hw => by
            change w.length < h₀ + 2
            dsimp only [ηv] at hw
            split_ifs at hw with hux huVx
            · rcases hw with (hw_top | ⟨d, hd, rfl⟩) | ⟨w₀, hw₀, rfl⟩
              · rcases hw_top with rfl | rfl | rfl <;> (simp; try omega)
              · simp only [List.length_cons, List.length_replicate]; omega
              · have hlt : w₀.length < h₀ := hmx.vertex_subset u (hux ▸ hx_Vx) hw₀
                simp only [pRL, List.length_cons]; omega
            · obtain ⟨w₀, hw₀, rfl⟩ := hw
              have hlt : w₀.length < h₀ := hmx.vertex_subset u huVx hw₀
              simp only [pRL, List.length_cons]; omega
            · have huVy : u ∈ V_y := (hVx_Vy_cover u hu).resolve_left huVx
              obtain ⟨w₀, hw₀, rfl⟩ := hw
              have hlt : w₀.length < h₀ := hmy.vertex_subset u huVy hw₀
              simp only [pLR, List.length_cons]; omega)
          (fun u₁ hu₁ u₂ hu₂ hne => by
            rw [Set.disjoint_left]
            intro w hw₁ hw₂
            have hnot_pRL_top : ∀ w₀, pRL w₀ ∉ ({[], [false], [true]} : Set (List Bool)) ∪ spineLL := by
              rintro w₀ (htop | ⟨d, _, heq⟩)
              · rcases htop with h1 | h1 | h1 <;> simp [pRL] at h1
              · simp [pRL] at heq
            have hnot_pLR_top : ∀ w₀, pLR w₀ ∉ ({[], [false], [true]} : Set (List Bool)) ∪ spineLL := by
              rintro w₀ (htop | ⟨d, _, heq⟩)
              · rcases htop with h1 | h1 | h1 <;> simp [pLR] at h1
              · simp [pLR] at heq
            dsimp only [ηv] at hw₁ hw₂
            split_ifs at hw₁ with h1x h1Vx <;> split_ifs at hw₂ with h2x h2Vx
            · exact hne (h1x.trans h2x.symm)
            · obtain ⟨w₂, hw₂', rfl⟩ := hw₂
              rcases hw₁ with htop | ⟨w₁, hw₁', heq⟩
              · exact hnot_pRL_top w₂ htop
              · simp only [pRL, List.cons.injEq, true_and] at heq
                exact Set.disjoint_left.mp (hmx.vertex_disjoint u₁ (h1x ▸ hx_Vx) u₂ h2Vx hne) hw₁' (heq ▸ hw₂')
            · obtain ⟨w₂, _, rfl⟩ := hw₂
              rcases hw₁ with htop | ⟨w₁, _, heq⟩
              · exact hnot_pLR_top w₂ htop
              · simp [pRL, pLR] at heq
            · obtain ⟨w₁, hw₁', rfl⟩ := hw₁
              rcases hw₂ with htop | ⟨w₂, hw₂', heq⟩
              · exact hnot_pRL_top w₁ htop
              · simp only [pRL, List.cons.injEq, true_and] at heq
                exact Set.disjoint_left.mp (hmx.vertex_disjoint u₁ h1Vx u₂ (h2x ▸ hx_Vx) hne) hw₁' (heq.symm ▸ hw₂')
            · obtain ⟨w₁, hw₁', rfl⟩ := hw₁
              obtain ⟨w₂, hw₂', heq⟩ := hw₂
              simp only [pRL, List.cons.injEq, true_and] at heq
              exact Set.disjoint_left.mp (hmx.vertex_disjoint u₁ h1Vx u₂ h2Vx hne) hw₁' (heq ▸ hw₂')
            · obtain ⟨w₁, _, rfl⟩ := hw₁
              obtain ⟨w₂, _, heq⟩ := hw₂
              simp [pRL, pLR] at heq
            · obtain ⟨w₁, _, rfl⟩ := hw₁
              rcases hw₂ with htop | ⟨w₂, _, heq⟩
              · exact hnot_pLR_top w₁ htop
              · simp [pRL, pLR] at heq
            · obtain ⟨w₁, _, rfl⟩ := hw₁
              obtain ⟨w₂, _, heq⟩ := hw₂
              simp [pRL, pLR] at heq
            · have h1Vy : u₁ ∈ V_y := (hVx_Vy_cover u₁ hu₁).resolve_left h1Vx
              have h2Vy : u₂ ∈ V_y := (hVx_Vy_cover u₂ hu₂).resolve_left h2Vx
              obtain ⟨w₁, hw₁', rfl⟩ := hw₁
              obtain ⟨w₂, hw₂', heq⟩ := hw₂
              simp only [pLR, List.cons.injEq, true_and] at heq
              exact Set.disjoint_left.mp (hmy.vertex_disjoint u₁ h1Vy u₂ h2Vy hne) hw₁' (heq ▸ hw₂'))
          (fun e₁ he₁ e₂ he₂ heq => by
            have hηe_g : ηe g = [false, true] := by dsimp only [ηe]; simp only [↓reduceIte]
            have hηe_x : ∀ e ∈ E(T_x), ηe e = pRL (ηex e) := by
              intro e hex
              have hne : e ≠ g := fun h => hETx_disj_g (h ▸ hex)
              dsimp only [ηe]; simp only [hne, hex, ↓reduceIte]
            have hηe_y : ∀ e ∈ E(T_y), ηe e = pLR (ηey e) := by
              intro e hey
              have hne : e ≠ g := fun h => hETy_disj_g (h ▸ hey)
              have hnotx : e ∉ E(T_x) := Set.disjoint_right.mp hETx_ETy_disj hey
              dsimp only [ηe]; simp only [hne, hnotx, ↓reduceIte]
            rcases hE_part e₁ he₁ with rfl | he₁x | he₁y <;>
              rcases hE_part e₂ he₂ with rfl | he₂x | he₂y
            · rfl
            · rw [hηe_g, hηe_x e₂ he₂x] at heq; cases heq
            · rw [hηe_g, hηe_y e₂ he₂y] at heq
              dsimp only [pLR] at heq
              injection heq with _ h2; injection h2 with _ hnil
              exact ((hmy.edge_mem e₂ he₂y).1 hnil.symm).elim
            · rw [hηe_x e₁ he₁x, hηe_g] at heq; cases heq
            · rw [hηe_x e₁ he₁x, hηe_x e₂ he₂x] at heq
              dsimp only [pRL] at heq
              injection heq with _ h2; injection h2 with _ heq'
              exact hmx.edge_injOn he₁x he₂x heq'
            · rw [hηe_x e₁ he₁x, hηe_y e₂ he₂y] at heq; cases heq
            · rw [hηe_y e₁ he₁y, hηe_g] at heq
              dsimp only [pLR] at heq
              injection heq with _ h2; injection h2 with _ hnil
              exact ((hmy.edge_mem e₁ he₁y).1 hnil).elim
            · rw [hηe_y e₁ he₁y, hηe_x e₂ he₂x] at heq; cases heq
            · rw [hηe_y e₁ he₁y, hηe_y e₂ he₂y] at heq
              dsimp only [pLR] at heq
              injection heq with _ h2; injection h2 with _ heq'
              exact hmy.edge_injOn he₁y he₂y heq')
          (fun e u v hl => by
            have huv : u ≠ v := fun h => hS₀.not_isLoopAt e u (h ▸ hl)
            rcases hE_part e hl.edge_mem with heg | hex | hey
            · subst e
              have hxf_mem : [false] ∈ ηv x := by
                dsimp only [ηv]; simp only [↓reduceIte]
                exact Or.inl (Or.inl (mem_insert_of_mem _ (mem_insert _ _)))
              have hy_not_Vx : y ∉ V_x := Set.disjoint_right.mp hVx_Vy_disj hy_Vy
              have hy_ne_x : y ≠ x := fun h => hy_not_Vx (h ▸ hx_Vx)
              have hy_mem : [false, true] ∈ ηv y := by
                dsimp only [ηv]; simp only [hy_ne_x, hy_not_Vx, ↓reduceIte]; exact ⟨[], hrooty, rfl⟩
              have hg_link : (binWordTree h).IsLink (ηe g) [false] [false, true] := by
                dsimp only [ηe]; simp only [↓reduceIte]
                exact ⟨List.cons_ne_nil _ _, by dsimp only [h]; simp; try omega, Or.inr ⟨rfl, rfl⟩⟩
              rcases hl.left_eq_or_eq hl_xy with rfl | rfl
              · rw [hl.right_unique hl_xy]
                exact ⟨[false], hxf_mem, [false, true], hy_mem, hg_link⟩
              · rw [hl.right_unique hl_xy.symm]
                exact ⟨[false, true], hy_mem, [false], hxf_mem, hg_link.symm⟩
            · have heg : e ≠ g := fun h => hETx_disj_g (h ▸ hex)
              obtain ⟨u', v', hl_x⟩ := T_x.exists_isLink_of_mem_edgeSet hex
              have hl_x0 : T₀.IsLink e u' v' := hl_x.mono hTx_le
              have hl_uv_x : T_x.IsLink e u v := by
                rcases hl.left_eq_or_eq hl_x0 with rfl | rfl
                · rw [hl.right_unique hl_x0]; exact hl_x
                · rw [hl.right_unique hl_x0.symm]; exact hl_x.symm
              obtain ⟨wx, hwx, wy, hwy, h_ne, h_lt, h_ends⟩ := exists_isLink_of_isMinorModel hmx hl_uv_x huv
              have hwx' : pRL wx ∈ ηv u := by
                dsimp only [ηv]; split_ifs
                · exact Or.inr (mem_image_of_mem _ hwx)
                · exact mem_image_of_mem _ hwx
                · exact (‹u ∉ V_x› hl_uv_x.left_mem).elim
              have hwy' : pRL wy ∈ ηv v := by
                dsimp only [ηv]; split_ifs
                · exact Or.inr (mem_image_of_mem _ hwy)
                · exact mem_image_of_mem _ hwy
                · exact (‹v ∉ V_x› hl_uv_x.right_mem).elim
              refine ⟨pRL wx, hwx', pRL wy, hwy', ?_⟩
              dsimp only [ηe]; simp only [heg, hex, ↓reduceIte]
              refine ⟨List.cons_ne_nil _ _, by simp [pRL, h]; omega, ?_⟩
              have hd1 := dropLast_cons_ne_nil true (List.cons_ne_nil false (ηex e))
              have hd2 := dropLast_cons_ne_nil false h_ne
              dsimp only [pRL]; rw [hd1, hd2]
              rcases h_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
            · have heg : e ≠ g := fun h => hETy_disj_g (h ▸ hey)
              have hnotx : e ∉ E(T_x) := Set.disjoint_right.mp hETx_ETy_disj hey
              obtain ⟨u', v', hl_y⟩ := T_y.exists_isLink_of_mem_edgeSet hey
              have hl_y0 : T₀.IsLink e u' v' := hl_y.mono hTy_le
              have hl_uv_y : T_y.IsLink e u v := by
                rcases hl.left_eq_or_eq hl_y0 with rfl | rfl
                · rw [hl.right_unique hl_y0]; exact hl_y
                · rw [hl.right_unique hl_y0.symm]; exact hl_y.symm
              obtain ⟨wx, hwx, wy, hwy, h_ne, h_lt, h_ends⟩ := exists_isLink_of_isMinorModel hmy hl_uv_y huv
              have hu_not_x : u ∉ V_x := Set.disjoint_right.mp hVx_Vy_disj hl_uv_y.left_mem
              have hv_not_x : v ∉ V_x := Set.disjoint_right.mp hVx_Vy_disj hl_uv_y.right_mem
              have hwx' : pLR wx ∈ ηv u := by
                dsimp only [ηv]
                simp only [show u ≠ x from fun h => hu_not_x (h ▸ hx_Vx), hu_not_x, ↓reduceIte]
                exact mem_image_of_mem _ hwx
              have hwy' : pLR wy ∈ ηv v := by
                dsimp only [ηv]
                simp only [show v ≠ x from fun h => hv_not_x (h ▸ hx_Vx), hv_not_x, ↓reduceIte]
                exact mem_image_of_mem _ hwy
              refine ⟨pLR wx, hwx', pLR wy, hwy', ?_⟩
              dsimp only [ηe]; simp only [heg, hnotx, ↓reduceIte]
              refine ⟨List.cons_ne_nil _ _, by simp [pLR, h]; omega, ?_⟩
              have hd1 := dropLast_cons_ne_nil false (List.cons_ne_nil true (ηey e))
              have hd2 := dropLast_cons_ne_nil true h_ne
              dsimp only [pLR]; rw [hd1, hd2]
              rcases h_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩)
          (fun u hu w₁ hw₁ w₂ hw₂ => ?_)
        have hlift_RL : ∀ u₀ ∈ V_x, (∀ w ∈ ηvx u₀, pRL w ∈ ηv u₀) →
            ∀ a b, a ∈ ηvx u₀ → b ∈ ηvx u₀ →
            Relation.ReflTransGen
              (((binWordTree h).deleteEdges (ηe '' E(T₀))).induce (ηv u₀)).Adj (pRL a) (pRL b) := by
          intro u₀ hu₀ hsub_u₀ a b ha hb
          obtain ⟨Kx, hKx_le, hVKx, hKx_conn⟩ := hmx.connected u₀ hu₀
          have hrel_x := hKx_conn.2 a (hVKx.symm ▸ ha) b (hVKx.symm ▸ hb); clear hb
          induction hrel_x with
          | refl => exact Relation.ReflTransGen.refl
          | @tail z₁ z₂ _ hz ih_r =>
            refine Relation.ReflTransGen.tail ih_r ?_
            obtain ⟨f, hlf⟩ := hz
            have hlf_del : ((binWordTree h₀).deleteEdges (ηex '' E(T_x))).IsLink f z₁ z₂ :=
              hlf.mono hKx_le
            rw [Graph.deleteEdges_isLink] at hlf_del
            obtain ⟨⟨hf_ne, hf_lt, hf_ends⟩, hf_not_img⟩ := hlf_del
            refine ⟨pRL f, ?_⟩
            rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
            refine ⟨⟨⟨List.cons_ne_nil _ _, by dsimp only [pRL, h]; simp; omega, ?_⟩, ?_⟩,
              hsub_u₀ z₁ (hVKx ▸ hlf.left_mem), hsub_u₀ z₂ (hVKx ▸ hlf.right_mem)⟩
            · have hd1 := dropLast_cons_ne_nil true (List.cons_ne_nil false f)
              have hd2 := dropLast_cons_ne_nil false hf_ne
              dsimp only [pRL]; rw [hd1, hd2]
              rcases hf_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
            · rintro ⟨e, he, heq⟩
              dsimp only [ηe] at heq
              rcases hE_part e he with rfl | hex | hey
              · simp only [↓reduceIte] at heq; dsimp only [pRL] at heq; cases heq
              · have hne : e ≠ g := fun h => hETx_disj_g (h ▸ hex)
                simp only [hne, hex, ↓reduceIte] at heq
                dsimp only [pRL] at heq
                injection heq with _ h2; injection h2 with _ heq'
                exact hf_not_img ⟨e, hex, heq'⟩
              · have hne : e ≠ g := fun h => hETy_disj_g (h ▸ hey)
                have hnotx : e ∉ E(T_x) := Set.disjoint_right.mp hETx_ETy_disj hey
                simp only [hne, hnotx, ↓reduceIte] at heq
                dsimp only [pRL, pLR] at heq; cases heq
        have hlift_LR : ∀ u₀ ∈ V_y, (∀ w ∈ ηvy u₀, pLR w ∈ ηv u₀) →
            ∀ a b, a ∈ ηvy u₀ → b ∈ ηvy u₀ →
            Relation.ReflTransGen
              (((binWordTree h).deleteEdges (ηe '' E(T₀))).induce (ηv u₀)).Adj (pLR a) (pLR b) := by
          intro u₀ hu₀ hsub_u₀ a b ha hb
          obtain ⟨Ky, hKy_le, hVKy, hKy_conn⟩ := hmy.connected u₀ hu₀
          have hrel_y := hKy_conn.2 a (hVKy.symm ▸ ha) b (hVKy.symm ▸ hb); clear hb
          induction hrel_y with
          | refl => exact Relation.ReflTransGen.refl
          | @tail z₁ z₂ _ hz ih_r =>
            refine Relation.ReflTransGen.tail ih_r ?_
            obtain ⟨f, hlf⟩ := hz
            have hlf_del : ((binWordTree h₀).deleteEdges (ηey '' E(T_y))).IsLink f z₁ z₂ :=
              hlf.mono hKy_le
            rw [Graph.deleteEdges_isLink] at hlf_del
            obtain ⟨⟨hf_ne, hf_lt, hf_ends⟩, hf_not_img⟩ := hlf_del
            refine ⟨pLR f, ?_⟩
            rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
            refine ⟨⟨⟨List.cons_ne_nil _ _, by dsimp only [pLR, h]; simp; omega, ?_⟩, ?_⟩,
              hsub_u₀ z₁ (hVKy ▸ hlf.left_mem), hsub_u₀ z₂ (hVKy ▸ hlf.right_mem)⟩
            · have hd1 := dropLast_cons_ne_nil false (List.cons_ne_nil true f)
              have hd2 := dropLast_cons_ne_nil true hf_ne
              dsimp only [pLR]; rw [hd1, hd2]
              rcases hf_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl ⟨rfl, rfl⟩
              · exact Or.inr ⟨rfl, rfl⟩
            · rintro ⟨e, he, heq⟩
              dsimp only [ηe] at heq
              rcases hE_part e he with rfl | hex | hey
              · simp only [↓reduceIte] at heq
                dsimp only [pLR] at heq
                injection heq with _ h2; injection h2 with _ hnil
                exact hf_ne hnil.symm
              · have hne : e ≠ g := fun h => hETx_disj_g (h ▸ hex)
                simp only [hne, hex, ↓reduceIte] at heq
                dsimp only [pRL, pLR] at heq; cases heq
              · have hne : e ≠ g := fun h => hETy_disj_g (h ▸ hey)
                have hnotx : e ∉ E(T_x) := Set.disjoint_right.mp hETx_ETy_disj hey
                simp only [hne, hnotx, ↓reduceIte] at heq
                dsimp only [pLR] at heq
                injection heq with _ h2; injection h2 with _ heq'
                exact hf_not_img ⟨e, hey, heq'⟩
        by_cases hux : u = x
        · subst u
          let Gx := ((binWordTree h).deleteEdges (ηe '' E(T₀))).induce (ηv x)
          have hnot_img : ∀ f : List Bool,
              (f = [false] ∨ f = [true] ∨ f = [true, false] ∨
                ∃ d < h₀, f = false :: false :: List.replicate d false) →
              f ∉ ηe '' E(T₀) := by
            rintro f hf ⟨e, he, heq⟩
            dsimp only [ηe] at heq
            rcases hE_part e he with rfl | hex | hey
            · simp only [↓reduceIte] at heq; subst heq
              rcases hf with h1 | h1 | h1 | ⟨_, _, h1⟩ <;> cases h1
            · have hne : e ≠ g := fun h => hETx_disj_g (h ▸ hex)
              simp only [hne, hex, ↓reduceIte] at heq
              dsimp only [pRL] at heq
              have hne_ex : ηex e ≠ [] := (hmx.edge_mem e hex).1
              rcases hf with h1 | h1 | h1 | ⟨_, _, h1⟩
              · rw [h1] at heq; cases heq
              · rw [h1] at heq; cases heq
              · rw [h1] at heq; injection heq with _ h2; injection h2 with _ hnil; exact hne_ex hnil
              · rw [h1] at heq; cases heq
            · have hne : e ≠ g := fun h => hETy_disj_g (h ▸ hey)
              have hnotx : e ∉ E(T_x) := Set.disjoint_right.mp hETx_ETy_disj hey
              simp only [hne, hnotx, ↓reduceIte] at heq
              dsimp only [pLR] at heq
              rcases hf with h1 | h1 | h1 | ⟨_, _, h1⟩ <;> (rw [h1] at heq; cases heq)
          have hnil_mem : [] ∈ ηv x := by
            dsimp only [ηv]; simp only [↓reduceIte]; exact Or.inl (Or.inl (mem_insert _ _))
          have hf_mem : [false] ∈ ηv x := by
            dsimp only [ηv]; simp only [↓reduceIte]; exact Or.inl (Or.inl (mem_insert_of_mem _ (mem_insert _ _)))
          have ht_mem : [true] ∈ ηv x := by
            dsimp only [ηv]; simp only [↓reduceIte]
            exact Or.inl (Or.inl (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))))
          have htf_mem : [true, false] ∈ ηv x := by
            dsimp only [ηv]; simp only [↓reduceIte]; exact Or.inr ⟨[], hrootx, rfl⟩
          have hadj_f : Gx.Adj [] [false] := ⟨[false], by
            rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
            exact ⟨⟨⟨List.cons_ne_nil _ _, by dsimp only [h]; simp; try omega, Or.inr ⟨rfl, rfl⟩⟩,
              hnot_img [false] (Or.inl rfl)⟩, hnil_mem, hf_mem⟩⟩
          have hadj_t : Gx.Adj [] [true] := ⟨[true], by
            rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
            exact ⟨⟨⟨List.cons_ne_nil _ _, by dsimp only [h]; simp; try omega, Or.inr ⟨rfl, rfl⟩⟩,
              hnot_img [true] (Or.inr (Or.inl rfl))⟩, hnil_mem, ht_mem⟩⟩
          have hadj_tf : Gx.Adj [true] [true, false] := ⟨[true, false], by
            rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
            exact ⟨⟨⟨List.cons_ne_nil _ _, by dsimp only [h]; simp; try omega, Or.inr ⟨rfl, rfl⟩⟩,
              hnot_img [true, false] (Or.inr (Or.inr (Or.inl rfl)))⟩, ht_mem, htf_mem⟩⟩
          have hspine_conn : ∀ d < h₀,
              Relation.ReflTransGen Gx.Adj [] (false :: false :: List.replicate d false) := by
            intro d hd
            have hrep : false :: false :: List.replicate d false = List.replicate (d + 2) false := rfl
            rw [hrep]
            exact reflTransGen_replicate_false (d + 2) (by dsimp only [h]; simp; omega)
              (fun j hj => by
                rcases j with _ | _ | j'
                · exact hnil_mem
                · exact hf_mem
                · dsimp only [ηv]; simp only [↓reduceIte]
                  exact Or.inl (Or.inr ⟨j', by omega, rfl⟩))
              (fun j hj1 hj2 => by
                rcases j with _ | _ | j'
                · omega
                · exact hnot_img [false] (Or.inl rfl)
                · exact hnot_img _ (Or.inr (Or.inr (Or.inr ⟨j', by omega, rfl⟩))))
          have hto_nil : ∀ w ∈ ηv x, Relation.ReflTransGen Gx.Adj [] w := by
            intro w hw
            dsimp only [ηv] at hw
            simp only [↓reduceIte] at hw
            rcases hw with (htop | ⟨d, hd, rfl⟩) | ⟨w₀, hw₀, rfl⟩
            · rcases htop with rfl | rfl | rfl
              · exact Relation.ReflTransGen.refl
              · exact Relation.ReflTransGen.single hadj_f
              · exact Relation.ReflTransGen.single hadj_t
            · exact hspine_conn d hd
            · refine Relation.ReflTransGen.trans
                (Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj_t) hadj_tf) ?_
              exact hlift_RL x hx_Vx
                (fun z hz => by dsimp only [ηv]; simp only [↓reduceIte]; exact Or.inr ⟨z, hz, rfl⟩)
                [] w₀ hrootx hw₀
          exact Relation.ReflTransGen.trans
            (reflTransGen_symm_of (fun _ _ h => h.symm) (hto_nil w₁ hw₁)) (hto_nil w₂ hw₂)
        · by_cases huVx : u ∈ V_x
          · dsimp only [ηv] at hw₁ hw₂
            simp only [hux, huVx, ↓reduceIte] at hw₁ hw₂
            obtain ⟨z₁, hz₁, rfl⟩ := hw₁
            obtain ⟨z₂, hz₂, rfl⟩ := hw₂
            exact hlift_RL u huVx
              (fun z hz => by dsimp only [ηv]; simp only [hux, huVx, ↓reduceIte]; exact ⟨z, hz, rfl⟩)
              z₁ z₂ hz₁ hz₂
          · have huVy : u ∈ V_y := (hVx_Vy_cover u hu).resolve_left huVx
            dsimp only [ηv] at hw₁ hw₂
            simp only [hux, huVx, ↓reduceIte] at hw₁ hw₂
            obtain ⟨z₁, hz₁, rfl⟩ := hw₁
            obtain ⟨z₂, hz₂, rfl⟩ := hw₂
            exact hlift_LR u huVy
              (fun z hz => by dsimp only [ηv]; simp only [hux, huVx, ↓reduceIte]; exact ⟨z, hz, rfl⟩)
              z₁ z₂ hz₁ hz₂
      · dsimp only [ηv]; simp only [↓reduceIte]; exact Or.inl (Or.inl (mem_insert _ _))
      · intro k
        have hget_eq : ∀ {L₁ L₂ : List α} (_hL : L₁ = L₂) {i₁ i₂ : ℕ} (_hi : i₁ = i₂)
            (h₁ : i₁ < L₁.length) (h₂ : i₂ < L₂.length), L₁[i₁]'h₁ = L₂[i₂]'h₂ := by
          rintro _ _ rfl _ _ rfl _ _; rfl
        have hk_bd : k.1 < 1 + W_y.support.length + W_x.support.length := hlen_full ▸ k.2
        have hsup_cons : W₀_full.support = x :: (W_y.support ++ W_x.support) := by
          dsimp only [W₀_full]
          rw [hW_sup_eq, List.singleton_append, List.cons_append]
        have hget : W₀_full.support[k] =
            (x :: (W_y.support ++ W_x.support))[k.1]'(by
              simp only [List.length_cons, List.length_append]; omega) :=
          hget_eq hsup_cons rfl k.2 _
        dsimp only [l]
        split_ifs with hk0 hky
        · refine ⟨by dsimp only [h]; simp; omega, ?_⟩
          have hkx : W₀_full.support[k] = x := by
            simp only [hget, hk0, List.getElem_cons_zero]
          rw [hkx]; dsimp only [ηv]; simp only [↓reduceIte]
          exact Or.inl (Or.inr ⟨h₀ - 1, by omega, rfl⟩)
        · refine ⟨by
            have hlen_y : (ly ⟨k.1 - 1, hky⟩).length = h₀ - 1 := (hly ⟨k.1 - 1, hky⟩).1
            dsimp only [pLR, h]; simp only [List.length_cons]; omega, ?_⟩
          obtain ⟨m', hm'⟩ : ∃ m', k.1 = m' + 1 := ⟨k.1 - 1, by omega⟩
          let ky : Fin W_y.support.length := ⟨k.1 - 1, hky⟩
          have hky_eq : W₀_full.support[k] = W_y.support[ky] := by
            simp only [hget, hm', List.getElem_cons_succ]
            rw [List.getElem_append_left (by omega)]
            exact hget_eq rfl (by dsimp only [ky]; omega) _ ky.2
          rw [hky_eq]
          have hmem_y : W_y.support[ky] ∈ V_y := hWy_mem ky
          have hnot_x : W_y.support[ky] ∉ V_x := Set.disjoint_right.mp hVx_Vy_disj hmem_y
          dsimp only [ηv]
          simp only [show W_y.support[ky] ≠ x from fun h => hnot_x (h ▸ hx_Vx),
            hnot_x, ↓reduceIte]
          exact mem_image_of_mem _ (hly ky).2
        · have hkx_lt : k.1 - 1 - W_y.support.length < W_x.support.length := by omega
          refine ⟨by
            have hlen_x : (lx ⟨k.1 - 1 - W_y.support.length, hkx_lt⟩).length = h₀ - 1 :=
              (hlx ⟨k.1 - 1 - W_y.support.length, hkx_lt⟩).1
            dsimp only [pRL, h]; simp only [List.length_cons]; omega, ?_⟩
          obtain ⟨m', hm'⟩ : ∃ m', k.1 = m' + 1 := ⟨k.1 - 1, by omega⟩
          let kx : Fin W_x.support.length := ⟨k.1 - 1 - W_y.support.length, hkx_lt⟩
          have hkx_eq : W₀_full.support[k] = W_x.support[kx] := by
            simp only [hget, hm', List.getElem_cons_succ]
            rw [List.getElem_append_right (by omega)]
            exact hget_eq rfl (by dsimp only [kx]; omega) _ kx.2
          rw [hkx_eq]
          have hmem_x : W_x.support[kx] ∈ V_x := hWx_mem kx
          dsimp only [ηv]
          split_ifs
          · exact Or.inr (mem_image_of_mem _ (hlx kx).2)
          · exact mem_image_of_mem _ (hlx kx).2
      · intro k₁ k₂ hlt
        have hsub_rep : ∀ d, subVal (List.replicate d false) = 0 := by
          intro d; induction d with
          | zero => rfl
          | succ d ih_d => simp [List.replicate_succ, subVal, ih_d]
        have hval_0 : subVal (false :: false :: List.replicate (h₀ - 1) false) = 0 := by
          simp [subVal, hsub_rep]
        have hval_LR : ∀ ky : Fin W_y.support.length,
            subVal (pLR (ly ky)) = 2 ^ (h₀ - 1) + subVal (ly ky) ∧
            subVal (ly ky) < 2 ^ (h₀ - 1) := by
          intro ky
          have hlen_y : (ly ky).length = h₀ - 1 := (hly ky).1
          have hlt_y := subVal_lt_pow (ly ky)
          rw [hlen_y] at hlt_y
          refine ⟨?_, hlt_y⟩
          dsimp only [pLR, subVal]
          simp only [hlen_y]
          try omega
        have hval_RL : ∀ kx : Fin W_x.support.length,
            subVal (pRL (lx kx)) = 2 ^ h₀ + subVal (lx kx) ∧
            subVal (lx kx) < 2 ^ (h₀ - 1) := by
          intro kx
          have hlen_x : (lx kx).length = h₀ - 1 := (hlx kx).1
          have hlt_x := subVal_lt_pow (lx kx)
          rw [hlen_x] at hlt_x
          have hexp : 2 ^ ((h₀ - 1) + 1) = 2 ^ h₀ := congrArg (2 ^ ·) (by omega)
          refine ⟨?_, hlt_x⟩
          dsimp only [pRL, subVal]
          simp only [List.length_cons, hlen_x, hexp]
          try omega
        have hpow_pos : 0 < 2 ^ (h₀ - 1) := by positivity
        have hpow_eq : 2 ^ h₀ = 2 * 2 ^ (h₀ - 1) := by
          rw [← pow_succ', show h₀ - 1 + 1 = h₀ by omega]
        have hk1_bd : k₁.1 < 1 + W_y.support.length + W_x.support.length := hlen_full ▸ k₁.2
        have hk2_bd : k₂.1 < 1 + W_y.support.length + W_x.support.length := hlen_full ▸ k₂.2
        simp only [Fin.lt_def] at hlt
        dsimp only [l]
        by_cases hk10 : k₁.1 = 0
        · have hk20 : ¬ k₂.1 = 0 := by omega
          simp only [hk10, hk20, ↓reduceDIte, hval_0]
          by_cases hk2y : k₂.1 - 1 < W_y.support.length
          · simp only [hk2y, ↓reduceDIte]
            obtain ⟨hv, _⟩ := hval_LR ⟨k₂.1 - 1, hk2y⟩; omega
          · simp only [hk2y, ↓reduceDIte]
            obtain ⟨hv, _⟩ := hval_RL ⟨k₂.1 - 1 - W_y.support.length, by omega⟩; omega
        · have hk20 : ¬ k₂.1 = 0 := by omega
          simp only [hk10, hk20, ↓reduceDIte]
          by_cases hk1y : k₁.1 - 1 < W_y.support.length
          · simp only [hk1y, ↓reduceDIte]
            by_cases hk2y : k₂.1 - 1 < W_y.support.length
            · simp only [hk2y, ↓reduceDIte]
              have hlt_y : (⟨k₁.1 - 1, hk1y⟩ : Fin W_y.support.length) < ⟨k₂.1 - 1, hk2y⟩ := by
                simp only [Fin.lt_def]; omega
              have hm_y := hmonoy hlt_y
              dsimp only at hm_y
              obtain ⟨hv1, _⟩ := hval_LR ⟨k₁.1 - 1, hk1y⟩
              obtain ⟨hv2, _⟩ := hval_LR ⟨k₂.1 - 1, hk2y⟩
              omega
            · simp only [hk2y, ↓reduceDIte]
              obtain ⟨hv1, hlt1⟩ := hval_LR ⟨k₁.1 - 1, hk1y⟩
              obtain ⟨hv2, _⟩ := hval_RL ⟨k₂.1 - 1 - W_y.support.length, by omega⟩
              omega
          · have hk2y : ¬ k₂.1 - 1 < W_y.support.length := by omega
            simp only [hk1y, hk2y, ↓reduceDIte]
            have hlt_x :
                (⟨k₁.1 - 1 - W_y.support.length, by omega⟩ : Fin W_x.support.length) <
                ⟨k₂.1 - 1 - W_y.support.length, by omega⟩ := by
              simp only [Fin.lt_def]; omega
            have hm_x := hmonox hlt_x
            dsimp only at hm_x
            obtain ⟨hv1, _⟩ := hval_RL ⟨k₁.1 - 1 - W_y.support.length, by omega⟩
            obtain ⟨hv2, _⟩ := hval_RL ⟨k₂.1 - 1 - W_y.support.length, by omega⟩
            omega

/-! ## 3. Greedy Monotone Divider and Spoke Placement -/

/-- Auxiliary inductive placement of `p` strictly increasing dividers and `m` strictly increasing
spoke indices inside monotone slot intervals `[a s, d s)`. -/
private theorem exists_monotone_dividers_and_spokes_aux :
    ∀ (n p m q H c₀ K : ℕ), p + m = n → 1 ≤ c₀ →
    ∀ (a d : Fin (q + 1) → ℕ) (g : Fin m → Fin (q + 1)) (f : Fin m → Fin (p + 1))
      (s₀ : Fin (q + 1)),
    c₀ ≤ a s₀ + K →
    (∀ r : Fin m, s₀ ≤ g r) →
    (∀ s : Fin (q + 1), a s + K + p + m < d s) →
    (∀ s₁ s₂ : Fin (q + 1), s₁ ≤ s₂ → a s₁ ≤ a s₂) →
    (∀ s : Fin (q + 1), d s ≤ H) →
    Monotone g → Monotone f →
    ∃ (b : Fin p → ℕ) (i : Fin m → ℕ),
      (∀ t : Fin p, c₀ ≤ b t ∧ b t < H) ∧ StrictMono b ∧
      (∀ r : Fin m, c₀ ≤ i r ∧ a (g r) ≤ i r ∧ i r < d (g r)) ∧ StrictMono i ∧
      (∀ (r : Fin m) (t : Fin p),
        ((f r).1 ≤ t.1 → i r < b t) ∧ (t.1 < (f r).1 → b t < i r)) := by
  intro n
  induction n with
  | zero =>
    intro p m _ H c₀ _ hpm _ _ _ _ _ _ _ _ _ _ _ _ _
    have hp0 : p = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hp0 hm0
    exact ⟨Fin.elim0, Fin.elim0, fun t => t.elim0, fun t => t.elim0,
      fun r => r.elim0, fun r => r.elim0, fun r => r.elim0⟩
  | succ n ih =>
    intro p m q H c₀ K hpm hc₀_pos a d g f s₀ hc₀ hr_s₀ hgap ha_mono hd_H hg_mono hf_mono
    rcases m with _ | m'
    · refine ⟨fun t => c₀ + t.1, Fin.elim0, ?_, ?_, fun r => r.elim0, fun r => r.elim0,
        fun r => r.elim0⟩
      · intro t
        dsimp only
        have ht := t.2
        have hlt := hgap s₀
        have hd_le := hd_H s₀
        exact ⟨by omega, by omega⟩
      · intro t₁ t₂ hlt; dsimp only; simp only [Fin.lt_def] at hlt; omega
    · by_cases hf0 : (f 0).1 = 0
      · let i₀ : ℕ := max c₀ (a (g 0))
        have hs₀_le : a s₀ ≤ a (g 0) := ha_mono s₀ (g 0) (hr_s₀ 0)
        have hi₀_le : i₀ ≤ a (g 0) + K := by dsimp only [i₀]; omega
        have hi₀_lt : i₀ < d (g 0) := by have := hgap (g 0); omega
        obtain ⟨b, i', hb_bd, hb_mono, hi'_bd, hi'_mono, hrel'⟩ :=
          ih p m' q H (i₀ + 1) (K + 1) (by omega) (by omega) a d
            (fun r' => g r'.succ) (fun r' => f r'.succ) (g 0)
            (by omega)
            (fun r' => hg_mono (Fin.zero_le _))
            (fun s => by have := hgap s; omega)
            ha_mono hd_H
            (fun r₁ r₂ hle => hg_mono (Fin.succ_le_succ_iff.mpr hle))
            (fun r₁ r₂ hle => hf_mono (Fin.succ_le_succ_iff.mpr hle))
        refine ⟨b, Fin.cons i₀ i', ?_, hb_mono, ?_, ?_, ?_⟩
        · exact fun t => ⟨le_trans (by dsimp only [i₀]; omega) (hb_bd t).1, (hb_bd t).2⟩
        · intro r
          refine Fin.cases ?_ (fun r' => ?_) r
          · simp only [Fin.cons_zero]
            exact ⟨by dsimp only [i₀]; omega, by dsimp only [i₀]; omega, hi₀_lt⟩
          · simp only [Fin.cons_succ]
            exact ⟨le_trans (by dsimp only [i₀]; omega) (hi'_bd r').1, (hi'_bd r').2.1,
              (hi'_bd r').2.2⟩
        · intro r₁ r₂ hlt
          cases r₁ using Fin.cases with
          | zero =>
            cases r₂ using Fin.cases with
            | zero => exact (lt_irrefl _ hlt).elim
            | succ r₂' => have := (hi'_bd r₂').1; simp only [Fin.cons_zero, Fin.cons_succ]; omega
          | succ r₁' =>
            cases r₂ using Fin.cases with
            | zero => simp at hlt
            | succ r₂' => exact hi'_mono (Fin.succ_lt_succ_iff.mp hlt)
        · intro r t
          cases r using Fin.cases with
          | zero =>
            simp only [Fin.cons_zero, hf0, Nat.zero_le, true_implies, not_lt_zero, false_implies,
              and_true]
            have := (hb_bd t).1; omega
          | succ r' => exact hrel' r' t
      · rcases p with _ | p'
        · have : (f 0).1 < 1 := (f 0).2
          omega
        · have hf_pos : ∀ r : Fin (m' + 1), 1 ≤ (f r).1 := by
            intro r
            have hle : (f 0).1 ≤ (f r).1 := hf_mono (Fin.zero_le r)
            omega
          let f' : Fin (m' + 1) → Fin (p' + 1) := fun r =>
            ⟨(f r).1 - 1, by have := (f r).2; have := hf_pos r; omega⟩
          have hf'_mono : Monotone f' := by
            intro r₁ r₂ hle
            have := hf_mono hle
            simp only [Fin.le_def, f'] at this ⊢
            omega
          have hc₀_lt_H : c₀ < H := by
            have := hgap s₀; have := hd_H s₀; omega
          obtain ⟨b', i, hb'_bd, hb'_mono, hi_bd, hi_mono, hrel'⟩ :=
            ih p' (m' + 1) q H (c₀ + 1) (K + 1) (by omega) (by omega) a d g f' s₀
              (by omega) hr_s₀ (fun s => by have := hgap s; omega)
              ha_mono hd_H hg_mono hf'_mono
          refine ⟨Fin.cons c₀ b', i, ?_, ?_, ?_, hi_mono, ?_⟩
          · intro t
            refine Fin.cases ?_ (fun t' => ?_) t
            · simp only [Fin.cons_zero]; exact ⟨le_rfl, hc₀_lt_H⟩
            · simp only [Fin.cons_succ]; exact ⟨by have := (hb'_bd t').1; omega, (hb'_bd t').2⟩
          · intro t₁ t₂ hlt
            cases t₁ using Fin.cases with
            | zero =>
              cases t₂ using Fin.cases with
              | zero => exact (lt_irrefl _ hlt).elim
              | succ t₂' => have := (hb'_bd t₂').1; simp only [Fin.cons_zero, Fin.cons_succ]; omega
            | succ t₁' =>
              cases t₂ using Fin.cases with
              | zero => simp at hlt
              | succ t₂' => exact hb'_mono (Fin.succ_lt_succ_iff.mp hlt)
          · exact fun r => ⟨by have := (hi_bd r).1; omega, (hi_bd r).2.1, (hi_bd r).2.2⟩
          · intro r t
            cases t using Fin.cases with
            | zero =>
              have hfp := hf_pos r; have hir := (hi_bd r).1
              simp only [Fin.cons_zero, Fin.val_zero]
              exact ⟨fun _ => by omega, fun _ => by omega⟩
            | succ t' =>
              have hr_t' := hrel' r t'; have hfp := hf_pos r
              simp only [Fin.cons_succ, Fin.val_succ]
              exact ⟨fun _ => hr_t'.1 (by dsimp only [f']; omega),
                fun _ => hr_t'.2 (by dsimp only [f']; omega)⟩

/-- Place `p` strictly increasing dividers `0 < b 0 < ... < b (p - 1) < H` and `m` strictly
increasing spoke indices `i 0 < ... < i (m - 1)` inside ordered intervals `[a s, d s)` of length
`≥ p + m + 2` in `[0, H)`. -/
theorem exists_monotone_dividers_and_spokes {p m q H : ℕ}
    (a d : Fin (q + 1) → ℕ) (g : Fin m → Fin (q + 1)) (f : Fin m → Fin (p + 1))
    (hlen : ∀ s : Fin (q + 1), a s + (p + m + 2) ≤ d s)
    (ha_mono : ∀ s₁ s₂ : Fin (q + 1), s₁ ≤ s₂ → a s₁ ≤ a s₂)
    (hd_H : ∀ s : Fin (q + 1), d s ≤ H)
    (hg_mono : Monotone g) (hf_mono : Monotone f) :
    ∃ (b : Fin p → ℕ) (i : Fin m → ℕ),
      (∀ t : Fin p, 1 ≤ b t ∧ b t < H) ∧ StrictMono b ∧
      (∀ r : Fin m, 1 ≤ i r ∧ a (g r) ≤ i r ∧ i r < d (g r)) ∧ StrictMono i ∧
      (∀ (r : Fin m) (t : Fin p),
        ((f r).1 ≤ t.1 → i r < b t) ∧ (t.1 < (f r).1 → b t < i r)) :=
  exists_monotone_dividers_and_spokes_aux (p + m) p m q H 1 1 rfl le_rfl a d g f 0
    (by omega) (fun _ => Fin.zero_le _) (fun s => by have := hlen s; omega)
    ha_mono hd_H hg_mono hf_mono
/-! ## 4. Cone Extension of `binWordTree` Tour Models to Spoke Intervals -/

/-- Extend a tour minor model `(ηv, ηe, l)` of `T` in `binWordTree h` (`1 ≤ h`) by depth `κ ≥ 1` to
`binWordTree (h + κ)` so that each tour entry `L[k]` owns the leaf-parent words of every spoke `i` in
`[2 ^ (κ + 1) * subVal (l k), 2 ^ (κ + 1) * (subVal (l k) + 1))` in `graphN d (h + κ + 1)`. -/
theorem cone_extend_binWord_tour {α : Type u} {β : Type v}
    {T : Graph α β} (hSimple : T.Simple)
    {L : List α} (_hL_mem : ∀ k : Fin L.length, L[k] ∈ V(T))
    {h : ℕ} (hh : 1 ≤ h) (κ : ℕ) (hκ : 1 ≤ κ)
    {ηv : α → Set (List Bool)} {ηe : β → List Bool}
    (hm : IsMinorModel T (binWordTree h) ηv ηe)
    {l : Fin L.length → List Bool}
    (hl_spec : ∀ k : Fin L.length, (l k).length = h - 1 ∧ l k ∈ ηv L[k])
    (hl_mono : StrictMono (fun k : Fin L.length => subVal (l k))) :
    ∃ (ηv' : α → Set (List Bool)),
      IsMinorModel T (binWordTree (h + κ)) ηv' ηe ∧
      ∀ (k : Fin L.length) (i : Fin (3 * 2 ^ ((h + κ + 1) - 1))),
        2 ^ (κ + 1) * subVal (l k) ≤ i.1 →
        i.1 < 2 ^ (κ + 1) * (subVal (l k) + 1) →
        ∃ (w : List Bool) (hw : w.length < h + κ),
          w ∈ ηv' L[k] ∧ treeYLeafParent (h + κ + 1) i = binNodeOfWord (h + κ) w hw := by
  let ηv' : α → Set (List Bool) := fun u =>
    ηv u ∪ {w | ∃ (k : Fin L.length) (p : List Bool),
      L[k] = u ∧ p ≠ [] ∧ p.length ≤ κ ∧ w = l k ++ p}
  have hl_inj : Injective l := by
    intro k₁ k₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Nat.ne_of_lt (hl_mono hlt) (congrArg subVal heq)
    · exact Nat.ne_of_gt (hl_mono hgt) (congrArg subVal heq)
  refine ⟨ηv', ?_, ?_⟩
  · refine isMinorModel_of_loopless_link
      (fun e _ u hl => hSimple.not_isLoopAt e u hl)
      (fun u hu => (hm.vertex_nonempty u hu).mono subset_union_left)
      (fun u hu w hw => by
        change w.length < h + κ
        rcases hw with hw₀ | ⟨k, p, _, _, hp_le, rfl⟩
        · exact lt_of_lt_of_le (hm.vertex_subset u hu hw₀) (Nat.le_add_right h κ)
        · have hlk := (hl_spec k).1
          rw [List.length_append, hlk]; omega)
      (fun u₁ hu₁ u₂ hu₂ hne => by
        rw [Set.disjoint_left]
        rintro w (hw₁ | ⟨k₁, p₁, hk₁u, hp₁_ne, _, rfl⟩) (hw₂ | ⟨k₂, p₂, hk₂u, hp₂_ne, _, heq⟩)
        · exact Set.disjoint_left.mp (hm.vertex_disjoint u₁ hu₁ u₂ hu₂ hne) hw₁ hw₂
        · subst heq
          have hlt₁ : (l k₂ ++ p₂).length < h := hm.vertex_subset u₁ hu₁ hw₁
          have hp₂_pos : 0 < p₂.length := List.length_pos_iff.mpr hp₂_ne
          rw [List.length_append, (hl_spec k₂).1] at hlt₁
          omega
        · have hlt₂ : (l k₁ ++ p₁).length < h := hm.vertex_subset u₂ hu₂ hw₂
          have hp₁_pos : 0 < p₁.length := List.length_pos_iff.mpr hp₁_ne
          rw [List.length_append, (hl_spec k₁).1] at hlt₂
          omega
        · have hlen_eq : (l k₁).length = (l k₂).length :=
            (hl_spec k₁).1.trans (hl_spec k₂).1.symm
          have htake := congrArg (List.take (h - 1)) heq
          rw [List.take_append_of_le_length (by rw [(hl_spec k₁).1]),
            List.take_append_of_le_length (by rw [(hl_spec k₂).1]),
            List.take_of_length_le (by rw [(hl_spec k₁).1]),
            List.take_of_length_le (by rw [(hl_spec k₂).1])] at htake
          have hk_eq : k₁ = k₂ := hl_inj htake
          exact hne (hk₁u.symm.trans (hk_eq ▸ hk₂u)))
      hm.edge_injOn
      (fun e u v hl => by
        have huv : u ≠ v := fun h => hSimple.not_isLoopAt e u (h ▸ hl)
        obtain ⟨x, hx, y, hy, h_ne, h_lt, h_ends⟩ := exists_isLink_of_isMinorModel hm hl huv
        exact ⟨x, Or.inl hx, y, Or.inl hy, h_ne, lt_of_lt_of_le h_lt (Nat.le_add_right h κ), h_ends⟩)
      (fun u hu w₁ hw₁ w₂ hw₂ => ?_)
    obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm.connected u hu
    have hbase_conn : ∀ a ∈ ηv u, ∀ b ∈ ηv u,
        Relation.ReflTransGen
          (((binWordTree (h + κ)).deleteEdges (ηe '' E(T))).induce (ηv' u)).Adj a b := by
      intro a ha b hb
      refine reflTransGen_mono_rel (fun z₁ z₂ hz => ?_)
        (hK_conn.2 a (hVK.symm ▸ ha) b (hVK.symm ▸ hb))
      obtain ⟨f, hlf⟩ := hz
      have hlf_del : ((binWordTree h).deleteEdges (ηe '' E(T))).IsLink f z₁ z₂ := hlf.mono hK_le
      rw [Graph.deleteEdges_isLink] at hlf_del
      obtain ⟨⟨hf_ne, hf_lt, hf_ends⟩, hf_not_img⟩ := hlf_del
      refine ⟨f, ?_⟩
      rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
      exact ⟨⟨⟨hf_ne, lt_of_lt_of_le hf_lt (Nat.le_add_right h κ), hf_ends⟩, hf_not_img⟩,
        Or.inl (hVK ▸ hlf.left_mem), Or.inl (hVK ▸ hlf.right_mem)⟩
    have hto_ηv : ∀ w ∈ ηv' u, ∃ z ∈ ηv u,
        Relation.ReflTransGen
          (((binWordTree (h + κ)).deleteEdges (ηe '' E(T))).induce (ηv' u)).Adj z w := by
      rintro w (hw₀ | ⟨k, p, hku, hp_ne, hp_le, rfl⟩)
      · exact ⟨w, hw₀, Relation.ReflTransGen.refl⟩
      · have hlk_u : l k ∈ ηv u := hku ▸ (hl_spec k).2
        refine ⟨l k, hlk_u, reflTransGen_cone_to_base (l k) p (Or.inl hlk_u) ?_ ?_⟩
        · intro q hq hql
          refine ⟨by rw [List.length_append, (hl_spec k).1]; omega, ?_⟩
          exact Or.inr ⟨k, q, hku, hq, hql.trans hp_le, rfl⟩
        · rintro d ⟨e, he, rfl⟩
          have hlt_e : (ηe e).length < h := (hm.edge_mem e he).2
          rw [(hl_spec k).1]; omega
    obtain ⟨z₁, hz₁, hc₁⟩ := hto_ηv w₁ hw₁
    obtain ⟨z₂, hz₂, hc₂⟩ := hto_ηv w₂ hw₂
    exact Relation.ReflTransGen.trans
      (reflTransGen_symm_of (fun _ _ h => h.symm) hc₁)
      (Relation.ReflTransGen.trans (hbase_conn z₁ hz₁ z₂ hz₂) hc₂)
  · intro k i hlo hhi
    rw [Nat.mul_add, Nat.mul_one] at hhi
    let r : ℕ := i.1 - 2 ^ (κ + 1) * subVal (l k)
    have hr_lt : r < 2 ^ (κ + 1) := by dsimp only [r]; omega
    have hi_eq : i.1 = 2 ^ (κ + 1) * subVal (l k) + r := by dsimp only [r]; omega
    let wr : List Bool := wordOfNat (κ + 1) r
    have hwr_len : wr.length = κ + 1 := length_wordOfNat (κ + 1) r
    have hwr_ne : wr ≠ [] := List.ne_nil_of_length_pos (by omega)
    let p : List Bool := wr.dropLast
    let b : Bool := wr.getLast hwr_ne
    have hwr_split : wr = p ++ [b] := (List.dropLast_append_getLast hwr_ne).symm
    have hp_len : p.length = κ := by dsimp only [p]; rw [List.length_dropLast, hwr_len]; omega
    have hp_ne : p ≠ [] := List.ne_nil_of_length_pos (by omega)
    let w : List Bool := l k ++ p
    have hw_len : w.length = h + κ - 1 := by
      dsimp only [w]; rw [List.length_append, (hl_spec k).1, hp_len]; omega
    have hw_lt : w.length < h + κ := by omega
    have hw_mem : w ∈ ηv' L[k] := Or.inr ⟨k, p, rfl, hp_ne, le_of_eq hp_len, rfl⟩
    have hwb_len : (w ++ [b]).length = h + κ := by
      rw [List.length_append, List.length_singleton, hw_len]; omega
    have hsub_wb : subVal (w ++ [b]) = i.1 := by
      have hassoc : w ++ [b] = l k ++ wr := by dsimp only [w]; rw [List.append_assoc, ← hwr_split]
      rw [hassoc, subVal_append, hwr_len, subVal_wordOfNat (κ + 1) hr_lt, hi_eq]
    refine ⟨w, hw_lt, hw_mem, ?_⟩
    convert treeYLeafParent_subVal_snoc (h := h + κ) w b hwb_len using 2
    ext; exact hsub_wb.symm
end GraphMinor.GM03
