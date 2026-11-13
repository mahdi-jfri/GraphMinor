module

public import GraphMinor.GM22.Section8b2
public import GraphMinor.GM22.Section7d2b
public import GraphMinor.GM22.Section7cAnnulus
public import GraphMinor.GM19.FrameExists
public import GraphMinor.GM19.Section6Cuff
public import GraphMinor.GM19.FeatureOrient
public import GraphMinor.GM19.FragmentDirection
public import GraphMinor.GM19.FragmentChord
public import GraphMinor.GM19.CircleOrder
public import GraphMinor.GM12.Section4DiscEnlargement
public import GraphMinor.Surface.ArcTools
public import GraphMinor.Surface.CutLift

/-!
# Graph Minors XXII, Section 8 (Part b3: Walk Decomposition across a $Z$-Division and Claim 4 of
Theorem 8.3)

This file proves walk-decomposition lemmas across a $(Z \cup W)$-division $\mathcal{A}$ of $J$
and establishes Claim (4) of the proof of Theorem (8.3) from:
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
Journal of Combinatorial Theory, Series B 102 (2012), 530–563 (page 560).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

universe u v w

variable {α : Type u} {β : Type v}
variable {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## Walk Decomposition across a $(Z \cup W)$-Division -/

/-- Any simple walk `W` in `H` between distinct vertices `u ≠ v` decomposes at the first vertex
`z ≠ u` that either lies in `Z` or equals `v` into `W = W₁.append W₂` where `W₁` has no internal
vertices in `Z` and `W₂` is strictly shorter than `W`. -/
theorem exists_first_hit_on_simpleWalk {H : Graph α β} {u v : α}
    (W : GraphWalk H u v) (hs : W.IsSimple) (huv : u ≠ v) (Z : Set α) :
    ∃ (z : α) (W₁ : GraphWalk H u z) (W₂ : GraphWalk H z v),
      W = W₁.append W₂ ∧
      W₁.IsSimple ∧ W₂.IsSimple ∧
      u ≠ z ∧ (z = v ∨ z ∈ Z) ∧
      (∀ y ∈ W₁.support, y ≠ u → y ≠ z → y ∉ Z) ∧
      W₂.edges.length < W.edges.length := by
  induction W with
  | nil hu => exact False.elim (huv rfl)
  | @cons x y w e hlk rest ih =>
    have hx_not_rest : x ∉ rest.support := (List.nodup_cons.mp hs).1
    have hrest_simple : rest.IsSimple := (List.nodup_cons.mp hs).2
    have hxy : x ≠ y := fun h => hx_not_rest (h ▸ rest.start_mem_support)
    by_cases hy : y = w ∨ y ∈ Z
    · refine ⟨y, GraphWalk.cons hlk (GraphWalk.nil hlk.right_mem), rest, rfl, ?_, hrest_simple,
        hxy, hy, ?_, by simp⟩
      · show [x, y].Nodup
        simp [hxy]
      · intro a ha hax hay
        simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact False.elim (hax rfl)
        · exact False.elim (hay rfl)
    · push Not at hy
      obtain ⟨z, W₁', W₂, hrest_eq, hW₁'_s, hW₂_s, hyz, hz_mem, hW₁'_int, hW₂_len⟩ :=
        ih hrest_simple hy.1
      have hW₁'_sub : ∀ a ∈ W₁'.support, a ∈ rest.support := by
        intro a ha
        rw [hrest_eq, GraphWalk.mem_support_append]
        exact Or.inl ha
      have hx_not_W₁' : x ∉ W₁'.support := fun hx => hx_not_rest (hW₁'_sub x hx)
      have hxz : x ≠ z := fun h => hx_not_W₁' (h ▸ W₁'.end_mem_support)
      let W₁ : GraphWalk H x z := GraphWalk.cons hlk W₁'
      have hW₁_s : W₁.IsSimple := List.nodup_cons.mpr ⟨hx_not_W₁', hW₁'_s⟩
      refine ⟨z, W₁, W₂, ?_, hW₁_s, hW₂_s, hxz, hz_mem, ?_, ?_⟩
      · rw [hrest_eq]
        rfl
      · intro a ha hax haz
        simp only [W₁, GraphWalk.support, List.mem_cons] at ha
        rcases ha with rfl | ha'
        · exact False.elim (hax rfl)
        · by_cases hay : a = y
          · subst hay
            exact hy.2
          · exact hW₁'_int a ha' hay haz
      · simp only [GraphWalk.edges, List.length_cons]
        omega

/-- If a simple walk in `J \ W_set` starts at `x ∈ V(A')` with `x = z ∨ x ∉ Z` and has no internal
vertices in `Z`, then every vertex and edge of the walk lies in `A'`. -/
private theorem walk_stays_in_piece_of_start_notMem_Z
    {J : Graph α β} {Z W_set : Set α} {𝒜 : Set (Graph α β)}
    (hZdiv : IsZDivision J (Z ∪ W_set) 𝒜)
    {A' : Graph α β} (hA' : A' ∈ 𝒜)
    {x z : α} (W : GraphWalk (J.deleteVerts W_set) x z) (hs : W.IsSimple)
    (hxA' : x ∈ V(A'))
    (hint : ∀ y ∈ W.support, y ≠ z → y ∉ Z) :
    (∀ y ∈ W.support, y ∈ V(A')) ∧ (∀ g ∈ W.edges, g ∈ E(A')) := by
  induction W with
  | nil _ =>
    exact ⟨by simp [hxA'], by simp⟩
  | @cons a b c e hlk rest ih =>
    have ha_not_rest : a ∉ rest.support := (List.nodup_cons.mp hs).1
    have hac : a ≠ c := fun h => ha_not_rest (h ▸ rest.end_mem_support)
    have hxZ : a ∉ Z := hint a List.mem_cons_self hac
    have ha_JW : a ∈ V(J.deleteVerts W_set) := hlk.left_mem
    rw [vertexSet_deleteVerts] at ha_JW
    have ha_not_W : a ∉ W_set := ha_JW.2
    have ha_not_ZW : a ∉ Z ∪ W_set := fun h => h.elim hxZ ha_not_W
    have hlk_J : J.IsLink e a b := hlk.mono Graph.deleteVerts_le
    have heJ : e ∈ E(J) := hlk_J.edge_mem
    have hEu := congrArg Graph.edgeSet hZdiv.2.2.1
    rw [edgeSet_subgraphSUnion hZdiv.2.1] at hEu
    rw [← hEu] at heJ
    obtain ⟨A'', hA'', heA''⟩ := mem_iUnion₂.mp heJ
    have hlk_A'' : A''.IsLink e a b := ((hZdiv.2.1 A'' hA'').isLink_iff heA'').mpr hlk_J
    have haA'' : a ∈ V(A'') := hlk_A''.left_mem
    have hA''_eq : A'' = A' := by
      by_contra hne
      exact ha_not_ZW ((hZdiv.2.2.2 A' hA' A'' hA'' (Ne.symm hne)).2 ⟨hxA', haA''⟩)
    subst A''
    have hbA' : b ∈ V(A') := hlk_A''.right_mem
    have hint_rest : ∀ y ∈ rest.support, y ≠ c → y ∉ Z :=
      fun y hy hyc => hint y (List.mem_cons_of_mem a hy) hyc
    obtain ⟨hV_rest, hE_rest⟩ := ih (List.nodup_cons.mp hs).2 hbA' hint_rest
    refine ⟨?_, ?_⟩
    · intro y hy
      simp only [GraphWalk.support, List.mem_cons] at hy
      rcases hy with rfl | hy'
      · exact hxA'
      · exact hV_rest y hy'
    · intro g hg
      simp only [GraphWalk.edges, List.mem_cons] at hg
      rcases hg with rfl | hg'
      · exact heA''
      · exact hE_rest g hg'

/-- Any non-trivial simple walk `W` in `J \ W_set` with no internal vertices in `Z` lies completely
inside a single piece `A' ∈ 𝒜`. -/
theorem walk_in_single_piece_of_notMem_Z
    {J : Graph α β} {Z W_set : Set α} {𝒜 : Set (Graph α β)}
    (hZdiv : IsZDivision J (Z ∪ W_set) 𝒜)
    {u z : α} (W : GraphWalk (J.deleteVerts W_set) u z) (hs : W.IsSimple) (huz : u ≠ z)
    (hint : ∀ y ∈ W.support, y ≠ u → y ≠ z → y ∉ Z) :
    ∃ A' ∈ 𝒜, (∀ y ∈ W.support, y ∈ V(A')) ∧ (∀ g ∈ W.edges, g ∈ E(A')) := by
  cases W with
  | nil _ => exact False.elim (huz rfl)
  | @cons u x z e hlk rest =>
    have hlk_J : J.IsLink e u x := hlk.mono Graph.deleteVerts_le
    have heJ : e ∈ E(J) := hlk_J.edge_mem
    have hEu := congrArg Graph.edgeSet hZdiv.2.2.1
    rw [edgeSet_subgraphSUnion hZdiv.2.1] at hEu
    rw [← hEu] at heJ
    obtain ⟨A', hA', heA'⟩ := mem_iUnion₂.mp heJ
    have hlk_A' : A'.IsLink e u x := ((hZdiv.2.1 A' hA').isLink_iff heA').mpr hlk_J
    have huA' : u ∈ V(A') := hlk_A'.left_mem
    have hxA' : x ∈ V(A') := hlk_A'.right_mem
    have hu_not_rest : u ∉ rest.support := (List.nodup_cons.mp hs).1
    have hint_rest : ∀ y ∈ rest.support, y ≠ z → y ∉ Z :=
      fun y hy hyz => hint y (List.mem_cons_of_mem u hy) (fun hyu => hu_not_rest (hyu ▸ hy)) hyz
    obtain ⟨hV_rest, hE_rest⟩ :=
      walk_stays_in_piece_of_start_notMem_Z hZdiv hA' rest (List.nodup_cons.mp hs).2 hxA' hint_rest
    refine ⟨A', hA', ?_, ?_⟩
    · intro y hy
      simp only [GraphWalk.support, List.mem_cons] at hy
      rcases hy with rfl | hy'
      · exact huA'
      · exact hV_rest y hy'
    · intro g hg
      simp only [GraphWalk.edges, List.mem_cons] at hg
      rcases hg with rfl | hg'
      · exact heA'
      · exact hE_rest g hg'


/-! ## Minimal Step Chains across a $(Z \cup W)$-Division -/

/-- A step chain of length `k` from `u` to `v` in `S_verts ⊆ Z` across `𝒜`:
a sequence of vertices `z : ℕ → α` in `S_verts` with `z 0 = u` and `z k = v`,
and pieces `A_seq : ℕ → Graph α β` in `𝒜` such that for each `m < k`,
both `z m` and `z (m + 1)` lie in `Z ∩ V(A_seq m)`. -/
def ValidChain (Z : Set α) (𝒜 : Set (Graph α β)) (S_verts : Set α) (u v : α)
    (k : ℕ) (z : ℕ → α) (A_seq : ℕ → Graph α β) : Prop :=
  z 0 = u ∧
  z k = v ∧
  (∀ m ≤ k, z m ∈ S_verts) ∧
  (∀ m < k, A_seq m ∈ 𝒜 ∧
    z m ∈ Z ∩ V(A_seq m) ∧
    z (m + 1) ∈ Z ∩ V(A_seq m))

private theorem exists_validChain_of_walk_aux
    {J : Graph α β} {Z W_set : Set α} {𝒜 : Set (Graph α β)}
    (hZdiv : IsZDivision J (Z ∪ W_set) 𝒜) {S_verts : Set α}
    (n : ℕ) :
    ∀ {u v : α} (W : GraphWalk (J.deleteVerts W_set) u v),
      W.edges.length ≤ n → W.IsSimple → u ∈ Z → v ∈ Z → u ∈ S_verts →
      (∀ y ∈ W.support, y ∈ Z → y ∈ S_verts) →
      ∃ (k : ℕ) (z : ℕ → α) (A_seq : ℕ → Graph α β),
        ValidChain Z 𝒜 S_verts u v k z A_seq := by
  induction n with
  | zero =>
    intro u v W hlen _ _ _ huS _
    have huv : u = v := by
      cases W with
      | nil _ => rfl
      | cons _ _ => simp [GraphWalk.edges] at hlen
    subst v
    exact ⟨0, fun _ => u, fun _ => J, rfl, rfl, fun _ _ => huS, fun m hm => by omega⟩
  | succ n ih =>
    intro u v W hlen hs huZ hvZ huS hsupp
    by_cases huv : u = v
    · subst v
      exact ⟨0, fun _ => u, fun _ => J, rfl, rfl, fun _ _ => huS, fun m hm => by omega⟩
    · obtain ⟨w, W₁, W₂, hW_eq, hs₁, hs₂, huw, hw_or, hint₁, hlen₂⟩ :=
        exists_first_hit_on_simpleWalk W hs huv Z
      have hwZ : w ∈ Z := hw_or.elim (fun h => h ▸ hvZ) id
      have hw_supp : w ∈ W.support := by
        rw [hW_eq, GraphWalk.mem_support_append]
        exact Or.inl W₁.end_mem_support
      have hwS : w ∈ S_verts := hsupp w hw_supp hwZ
      obtain ⟨A', hA', hV₁, _⟩ := walk_in_single_piece_of_notMem_Z hZdiv W₁ hs₁ huw hint₁
      have huA' : u ∈ V(A') := hV₁ u W₁.start_mem_support
      have hwA' : w ∈ V(A') := hV₁ w W₁.end_mem_support
      have hsupp₂ : ∀ y ∈ W₂.support, y ∈ Z → y ∈ S_verts := by
        intro y hy hyZ
        apply hsupp y _ hyZ
        rw [hW_eq, GraphWalk.mem_support_append]
        exact Or.inr hy
      obtain ⟨k, z, A_seq, hz0, hzk, hzS, hA_seq⟩ :=
        ih W₂ (by omega) hs₂ hwZ hvZ hwS hsupp₂
      let z' : ℕ → α := fun m => match m with | 0 => u | m' + 1 => z m'
      let A_seq' : ℕ → Graph α β := fun m => match m with | 0 => A' | m' + 1 => A_seq m'
      refine ⟨k + 1, z', A_seq', rfl, hzk, ?_, ?_⟩
      · intro m hm
        cases m with
        | zero => exact huS
        | succ m' => exact hzS m' (by omega)
      · intro m hm
        cases m with
        | zero =>
          dsimp only [A_seq', z']
          rw [hz0]
          exact ⟨hA', ⟨huZ, huA'⟩, ⟨hwZ, hwA'⟩⟩
        | succ m' =>
          dsimp only [A_seq', z']
          exact hA_seq m' (by omega)

/-- Every simple walk in `J \ W_set` between `u ∈ Z` and `v ∈ Z` yields a `ValidChain` whose
vertices lie in `W.support ∩ Z`. -/
theorem exists_validChain_of_walk
    {J : Graph α β} {Z W_set : Set α} {𝒜 : Set (Graph α β)}
    (hZdiv : IsZDivision J (Z ∪ W_set) 𝒜)
    {u v : α} (W : GraphWalk (J.deleteVerts W_set) u v) (hs : W.IsSimple)
    (huZ : u ∈ Z) (hvZ : v ∈ Z)
    {S_verts : Set α} (hsupp : ∀ y ∈ W.support, y ∈ Z → y ∈ S_verts) :
    ∃ (k : ℕ) (z : ℕ → α) (A_seq : ℕ → Graph α β),
      ValidChain Z 𝒜 S_verts u v k z A_seq :=
  exists_validChain_of_walk_aux hZdiv W.edges.length W le_rfl hs huZ hvZ
    (hsupp u W.start_mem_support huZ) hsupp

/-- Taking a `ValidChain` of minimum length `k` ensures that both `z` (on `0..k`) and `A_seq`
(on `0..k-1`) are injective. -/
theorem exists_minimal_validChain
    {Z : Set α} {𝒜 : Set (Graph α β)} {S_verts : Set α} {u v : α}
    (hex : ∃ (k : ℕ) (z : ℕ → α) (A_seq : ℕ → Graph α β),
      ValidChain Z 𝒜 S_verts u v k z A_seq) :
    ∃ (k : ℕ) (z : ℕ → α) (A_seq : ℕ → Graph α β),
      ValidChain Z 𝒜 S_verts u v k z A_seq ∧
      (∀ i ≤ k, ∀ j ≤ k, z i = z j → i = j) ∧
      (∀ i < k, ∀ j < k, A_seq i = A_seq j → i = j) := by
  classical
  let k := Nat.find hex
  obtain ⟨z, A_seq, hvc⟩ := Nat.find_spec hex
  have hmin : ∀ k' < k, ¬ ∃ (z' : ℕ → α) (A_seq' : ℕ → Graph α β),
      ValidChain Z 𝒜 S_verts u v k' z' A_seq' := fun k' hk' => Nat.find_min hex hk'
  refine ⟨k, z, A_seq, hvc, ?_, ?_⟩
  · -- Injectivity of `z` on `0..k`: if `z i = z j` for `i < j ≤ k`, splice out `i..j`.
    intro i hi j hj hij_eq
    by_contra hne
    wlog hij : i < j generalizing i j
    · exact this j hj i hi hij_eq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hij) (Ne.symm hne))
    let d : ℕ := j - i
    let k' : ℕ := k - d
    have hk'_lt : k' < k := by omega
    let z' : ℕ → α := fun m => if m ≤ i then z m else z (m + d)
    let A_seq' : ℕ → Graph α β := fun m => if m < i then A_seq m else A_seq (m + d)
    apply hmin k' hk'_lt
    refine ⟨z', A_seq', ?_, ?_, ?_, ?_⟩
    · simp only [z', Nat.zero_le, ↓reduceIte, hvc.1]
    · dsimp only [z']
      by_cases hi_last : k' ≤ i
      · have h_eq_i : k' = i := by omega
        have hj_last : j = k := by omega
        simp only [hi_last, ↓reduceIte]
        rw [h_eq_i, hij_eq, hj_last, hvc.2.1]
      · have h_sum : k' + d = k := by omega
        simp only [hi_last, ↓reduceIte]
        rw [h_sum, hvc.2.1]
    · intro m hm
      dsimp only [z']
      split_ifs with hmi
      · exact hvc.2.2.1 m (by omega)
      · exact hvc.2.2.1 (m + d) (by omega)
    · intro m hm
      dsimp only [A_seq', z']
      by_cases hmi : m < i
      · have hm1 : m ≤ i := le_of_lt hmi
        have hm2 : m + 1 ≤ i := by omega
        simp only [hmi, hm1, hm2, ↓reduceIte]
        exact hvc.2.2.2 m (by omega)
      · have hm2 : ¬ (m + 1 ≤ i) := by omega
        simp only [hmi, hm2, ↓reduceIte]
        obtain ⟨hA_mem, hcast, hsucc⟩ := hvc.2.2.2 (m + d) (by omega)
        have hsucc' : z (m + 1 + d) ∈ Z ∩ V(A_seq (m + d)) := by
          have : m + 1 + d = m + d + 1 := by omega
          rw [this]
          exact hsucc
        refine ⟨hA_mem, ?_, hsucc'⟩
        by_cases hm1 : m ≤ i
        · have h_eq : m = i := by omega
          have hj_eq : m + d = j := by omega
          simp only [hm1, ↓reduceIte]
          rw [h_eq, hij_eq, ← hj_eq]
          exact h_eq ▸ hcast
        · simp only [hm1, ↓reduceIte]
          exact hcast
  · -- Injectivity of `A_seq` on `0..k-1`: if `A_seq i = A_seq j` for `i < j < k`, collapse `i..j`.
    intro i hi j hj hij_eq
    by_contra hne
    wlog hij : i < j generalizing i j
    · exact this j hj i hi hij_eq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.mp hij) (Ne.symm hne))
    let d : ℕ := j - i
    let k' : ℕ := k - d
    have hk'_lt : k' < k := by omega
    let z' : ℕ → α := fun m => if m ≤ i then z m else z (m + d)
    let A_seq' : ℕ → Graph α β := fun m => if m ≤ i then A_seq m else A_seq (m + d)
    apply hmin k' hk'_lt
    refine ⟨z', A_seq', ?_, ?_, ?_, ?_⟩
    · simp only [z', Nat.zero_le, ↓reduceIte, hvc.1]
    · dsimp only [z']
      have h_not : ¬ k' ≤ i := by omega
      have h_sum : k' + d = k := by omega
      simp only [h_not, ↓reduceIte]
      rw [h_sum, hvc.2.1]
    · intro m hm
      dsimp only [z']
      split_ifs with hmi
      · exact hvc.2.2.1 m (by omega)
      · exact hvc.2.2.1 (m + d) (by omega)
    · intro m hm
      dsimp only [A_seq', z']
      by_cases hmi : m < i
      · have hm1 : m ≤ i := le_of_lt hmi
        have hm2 : m + 1 ≤ i := by omega
        simp only [hm1, hm2, ↓reduceIte]
        exact hvc.2.2.2 m (by omega)
      · by_cases h_eq : m = i
        · subst m
          have hm1 : i ≤ i := le_rfl
          have hm2 : ¬ (i + 1 ≤ i) := by omega
          have hj_sum : i + 1 + d = j + 1 := by omega
          simp only [hm1, hm2, ↓reduceIte, hj_sum]
          refine ⟨(hvc.2.2.2 i hi).1, (hvc.2.2.2 i hi).2.1, ?_⟩
          rw [hij_eq]
          exact (hvc.2.2.2 j hj).2.2
        · have hm1 : ¬ m ≤ i := by omega
          have hm2 : ¬ (m + 1 ≤ i) := by omega
          have h_add : m + 1 + d = m + d + 1 := by omega
          simp only [hm1, hm2, ↓reduceIte, h_add]
          exact hvc.2.2.2 (m + d) (by omega)

/-! ## Chords along a Minimal Step Chain -/

/-- Along an injective `ValidChain` `(k, z, A_seq)` from `u` to `v` in `S_verts ⊆ Z`,
the union of chords `F m ⊆ D (A_seq m)` between `α_map (z m)` and `α_map (z (m + 1))`
forms a set `M ⊆ Δ₀` that is either `{α_map u}` (if `u = v`) or a line with ends
`α_map u, α_map v` (if `u ≠ v`), and meets `subBd Δ₀` and `D B` (for `B ∉ A_seq`) only
inside `α_map '' S_verts`. -/
theorem exists_line_of_validChain
    (hS : IsClosedSurface S)
    {Z : Set α} {𝒜 : Set (Graph α β)} {Δ₀ PiSet : Set S}
    {ιV : S ↪ α} {α_map : α → S} {D : Graph α β → Set S}
    (hα_Δ₀ : α_map '' Z ⊆ Δ₀)
    (hinj : InjOn α_map Z)
    (hD : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Z ∩ V(A), α_map v ∈ subBd (D A))
    (hD_inter : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
      D A ∩ D A' = α_map '' ((Z ∩ V(A)) ∩ (Z ∩ V(A'))))
    (hD_bdΔ₀ : ∀ A ∈ 𝒜,
      D A ∩ subBd Δ₀ = α_map '' ((Z ∩ V(A)) ∩ (ιV '' PiSet)))
    {S_verts : Set α} (hS_sub_Z : S_verts ⊆ Z)
    {u v : α} {k : ℕ} {z : ℕ → α} {A_seq : ℕ → Graph α β}
    (hvc : ValidChain Z 𝒜 S_verts u v k z A_seq)
    (hz_inj : ∀ i ≤ k, ∀ j ≤ k, z i = z j → i = j)
    (hA_inj : ∀ i < k, ∀ j < k, A_seq i = A_seq j → i = j) :
    ∃ M : Set S,
      M ⊆ {α_map u} ∪ ⋃ m < k, D (A_seq m) ∧
      M ⊆ Δ₀ ∧
      α_map u ∈ M ∧ α_map v ∈ M ∧
      ((u = v ∧ M = {α_map u}) ∨
        (u ≠ v ∧ IsLineWithEnds M (α_map u) (α_map v))) ∧
      M ∩ subBd Δ₀ ⊆ α_map '' S_verts ∧
      (∀ B ∈ 𝒜, (∀ m < k, A_seq m ≠ B) → M ∩ D B ⊆ (α_map '' S_verts) ∩ D B) ∧
      (∀ m < k, M ∩ D (A_seq m) ∩ subBd (D (A_seq m)) ⊆ α_map '' S_verts) := by
  classical
  have hbd_eq : ∀ A ∈ 𝒜, subBd (D A) = discBd (D A) := by
    intro A hA
    rw [GM11.subBd_eq_frontier, GM11.IsClosedDisc.frontier_eq_discBd hS (hD A hA).1]
  have hex_F : ∀ m : ℕ, m < k → ∃ F_m : Set S,
      IsLineWithEnds F_m (α_map (z m)) (α_map (z (m + 1))) ∧
      F_m ⊆ D (A_seq m) ∧
      F_m ∩ subBd (D (A_seq m)) = {α_map (z m), α_map (z (m + 1))} := by
    intro m hm
    obtain ⟨hAm, hzm, hzm1⟩ := hvc.2.2.2 m hm
    have hm_bd : α_map (z m) ∈ subBd (D (A_seq m)) := hα_bdA (A_seq m) hAm (z m) hzm
    have hm1_bd : α_map (z (m + 1)) ∈ subBd (D (A_seq m)) := hα_bdA (A_seq m) hAm (z (m + 1)) hzm1
    have hm_D : α_map (z m) ∈ D (A_seq m) :=
      GM14.Whitney.subBd_subset_of subset_rfl (hD (A_seq m) hAm).1.isClosed hm_bd
    have hm1_D : α_map (z (m + 1)) ∈ D (A_seq m) :=
      GM14.Whitney.subBd_subset_of subset_rfl (hD (A_seq m) hAm).1.isClosed hm1_bd
    have hne_z : z m ≠ z (m + 1) := fun heq => by
      have := hz_inj m (by omega) (m + 1) (by omega) heq
      omega
    have hne_α : α_map (z m) ≠ α_map (z (m + 1)) :=
      fun heq => hne_z (hinj hzm.1 hzm1.1 heq)
    obtain ⟨F_m, hF_line, hF_sub, hF_int⟩ :=
      exists_chord_in_closedDisc (hD (A_seq m) hAm).1 hm_D hm1_D hne_α
    refine ⟨F_m, hF_line, hF_sub, ?_⟩
    apply Subset.antisymm
    · intro x ⟨hxF, hxbd⟩
      rw [hbd_eq (A_seq m) hAm] at hxbd
      by_contra hnot
      exact (hF_int ⟨hxF, hnot⟩).2 hxbd
    · rintro x (rfl | rfl)
      · exact ⟨GM11.IsLineWithEnds.left_mem hF_line, hm_bd⟩
      · exact ⟨GM11.IsLineWithEnds.right_mem hF_line, hm1_bd⟩
  let F : ℕ → Set S := fun m =>
    if hm : m < k then Classical.choose (hex_F m hm) else ∅
  have hF_spec : ∀ m (hm : m < k),
      IsLineWithEnds (F m) (α_map (z m)) (α_map (z (m + 1))) ∧
      F m ⊆ D (A_seq m) ∧
      F m ∩ subBd (D (A_seq m)) = {α_map (z m), α_map (z (m + 1))} := by
    intro m hm
    simpa [F, hm] using Classical.choose_spec (hex_F m hm)
  let M_pre (j : ℕ) : Set S := {α_map (z 0)} ∪ ⋃ m < j, F m
  have hF_inter_other : ∀ m (hm : m < k), ∀ B ∈ 𝒜, A_seq m ≠ B →
      F m ∩ D B ⊆ {α_map (z m), α_map (z (m + 1))} := by
    intro m hm B hB hne x ⟨hxF, hxB⟩
    obtain ⟨hAm, _, _⟩ := hvc.2.2.2 m hm
    have hx_inter : x ∈ D (A_seq m) ∩ D B := ⟨(hF_spec m hm).2.1 hxF, hxB⟩
    rw [hD_inter (A_seq m) hAm B hB hne] at hx_inter
    obtain ⟨w, ⟨hwAm, _⟩, rfl⟩ := hx_inter
    have hw_bd : α_map w ∈ subBd (D (A_seq m)) := hα_bdA (A_seq m) hAm w hwAm
    rw [← (hF_spec m hm).2.2]
    exact ⟨hxF, hw_bd⟩
  have hM_pre_other : ∀ j ≤ k, ∀ B ∈ 𝒜, (∀ m < j, A_seq m ≠ B) →
      M_pre j ∩ D B ⊆ (α_map '' (z '' {m | m ≤ j})) ∩ D B := by
    intro j hj B hB hne x ⟨hxM, hxB⟩
    refine ⟨?_, hxB⟩
    rcases hxM with rfl | hxU
    · exact ⟨z 0, ⟨0, Nat.zero_le j, rfl⟩, rfl⟩
    · obtain ⟨m, hm_lt, hxF⟩ := mem_iUnion₂.mp hxU
      have hm_k : m < k := lt_of_lt_of_le hm_lt hj
      rcases hF_inter_other m hm_k B hB (hne m hm_lt) ⟨hxF, hxB⟩ with rfl | rfl
      · exact ⟨z m, ⟨m, le_of_lt hm_lt, rfl⟩, rfl⟩
      · exact ⟨z (m + 1), ⟨m + 1, hm_lt, rfl⟩, rfl⟩
  have hM_pre_line : ∀ j ≤ k,
      (j = 0 ∧ M_pre j = {α_map (z 0)}) ∨
      (0 < j ∧ IsLineWithEnds (M_pre j) (α_map (z 0)) (α_map (z j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      left
      refine ⟨rfl, ?_⟩
      ext x
      simp [M_pre]
    | succ j ih =>
      intro hj1
      right
      refine ⟨Nat.succ_pos j, ?_⟩
      have hM_succ : M_pre (j + 1) = M_pre j ∪ F j := by
        ext x
        simp only [M_pre, mem_union, mem_singleton_iff, mem_iUnion, Nat.lt_succ_iff]
        constructor
        · rintro (rfl | ⟨m, hm, hxm⟩)
          · exact Or.inl (Or.inl rfl)
          · rcases lt_or_eq_of_le hm with hlt | rfl
            · exact Or.inl (Or.inr ⟨m, hlt, hxm⟩)
            · exact Or.inr hxm
        · rintro ((rfl | ⟨m, hlt, hxm⟩) | hxj)
          · exact Or.inl rfl
          · exact Or.inr ⟨m, le_of_lt hlt, hxm⟩
          · exact Or.inr ⟨j, le_rfl, hxj⟩
      rw [hM_succ]
      have hj_lt : j < k := hj1
      obtain ⟨hFj_line, hFj_sub, hFj_bd⟩ := hF_spec j hj_lt
      rcases ih (le_of_lt hj1) with ⟨rfl, hM0⟩ | ⟨hj_pos, hMj_line⟩
      · rw [hM0, singleton_union, insert_eq_of_mem (GM11.IsLineWithEnds.left_mem hFj_line)]
        exact hFj_line
      · refine hMj_line.union hFj_line ?_
        apply Subset.antisymm
        · intro x ⟨hxMj, hxFj⟩
          obtain ⟨hAj, _, hzj1⟩ := hvc.2.2.2 j hj_lt
          have hne_B : ∀ m < j, A_seq m ≠ A_seq j :=
            fun m hm heq => ne_of_lt hm (hA_inj m (lt_of_lt_of_le hm (le_of_lt hj1)) j hj_lt heq)
          have hx_in_img : x ∈ α_map '' (z '' {m | m ≤ j}) :=
            (hM_pre_other j (le_of_lt hj1) (A_seq j) hAj hne_B ⟨hxMj, hFj_sub hxFj⟩).1
          obtain ⟨w, ⟨m, hm_le, rfl⟩, hxw⟩ := hx_in_img
          have hm_le' : m ≤ j := hm_le
          have hzm_Z : z m ∈ Z := hS_sub_Z (hvc.2.2.1 m (le_trans hm_le' (le_of_lt hj1)))
          have hx_in : x ∈ ({α_map (z j), α_map (z (j + 1))} : Set S) := by
            rcases eq_or_lt_of_le hm_le' with rfl | hm_lt
            · rw [← hxw]
              exact Or.inl rfl
            · obtain ⟨hAm, hzm_Am, _⟩ := hvc.2.2.2 m (lt_of_lt_of_le hm_lt (le_of_lt hj1))
              have hzm_DA : α_map (z m) ∈ D (A_seq m) :=
                GM14.Whitney.subBd_subset_of subset_rfl (hD (A_seq m) hAm).1.isClosed
                  (hα_bdA (A_seq m) hAm (z m) hzm_Am)
              have hx_DA_DAj : x ∈ D (A_seq m) ∩ D (A_seq j) := ⟨hxw ▸ hzm_DA, hFj_sub hxFj⟩
              rw [hD_inter (A_seq m) hAm (A_seq j) hAj (hne_B m hm_lt)] at hx_DA_DAj
              obtain ⟨q, ⟨_, hqAj⟩, hxq⟩ := hx_DA_DAj
              have hx_bdj : x ∈ subBd (D (A_seq j)) := hxq ▸ hα_bdA (A_seq j) hAj q hqAj
              rw [← hFj_bd]
              exact ⟨hxFj, hx_bdj⟩
          rcases hx_in with hxj | hxj1
          · exact mem_singleton_iff.mpr hxj
          · exfalso
            have heq_z : z m = z (j + 1) := hinj hzm_Z hzj1.1 (hxw.trans hxj1)
            have hm_eq : m = j + 1 := hz_inj m (by omega) (j + 1) hj1 heq_z
            omega
        · intro x hx
          rw [mem_singleton_iff.mp hx]
          exact ⟨GM11.IsLineWithEnds.right_mem hMj_line, GM11.IsLineWithEnds.left_mem hFj_line⟩
  let M := M_pre k
  have hS_img : α_map '' (z '' {m | m ≤ k}) ⊆ α_map '' S_verts := by
    rintro _ ⟨w, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨z m, hvc.2.2.1 m hm, rfl⟩
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x (hx0 | hxU)
    · rw [mem_singleton_iff.mp hx0, hvc.1]
      exact Or.inl rfl
    · obtain ⟨m, hm, hxF⟩ := mem_iUnion₂.mp hxU
      exact Or.inr (mem_iUnion₂.mpr ⟨m, hm, (hF_spec m hm).2.1 hxF⟩)
  · rintro x (hx0 | hxU)
    · rw [mem_singleton_iff.mp hx0]
      exact hα_Δ₀ ⟨z 0, hS_sub_Z (hvc.2.2.1 0 (Nat.zero_le k)), rfl⟩
    · obtain ⟨m, hm, hxF⟩ := mem_iUnion₂.mp hxU
      exact (hD (A_seq m) (hvc.2.2.2 m hm).1).2 ((hF_spec m hm).2.1 hxF)
  · rw [← hvc.1]
    exact Or.inl rfl
  · rw [← hvc.2.1]
    rcases hM_pre_line k le_rfl with ⟨rfl, _⟩ | ⟨_, hline⟩
    · exact Or.inl rfl
    · exact GM11.IsLineWithEnds.right_mem hline
  · rcases hM_pre_line k le_rfl with ⟨hk0, hM0⟩ | ⟨hk_pos, hline⟩
    · left
      have huv : u = v := by rw [← hvc.1, ← hvc.2.1, hk0]
      rw [hvc.1] at hM0
      exact ⟨huv, hM0⟩
    · right
      have huv : u ≠ v := by
        rw [← hvc.1, ← hvc.2.1]
        intro heq
        have := hz_inj 0 (Nat.zero_le k) k le_rfl heq
        omega
      rw [hvc.1, hvc.2.1] at hline
      exact ⟨huv, hline⟩
  · rintro x ⟨hxM, hxbd⟩
    rcases hxM with rfl | hxU
    · exact ⟨z 0, hvc.2.2.1 0 (Nat.zero_le k), rfl⟩
    · obtain ⟨m, hm, hxF⟩ := mem_iUnion₂.mp hxU
      obtain ⟨hAm, _, _⟩ := hvc.2.2.2 m hm
      have hx_in : x ∈ D (A_seq m) ∩ subBd Δ₀ := ⟨(hF_spec m hm).2.1 hxF, hxbd⟩
      rw [hD_bdΔ₀ (A_seq m) hAm] at hx_in
      obtain ⟨w, ⟨hwAm, _⟩, rfl⟩ := hx_in
      have hw_bd : α_map w ∈ subBd (D (A_seq m)) := hα_bdA (A_seq m) hAm w hwAm
      have hx_ends : α_map w ∈ ({α_map (z m), α_map (z (m + 1))} : Set S) := by
        rw [← (hF_spec m hm).2.2]
        exact ⟨hxF, hw_bd⟩
      rcases hx_ends with heq | heq
      · exact heq ▸ ⟨z m, hvc.2.2.1 m (le_of_lt hm), rfl⟩
      · exact heq ▸ ⟨z (m + 1), hvc.2.2.1 (m + 1) hm, rfl⟩
  · intro B hB hne
    exact (hM_pre_other k le_rfl B hB hne).trans (inter_subset_inter_left (D B) hS_img)
  · intro m hm x ⟨⟨hxM, hxD⟩, hxbd⟩
    rcases hxM with rfl | hxU
    · exact ⟨z 0, hvc.2.2.1 0 (Nat.zero_le k), rfl⟩
    · obtain ⟨m', hm', hxFm'⟩ := mem_iUnion₂.mp hxU
      by_cases hmm' : m' = m
      · subst m'
        have hx_ends : x ∈ ({α_map (z m), α_map (z (m + 1))} : Set S) := by
          rw [← (hF_spec m hm).2.2]
          exact ⟨hxFm', hxbd⟩
        rcases hx_ends with rfl | rfl
        · exact ⟨z m, hvc.2.2.1 m (le_of_lt hm), rfl⟩
        · exact ⟨z (m + 1), hvc.2.2.1 (m + 1) hm, rfl⟩
      · have hne_A : A_seq m' ≠ A_seq m := fun heq => hmm' (hA_inj m' hm' m hm heq)
        rcases hF_inter_other m' hm' (A_seq m) (hvc.2.2.2 m hm).1 hne_A ⟨hxFm', hxD⟩ with rfl | rfl
        · exact ⟨z m', hvc.2.2.1 m' (le_of_lt hm'), rfl⟩
        · exact ⟨z (m' + 1), hvc.2.2.1 (m' + 1) hm', rfl⟩

/-! ## Opposite Arcs on the Boundary of a Closed Disc -/

/-- If `L ⊆ discBd D` is a line with ends `a, b` (`IsLineWithEnds L a b`), `x ∈ L \ {a, b}`,
and `y ∈ discBd D \ L`, then `orient.pos D a x b ↔ orient.pos D a b y`. -/
theorem orient_pos_of_line_in_discBd
    (orient : GM19.SurfaceOrientation S) {D L : Set S} {a b x y : S}
    (hD : IsClosedDisc D) (hL : IsLineWithEnds L a b) (hL_sub : L ⊆ discBd D)
    (hx : x ∈ L \ {a, b}) (hy : y ∈ discBd D \ L) :
    orient.pos D a x b ↔ orient.pos D a b y := by
  obtain ⟨φ, hφc, hφi, hφr, hφ_pos⟩ := orient.isDirection D hD
  have ha_bd : a ∈ discBd D := hL_sub (GM11.IsLineWithEnds.left_mem hL)
  have hb_bd : b ∈ discBd D := hL_sub (GM11.IsLineWithEnds.right_mem hL)
  have hx_bd : x ∈ discBd D := hL_sub hx.1
  have hy_bd : y ∈ discBd D := hy.1
  obtain ⟨u, rfl⟩ : a ∈ range φ := hφr.symm ▸ ha_bd
  obtain ⟨v, rfl⟩ : b ∈ range φ := hφr.symm ▸ hb_bd
  obtain ⟨x_C, rfl⟩ : x ∈ range φ := hφr.symm ▸ hx_bd
  obtain ⟨y_C, rfl⟩ : y ∈ range φ := hφr.symm ▸ hy_bd
  have hab : φ u ≠ φ v := by
    obtain ⟨f, hf0, hf1⟩ := hL
    intro heq
    exact zero_ne_one (f.injective (Subtype.ext (hf0.trans (heq.trans hf1.symm))))
  have huv : u ≠ v := fun h => hab (congrArg φ h)
  have hux : u ≠ x_C := fun h => hx.2 (Or.inl (congrArg φ h.symm))
  have hvx : x_C ≠ v := fun h => hx.2 (Or.inr (congrArg φ h))
  have huy : u ≠ y_C := fun h => hy.2 (congrArg φ h ▸ GM11.IsLineWithEnds.left_mem hL)
  have hvy : v ≠ y_C := fun h => hy.2 (congrArg φ h ▸ GM11.IsLineWithEnds.right_mem hL)
  obtain ⟨θ, hθ, hv_eq⟩ := exists_circle_angle u v
  have hθ0 : θ ≠ 0 := fun h => huv (by simpa [h] using hv_eq.symm)
  have hθ_Ioo : θ ∈ Ioo 0 (2 * Real.pi) := ⟨lt_of_le_of_ne hθ.1 hθ0.symm, hθ.2⟩
  obtain ⟨a_arc, b_arc, hab_arcs, ha_arc, hb_arc, hcov_arcs⟩ := circle_two_arcs' u hθ_Ioo
  let p : unitInterval → S := φ ∘ a_arc
  let q : unitInterval → S := φ ∘ b_arc
  have hpq : IsTwoArcs p q :=
    ⟨⟨hφc.comp hab_arcs.1.1, hφi.comp hab_arcs.1.2⟩,
     ⟨hφc.comp hab_arcs.2.1, hφi.comp hab_arcs.2.2⟩,
     congrArg φ hab_arcs.3, congrArg φ hab_arcs.4,
     fun s t h => hab_arcs.5 s t (hφi h)⟩
  have hp0 : p 0 = φ u := by simp [p, ha_arc]
  have hp1 : p 1 = φ v := by simp [p, ha_arc, ← hv_eq]
  have hq0 : q 0 = φ u := hpq.3.trans hp0
  have hq1 : q 1 = φ v := hpq.4.trans hp1
  have hcov_pq : range p ∪ range q = discBd D := by
    dsimp only [p, q]
    rw [range_comp, range_comp, ← image_union, hcov_arcs, image_univ, hφr]
  -- Show that `L = range p` or `L = range q`.
  obtain ⟨f_L, hf0, hf1⟩ := hL
  let u_L : unitInterval → S := fun t => (f_L t).1
  have hu_L : IsArcMap u_L := ⟨continuous_subtype_val.comp f_L.continuous,
    fun s t h => f_L.injective (Subtype.ext h)⟩
  have hru_L : range u_L = L := by
    ext z
    exact ⟨fun ⟨t, ht⟩ => ht ▸ (f_L t).2, fun hz => ⟨f_L.symm ⟨z, hz⟩, by simp [u_L]⟩⟩
  have hconn_L : IsPreconnected (u_L '' Ioo 0 1) :=
    isPreconnected_Ioo.image _ hu_L.1.continuousOn
  have hAc : IsClosed (range p) := (isCompact_range hpq.1.1).isClosed
  have hBc : IsClosed (range q) := (isCompact_range hpq.2.1).isClosed
  have hcov_uL : u_L '' Ioo 0 1 ⊆ range p ∪ range q := by
    rintro _ ⟨t, -, rfl⟩
    rw [hcov_pq]
    exact hL_sub (hru_L ▸ ⟨t, rfl⟩)
  have h_sub_or : u_L '' Ioo 0 1 ⊆ range p ∨ u_L '' Ioo 0 1 ⊆ range q := by
    by_contra hnot
    obtain ⟨hnp, hnq⟩ := not_or.mp hnot
    obtain ⟨z₁, hz₁, hz₁p⟩ := not_subset.mp hnp
    obtain ⟨z₂, hz₂, hz₂q⟩ := not_subset.mp hnq
    obtain ⟨z, ⟨t, ht, rfl⟩, ⟨r, hr⟩, ⟨r', hr'⟩⟩ :=
      isPreconnected_closed_iff.mp hconn_L _ _ hAc hBc hcov_uL
        ⟨z₂, hz₂, (hcov_uL hz₂).resolve_right hz₂q⟩
        ⟨z₁, hz₁, (hcov_uL hz₁).resolve_left hz₁p⟩
    rcases hpq.5 r r' (hr.trans hr'.symm) with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ht.1.ne' (hu_L.2 (hr.symm.trans (hp0.trans hf0.symm)))
    · exact ht.2.ne (hu_L.2 (hr.symm.trans (hp1.trans hf1.symm)))
  have h_eq_of_sub : ∀ {w : unitInterval → S}, IsArcMap w → w 0 = φ u → w 1 = φ v →
      u_L '' Ioo 0 1 ⊆ range w → L = range w := by
    intro w hw hw0 hw1 hsub
    rw [← hru_L]
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      rcases eq_or_ne t 0 with rfl | h0
      · exact ⟨0, hw0.trans hf0.symm⟩
      rcases eq_or_ne t 1 with rfl | h1
      · exact ⟨1, hw1.trans hf1.symm⟩
      exact hsub ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩, rfl⟩
    · rintro _ ⟨r, rfl⟩
      by_contra hcon
      have hA1 : IsClosed (w '' Iic r) := (isClosed_Iic.isCompact.image hw.1).isClosed
      have hB1 : IsClosed (w '' Ici r) := (isClosed_Ici.isCompact.image hw.1).isClosed
      have h1 : range u_L ⊆ range w := by
        rintro _ ⟨t, rfl⟩
        rcases eq_or_ne t 0 with rfl | h0
        · exact ⟨0, hw0.trans hf0.symm⟩
        rcases eq_or_ne t 1 with rfl | h1
        · exact ⟨1, hw1.trans hf1.symm⟩
        exact hsub ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr h0, unitInterval.lt_one_iff_ne_one.mpr h1⟩, rfl⟩
      have hcov1 : range u_L ⊆ w '' Iic r ∪ w '' Ici r := fun z hz => by
        obtain ⟨s, rfl⟩ := h1 hz
        rcases le_total s r with h | h
        · exact .inl ⟨s, h, rfl⟩
        · exact .inr ⟨s, h, rfl⟩
      obtain ⟨z, hz, ⟨s₁, hs₁, rfl⟩, ⟨s₂, hs₂, he⟩⟩ :=
        isPreconnected_closed_iff.mp (isPreconnected_range hu_L.1) _ _ hA1 hB1 hcov1
          ⟨φ u, ⟨0, hf0⟩, 0, unitInterval.nonneg', hw0⟩
          ⟨φ v, ⟨1, hf1⟩, 1, unitInterval.le_one', hw1⟩
      have hs12 : s₂ = s₁ := hw.2 he
      subst hs12
      have hsr : s₂ = r := le_antisymm hs₁ hs₂
      subst hsr
      exact hcon hz
  have hcyc_a : ∀ z : Circle, φ z ∈ range p \ {φ u, φ v} → GM19.CircleCyclic u z v := by
    rintro z ⟨⟨r, hr⟩, hz_not⟩
    have hz_eq : z = a_arc r := hφi hr.symm
    have hr0 : (0 : ℝ) < r.1 := by
      refine lt_of_le_of_ne r.2.1 fun h0 => hz_not (Or.inl ?_)
      have : r = 0 := Subtype.ext h0.symm
      rw [← hr, this, hp0]
    have hr1 : (r : ℝ) < 1 := by
      refine lt_of_le_of_ne r.2.2 fun h1 => hz_not (Or.inr ?_)
      have : r = 1 := Subtype.ext h1
      rw [← hr, this, hp1]
      rfl
    exact ⟨r.1 * θ, θ, mul_pos hr0 hθ_Ioo.1, mul_lt_of_lt_one_left hθ_Ioo.1 hr1, hθ_Ioo.2,
      hz_eq.trans (ha_arc r), hv_eq⟩
  have hcyc_b : ∀ z : Circle, φ z ∈ range q \ {φ u, φ v} → GM19.CircleCyclic u v z := by
    rintro z ⟨⟨r, hr⟩, hz_not⟩
    have hz_eq : z = b_arc r := hφi hr.symm
    have hr0 : (0 : ℝ) < r.1 := by
      refine lt_of_le_of_ne r.2.1 fun h0 => hz_not (Or.inl ?_)
      have : r = 0 := Subtype.ext h0.symm
      rw [← hr, this, hq0]
    have hr1 : (r : ℝ) < 1 := by
      refine lt_of_le_of_ne r.2.2 fun h1 => hz_not (Or.inr ?_)
      have : r = 1 := Subtype.ext h1
      rw [← hr, this, hq1]
      rfl
    have hdiff_pos : 0 < 2 * Real.pi - θ := sub_pos.mpr hθ_Ioo.2
    exact ⟨θ, 2 * Real.pi - r.1 * (2 * Real.pi - θ), hθ_Ioo.1,
      by nlinarith, by nlinarith [mul_pos hr0 hdiff_pos],
      hv_eq, hz_eq.trans (hb_arc r)⟩
  rw [hφ_pos u x_C v hux hvx huv, hφ_pos u v y_C huv hvy huy]
  rcases h_sub_or with hsub_p | hsub_q
  · have hL_eq : L = range p := h_eq_of_sub hpq.1 hp0 hp1 hsub_p
    have hx_p : φ x_C ∈ range p \ {φ u, φ v} := hL_eq ▸ hx
    have hy_q : φ y_C ∈ range q \ {φ u, φ v} := by
      refine ⟨(hcov_pq ▸ hy.1).resolve_left (hL_eq ▸ hy.2), ?_⟩
      rintro (h1 | h2)
      · exact huy (hφi h1.symm)
      · exact hvy (hφi h2.symm)
    exact iff_of_true (hcyc_a x_C hx_p) (hcyc_b y_C hy_q)
  · have hL_eq : L = range q := h_eq_of_sub hpq.2 hq0 hq1 hsub_q
    have hx_q : φ x_C ∈ range q \ {φ u, φ v} := hL_eq ▸ hx
    have hy_p : φ y_C ∈ range p \ {φ u, φ v} := by
      refine ⟨(hcov_pq ▸ hy.1).resolve_right (hL_eq ▸ hy.2), ?_⟩
      rintro (h1 | h2)
      · exact huy (hφi h1.symm)
      · exact hvy (hφi h2.symm)
    exact iff_of_false
      (fun h => cyclic_not_swap (hcyc_b x_C hx_q) h)
      (fun h => cyclic_not_swap (hcyc_a y_C hy_p) h)

omit [T2Space S] in
/-- Cyclic rotation preserves `orient.pos` on the boundary of a closed disc `D`. -/
theorem orient_pos_rotate
    (orient : GM19.SurfaceOrientation S) {D : Set S} {a b c : S}
    (hD : IsClosedDisc D) (ha : a ∈ discBd D) (hb : b ∈ discBd D) (hc : c ∈ discBd D)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    orient.pos D a b c ↔ orient.pos D b c a := by
  obtain ⟨φ, _, hφi, hφr, hφ_pos⟩ := orient.isDirection D hD
  obtain ⟨u, rfl⟩ : a ∈ range φ := hφr.symm ▸ ha
  obtain ⟨v, rfl⟩ : b ∈ range φ := hφr.symm ▸ hb
  obtain ⟨w, rfl⟩ : c ∈ range φ := hφr.symm ▸ hc
  have huv : u ≠ v := fun h => hab (congrArg φ h)
  have hvw : v ≠ w := fun h => hbc (congrArg φ h)
  have huw : u ≠ w := fun h => hac (congrArg φ h)
  rw [hφ_pos u v w huv hvw huw, hφ_pos v w u hvw huw.symm huv.symm]
  exact ⟨GM19.CircleCyclic.rotate, fun h => h.rotate.rotate⟩

omit [T2Space S] in
/-- Removing a subset of `discBd D` from a closed disc `D` leaves a preconnected set. -/
theorem isPreconnected_disc_sdiff_of_subset_discBd {D A : Set S}
    (hD : IsClosedDisc D) (hA : A ⊆ discBd D) :
    IsPreconnected (D \ A) :=
  hD.isPreconnected_discInt.subset_closure (fun _ hx => ⟨hx.1, fun h => hx.2 (hA h)⟩)
    (sdiff_subset.trans hD.subset_closure_discInt)

omit [T2Space S] in
/-- Every point of a closed disc `D` lies in the closure of `D \ A` for any `A ⊆ discBd D`. -/
theorem subset_closure_disc_sdiff_of_subset_discBd {D A : Set S}
    (hD : IsClosedDisc D) (hA : A ⊆ discBd D) :
    D ⊆ closure (D \ A) :=
  hD.subset_closure_discInt.trans (closure_mono fun _ hx => ⟨hx.1, fun h => hx.2 (hA h)⟩)

/-- Three pairwise disjoint lines `L 0, L 1, L 2` in a closed disc `B` connecting `s 0, s 1, s 2`
on `discBd D_in` (`D_in ⊆ B \ discBd B`) to `t' 0, t' 1, t' 2` on `discBd B` preserve the cyclic
orientation `orient.pos` between `D_in` and `B`. -/
theorem orient_pos_of_three_lines_between_discs
    (orient : GM19.SurfaceOrientation S) {B D_in : Set S}
    (hB : IsClosedDisc B) (hDin : IsClosedDisc D_in) (hDin_sub : D_in ⊆ B \ discBd B)
    {L : Fin 3 → Set S} {s t' : Fin 3 → S}
    (hL_sub : ∀ i, L i ⊆ B)
    (hL_line : ∀ i, IsLineWithEnds (L i) (s i) (t' i))
    (hs_bd : ∀ i, s i ∈ discBd D_in)
    (hL_Din : ∀ i, L i ∩ D_in = {s i})
    (hL_bdB : ∀ i, L i ∩ discBd B = {t' i})
    (hL_disj : Pairwise (fun i j => Disjoint (L i) (L j))) :
    orient.pos D_in (s 0) (s 1) (s 2) ↔ orient.pos B (t' 0) (t' 1) (t' 2) := by
  have hs_mem : ∀ i, s i ∈ L i := fun i => GM11.IsLineWithEnds.left_mem (hL_line i)
  have ht'_mem : ∀ i, t' i ∈ L i := fun i => GM11.IsLineWithEnds.right_mem (hL_line i)
  have hs_ne : ∀ {i j}, i ≠ j → s i ≠ s j :=
    fun hij heq => (hL_disj hij).le_bot ⟨hs_mem _, heq ▸ hs_mem _⟩
  have ht'_ne : ∀ {i j}, i ≠ j → t' i ≠ t' j :=
    fun hij heq => (hL_disj hij).le_bot ⟨ht'_mem _, heq ▸ ht'_mem _⟩
  have ht'_bd : ∀ i, t' i ∈ discBd B := fun i => ((hL_bdB i).symm ▸ mem_singleton (t' i)).2
  have hs_Din : ∀ i, s i ∈ D_in := fun i => Surface.discBd_subset D_in (hs_bd i)
  have ht'_not_Din : ∀ i, t' i ∉ D_in := fun i h => (hDin_sub h).2 (ht'_bd i)
  have hs_ne_t' : ∀ i j, s i ≠ t' j := fun i j heq => ht'_not_Din j (heq ▸ hs_Din i)
  -- Step 1: Split `discBd D_in` at `s 0` and `s 1` and pick the arc `J'` avoiding `s 2`.
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ_union, hJ_inter⟩ :=
    hDin.isOArc_discBd.lines (hs_bd 0) (hs_bd 1) (hs_ne (by decide))
  have hs2_not_inter : s 2 ∉ J₁ ∩ J₂ := by
    rw [hJ_inter]
    rintro (h | h)
    · exact hs_ne (by decide) h
    · exact hs_ne (by decide) h
  have hex_J' : ∃ J' : Set S,
      IsLineWithEnds J' (s 0) (s 1) ∧ J' ⊆ discBd D_in ∧ s 2 ∈ discBd D_in \ J' := by
    by_cases hs2_J₁ : s 2 ∈ J₁
    · exact ⟨J₂, hJ₂, hJ_union ▸ subset_union_right, ⟨hs_bd 2, fun h2 => hs2_not_inter ⟨hs2_J₁, h2⟩⟩⟩
    · exact ⟨J₁, hJ₁, hJ_union ▸ subset_union_left, ⟨hs_bd 2, hs2_J₁⟩⟩
  obtain ⟨J', hJ'_line, hJ'_sub, hs2_not_J'⟩ := hex_J'
  have hJ'_Din : J' ⊆ D_in := hJ'_sub.trans (Surface.discBd_subset D_in)
  -- Pick a midpoint `m ∈ J' \ {s 0, s 1}`.
  obtain ⟨f_J', hfJ'0, hfJ'1⟩ := id hJ'_line
  let t_half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let m : S := (f_J' t_half).1
  have hm_mem : m ∈ J' \ {s 0, s 1} := by
    refine ⟨(f_J' t_half).2, ?_⟩
    rintro (h0 | h1)
    · have heq := f_J'.injective (Subtype.ext (h0.trans hfJ'0.symm))
      exact absurd (congrArg Subtype.val heq) (by norm_num [t_half])
    · have heq := f_J'.injective (Subtype.ext (h1.trans hfJ'1.symm))
      exact absurd (congrArg Subtype.val heq) (by norm_num [t_half])
  have h_step1 : orient.pos D_in (s 0) (s 1) (s 2) ↔ orient.pos D_in (s 0) m (s 1) :=
    (orient_pos_of_line_in_discBd orient hDin hJ'_line hJ'_sub hm_mem hs2_not_J').symm
  -- Step 2: Form the combined arc `F' = L 0 ∪ (J' ∪ L 1)`.
  have hJ'_inter_L1 : J' ∩ L 1 = {s 1} := by
    apply Subset.antisymm
    · intro x ⟨hxJ', hxL1⟩
      have hx : x ∈ L 1 ∩ D_in := ⟨hxL1, hJ'_Din hxJ'⟩
      rwa [hL_Din 1] at hx
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨GM11.IsLineWithEnds.right_mem hJ'_line, hs_mem 1⟩
  have hJ'L1_line : IsLineWithEnds (J' ∪ L 1) (s 0) (t' 1) :=
    hJ'_line.union (hL_line 1) hJ'_inter_L1
  have hL0_inter_J'L1 : L 0 ∩ (J' ∪ L 1) = {s 0} := by
    apply Subset.antisymm
    · rintro x ⟨hxL0, hxJ' | hxL1⟩
      · have hx : x ∈ L 0 ∩ D_in := ⟨hxL0, hJ'_Din hxJ'⟩
        rwa [hL_Din 0] at hx
      · exact False.elim ((hL_disj (by decide)).le_bot ⟨hxL0, hxL1⟩)
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨hs_mem 0, Or.inl (GM11.IsLineWithEnds.left_mem hJ'_line)⟩
  let F' : Set S := L 0 ∪ (J' ∪ L 1)
  have hF'_line : IsLineWithEnds F' (t' 0) (t' 1) :=
    (hL_line 0).symm.union hJ'L1_line hL0_inter_J'L1
  have hF'_sub : F' ⊆ B :=
    union_subset (hL_sub 0) (union_subset (hJ'_Din.trans (hDin_sub.trans sdiff_subset)) (hL_sub 1))
  have hF'_bdB : F' ∩ discBd B = {t' 0, t' 1} := by
    ext x
    constructor
    · rintro ⟨hxL0 | hxJ' | hxL1, hxbd⟩
      · have hx : x ∈ L 0 ∩ discBd B := ⟨hxL0, hxbd⟩
        rw [hL_bdB 0] at hx
        exact Or.inl hx
      · exact False.elim ((hDin_sub (hJ'_Din hxJ')).2 hxbd)
      · have hx : x ∈ L 1 ∩ discBd B := ⟨hxL1, hxbd⟩
        rw [hL_bdB 1] at hx
        exact Or.inr hx
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (ht'_mem 0), ht'_bd 0⟩
      · exact ⟨Or.inr (Or.inr (ht'_mem 1)), ht'_bd 1⟩
  -- Step 3: Cut `B` along `F'` and select the subdisc `Δ'` containing `K = (D_in \ J') ∪ L 2`.
  obtain ⟨E₁, E₂, hE₁, hE₂, hE_union, hE_inter, hE₁_int, hE₂_int, _, _, hE_conn⟩ :=
    disc_iArc_split_subdiscs hB hF'_line hF'_sub (ht'_ne (by decide)) hF'_bdB
  let K : Set S := (D_in \ J') ∪ L 2
  have hK_sub : K ⊆ B :=
    union_subset (sdiff_subset.trans (hDin_sub.trans sdiff_subset)) (hL_sub 2)
  have hK_disj : Disjoint K F' := by
    rw [disjoint_left]
    rintro x (⟨hxDin, hx_not_J'⟩ | hxL2) (hxL0 | hxJ' | hxL1)
    · have hx : x ∈ L 0 ∩ D_in := ⟨hxL0, hxDin⟩
      rw [hL_Din 0] at hx
      exact hx_not_J' (hx ▸ GM11.IsLineWithEnds.left_mem hJ'_line)
    · exact hx_not_J' hxJ'
    · have hx : x ∈ L 1 ∩ D_in := ⟨hxL1, hxDin⟩
      rw [hL_Din 1] at hx
      exact hx_not_J' (hx ▸ GM11.IsLineWithEnds.right_mem hJ'_line)
    · exact (hL_disj (by decide)).le_bot ⟨hxL2, hxL0⟩
    · have hx : x ∈ L 2 ∩ D_in := ⟨hxL2, hJ'_Din hxJ'⟩
      rw [hL_Din 2] at hx
      exact hs2_not_J'.2 (hx ▸ hxJ')
    · exact (hL_disj (by decide)).le_bot ⟨hxL2, hxL1⟩
  have hL2_pre : IsPreconnected (L 2) := by
    obtain ⟨f, _, _⟩ := hL_line 2
    have hEq : L 2 = range (fun t : unitInterval => (f t).1) :=
      Subset.antisymm (fun x hx => ⟨f.symm ⟨x, hx⟩, by simp⟩) (by rintro _ ⟨t, rfl⟩; exact (f t).2)
    rw [hEq]
    exact isPreconnected_range (continuous_subtype_val.comp f.continuous)
  have hK_pre : IsPreconnected (K \ F') := by
    rw [sdiff_eq_left.mpr hK_disj]
    refine (isPreconnected_disc_sdiff_of_subset_discBd hDin hJ'_sub).union' ?_ hL2_pre
    exact ⟨s 2, ⟨hs_Din 2, hs2_not_J'.2⟩, hs_mem 2⟩
  have hex_Δ' : ∃ Δ' : Set S,
      IsClosedDisc Δ' ∧ Δ' ⊆ B ∧ F' ⊆ Δ' ∧
      Δ' \ discBd Δ' ⊆ (B \ discBd B) \ F' ∧ K ⊆ Δ' := by
    rcases hE_conn K hK_sub hK_pre with h1 | h2
    · exact ⟨E₁, hE₁, hE_union ▸ subset_union_left, hE_inter ▸ inter_subset_left, hE₁_int, h1⟩
    · exact ⟨E₂, hE₂, hE_union ▸ subset_union_right, hE_inter ▸ inter_subset_right, hE₂_int, h2⟩
  obtain ⟨Δ', hΔ', hΔ'_sub, hF'_Δ', hΔ'_int, hK_Δ'⟩ := hex_Δ'
  have hDin_Δ' : D_in ⊆ Δ' := by
    have hsub : D_in \ J' ⊆ Δ' := subset_union_left.trans hK_Δ'
    exact (subset_closure_disc_sdiff_of_subset_discBd hDin hJ'_sub).trans
      (closure_minimal hsub hΔ'.isClosed)
  have hF'_bdΔ' : F' ⊆ discBd Δ' := by
    intro x hxF'
    by_contra hx_not_bd
    exact (hΔ'_int ⟨hF'_Δ' hxF', hx_not_bd⟩).2 hxF'
  have ht'2_bdΔ' : t' 2 ∈ discBd Δ' \ F' := by
    have ht'2_K : t' 2 ∈ K := Or.inr (ht'_mem 2)
    refine ⟨?_, disjoint_left.mp hK_disj ht'2_K⟩
    by_contra hx_not_bd
    exact (hΔ'_int ⟨hK_Δ' ht'2_K, hx_not_bd⟩).1.2 (ht'_bd 2)
  -- Step 4: Transfer orientation from `D_in` to `Δ'` and across the arcs in `discBd Δ'`.
  have hJ'_bdΔ' : J' ⊆ discBd Δ' :=
    (subset_union_left.trans subset_union_right).trans hF'_bdΔ'
  have hJ'L1_bdΔ' : J' ∪ L 1 ⊆ discBd Δ' :=
    subset_union_right.trans hF'_bdΔ'
  have hs0_J' : s 0 ∈ J' := GM11.IsLineWithEnds.left_mem hJ'_line
  have hs1_J' : s 1 ∈ J' := GM11.IsLineWithEnds.right_mem hJ'_line
  have h_step2 : orient.pos D_in (s 0) m (s 1) ↔ orient.pos Δ' (s 0) m (s 1) :=
    orient.agree D_in Δ' hDin hΔ' hDin_Δ' (s 0) m (s 1)
      ⟨hJ'_sub hs0_J', hJ'_bdΔ' hs0_J'⟩
      ⟨hJ'_sub hm_mem.1, hJ'_bdΔ' hm_mem.1⟩
      ⟨hJ'_sub hs1_J', hJ'_bdΔ' hs1_J'⟩
      (fun h => hm_mem.2 (Or.inl h.symm))
      (fun h => hm_mem.2 (Or.inr h))
      (hs_ne (by decide))
  have ht'1_not_J' : t' 1 ∈ discBd Δ' \ J' :=
    ⟨hF'_bdΔ' (Or.inr (Or.inr (ht'_mem 1))), fun h => ht'_not_Din 1 (hJ'_Din h)⟩
  have h_step3a : orient.pos Δ' (s 0) m (s 1) ↔ orient.pos Δ' (s 0) (s 1) (t' 1) :=
    orient_pos_of_line_in_discBd orient hΔ' hJ'_line hJ'_bdΔ' hm_mem ht'1_not_J'
  have hs1_J'L1 : s 1 ∈ (J' ∪ L 1) \ {s 0, t' 1} := by
    refine ⟨Or.inl hs1_J', ?_⟩
    rintro (h0 | h1)
    · exact hs_ne (by decide) h0
    · exact hs_ne_t' 1 1 h1
  have ht'0_not_J'L1 : t' 0 ∈ discBd Δ' \ (J' ∪ L 1) := by
    refine ⟨hF'_bdΔ' (Or.inl (ht'_mem 0)), ?_⟩
    rintro (hJ' | hL1)
    · exact ht'_not_Din 0 (hJ'_Din hJ')
    · exact (hL_disj (by decide)).le_bot ⟨ht'_mem 0, hL1⟩
  have h_step3b : orient.pos Δ' (s 0) (s 1) (t' 1) ↔ orient.pos Δ' (s 0) (t' 1) (t' 0) :=
    orient_pos_of_line_in_discBd orient hΔ' hJ'L1_line hJ'L1_bdΔ' hs1_J'L1 ht'0_not_J'L1
  have h_rot : orient.pos Δ' (s 0) (t' 1) (t' 0) ↔ orient.pos Δ' (t' 0) (s 0) (t' 1) :=
    (orient_pos_rotate orient hΔ'
      ht'0_not_J'L1.1 (hJ'_bdΔ' hs0_J') ht'1_not_J'.1
      (hs_ne_t' 0 0).symm (hs_ne_t' 0 1) (ht'_ne (by decide))).symm
  have hs0_F' : s 0 ∈ F' \ {t' 0, t' 1} := by
    refine ⟨Or.inl (hs_mem 0), ?_⟩
    rintro (h0 | h1)
    · exact hs_ne_t' 0 0 h0
    · exact hs_ne_t' 0 1 h1
  have h_step3c : orient.pos Δ' (t' 0) (s 0) (t' 1) ↔ orient.pos Δ' (t' 0) (t' 1) (t' 2) :=
    orient_pos_of_line_in_discBd orient hΔ' hF'_line hF'_bdΔ' hs0_F' ht'2_bdΔ'
  -- Step 5: Transfer orientation from `Δ'` to `B`.
  have h_step4 : orient.pos Δ' (t' 0) (t' 1) (t' 2) ↔ orient.pos B (t' 0) (t' 1) (t' 2) :=
    orient.agree Δ' B hΔ' hB hΔ'_sub (t' 0) (t' 1) (t' 2)
      ⟨ht'0_not_J'L1.1, ht'_bd 0⟩
      ⟨ht'1_not_J'.1, ht'_bd 1⟩
      ⟨ht'2_bdΔ'.1, ht'_bd 2⟩
      (ht'_ne (by decide)) (ht'_ne (by decide)) (ht'_ne (by decide))
  exact h_step1.trans (h_step2.trans (h_step3a.trans (h_step3b.trans (h_rot.trans (h_step3c.trans h_step4)))))

/-- Given a closed disc `Δ₀` on a sphere `S` and three distinct points `t 0, t 1, t 2 ∈ subBd Δ₀`,
there exist an enclosing closed disc `B` (`Δ₀ ⊆ B \ discBd B`), three points `t' 0, t' 1, t' 2 ∈ discBd B`,
and three pairwise disjoint lines `R 0, R 1, R 2 ⊆ B` with `IsLineWithEnds (R i) (t i) (t' i)`,
`R i ∩ Δ₀ = {t i}`, `R i ∩ discBd B = {t' i}`, and
`orient.pos Δ₀ (t 0) (t 1) (t 2) ↔ orient.pos B (t' 0) (t' 1) (t' 2)`. -/
theorem exists_collar_radial_lines
    (hS : IsSphere S) (orient : GM19.SurfaceOrientation S)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    {t : Fin 3 → S} (ht_bd : ∀ i, t i ∈ subBd Δ₀) (ht_inj : Function.Injective t) :
    ∃ (B : Set S) (t' : Fin 3 → S) (R : Fin 3 → Set S),
      IsClosedDisc B ∧
      Δ₀ ⊆ B \ discBd B ∧
      (∀ i, R i ⊆ B) ∧
      (∀ i, IsLineWithEnds (R i) (t i) (t' i)) ∧
      (∀ i, R i ∩ Δ₀ = {t i}) ∧
      (∀ i, R i ∩ discBd B = {t' i}) ∧
      Pairwise (fun i j => Disjoint (R i) (R j)) ∧
      (orient.pos Δ₀ (t 0) (t 1) (t 2) ↔ orient.pos B (t' 0) (t' 1) (t' 2)) := by
  have : Nonempty S := (GM14.IsClosedDisc.nonempty hΔ₀).nonempty
  obtain ⟨hS_closed, hS_conn⟩ := GM11.IsSphere.isClosedSurface hS
  have : ConnectedSpace S := hS_conn
  have hbd_Δ₀ : subBd Δ₀ = discBd Δ₀ := GM14.IsClosedDisc.subBd_eq_discBd hS_closed hΔ₀
  obtain ⟨D_out, hD_out, _, _, hint_out⟩ := exists_complementary_closedDisc_in_sphere hS hΔ₀
  have hbd_out : subBd D_out = discBd D_out := GM14.IsClosedDisc.subBd_eq_discBd hS_closed hD_out
  obtain ⟨Ψ, Ψ', hΨ_c, hΨ'_c, hΨ_l, _, _, _, hΨ_int⟩ :=
    exists_disc_shrink_map_8_3 hD_out isClosed_empty (empty_subset _)
  let Δ_far : Set S := Ψ '' D_out
  have hΔ_far : IsClosedDisc Δ_far := (hD_out.image hΨ_c hΨ'_c hΨ_l).1
  have hΔ₀_disj_far : Disjoint Δ₀ Δ_far := by
    rw [disjoint_right]
    rintro _ ⟨x, hx, rfl⟩ hxΔ₀
    have h1 : Ψ x ∈ D_out \ subBd D_out := hbd_out.symm ▸ hΨ_int x ⟨hx, notMem_empty x⟩
    rw [hint_out] at h1
    exact h1.2 hxΔ₀
  obtain ⟨B, hB, hΔ₀_B, hB_far⟩ :=
    GM12.exists_disc_enlargement_avoiding hS_closed hΔ₀ hΔ_far.isClosed hΔ₀_disj_far
  have hbd_B : subBd B = discBd B := GM14.IsClosedDisc.subBd_eq_discBd hS_closed hB
  obtain ⟨c, _, hci, _, hcs1, _, hcs2, hc_pos⟩ :=
    exists_oriented_collar hS_closed orient hΔ₀ hB hΔ_far hΔ₀_B hB_far
  have hS1 : ∀ w : Circle, (w : ℂ) ∈ sphere (0 : ℂ) 1 :=
    fun w => mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
  have hS2 : ∀ w : Circle, ((2 : ℝ) : ℂ) * w ∈ sphere (0 : ℂ) 2 := fun w => by
    rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, Complex.norm_real]
    norm_num
  have hw_ex : ∀ i : Fin 3, ∃ w : Circle, c w = t i := by
    intro i
    have hi : t i ∈ c '' sphere (0 : ℂ) 1 := by
      rw [hcs1, ← hbd_Δ₀]
      exact ht_bd i
    obtain ⟨z, hz, hcz⟩ := hi
    exact ⟨⟨z, by simpa [Submonoid.unitSphere] using hz⟩, hcz⟩
  choose w hw using hw_ex
  have hw_inj : Function.Injective w := fun i j heq =>
    ht_inj (by rw [← hw i, ← hw j, heq])
  let t' : Fin 3 → S := fun i => c (((2 : ℝ) : ℂ) * (w i : ℂ))
  have ht'_bd : range t' ⊆ subBd B := by
    rintro _ ⟨i, rfl⟩
    rw [hbd_B, ← hcs2]
    exact mem_image_of_mem c (hS2 (w i))
  have ht'_inj : Function.Injective t' := fun i j heq => by
    have h1 := sphere_subset_closedBall (hS2 (w i))
    have h2 := sphere_subset_closedBall (hS2 (w j))
    exact hw_inj (Circle.ext (mul_left_cancel₀ (by norm_num) (hci h1 h2 heq)))
  have h_orient : ∀ j₁ j₂ j₃ : Fin 3, j₁ ≠ j₂ → j₂ ≠ j₃ → j₁ ≠ j₃ →
      (orient.pos Δ₀ (t j₁) (t j₂) (t j₃) ↔ orient.pos B (t' j₁) (t' j₂) (t' j₃)) := by
    intro j₁ j₂ j₃ h12 h23 h13
    rw [← hw j₁, ← hw j₂, ← hw j₃]
    exact hc_pos (w j₁) (w j₂) (w j₃) (hw_inj.ne h12) (hw_inj.ne h23) (hw_inj.ne h13)
  have ht_range : range t ⊆ subBd Δ₀ := by
    rintro _ ⟨i, rfl⟩
    exact ht_bd i
  obtain ⟨M, R, hMU, _, _, hMU_B, _, _, hR_line, _, hR_disj, _, hR_Δ₀, hR_bdB⟩ :=
    exists_annulus_drawing hS_closed orient hΔ₀ hB hΔ_far (hbd_B.symm ▸ hΔ₀_B) hB_far
      t t' ht_range ht_inj ht'_bd ht'_inj h_orient
  refine ⟨B, t', R, hB, hΔ₀_B, ?_, hR_line, hR_Δ₀, fun i => hbd_B ▸ hR_bdB i, hR_disj,
    h_orient 0 1 2 (by decide) (by decide) (by decide)⟩
  intro i
  exact (subset_iUnion R i).trans (hMU ▸ hMU_B)

/-! ## Claim (4) of Theorem 8.3 -/

/-- **Claim (4) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 560):
"(4) For each $A \in \mathcal{A}$, if $|\bar{\pi}(A)| = 3$ and $\pi(A)$ is $s_1, s_2, s_3$ say,
then $s_1, s_2, s_3$ determine the clockwise orientation of $D(A)$." -/
theorem lemma_8_3_claim_4
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Surface.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀)
    (h_compl_r₀ : univ \ r₀ ⊆ Δ₀)
    (hbd_Δ₀ : subBd Δ₀ ∩ Γ.U = PiSet)
    (h_disc_compl : IsClosedDisc (univ \ r₀))
    (h_bd_compl : discBd (univ \ r₀) = C₀.U)
    {α_map : α → S} {D : Graph α β → Set S}
    (hα_Δ₀ : α_map '' Z ⊆ Δ₀)
    (hα_Pi : ∀ p ∈ PiSet, α_map (ιV p) = p)
    (hinj : InjOn α_map Z)
    (hD : ∀ A ∈ 𝒜, IsClosedDisc (D A) ∧ D A ⊆ Δ₀)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), α_map v ∈ subBd (D A))
    (hα_inA : ∀ v ∈ Z, ∀ A ∈ 𝒜, α_map v ∈ D A → v ∈ Set.range (πA A))
    (hD_inter : ∀ A ∈ 𝒜, ∀ A' ∈ 𝒜, A ≠ A' →
      D A ∩ D A' = α_map '' (Set.range (πA A) ∩ Set.range (πA A')))
    (hD_bdΔ₀ : ∀ A ∈ 𝒜,
      D A ∩ subBd Δ₀ = α_map '' (Set.range (πA A) ∩ (ιV '' PiSet))) :
    ∀ A ∈ 𝒜, EnumeratesClockwise orient (D A) (α_map ∘ πA A) := by
  intro A hA h3
  obtain ⟨hS_closed, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hbd_Δ₀_eq : subBd Δ₀ = discBd Δ₀ := GM14.IsClosedDisc.subBd_eq_discBd hS_closed hΔ₀
  have hbd_DA_eq : subBd (D A) = discBd (D A) :=
    GM14.IsClosedDisc.subBd_eq_discBd hS_closed (hD A hA).1
  have hπ_eq_Z : ∀ B' ∈ 𝒜, Set.range (πA B') = Z ∩ V(B') :=
    fun B' hB' => (h83.hyp_vii B' hB').2.2
  let idx : Fin 3 → Fin (πLen A) := fun i => ⟨i.1, by omega⟩
  have hidx_inj : Function.Injective idx :=
    fun i j h => Fin.ext (congrArg (fun x : Fin (πLen A) => x.1) h)
  have hidx_surj : ∀ m : Fin (πLen A), ∃ i : Fin 3, idx i = m :=
    fun m => ⟨⟨m.1, by omega⟩, rfl⟩
  let s : Fin 3 → S := fun i => α_map (πA A (idx i))
  obtain ⟨P₀, t₀, hP₀, hP₀_disj, hP₀_pos⟩ := h83.hyp_viii A hA
  let P : Fin 3 → Graph α β := fun i => P₀ (idx i)
  let t : Fin 3 → S := fun i => t₀ (idx i)
  have ht_Pi : ∀ i, t i ∈ PiSet := fun i => (hP₀ (idx i)).1
  have hP_path : ∀ i, IsGraphPathWithEnds (J.deleteVerts W) (P i) (πA A (idx i)) (ιV (t i)) :=
    fun i => (hP₀ (idx i)).2
  have hs_P : ∀ i, πA A (idx i) ∈ V(P i) := by
    intro i
    obtain ⟨_, W_i, _, hV_i, _⟩ := hP_path i
    rw [hV_i]
    exact W_i.start_mem_support
  have ht_P : ∀ i, ιV (t i) ∈ V(P i) := by
    intro i
    obtain ⟨_, W_i, _, hV_i, _⟩ := hP_path i
    rw [hV_i]
    exact W_i.end_mem_support
  have hP_disj : Pairwise (fun i j => Disjoint V(P i) V(P j)) :=
    fun i j hij => hP₀_disj (hidx_inj.ne hij)
  have h_pos_compl : orient.pos (univ \ r₀) (t 0) (t 1) (t 2) := hP₀_pos h3
  have ht_inj : Function.Injective t := by
    intro i j heq
    by_contra hij
    exact (hP_disj hij).le_bot ⟨ht_P i, heq ▸ ht_P j⟩
  have ht_bd_compl : ∀ i, t i ∈ discBd (univ \ r₀) := by
    intro i
    rw [h_bd_compl]
    exact C₀.V_subset_U (h83.hyp_iii.1 (ht_Pi i))
  have ht_subBd_Δ₀ : ∀ i, t i ∈ subBd Δ₀ :=
    fun i => (hbd_Δ₀.symm ▸ ht_Pi i).1
  have ht_bd_Δ₀ : ∀ i, t i ∈ discBd Δ₀ :=
    fun i => hbd_Δ₀_eq ▸ ht_subBd_Δ₀ i
  have h_pos_Δ₀ : orient.pos Δ₀ (t 0) (t 1) (t 2) :=
    (orient.agree (univ \ r₀) Δ₀ h_disc_compl hΔ₀ h_compl_r₀ (t 0) (t 1) (t 2)
      ⟨ht_bd_compl 0, ht_bd_Δ₀ 0⟩
      ⟨ht_bd_compl 1, ht_bd_Δ₀ 1⟩
      ⟨ht_bd_compl 2, ht_bd_Δ₀ 2⟩
      (ht_inj.ne (by decide)) (ht_inj.ne (by decide)) (ht_inj.ne (by decide))).mp h_pos_compl
  obtain ⟨B, t', R, hB, hΔ₀_B, hR_B, hR_line, hR_Δ₀, hR_bdB, hR_disj, h_orient_Δ₀_B⟩ :=
    exists_collar_radial_lines h83.hyp_i.1 orient hΔ₀ ht_subBd_Δ₀ ht_inj
  have h_pos_B : orient.pos B (t' 0) (t' 1) (t' 2) := h_orient_Δ₀_B.mp h_pos_Δ₀
  -- Build a minimal valid chain and line `M i` in `Δ₀` for each path `P i`.
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  have hα_bdA' : ∀ B' ∈ 𝒜, ∀ v ∈ Z ∩ V(B'), α_map v ∈ subBd (D B') :=
    fun B' hB' v hv => hα_bdA B' hB' v ((hπ_eq_Z B' hB').symm ▸ hv)
  have hD_inter' : ∀ B₁ ∈ 𝒜, ∀ B₂ ∈ 𝒜, B₁ ≠ B₂ →
      D B₁ ∩ D B₂ = α_map '' ((Z ∩ V(B₁)) ∩ (Z ∩ V(B₂))) := by
    intro B₁ hB₁ B₂ hB₂ hne
    rw [hD_inter B₁ hB₁ B₂ hB₂ hne, hπ_eq_Z B₁ hB₁, hπ_eq_Z B₂ hB₂]
  have hD_bdΔ₀' : ∀ B' ∈ 𝒜,
      D B' ∩ subBd Δ₀ = α_map '' ((Z ∩ V(B')) ∩ (ιV '' PiSet)) := by
    intro B' hB'
    rw [hD_bdΔ₀ B' hB', hπ_eq_Z B' hB']
  have hs_Z : ∀ i, πA A (idx i) ∈ Z := by
    intro i
    have hmem : πA A (idx i) ∈ Set.range (πA A) := ⟨idx i, rfl⟩
    rw [hπ_eq_Z A hA] at hmem
    exact hmem.1
  have ht_Z : ∀ i, ιV (t i) ∈ Z :=
    fun i => h83.hyp_vi.2.1 ⟨t i, ht_Pi i, rfl⟩
  have hex_chain : ∀ i : Fin 3, ∃ (k : ℕ) (z : ℕ → α) (A_seq : ℕ → Graph α β),
      ValidChain Z 𝒜 (V(P i) ∩ Z) (πA A (idx i)) (ιV (t i)) k z A_seq ∧
      (∀ m₁ ≤ k, ∀ m₂ ≤ k, z m₁ = z m₂ → m₁ = m₂) ∧
      (∀ m₁ < k, ∀ m₂ < k, A_seq m₁ = A_seq m₂ → m₁ = m₂) := by
    intro i
    obtain ⟨hle_i, W₀_i, hs₀_i, hV_i, _⟩ := hP_path i
    obtain ⟨W_i, hsupp_i, _⟩ := W₀_i.exists_transfer (G' := J.deleteVerts W)
      (fun _ _ _ _ hlk => hlk.mono hle_i)
      (fun z hz => hle_i.vertexSet_mono (W₀_i.mem_vertexSet_of_mem_support hz))
    have hW_i_simp : W_i.IsSimple := by
      change W_i.support.Nodup
      rw [hsupp_i]
      exact hs₀_i
    have hex_vc := exists_validChain_of_walk (S_verts := V(P i) ∩ Z) hZdiv W_i hW_i_simp (hs_Z i) (ht_Z i)
      (fun y hy hyZ => ⟨by rw [hV_i, ← hsupp_i]; exact hy, hyZ⟩)
    exact exists_minimal_validChain hex_vc
  choose k z A_seq hvc hz_inj hA_inj using hex_chain
  have hex_M : ∀ i : Fin 3, ∃ M : Set S,
      M ⊆ {s i} ∪ ⋃ m < k i, D (A_seq i m) ∧
      M ⊆ Δ₀ ∧
      s i ∈ M ∧ t i ∈ M ∧
      ((πA A (idx i) = ιV (t i) ∧ M = {s i}) ∨
        (πA A (idx i) ≠ ιV (t i) ∧ IsLineWithEnds M (s i) (t i))) ∧
      M ∩ subBd Δ₀ ⊆ α_map '' (V(P i) ∩ Z) ∧
      (∀ B' ∈ 𝒜, (∀ m < k i, A_seq i m ≠ B') → M ∩ D B' ⊆ (α_map '' (V(P i) ∩ Z)) ∩ D B') := by
    intro i
    obtain ⟨M, hM_cov, hM_Δ₀, hs_M, ht_M, hM_cases, hM_bd, hM_other, _⟩ :=
      exists_line_of_validChain hS_closed hα_Δ₀ hinj hD hα_bdA' hD_inter' hD_bdΔ₀'
        inter_subset_right (hvc i) (hz_inj i) (hA_inj i)
    have hα_t : α_map (ιV (t i)) = t i := hα_Pi (t i) (ht_Pi i)
    rw [hα_t] at ht_M hM_cases
    exact ⟨M, hM_cov, hM_Δ₀, hs_M, ht_M, hM_cases, hM_bd, hM_other⟩
  choose M hM_cov hM_Δ₀ hs_M ht_M hM_cases hM_bd hM_other using hex_M
  -- Disjointness of `α_map '' (V(P i) ∩ Z)` for `i ≠ j`.
  have hαP_disj : ∀ {i j : Fin 3}, i ≠ j →
      Disjoint (α_map '' (V(P i) ∩ Z)) (α_map '' (V(P j) ∩ Z)) := by
    intro i j hij
    rw [disjoint_left]
    rintro _ ⟨u, ⟨huP, huZ⟩, rfl⟩ ⟨v, ⟨hvP, hvZ⟩, huv⟩
    have heq : u = v := hinj huZ hvZ huv.symm
    exact (hP_disj hij).le_bot ⟨huP, heq ▸ hvP⟩
  -- Key fact 1: `V(P i) ∩ (Z ∩ V(A)) = {πA A (idx i)}`.
  have hP_inter_ZA : ∀ i : Fin 3, V(P i) ∩ (Z ∩ V(A)) = {πA A (idx i)} := by
    intro i
    ext x
    constructor
    · rintro ⟨hxP, hxZA⟩
      have hx_range : x ∈ Set.range (πA A) := (hπ_eq_Z A hA).symm ▸ hxZA
      obtain ⟨m_idx, rfl⟩ := hx_range
      obtain ⟨j, rfl⟩ := hidx_surj m_idx
      by_contra hne
      have hij : i ≠ j := fun h => hne (congrArg (fun r => πA A (idx r)) h.symm)
      exact (hP_disj hij).le_bot ⟨hxP, hs_P j⟩
    · rintro rfl
      exact ⟨hs_P i, (hπ_eq_Z A hA) ▸ ⟨idx i, rfl⟩⟩
  -- Key fact 2: `A_seq i m ≠ A` for all `m < k i`.
  have hA_seq_ne_A : ∀ (i : Fin 3) (m : ℕ), m < k i → A_seq i m ≠ A := by
    intro i m hm heq
    obtain ⟨_, hzm, hzm1⟩ := (hvc i).2.2.2 m hm
    rw [heq] at hzm hzm1
    have h1 : z i m ∈ V(P i) ∩ (Z ∩ V(A)) :=
      ⟨((hvc i).2.2.1 m (le_of_lt hm)).1, hzm⟩
    have h2 : z i (m + 1) ∈ V(P i) ∩ (Z ∩ V(A)) :=
      ⟨((hvc i).2.2.1 (m + 1) hm).1, hzm1⟩
    rw [hP_inter_ZA i, mem_singleton_iff] at h1 h2
    have hm_eq := hz_inj i m (le_of_lt hm) (m + 1) hm (h1.trans h2.symm)
    omega
  -- Key fact 3: `M i ∩ D A = {s i}`.
  have hM_inter_DA : ∀ i : Fin 3, M i ∩ D A = {s i} := by
    intro i
    apply Subset.antisymm
    · intro x hx
      have hx' := hM_other i A hA (hA_seq_ne_A i) hx
      obtain ⟨⟨v, ⟨hvP, hvZ⟩, rfl⟩, hvDA⟩ := hx'
      have hv_range : v ∈ Z ∩ V(A) := (hπ_eq_Z A hA) ▸ hα_inA v hvZ A hA hvDA
      have hv_eq : v ∈ ({πA A (idx i)} : Set α) := hP_inter_ZA i ▸ ⟨hvP, hv_range⟩
      exact mem_singleton_iff.mpr (congrArg α_map (mem_singleton_iff.mp hv_eq))
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨hs_M i, Surface.discBd_subset (D A) (hbd_DA_eq ▸ hα_bdA A hA (πA A (idx i)) ⟨idx i, rfl⟩)⟩
  -- Key fact 4: `A_seq i m₁ ≠ A_seq j m₂` for `i ≠ j` (by pigeonhole: 2 + 2 = 4 > 3 ≥ |πBar(A')|).
  have hA_seq_disj : ∀ {i j : Fin 3}, i ≠ j → ∀ m₁ < k i, ∀ m₂ < k j, A_seq i m₁ ≠ A_seq j m₂ := by
    intro i j hij m₁ hm₁ m₂ hm₂ heq
    obtain ⟨hA', hzm₁, hzm₁'⟩ := (hvc i).2.2.2 m₁ hm₁
    obtain ⟨_, hzm₂, hzm₂'⟩ := (hvc j).2.2.2 m₂ hm₂
    have hzm₂A' : z j m₂ ∈ Z ∩ V(A_seq i m₁) := heq ▸ hzm₂
    have hzm₂'A' : z j (m₂ + 1) ∈ Z ∩ V(A_seq i m₁) := heq ▸ hzm₂'
    have hu₁_P : z i m₁ ∈ V(P i) := ((hvc i).2.2.1 m₁ (le_of_lt hm₁)).1
    have hu₂_P : z i (m₁ + 1) ∈ V(P i) := ((hvc i).2.2.1 (m₁ + 1) hm₁).1
    have hv₁_P : z j m₂ ∈ V(P j) := ((hvc j).2.2.1 m₂ (le_of_lt hm₂)).1
    have hv₂_P : z j (m₂ + 1) ∈ V(P j) := ((hvc j).2.2.1 (m₂ + 1) hm₂).1
    obtain ⟨a₁, ha₁⟩ : z i m₁ ∈ Set.range (πA (A_seq i m₁)) := (hπ_eq_Z (A_seq i m₁) hA').symm ▸ hzm₁
    obtain ⟨a₂, ha₂⟩ : z i (m₁ + 1) ∈ Set.range (πA (A_seq i m₁)) := (hπ_eq_Z (A_seq i m₁) hA').symm ▸ hzm₁'
    obtain ⟨b₁, hb₁⟩ : z j m₂ ∈ Set.range (πA (A_seq i m₁)) := (hπ_eq_Z (A_seq i m₁) hA').symm ▸ hzm₂A'
    obtain ⟨b₂, hb₂⟩ : z j (m₂ + 1) ∈ Set.range (πA (A_seq i m₁)) := (hπ_eq_Z (A_seq i m₁) hA').symm ▸ hzm₂'A'
    have ha₁₂ : a₁.1 ≠ a₂.1 := fun h => by
      have heq_z : z i m₁ = z i (m₁ + 1) := ha₁.symm.trans (congrArg (πA (A_seq i m₁)) (Fin.ext h) |>.trans ha₂)
      have := hz_inj i m₁ (le_of_lt hm₁) (m₁ + 1) hm₁ heq_z
      omega
    have hb₁₂ : b₁.1 ≠ b₂.1 := fun h => by
      have heq_z : z j m₂ = z j (m₂ + 1) := hb₁.symm.trans (congrArg (πA (A_seq i m₁)) (Fin.ext h) |>.trans hb₂)
      have := hz_inj j m₂ (le_of_lt hm₂) (m₂ + 1) hm₂ heq_z
      omega
    have hab₁₁ : a₁.1 ≠ b₁.1 := fun h =>
      (hP_disj hij).le_bot ⟨hu₁_P, ha₁.symm.trans (congrArg (πA (A_seq i m₁)) (Fin.ext h) |>.trans hb₁) ▸ hv₁_P⟩
    have hab₁₂ : a₁.1 ≠ b₂.1 := fun h =>
      (hP_disj hij).le_bot ⟨hu₁_P, ha₁.symm.trans (congrArg (πA (A_seq i m₁)) (Fin.ext h) |>.trans hb₂) ▸ hv₂_P⟩
    have hab₂₁ : a₂.1 ≠ b₁.1 := fun h =>
      (hP_disj hij).le_bot ⟨hu₂_P, ha₂.symm.trans (congrArg (πA (A_seq i m₁)) (Fin.ext h) |>.trans hb₁) ▸ hv₁_P⟩
    have hab₂₂ : a₂.1 ≠ b₂.1 := fun h =>
      (hP_disj hij).le_bot ⟨hu₂_P, ha₂.symm.trans (congrArg (πA (A_seq i m₁)) (Fin.ext h) |>.trans hb₂) ▸ hv₂_P⟩
    have hlen_le : πLen (A_seq i m₁) ≤ 3 := (h83.hyp_vii (A_seq i m₁) hA').1
    have := a₁.2; have := a₂.2; have := b₁.2; have := b₂.2
    omega
  -- Key fact 5: `M 0, M 1, M 2` are pairwise disjoint.
  have hM_sub_αP_of_inter : ∀ {i j : Fin 3}, i ≠ j → ∀ x ∈ M i ∩ M j,
      x ∈ α_map '' (V(P j) ∩ Z) := by
    intro i j hij x ⟨hxMi, hxMj⟩
    rcases hM_cov i hxMi with rfl | hU
    · have hs_DA : s i ∈ D A :=
        Surface.discBd_subset (D A) (hbd_DA_eq ▸ hα_bdA A hA (πA A (idx i)) ⟨idx i, rfl⟩)
      have hx_eq : s i ∈ ({s j} : Set S) := hM_inter_DA j ▸ ⟨hxMj, hs_DA⟩
      rw [mem_singleton_iff.mp hx_eq]
      exact ⟨πA A (idx j), ⟨hs_P j, hs_Z j⟩, rfl⟩
    · obtain ⟨m₁, hm₁, hxD⟩ := mem_iUnion₂.mp hU
      have hB' : A_seq i m₁ ∈ 𝒜 := ((hvc i).2.2.2 m₁ hm₁).1
      exact (hM_other j (A_seq i m₁) hB' (fun m₂ hm₂ => (hA_seq_disj hij m₁ hm₁ m₂ hm₂).symm)
        ⟨hxMj, hxD⟩).1
  have hM_disj : Pairwise (fun i j => Disjoint (M i) (M j)) := by
    intro i j hij
    rw [disjoint_left]
    intro x hxMi hxMj
    exact (hαP_disj hij).le_bot
      ⟨hM_sub_αP_of_inter hij.symm x ⟨hxMj, hxMi⟩, hM_sub_αP_of_inter hij x ⟨hxMi, hxMj⟩⟩
  -- Key fact 6: Append the collar radial lines `R i` to `M i` to form `L i = M i ∪ R i`.
  let L : Fin 3 → Set S := fun i => M i ∪ R i
  have hDin_sub_B : D A ⊆ B \ discBd B := (hD A hA).2.trans hΔ₀_B
  have hL_sub : ∀ i, L i ⊆ B :=
    fun i => union_subset ((hM_Δ₀ i).trans (hΔ₀_B.trans sdiff_subset)) (hR_B i)
  have hL_line : ∀ i, IsLineWithEnds (L i) (s i) (t' i) := by
    intro i
    rcases hM_cases i with ⟨heq_st, hM_eq⟩ | ⟨_, hM_line⟩
    · have hs_eq_t : s i = t i := by
        dsimp only [s]
        rw [heq_st, hα_Pi (t i) (ht_Pi i)]
      have hL_eq : L i = R i := by
        dsimp only [L]
        rw [hM_eq, hs_eq_t, union_eq_right.mpr
          (singleton_subset_iff.mpr (GM11.IsLineWithEnds.left_mem (hR_line i)))]
      rw [hL_eq, hs_eq_t]
      exact hR_line i
    · have hMR_inter : M i ∩ R i = {t i} := by
        apply Subset.antisymm
        · intro x ⟨hxM, hxR⟩
          have hx : x ∈ R i ∩ Δ₀ := ⟨hxR, hM_Δ₀ i hxM⟩
          rwa [hR_Δ₀ i] at hx
        · intro x hx
          rw [mem_singleton_iff.mp hx]
          exact ⟨ht_M i, GM11.IsLineWithEnds.left_mem (hR_line i)⟩
      exact hM_line.union (hR_line i) hMR_inter
  have hs_bd : ∀ i, s i ∈ discBd (D A) :=
    fun i => hbd_DA_eq ▸ hα_bdA A hA (πA A (idx i)) ⟨idx i, rfl⟩
  have hL_Din : ∀ i, L i ∩ D A = {s i} := by
    intro i
    apply Subset.antisymm
    · rintro x ⟨hxM | hxR, hxDA⟩
      · exact hM_inter_DA i ▸ ⟨hxM, hxDA⟩
      · have hx_t : x ∈ R i ∩ Δ₀ := ⟨hxR, (hD A hA).2 hxDA⟩
        rw [hR_Δ₀ i, mem_singleton_iff] at hx_t
        subst hx_t
        have ht_DA : α_map (ιV (t i)) ∈ D A := by rwa [hα_Pi (t i) (ht_Pi i)]
        have ht_ZA : ιV (t i) ∈ Z ∩ V(A) :=
          (hπ_eq_Z A hA) ▸ hα_inA (ιV (t i)) (ht_Z i) A hA ht_DA
        have ht_eq : ιV (t i) ∈ ({πA A (idx i)} : Set α) :=
          hP_inter_ZA i ▸ ⟨ht_P i, ht_ZA⟩
        rw [mem_singleton_iff] at ht_eq
        have hs_eq : s i = t i := by
          dsimp only [s]
          rw [← ht_eq, hα_Pi (t i) (ht_Pi i)]
        exact mem_singleton_iff.mpr hs_eq.symm
    · intro x hx
      rw [mem_singleton_iff.mp hx]
      exact ⟨Or.inl (hs_M i), Surface.discBd_subset (D A) (hs_bd i)⟩
  have hL_bdB : ∀ i, L i ∩ discBd B = {t' i} := by
    intro i
    ext x
    constructor
    · rintro ⟨hxM | hxR, hxbd⟩
      · exact False.elim ((hΔ₀_B (hM_Δ₀ i hxM)).2 hxbd)
      · exact hR_bdB i ▸ ⟨hxR, hxbd⟩
    · rintro rfl
      exact ⟨Or.inr (GM11.IsLineWithEnds.right_mem (hR_line i)),
        (hR_bdB i ▸ mem_singleton (t' i)).2⟩
  have hMR_disj : ∀ {i j : Fin 3}, i ≠ j → Disjoint (M i) (R j) := by
    intro i j hij
    rw [disjoint_left]
    intro x hxM hxR
    have hx_t : x ∈ R j ∩ Δ₀ := ⟨hxR, hM_Δ₀ i hxM⟩
    rw [hR_Δ₀ j, mem_singleton_iff] at hx_t
    subst hx_t
    have ht_Mi : t j ∈ α_map '' (V(P i) ∩ Z) :=
      hM_bd i ⟨hxM, ht_subBd_Δ₀ j⟩
    have ht_Mj : t j ∈ α_map '' (V(P j) ∩ Z) :=
      ⟨ιV (t j), ⟨ht_P j, ht_Z j⟩, hα_Pi (t j) (ht_Pi j)⟩
    exact (hαP_disj hij).le_bot ⟨ht_Mi, ht_Mj⟩
  have hL_disj : Pairwise (fun i j => Disjoint (L i) (L j)) := by
    intro i j hij
    dsimp only [L]
    exact (hM_disj hij).union_left (hMR_disj hij.symm).symm |>.union_right
      ((hMR_disj hij).union_left (hR_disj hij))
  exact (orient_pos_of_three_lines_between_discs orient hB (hD A hA).1 hDin_sub_B
    hL_sub hL_line hs_bd hL_Din hL_bdB hL_disj).mpr h_pos_B

end GraphMinor.GM22

