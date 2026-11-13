module

public import GraphMinor.GM22.Section2Forest

/-!
# Graph Minors XXII, Section 2 (Part 3): $Z$-Divisions and Proofs of 2.5, 2.6, and 2.7

This file proves **2.5** (`theorem_2_5`), **2.6** (`theorem_2_6`), and **2.7** (`theorem_2_7`) of
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 532–534).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w u' v'

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {ι : Type w} [Fintype ι]

/-! ## 1. Basic Properties of Indexed $Z$-Divisions -/

theorem IsIndexedZDivision.vertexSet_iUnion {G : Graph α β} {Z : Set α} {A : ι → Graph α β}
    (hdiv : IsIndexedZDivision G Z A) : (⋃ i : ι, V(A i)) = V(G) := by
  have h := congr_arg Graph.vertexSet hdiv.2.1
  simpa [vertexSet_subgraphSUnion] using h

theorem IsIndexedZDivision.edgeSet_iUnion {G : Graph α β} {Z : Set α} {A : ι → Graph α β}
    (hdiv : IsIndexedZDivision G Z A) : (⋃ i : ι, E(A i)) = E(G) := by
  have hle : ∀ P ∈ range A, P ≤ G := by rintro _ ⟨i, rfl⟩; exact hdiv.1 i
  have h := congr_arg Graph.edgeSet hdiv.2.1
  rw [edgeSet_subgraphSUnion hle] at h
  simpa using h

/-- If a simple walk `W` of positive length in `M ≤ G` has no internal vertex in `Z`, where `A` is
an indexed `Z`-division of `G`, then all vertices and edges of `W` belong to a single piece `A i`. -/
theorem exists_piece_of_simple_walk_no_internal_Z
    {G M : Graph α β} {Z : Set α} {A : ι → Graph α β}
    (hMG : M ≤ G) (hdiv : IsIndexedZDivision G Z A)
    {u v : α} {W : GraphWalk M u v} (hW : W.IsSimple) (hpos : 0 < W.length)
    (hno_int : ∀ z ∈ W.support, z ∈ Z → z = u ∨ z = v) :
    ∃ i : ι, (∀ z ∈ W.support, z ∈ V(A i)) ∧ (∀ e ∈ W.edges, e ∈ E(A i)) := by
  cases W with
  | nil _ => simp [GraphWalk.length] at hpos
  | @cons _ m _ e₁ h₁ rest =>
    have he₁G : e₁ ∈ E(G) := hMG.edgeSet_mono h₁.edge_mem
    rw [← hdiv.edgeSet_iUnion, mem_iUnion] at he₁G
    obtain ⟨i, he₁_Ai⟩ := he₁G
    have hnd := List.nodup_cons.mp hW
    have hrest_no_Z : ∀ z ∈ rest.support, z ≠ v → z ∉ Z := by
      intro z hz hzv hzZ
      rcases hno_int z (List.mem_cons_of_mem _ hz) hzZ with rfl | rfl
      · exact hnd.1 hz
      · exact hzv rfl
    have hind : ∀ {a b : α} (R : GraphWalk M a b),
        R.IsSimple → a ∈ V(A i) → (∀ z ∈ R.support, z ≠ b → z ∉ Z) →
        (∀ z ∈ R.support, z ∈ V(A i)) ∧ (∀ e ∈ R.edges, e ∈ E(A i)) := by
      intro a b R
      induction R with
      | nil _ =>
        intro _ ha _
        exact ⟨by simp [ha], by simp⟩
      | @cons a₁ m₁ b₁ e₂ h₂ rest₂ ih =>
        intro hR_simp ha₁ hR_no_Z
        have hnd_R := List.nodup_cons.mp hR_simp
        have ha₁_ne_b₁ : a₁ ≠ b₁ := fun h => hnd_R.1 (h ▸ rest₂.end_mem_support)
        have ha₁_not_Z : a₁ ∉ Z := hR_no_Z a₁ (by simp) ha₁_ne_b₁
        have he₂G : e₂ ∈ E(G) := hMG.edgeSet_mono h₂.edge_mem
        rw [← hdiv.edgeSet_iUnion, mem_iUnion] at he₂G
        obtain ⟨j, he₂_Aj⟩ := he₂G
        have hl₂_Aj : (A j).IsLink e₂ a₁ m₁ :=
          ((hdiv.1 j).isLink_iff he₂_Aj).mpr (h₂.mono hMG)
        have hij : i = j := by
          by_contra hne
          have ha₁_Z : a₁ ∈ Z := (hdiv.2.2 i j hne).2 ⟨ha₁, hl₂_Aj.left_mem⟩
          exact ha₁_not_Z ha₁_Z
        subst hij
        have ⟨hV_rest₂, hE_rest₂⟩ := ih hnd_R.2 hl₂_Aj.right_mem
          (fun z hz => hR_no_Z z (List.mem_cons_of_mem _ hz))
        refine ⟨?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ha₁
          · exact hV_rest₂ z hz
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact he₂_Aj
          · exact hE_rest₂ e he
    have hl₁_Ai : (A i).IsLink e₁ u m :=
      ((hdiv.1 i).isLink_iff he₁_Ai).mpr (h₁.mono hMG)
    have ⟨hV_rest, hE_rest⟩ := hind rest hnd.2 hl₁_Ai.right_mem hrest_no_Z
    refine ⟨i, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hl₁_Ai.left_mem
      · exact hV_rest z hz
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact he₁_Ai
      · exact hE_rest e he

/-! ## 2. Proof of 2.5 -/

omit [Fintype ι] in
/-- **Graph Minors XXII, 2.5 Claim (1)** (Section 2, page 533):
"For $1 \le i \le k$, if $v \in Z'_i$, then $v \in V(L'_i)$ if and only if $\alpha(v) \in V(L)$." -/
theorem lemma_2_5_claim_1 {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v))
    (i : ι) {v : α'} (hv : v ∈ Z' ∩ V(A' i)) :
    v ∈ V(L' i) ↔ α_map v ∈ V(L) := by
  have hαv : α_map v ∈ Z ∩ V(A i) := by
    rw [← h_a i]
    exact mem_image_of_mem α_map hv
  rw [← areConnectedIn_self_iff, h_c i v hv v hv, areConnectedIn_self_iff,
    vertexSet_subgraphInter, mem_inter_iff, and_iff_left hαv.2]

/-- **Graph Minors XXII, 2.5 Claim (2)** (Section 2, page 533):
"For $1 \le i \le k$, $L'_i = L' \cap A'_i$." -/
theorem lemma_2_5_claim_2 {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {G' : Graph α' β'} {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (_hLG : L ≤ G) (_hdiv : IsIndexedZDivision G Z A) (hdiv' : IsIndexedZDivision G' Z' A')
    (hL'_le : ∀ i : ι, L' i ≤ A' i)
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v))
    (i : ι) :
    L' i = subgraphInter G' (subgraphSUnion G' (range L')) (A' i) := by
  let L'_total := subgraphSUnion G' (range L')
  have hL'_G' : ∀ P ∈ range L', P ≤ G' := by
    rintro _ ⟨j, rfl⟩
    exact (hL'_le j).trans (hdiv'.1 j)
  have htot_G' : L'_total ≤ G' := subgraphSUnion_le hL'_G'
  have hLi_G' : L' i ≤ G' := (hL'_le i).trans (hdiv'.1 i)
  refine (Compatible.of_le_le hLi_G' (subgraphInter_le htot_G')).ext ?_ ?_
  · rw [vertexSet_subgraphInter, vertexSet_subgraphSUnion]
    apply Subset.antisymm
    · intro v hv
      exact ⟨mem_iUnion₂.mpr ⟨L' i, ⟨i, rfl⟩, hv⟩, (hL'_le i).vertexSet_mono hv⟩
    · rintro v ⟨hv_tot, hv_Ai⟩
      obtain ⟨_, ⟨j, rfl⟩, hv_Lj⟩ := mem_iUnion₂.mp hv_tot
      by_cases hji : j = i
      · exact hji ▸ hv_Lj
      · have hv_Aj : v ∈ V(A' j) := (hL'_le j).vertexSet_mono hv_Lj
        have hv_Z' : v ∈ Z' := (hdiv'.2.2 i j (Ne.symm hji)).2 ⟨hv_Ai, hv_Aj⟩
        have hαv : α_map v ∈ V(L) :=
          (lemma_2_5_claim_1 h_a h_c j ⟨hv_Z', hv_Aj⟩).mp hv_Lj
        exact (lemma_2_5_claim_1 h_a h_c i ⟨hv_Z', hv_Ai⟩).mpr hαv
  · rw [edgeSet_subgraphInter htot_G' (hdiv'.1 i), edgeSet_subgraphSUnion hL'_G']
    apply Subset.antisymm
    · intro e he
      exact ⟨mem_iUnion₂.mpr ⟨L' i, ⟨i, rfl⟩, he⟩, (hL'_le i).edgeSet_mono he⟩
    · rintro e ⟨he_tot, he_Ai⟩
      obtain ⟨_, ⟨j, rfl⟩, he_Lj⟩ := mem_iUnion₂.mp he_tot
      by_cases hji : j = i
      · exact hji ▸ he_Lj
      · exfalso
        have he_Aj : e ∈ E(A' j) := (hL'_le j).edgeSet_mono he_Lj
        exact disjoint_left.mp (hdiv'.2.2 i j (Ne.symm hji)).1 he_Ai he_Aj

/-- **Graph Minors XXII, 2.5 Claim (3)** (Section 2, page 533):
"If $u, v \in Z'$ are $L'$-connected then $\alpha(u)$ and $\alpha(v)$ are $L$-connected." -/
theorem lemma_2_5_claim_3 {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {G' : Graph α' β'} {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (hLG : L ≤ G) (hdiv : IsIndexedZDivision G Z A) (hdiv' : IsIndexedZDivision G' Z' A')
    (hL'_le : ∀ i : ι, L' i ≤ A' i)
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v))
    {u v : α'} (hu : u ∈ Z') (hv : v ∈ Z')
    (hconn : AreConnectedIn (subgraphSUnion G' (range L')) u v) :
    AreConnectedIn L (α_map u) (α_map v) := by
  let L'_total := subgraphSUnion G' (range L')
  have hL'_G' : ∀ P ∈ range L', P ≤ G' := by
    rintro _ ⟨j, rfl⟩
    exact (hL'_le j).trans (hdiv'.1 j)
  have htot_G' : L'_total ≤ G' := subgraphSUnion_le hL'_G'
  rw [areConnectedIn_iff_walk] at hconn
  rcases hconn with ⟨hu_tot, _, ⟨W₀⟩⟩
  obtain ⟨W, hW_simp, _, _⟩ := exists_isSimple_subwalk W₀
  -- Strong induction on the length of the simple walk `W` in `L'_total`.
  have hind : ∀ n, ∀ {x y : α'}, x ∈ Z' → y ∈ Z' → x ∈ V(L'_total) →
      ∀ (W₁ : GraphWalk L'_total x y), W₁.IsSimple → W₁.length = n →
      AreConnectedIn L (α_map x) (α_map y) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hx hy hx_tot W₁ hW₁_simp hlen
      by_cases hpos : 0 < W₁.length
      · by_cases hint : ∃ z ∈ W₁.support, z ∈ Z' ∧ z ≠ x ∧ z ≠ y
        · obtain ⟨z, hz_supp, hzZ', hzx, hzy⟩ := hint
          obtain ⟨P₁, P₂, rfl⟩ := W₁.exists_append_of_mem hz_supp
          have ⟨hP₁_simp, hP₂_simp⟩ := isSimple_of_append hW₁_simp
          have hP₁_pos : 0 < P₁.length := by
            cases P₁ with
            | nil _ => exact (hzx rfl).elim
            | cons _ _ => simp [GraphWalk.length]
          have hP₂_pos : 0 < P₂.length := by
            cases P₂ with
            | nil _ => exact (hzy rfl).elim
            | cons _ _ => simp [GraphWalk.length]
          have hlen_sum : (P₁.append P₂).length = P₁.length + P₂.length :=
            GraphWalk.length_append P₁ P₂
          have hz_tot : z ∈ V(L'_total) := P₂.mem_vertexSet_of_mem_support P₂.start_mem_support
          have h₁ := ih P₁.length (by omega) hx hzZ' hx_tot P₁ hP₁_simp rfl
          have h₂ := ih P₂.length (by omega) hzZ' hy hz_tot P₂ hP₂_simp rfl
          exact h₁.trans h₂
        · push Not at hint
          have hno_int : ∀ z ∈ W₁.support, z ∈ Z' → z = x ∨ z = y := by
            intro z hz hzZ'
            by_cases hzx : z = x
            · exact Or.inl hzx
            · exact Or.inr (hint z hz hzZ' hzx)
          obtain ⟨i, hV_i, hE_i⟩ :=
            exists_piece_of_simple_walk_no_internal_Z htot_G' hdiv' hW₁_simp hpos hno_int
          have hclaim2 := lemma_2_5_claim_2 hLG hdiv hdiv' hL'_le h_a h_c i
          have hx_Ai : x ∈ V(A' i) := hV_i x W₁.start_mem_support
          have hy_Ai : y ∈ V(A' i) := hV_i y W₁.end_mem_support
          obtain ⟨W_i, _, _⟩ := W₁.exists_transfer (G' := L' i)
            (fun e a b he hl => by
              rw [hclaim2, subgraphInter_isLink htot_G' (hdiv'.1 i)]
              exact ⟨hl, ((hdiv'.1 i).isLink_iff (hE_i e he)).mpr (hl.mono htot_G')⟩)
            (fun z hz => by
              rw [hclaim2, vertexSet_subgraphInter]
              exact ⟨W₁.mem_vertexSet_of_mem_support hz, hV_i z hz⟩)
          have hconn_Li : AreConnectedIn (L' i) x y := by
            rw [areConnectedIn_iff_walk]
            exact ⟨W_i.mem_vertexSet_of_mem_support W_i.start_mem_support,
              W_i.mem_vertexSet_of_mem_support W_i.end_mem_support, ⟨W_i⟩⟩
          have hconn_inter := (h_c i x ⟨hx, hx_Ai⟩ y ⟨hy, hy_Ai⟩).mp hconn_Li
          exact hconn_inter.mono (subgraphInter_le_left hLG (hdiv.1 i))
      · cases W₁ with
        | nil _ =>
          rw [vertexSet_subgraphSUnion] at hx_tot
          obtain ⟨_, ⟨i, rfl⟩, hx_Li⟩ := mem_iUnion₂.mp hx_tot
          have hx_Ai : x ∈ V(A' i) := (hL'_le i).vertexSet_mono hx_Li
          have hαx : α_map x ∈ V(L) :=
            (lemma_2_5_claim_1 h_a h_c i ⟨hx, hx_Ai⟩).mp hx_Li
          exact areConnectedIn_self_iff.mpr hαx
        | cons _ _ => simp [GraphWalk.length] at hpos
  exact hind W.length hu hv hu_tot W hW_simp rfl

/-- **Graph Minors XXII, 2.5 Claim (4)** (Section 2, page 533):
"If $u, v \in Z'$ and $\alpha(u) = \alpha(v) \in V(L)$ then $u, v$ are $L'$-connected." -/
theorem lemma_2_5_claim_4 {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {G' : Graph α' β'} {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (_hLG : L ≤ G) (_hdiv : IsIndexedZDivision G Z A) (hdiv' : IsIndexedZDivision G' Z' A')
    (hZ' : Z' ⊆ V(G')) (hL'_le : ∀ i : ι, L' i ≤ A' i)
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_b : ∀ u ∈ Z', ∀ v ∈ Z', u ≠ v → α_map u = α_map v →
      ∃ i : ι, u ∈ V(A' i) ∧ v ∈ V(A' i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v))
    {u v : α'} (hu : u ∈ Z') (hv : v ∈ Z')
    (heq : α_map u = α_map v) (hαL : α_map u ∈ V(L)) :
    AreConnectedIn (subgraphSUnion G' (range L')) u v := by
  have hL'_G' : ∀ P ∈ range L', P ≤ G' := by
    rintro _ ⟨j, rfl⟩
    exact (hL'_le j).trans (hdiv'.1 j)
  have hex_i : ∃ i : ι, u ∈ V(A' i) ∧ v ∈ V(A' i) := by
    by_cases huv : u = v
    · subst huv
      have huG' : u ∈ V(G') := hZ' hu
      rw [← hdiv'.vertexSet_iUnion, mem_iUnion] at huG'
      obtain ⟨i, huAi⟩ := huG'
      exact ⟨i, huAi, huAi⟩
    · exact h_b u hu v hv huv heq
  obtain ⟨i, huAi, hvAi⟩ := hex_i
  have hα_Ai : α_map u ∈ Z ∩ V(A i) := by
    rw [← h_a i]
    exact mem_image_of_mem α_map ⟨hu, huAi⟩
  have hconn_inter : AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v) := by
    rw [← heq, areConnectedIn_self_iff, vertexSet_subgraphInter]
    exact ⟨hαL, hα_Ai.2⟩
  have hconn_Li : AreConnectedIn (L' i) u v :=
    (h_c i u ⟨hu, huAi⟩ v ⟨hv, hvAi⟩).mpr hconn_inter
  exact hconn_Li.mono (le_subgraphSUnion hL'_G' ⟨i, rfl⟩)

/-- **Graph Minors XXII, 2.5 Claim (5)** (Section 2, page 533):
"If $u, v \in Z'$ and there is a path $P$ of $L$ with ends $\alpha(u), \alpha(v)$ and with no
internal vertex in $Z$, then $u, v$ are $L'$-connected." -/
theorem lemma_2_5_claim_5 {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {G' : Graph α' β'} {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (hLG : L ≤ G) (hdiv : IsIndexedZDivision G Z A) (hdiv' : IsIndexedZDivision G' Z' A')
    (hZ' : Z' ⊆ V(G')) (hL'_le : ∀ i : ι, L' i ≤ A' i)
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_b : ∀ u ∈ Z', ∀ v ∈ Z', u ≠ v → α_map u = α_map v →
      ∃ i : ι, u ∈ V(A' i) ∧ v ∈ V(A' i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v))
    {u v : α'} (hu : u ∈ Z') (hv : v ∈ Z')
    {W : GraphWalk L (α_map u) (α_map v)} (hW : W.IsSimple)
    (hno_int : ∀ z ∈ W.support, z ∈ Z → z = α_map u ∨ z = α_map v) :
    AreConnectedIn (subgraphSUnion G' (range L')) u v := by
  have hL'_G' : ∀ P ∈ range L', P ≤ G' := by
    rintro _ ⟨j, rfl⟩
    exact (hL'_le j).trans (hdiv'.1 j)
  by_cases hpos : 0 < W.length
  · obtain ⟨i, hV_i, hE_i⟩ :=
      exists_piece_of_simple_walk_no_internal_Z hLG hdiv hW hpos hno_int
    have hαu_Ai : α_map u ∈ V(A i) := hV_i (α_map u) W.start_mem_support
    have hαv_Ai : α_map v ∈ V(A i) := hV_i (α_map v) W.end_mem_support
    -- Note that `α_map u, α_map v ∈ Z`: each `z ∈ Z'` belongs to `Z' ∩ V(A' j)` for some `j`,
    -- so `α_map z ∈ Z ∩ V(A j) ⊆ Z` by `h_a j`.
    have hα_mem_Z : ∀ x ∈ Z', α_map x ∈ Z := by
      intro x hx
      have hxG' : x ∈ V(G') := hZ' hx
      rw [← hdiv'.vertexSet_iUnion, mem_iUnion] at hxG'
      obtain ⟨j, hxAj⟩ := hxG'
      have : α_map x ∈ Z ∩ V(A j) := by
        rw [← h_a j]
        exact mem_image_of_mem α_map ⟨hx, hxAj⟩
      exact this.1
    have hαu_Zi : α_map u ∈ α_map '' (Z' ∩ V(A' i)) := by
      rw [h_a i]
      exact ⟨hα_mem_Z u hu, hαu_Ai⟩
    have hαv_Zi : α_map v ∈ α_map '' (Z' ∩ V(A' i)) := by
      rw [h_a i]
      exact ⟨hα_mem_Z v hv, hαv_Ai⟩
    obtain ⟨u', hu'_mem, hu'_eq⟩ := hαu_Zi
    obtain ⟨v', hv'_mem, hv'_eq⟩ := hαv_Zi
    obtain ⟨W_inter, _, _⟩ := W.exists_transfer (G' := subgraphInter G L (A i))
      (fun e a b he hl => by
        rw [subgraphInter_isLink hLG (hdiv.1 i)]
        exact ⟨hl, ((hdiv.1 i).isLink_iff (hE_i e he)).mpr (hl.mono hLG)⟩)
      (fun z hz => by
        rw [vertexSet_subgraphInter]
        exact ⟨W.mem_vertexSet_of_mem_support hz, hV_i z hz⟩)
    have hconn_inter : AreConnectedIn (subgraphInter G L (A i)) (α_map u') (α_map v') := by
      rw [hu'_eq, hv'_eq, areConnectedIn_iff_walk]
      exact ⟨W_inter.mem_vertexSet_of_mem_support W_inter.start_mem_support,
        W_inter.mem_vertexSet_of_mem_support W_inter.end_mem_support, ⟨W_inter⟩⟩
    have hconn_Li : AreConnectedIn (L' i) u' v' :=
      (h_c i u' hu'_mem v' hv'_mem).mpr hconn_inter
    have hconn_tot : AreConnectedIn (subgraphSUnion G' (range L')) u' v' :=
      hconn_Li.mono (le_subgraphSUnion hL'_G' ⟨i, rfl⟩)
    have hconn_uu' : AreConnectedIn (subgraphSUnion G' (range L')) u u' :=
      lemma_2_5_claim_4 hLG hdiv hdiv' hZ' hL'_le h_a h_b h_c hu hu'_mem.1
        hu'_eq.symm (W.mem_vertexSet_of_mem_support W.start_mem_support)
    have hconn_v'v : AreConnectedIn (subgraphSUnion G' (range L')) v' v :=
      lemma_2_5_claim_4 hLG hdiv hdiv' hZ' hL'_le h_a h_b h_c hv'_mem.1 hv
        hv'_eq (hv'_eq.symm ▸ W.mem_vertexSet_of_mem_support W.end_mem_support)
    exact hconn_uu'.trans (hconn_tot.trans hconn_v'v)
  · have hα_eq : α_map u = α_map v := by
      have hlen0 : W.length = 0 := by omega
      have h0 : ∀ {a b : α} (W₀ : GraphWalk L a b), W₀.length = 0 → a = b := by
        intro a b W₀ h0
        cases W₀ with
        | nil _ => rfl
        | cons _ _ => simp [GraphWalk.length] at h0
      exact h0 W hlen0
    exact lemma_2_5_claim_4 hLG hdiv hdiv' hZ' hL'_le h_a h_b h_c hu hv hα_eq
      (W.mem_vertexSet_of_mem_support W.start_mem_support)

/-- **Graph Minors XXII, 2.5 Claim (6)** (Section 2, page 533):
"If $u, v \in Z'$ and $\alpha(u), \alpha(v)$ are $L$-connected then $u, v$ are $L'$-connected." -/
theorem lemma_2_5_claim_6 {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {G' : Graph α' β'} {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (hLG : L ≤ G) (hdiv : IsIndexedZDivision G Z A) (hdiv' : IsIndexedZDivision G' Z' A')
    (hZ' : Z' ⊆ V(G')) (hL'_le : ∀ i : ι, L' i ≤ A' i)
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_b : ∀ u ∈ Z', ∀ v ∈ Z', u ≠ v → α_map u = α_map v →
      ∃ i : ι, u ∈ V(A' i) ∧ v ∈ V(A' i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v))
    {u v : α'} (hu : u ∈ Z') (hv : v ∈ Z')
    (hconn : AreConnectedIn L (α_map u) (α_map v)) :
    AreConnectedIn (subgraphSUnion G' (range L')) u v := by
  rw [areConnectedIn_iff_walk] at hconn
  rcases hconn with ⟨_, _, ⟨W₀⟩⟩
  obtain ⟨W, hW_simp, _, _⟩ := exists_isSimple_subwalk W₀
  -- Every `z ∈ Z ∩ V(L)` is in the image of `Z'` under `α_map` by `h_a`.
  have hsurj_Z : ∀ z ∈ Z, z ∈ V(L) → ∃ w ∈ Z', α_map w = z := by
    intro z hzZ hzL
    have hzG : z ∈ V(G) := hLG.vertexSet_mono hzL
    rw [← hdiv.vertexSet_iUnion, mem_iUnion] at hzG
    obtain ⟨i, hzAi⟩ := hzG
    have hz_img : z ∈ α_map '' (Z' ∩ V(A' i)) := by
      rw [h_a i]
      exact ⟨hzZ, hzAi⟩
    obtain ⟨w, ⟨hwZ', _⟩, rfl⟩ := hz_img
    exact ⟨w, hwZ', rfl⟩
  -- Strong induction on the length of the simple walk `W` in `L`.
  have hind : ∀ n, ∀ {x y : α'}, x ∈ Z' → y ∈ Z' →
      ∀ (W₁ : GraphWalk L (α_map x) (α_map y)), W₁.IsSimple → W₁.length = n →
      AreConnectedIn (subgraphSUnion G' (range L')) x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hx hy W₁ hW₁_simp hlen
      by_cases hint : ∃ z ∈ W₁.support, z ∈ Z ∧ z ≠ α_map x ∧ z ≠ α_map y
      · obtain ⟨z, hz_supp, hzZ, hzx, hzy⟩ := hint
        have hzL : z ∈ V(L) := W₁.mem_vertexSet_of_mem_support hz_supp
        obtain ⟨w, hwZ', hw_eq⟩ := hsurj_Z z hzZ hzL
        subst hw_eq
        obtain ⟨P₁, P₂, rfl⟩ := W₁.exists_append_of_mem hz_supp
        have ⟨hP₁_simp, hP₂_simp⟩ := isSimple_of_append hW₁_simp
        have hlen_pos : ∀ {a b : α} (Q : GraphWalk L a b), a ≠ b → 0 < Q.length := by
          intro a b Q hab
          cases Q with
          | nil _ => exact (hab rfl).elim
          | cons _ _ => simp [GraphWalk.length]
        have hP₁_pos : 0 < P₁.length := hlen_pos P₁ (Ne.symm hzx)
        have hP₂_pos : 0 < P₂.length := hlen_pos P₂ hzy
        have hlen_sum : (P₁.append P₂).length = P₁.length + P₂.length :=
          GraphWalk.length_append P₁ P₂
        have h₁ := ih P₁.length (by omega) hx hwZ' P₁ hP₁_simp rfl
        have h₂ := ih P₂.length (by omega) hwZ' hy P₂ hP₂_simp rfl
        exact h₁.trans h₂
      · push Not at hint
        have hno_int : ∀ z ∈ W₁.support, z ∈ Z → z = α_map x ∨ z = α_map y := by
          intro z hz hzZ
          by_cases hzx : z = α_map x
          · exact Or.inl hzx
          · exact Or.inr (hint z hz hzZ hzx)
        exact lemma_2_5_claim_5 hLG hdiv hdiv' hZ' hL'_le h_a h_b h_c hx hy hW₁_simp hno_int
  exact hind W.length hu hv W hW_simp rfl

/-- **Graph Minors XXII, 2.5** (Section 2, pages 532–533):
"Let $L$ be a subgraph of a graph $G$, let $Z \subseteq V(G)$, and let $\{A_1, \ldots, A_k\}$ be a
$Z$-division of $G$. Let $G'$ be a graph, let $Z' \subseteq V(G')$, and let $\{A'_1, \ldots, A'_k\}$
be a $Z'$-division of $G'$. Let $\alpha : Z' \to Z$ be a function, and for $1 \le i \le k$ let
$L'_i \subseteq A'_i$, such that
(a) for $1 \le i \le k$, $\alpha$ maps $Z' \cap V(A'_i)$ onto $Z \cap V(A_i)$, and"
"(b) if $u, v \in Z'$ are distinct and $\alpha(u) = \alpha(v)$ then $u, v \in V(A'_i)$ for some $i$
($1 \le i \le k$),
(c) for $1 \le i \le k$, $u, v \in Z' \cap V(A'_i)$ are $L'_i$-connected if and only if
$\alpha(u), \alpha(v)$ are $L \cap A_i$-connected.
Let $L' = L'_1 \cup \cdots \cup L'_k$. Then $L'_i = L' \cap A'_i$ for $1 \le i \le k$, and
$u, v \in Z'$ are $L'$-connected if and only if $\alpha(u), \alpha(v)$ are $L$-connected." -/
theorem theorem_2_5_proof {G L : Graph α β} {Z : Set α} {A : ι → Graph α β}
    {G' : Graph α' β'} {Z' : Set α'} {A' : ι → Graph α' β'}
    {α_map : α' → α} {L' : ι → Graph α' β'}
    (hLG : L ≤ G) (_hZ : Z ⊆ V(G)) (hdiv : IsIndexedZDivision G Z A)
    (hZ' : Z' ⊆ V(G')) (hdiv' : IsIndexedZDivision G' Z' A')
    (hL'_le : ∀ i : ι, L' i ≤ A' i)
    (h_a : ∀ i : ι, α_map '' (Z' ∩ V(A' i)) = Z ∩ V(A i))
    (h_b : ∀ u ∈ Z', ∀ v ∈ Z', u ≠ v → α_map u = α_map v →
      ∃ i : ι, u ∈ V(A' i) ∧ v ∈ V(A' i))
    (h_c : ∀ i : ι, ∀ u ∈ Z' ∩ V(A' i), ∀ v ∈ Z' ∩ V(A' i),
      AreConnectedIn (L' i) u v ↔
        AreConnectedIn (subgraphInter G L (A i)) (α_map u) (α_map v)) :
    (∀ i : ι, L' i = subgraphInter G' (subgraphSUnion G' (range L')) (A' i)) ∧
      (∀ u ∈ Z', ∀ v ∈ Z',
        AreConnectedIn (subgraphSUnion G' (range L')) u v ↔
          AreConnectedIn L (α_map u) (α_map v)) := by
  refine ⟨fun i => lemma_2_5_claim_2 hLG hdiv hdiv' hL'_le h_a h_c i,
    fun u hu v hv => ⟨lemma_2_5_claim_3 hLG hdiv hdiv' hL'_le h_a h_c hu hv,
      lemma_2_5_claim_6 hLG hdiv hdiv' hZ' hL'_le h_a h_b h_c hu hv⟩⟩

/-! ## 3. Proofs of 2.6 and 2.7 -/

/-- The `subgraphSUnion` of a 2-element family `![P₁, P₂]` equals `subgraphUnion G P₁ P₂`. -/
theorem subgraphSUnion_range_pair {G P₁ P₂ : Graph α β} (h₁ : P₁ ≤ G) (h₂ : P₂ ≤ G) :
    subgraphSUnion G (range (![P₁, P₂] : Fin 2 → Graph α β)) = subgraphUnion G P₁ P₂ := by
  have hle_range : ∀ P ∈ range (![P₁, P₂] : Fin 2 → Graph α β), P ≤ G := by
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> [exact h₁; exact h₂]
  refine (Compatible.of_le_le (subgraphSUnion_le hle_range) (subgraphUnion_le h₁ h₂)).ext ?_ ?_
  · rw [vertexSet_subgraphSUnion, vertexSet_subgraphUnion]
    ext v
    simp only [mem_iUnion, mem_range, mem_union]
    exact ⟨by rintro ⟨_, ⟨i, rfl⟩, hv⟩; fin_cases i <;> [exact Or.inl hv; exact Or.inr hv],
      by rintro (hv | hv) <;> [exact ⟨P₁, ⟨0, rfl⟩, hv⟩; exact ⟨P₂, ⟨1, rfl⟩, hv⟩]⟩
  · rw [edgeSet_subgraphSUnion hle_range, edgeSet_subgraphUnion h₁ h₂]
    ext e
    simp only [mem_iUnion, mem_range, mem_union]
    exact ⟨by rintro ⟨_, ⟨i, rfl⟩, he⟩; fin_cases i <;> [exact Or.inl he; exact Or.inr he],
      by rintro (he | he) <;> [exact ⟨P₁, ⟨0, rfl⟩, he⟩; exact ⟨P₂, ⟨1, rfl⟩, he⟩]⟩

/-- A separation `(A, B)` of `G` with `V(A) ∩ V(B) ⊆ Z` forms an indexed `Z`-division over `Fin 2`. -/
theorem isIndexedZDivision_of_isGraphSeparation {G A B : Graph α β} {Z : Set α}
    (hsep : IsGraphSeparation G A B) (hAB_Z : V(A) ∩ V(B) ⊆ Z) :
    IsIndexedZDivision G Z (![A, B] : Fin 2 → Graph α β) := by
  have hle : ∀ i : Fin 2, (![A, B] i) ≤ G := by
    intro i; fin_cases i <;> [exact hsep.1; exact hsep.2.1]
  refine ⟨hle, ?_, ?_⟩
  · rw [subgraphSUnion_range_pair hsep.1 hsep.2.1, IsGraphSeparation.subgraphUnion_eq hsep]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact ⟨hsep.2.2.2.2, hAB_Z⟩
    · exact ⟨hsep.2.2.2.2.symm, inter_comm V(B) V(A) ▸ hAB_Z⟩
    · exact (hij rfl).elim

/-- **Graph Minors XXII, 2.6** (Section 2, page 534):
"Let $(A, B)$ be a separation of a graph $G$, let $Z \subseteq V(G)$ with $V(A \cap B) \subseteq Z$,
and let $L' \subseteq A$ with the same effect on $Z \cap V(A)$ as $L \cap A$. Then
$L' \cup (L \cap B) \subseteq G$ has the same effect on $Z$ as $L$." -/
theorem theorem_2_6_proof {G L A B L' : Graph α β} {Z : Set α}
    (hLG : L ≤ G) (hsep : IsGraphSeparation G A B) (hZ : Z ⊆ V(G))
    (hAB_Z : V(A) ∩ V(B) ⊆ Z) (hL'A : L' ≤ A)
    (heff : effectOn L' (Z ∩ V(A)) = effectOn (subgraphInter G L A) (Z ∩ V(A))) :
    effectOn (subgraphUnion G L' (subgraphInter G L B)) Z = effectOn L Z := by
  let A_fam : Fin 2 → Graph α β := ![A, B]
  let L'_fam : Fin 2 → Graph α β := ![L', subgraphInter G L B]
  have hdiv : IsIndexedZDivision G Z A_fam :=
    isIndexedZDivision_of_isGraphSeparation hsep hAB_Z
  have hL'_le : ∀ i : Fin 2, L'_fam i ≤ A_fam i := by
    intro i
    fin_cases i
    · exact hL'A
    · exact subgraphInter_le_right hLG hsep.2.1
  have h_a : ∀ i : Fin 2, (id : α → α) '' (Z ∩ V(A_fam i)) = Z ∩ V(A_fam i) :=
    fun i => image_id _
  have h_b : ∀ u ∈ Z, ∀ v ∈ Z, u ≠ v → (id : α → α) u = id v →
      ∃ i : Fin 2, u ∈ V(A_fam i) ∧ v ∈ V(A_fam i) :=
    fun _ _ _ _ hne heq => (hne heq).elim
  have h_c : ∀ i : Fin 2, ∀ u ∈ Z ∩ V(A_fam i), ∀ v ∈ Z ∩ V(A_fam i),
      AreConnectedIn (L'_fam i) u v ↔
        AreConnectedIn (subgraphInter G L (A_fam i)) u v := by
    intro i u hu v hv
    fin_cases i
    · exact effectOn_eq_iff_areConnectedIn.mp heff u hu v hv
    · rfl
  have ⟨_, hconn_iff⟩ :=
    theorem_2_5_proof hLG hZ hdiv hZ hdiv hL'_le h_a h_b h_c
  have hSUnion_eq :
      subgraphSUnion G (range L'_fam) = subgraphUnion G L' (subgraphInter G L B) :=
    subgraphSUnion_range_pair (hL'A.trans hsep.1) (subgraphInter_le hLG)
  rw [← hSUnion_eq, effectOn_eq_iff_areConnectedIn]
  exact hconn_iff

/-- **Graph Minors XXII, 2.7** (Section 2, page 534):
"Let $L$ be a subgraph of $G$, vital for $Z \subseteq V(G)$, and let $(A, B)$ be a separation of $G$.
Then $L \cap A$ is vital for $(Z \cap V(A)) \cup V(A \cap B)$ in $A$." -/
theorem theorem_2_7_proof {G L A B : Graph α β} {Z : Set α}
    (hZ : Z ⊆ V(G)) (hvit : IsVitalFor G L Z) (hsep : IsGraphSeparation G A B) :
    IsVitalFor A (subgraphInter G L A) ((Z ∩ V(A)) ∪ (V(A) ∩ V(B))) := by
  let Z' := Z ∪ (V(A) ∩ V(B))
  have hVL : V(L) = V(G) := hvit.vertexSet_eq
  have hAB_G : V(A) ∩ V(B) ⊆ V(G) :=
    inter_subset_left.trans hsep.1.vertexSet_mono
  have hZ'_G : Z' ⊆ V(G) := union_subset hZ hAB_G
  have hZ'_L : Z' ⊆ V(L) := hVL.symm ▸ hZ'_G
  have hvit_Z' : IsVitalFor G L Z' := hvit.mono_Z subset_union_left hZ'_L
  have hZ'_inter : Z' ∩ V(A) = (Z ∩ V(A)) ∪ (V(A) ∩ V(B)) := by
    ext v
    simp only [Z', mem_inter_iff, mem_union]
    tauto
  refine ⟨subgraphInter_le_right hvit.1 hsep.1, ?_, ?_⟩
  · rw [vertexSet_subgraphInter, ← hZ'_inter]
    exact inter_subset_inter_left V(A) hZ'_L
  · intro L' hL'A heff'
    rw [← hZ'_inter] at heff'
    have heff_union : effectOn (subgraphUnion G L' (subgraphInter G L B)) Z' = effectOn L Z' :=
      theorem_2_6_proof hvit.1 hsep hZ'_G subset_union_right hL'A heff'
    have hL'G : L' ≤ G := hL'A.trans hsep.1
    have hLBG : subgraphInter G L B ≤ G := subgraphInter_le hvit.1
    have hunion_G : subgraphUnion G L' (subgraphInter G L B) ≤ G :=
      subgraphUnion_le hL'G hLBG
    have heq_union : subgraphUnion G L' (subgraphInter G L B) = L :=
      hvit_Z'.2.2 _ hunion_G heff_union
    -- Now intersect both sides of `L' ∪ (L ∩ B) = L` with `A` using `lemma_2_5_claim_2`.
    let A_fam : Fin 2 → Graph α β := ![A, B]
    let L'_fam : Fin 2 → Graph α β := ![L', subgraphInter G L B]
    have hdiv : IsIndexedZDivision G Z' A_fam :=
      isIndexedZDivision_of_isGraphSeparation hsep subset_union_right
    have hL'_le : ∀ i : Fin 2, L'_fam i ≤ A_fam i := by
      intro i
      fin_cases i
      · exact hL'A
      · exact subgraphInter_le_right hvit.1 hsep.2.1
    have h_a : ∀ i : Fin 2, (id : α → α) '' (Z' ∩ V(A_fam i)) = Z' ∩ V(A_fam i) :=
      fun i => image_id _
    have h_c : ∀ i : Fin 2, ∀ u ∈ Z' ∩ V(A_fam i), ∀ v ∈ Z' ∩ V(A_fam i),
        AreConnectedIn (L'_fam i) u v ↔
          AreConnectedIn (subgraphInter G L (A_fam i)) u v := by
      intro i u hu v hv
      fin_cases i
      · exact effectOn_eq_iff_areConnectedIn.mp heff' u hu v hv
      · rfl
    have hclaim2 := lemma_2_5_claim_2 hvit.1 hdiv hdiv hL'_le h_a h_c 0
    have hSUnion_eq :
        subgraphSUnion G (range L'_fam) = subgraphUnion G L' (subgraphInter G L B) :=
      subgraphSUnion_range_pair hL'G hLBG
    change L' = subgraphInter G (subgraphSUnion G (range L'_fam)) A at hclaim2
    rw [hSUnion_eq, heq_union] at hclaim2
    exact hclaim2

end GraphMinor.GM22
