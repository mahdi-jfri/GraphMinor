module

public import GraphMinor.HP25.Lemma43ClaimB
public import GraphMinor.HP25.Fan
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Prop34

/-!
# Lemma 4.3, second case: the side of `y` is part of a fan

Humeau and Pous, proof of Lemma 4.3 (page 15): "$G$ is the path composition along $P$ of an edge
subgraph of a web (made of the green triangular shapes and whose rib is a fan graph) with frame
$zyxP$ with a graph $H$".

Here we build that web (`Case2.fan_side`). Its vertices are those of `G` outside the component
`𝒞_C^P`: the vertex `y`, the path `P`, and the other components of `G - P - y`. Number `P` from `z`
to `x` as `q 0, …, q n`. By Claim B each other component has its neighbours on `P` in a window
`q i, q (i+1)`; put it in the block `i` of the fan. The fan graph with these blocks
(`fanGraph`, a web with frame `y q 0 … q n = y P⁻¹` by `isWebOn_fanGraph`) contains every edge of
`G` outside `𝒞_C^P`, and `P` is induced in it.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The pair `l[k], l[k+1]` is an edge of the list `l`. -/
theorem isListEdge_getElem (l : List V) (k : ℕ) (hk : k + 1 < l.length) :
    IsListEdge l (l[k]'(by omega)) l[k + 1] :=
  ⟨(l[k], l[k + 1]), List.mem_iff_getElem.mpr ⟨k, by simp; omega, by simp⟩, rfl⟩

/-- **A window of two.** A set of indices below `N ≥ 2` whose members differ by at most one lies in
a window `{i, i + 1}` with `i + 1 < N`. -/
theorem exists_window {N : ℕ} (J : ℕ → Prop) (hN : 2 ≤ N) (hJ : ∀ j, J j → j < N)
    (hpair : ∀ j j', J j → J j' → j' ≤ j + 1) : ∃ i, i + 1 < N ∧ ∀ j, J j → j = i ∨ j = i + 1 := by
  classical
  by_cases hne : ∃ j, J j
  · have h0 := Nat.find_spec hne
    have hlt := hJ _ h0
    by_cases hk : Nat.find hne + 1 < N
    · refine ⟨Nat.find hne, hk, fun j hj => ?_⟩
      have h1 := Nat.find_min' hne hj
      have h2 := hpair _ _ h0 hj
      omega
    · refine ⟨Nat.find hne - 1, by omega, fun j hj => ?_⟩
      have h1 := Nat.find_min' hne hj
      have h2 := hJ j hj
      omega
  · exact ⟨0, by omega, fun j hj => absurd ⟨j, hj⟩ hne⟩

namespace Case2

variable {S : Set V} {x y z ℓ : V} {L P : List V}

/-- `y` is not on `P`. -/
theorem y_not_mem (hc : Case2 G S x y z ℓ L P) : y ∉ P := by
  intro hyP
  have hnd := hc.cyc.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  rcases hc.mu.1.2.2.2.2 y hyP (by simp) with h | h
  · exact hnd.1.1 h.symm
  · exact hnd.2.1.1 h

/-- The vertices of `P`, numbered from `z` to `x`. -/
noncomputable def fq (P : List V) (x : V) (i : ℕ) : V := P.getD (P.length - 1 - i) x

/-- The vertices of `G` outside `𝒞_C^P`, `P` and `y`. -/
def outer (G : SimpleGraph V) (S : Set V) (y ℓ : V) (P : List V) : Set V :=
  {v | v ∈ S ∧ ¬ (v ∈ P ∨ v = y) ∧ v ∉ compOf G S {v | v ∈ P} ℓ}

open Classical in
/-- The window of a component: an index `i` such that the component has its neighbours on `P`
among `fq i`, `fq (i+1)`. -/
noncomputable def widx (G : SimpleGraph V) (x : V) (P : List V) (Zs : Set V) : ℕ :=
  if h : ∃ i, i + 1 < P.length ∧ ∀ u ∈ Zs, ∀ j ≤ P.length - 1, G.Adj u (fq P x j) →
      j = i ∨ j = i + 1 then Classical.choose h else 0

/-- The blocks of the fan. -/
def fK (G : SimpleGraph V) (S : Set V) (x y ℓ : V) (P : List V) (i : ℕ) : Set V :=
  {v | v ∈ outer G S y ℓ P ∧ widx G x P (compOf G S {u | u ∈ P ∨ u = y} v) = i}

theorem fq_eq {i : ℕ} (hN : 2 ≤ P.length) :
    fq P x i = P[P.length - 1 - i]'(by omega) := by
  unfold fq
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

theorem window (hc : Case2 G S x y z ℓ L P) [Finite V] {v : V} (hv : v ∈ outer G S y ℓ P) :
    widx G x P (compOf G S {u | u ∈ P ∨ u = y} v) + 1 < P.length ∧
      ∀ u ∈ compOf G S {u | u ∈ P ∨ u = y} v, ∀ j ≤ P.length - 1, G.Adj u (fq P x j) →
        j = widx G x P (compOf G S {u | u ∈ P ∨ u = y} v) ∨
          j = widx G x P (compOf G S {u | u ∈ P ∨ u = y} v) + 1 := by
  have hN := hc.mu.1.two_le_length hc.cyc
  have hex : ∃ i, i + 1 < P.length ∧ ∀ u ∈ compOf G S {u | u ∈ P ∨ u = y} v,
      ∀ j ≤ P.length - 1, G.Adj u (fq P x j) → j = i ∨ j = i + 1 := by
    obtain ⟨i, hi, hJ⟩ := exists_window (N := P.length)
      (fun j => j ≤ P.length - 1 ∧ ∃ u ∈ compOf G S {u | u ∈ P ∨ u = y} v, G.Adj u (fq P x j))
      hN (fun j hj => by omega) (by
        rintro j j' ⟨hj, u, hu, hau⟩ ⟨hj', u', hu', hau'⟩
        rw [fq_eq hN] at hau
        rw [fq_eq hN] at hau'
        have := hc.claim_B ⟨hv.1, hv.2.1⟩ hv.2.2 hu' hu (by omega) (by omega) hau' hau
        omega)
    exact ⟨i, hi, fun u hu j hj hadj => hJ j ⟨hj, u, hu, hadj⟩⟩
  unfold widx
  simp only [hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem mem_block_cases {q : ℕ → V} {K : ℕ → Set V} {i : ℕ} {w : V} (h : w ∈ fanBlock y q K i) :
    w = y ∨ w = q i ∨ w = q (i + 1) ∨ w ∈ K i := by
  simp only [fanBlock, mem_union, mem_insert_iff, mem_singleton_iff] at h
  tauto

theorem mem_block_y {q : ℕ → V} {K : ℕ → Set V} {i : ℕ} : y ∈ fanBlock y q K i :=
  Or.inl (Or.inl rfl)

theorem mem_block_q {q : ℕ → V} {K : ℕ → Set V} {i : ℕ} : q i ∈ fanBlock y q K i :=
  Or.inl (Or.inr (Or.inl rfl))

theorem mem_block_q₁ {q : ℕ → V} {K : ℕ → Set V} {i : ℕ} : q (i + 1) ∈ fanBlock y q K i :=
  Or.inl (Or.inr (Or.inr rfl))

theorem mem_block_K {q : ℕ → V} {K : ℕ → Set V} {i : ℕ} {w : V} (h : w ∈ K i) :
    w ∈ fanBlock y q K i :=
  Or.inr h

/-- **The side of `y`** (page 15). The vertices of `G` outside `𝒞_C^P` carry a web with frame
`y P⁻¹` that contains every edge of `G` among them, and in which `P` is induced. -/
theorem fan_side [Finite V] (hc : Case2 G S x y z ℓ L P) :
    ∃ W₁ : SimpleGraph V, IsWebOn W₁ (S \ compOf G S {v | v ∈ P} ℓ) (y :: P.reverse) ∧
      restrict G (S \ compOf G S {v | v ∈ P} ℓ) ≤ W₁ ∧
      ∀ u ∈ P, ∀ v ∈ P, W₁.Adj u v → IsListEdge P u v := by
  have hN := hc.mu.1.two_le_length hc.cyc
  have hnd := hc.mu.1.2.1
  have hq : ∀ i, fq P x i = P[P.length - 1 - i]'(by omega) := fun i => fq_eq hN
  have hqP : ∀ i, fq P x i ∈ P := fun i => by rw [hq]; exact List.getElem_mem _
  have hPq : ∀ v ∈ P, ∃ i ≤ P.length - 1, fq P x i = v := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hv
    refine ⟨P.length - 1 - t, by omega, ?_⟩
    rw [hq]
    congr 1
    omega
  have hyP := hc.y_not_mem
  have hyK : y ∉ compOf G S {v | v ∈ P} ℓ := hc.mu.1.y_not_mem hc.max.2.1 hc.cyc hc.mem
  have hoP : ∀ {w}, w ∈ outer G S y ℓ P → w ∉ P := fun hw hwP => hw.2.1 (Or.inl hwP)
  have hfd : FanData y (fq P x) (fK G S x y ℓ P) (P.length - 1) := {
    inj := fun i hi j hj e => by
      rw [hq, hq] at e
      have := hnd.getElem_inj_iff.mp e
      omega
    ne := fun i _ e => hyP (e ▸ hqP i)
    Ky := fun i _ hy => hy.1.2.1 (Or.inr rfl)
    Kq := fun i _ j _ hqK => hoP hqK.1 (hqP j)
    KK := fun i _ j _ hij => Set.disjoint_left.mpr fun v hvi hvj => hij (hvi.2.symm.trans hvj.2) }
  -- every vertex outside `𝒞_C^P` lies in a block
  have hblock : ∀ v ∈ S \ compOf G S {v | v ∈ P} ℓ,
      ∃ i < P.length - 1, v ∈ fanBlock y (fq P x) (fK G S x y ℓ P) i := by
    intro v hv
    by_cases hvy : v = y
    · exact ⟨0, by omega, hvy ▸ mem_block_y⟩
    by_cases hvP : v ∈ P
    · obtain ⟨i, hi, rfl⟩ := hPq v hvP
      by_cases hin : i < P.length - 1
      · exact ⟨i, hin, mem_block_q⟩
      · obtain rfl : i = P.length - 1 - 1 + 1 := by omega
        exact ⟨P.length - 1 - 1, by omega, mem_block_q₁⟩
    · have hvo : v ∈ outer G S y ℓ P := ⟨hv.1, fun h' => h'.elim hvP hvy, hv.2⟩
      exact ⟨_, by have := (hc.window hvo).1; omega, mem_block_K ⟨hvo, rfl⟩⟩
  have hset : fanSet y (fq P x) (fK G S x y ℓ P) (P.length - 1) =
      S \ compOf G S {v | v ∈ P} ℓ := by
    ext v
    refine ⟨fun ⟨i, _, hv⟩ => ?_, fun hv => hblock v hv⟩
    rcases mem_block_cases hv with rfl | rfl | rfl | hv
    · exact ⟨hc.sub _ (by simp), hyK⟩
    · exact ⟨hc.P_sub _ (hqP i), fun hk => hc.K_not_mem hk (hqP i)⟩
    · exact ⟨hc.P_sub _ (hqP _), fun hk => hc.K_not_mem hk (hqP _)⟩
    · exact ⟨hv.1.1, hv.1.2.2⟩
  have hframe : fanFrame y (fq P x) (P.length - 1) = y :: P.reverse := by
    unfold fanFrame
    congr 1
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, hq]
  refine ⟨fanGraph y (fq P x) (fK G S x y ℓ P) (P.length - 1), ?_, ?_, ?_⟩
  · have := isWebOn_fanGraph (by omega) hfd
    rwa [hset, hframe] at this
  · -- the edges of `G` outside `𝒞_C^P`
    rintro u v ⟨huv, hu, hv⟩
    refine ⟨G.ne_of_adj huv, ?_⟩
    -- an edge at `y`
    have hyw : ∀ w ∈ S \ compOf G S {v | v ∈ P} ℓ, ∃ i < P.length - 1,
        y ∈ fanBlock y (fq P x) (fK G S x y ℓ P) i ∧
          w ∈ fanBlock y (fq P x) (fK G S x y ℓ P) i := fun w hw => by
      obtain ⟨i, hi, hwi⟩ := hblock w hw
      exact ⟨i, hi, mem_block_y, hwi⟩
    -- an edge from `P` to an outer vertex
    have hPo : ∀ a b, G.Adj a b → a ∈ P → b ∈ outer G S y ℓ P → ∃ i < P.length - 1,
        a ∈ fanBlock y (fq P x) (fK G S x y ℓ P) i ∧
          b ∈ fanBlock y (fq P x) (fK G S x y ℓ P) i := by
      intro a b hab ha hb
      obtain ⟨j, hj, rfl⟩ := hPq a ha
      obtain ⟨hw1, hw2⟩ := hc.window hb
      refine ⟨_, by omega, ?_, mem_block_K ⟨hb, rfl⟩⟩
      rcases hw2 b mem_compOf_self j hj hab.symm with rfl | rfl
      · exact mem_block_q
      · exact mem_block_q₁
    by_cases huy : u = y
    · subst huy; exact hyw v hv
    by_cases hvy : v = y
    · subst hvy
      obtain ⟨i, hi, h1, h2⟩ := hyw u hu
      exact ⟨i, hi, h2, h1⟩
    by_cases huP : u ∈ P
    · by_cases hvP : v ∈ P
      · -- two vertices of `P`: consecutive, as `P` is induced
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem huP
        obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hvP
        have hne : t ≠ t' := fun e => by subst e; exact G.ne_of_adj huv rfl
        have h1 : ¬ t + 2 ≤ t' := fun h' =>
          hc.mu.induced hc.ℓ_mem_S hc.ℓ_not_mem h' ht' huv
        have h2 : ¬ t' + 2 ≤ t := fun h' =>
          hc.mu.induced hc.ℓ_mem_S hc.ℓ_not_mem h' ht huv.symm
        rcases (show t' = t + 1 ∨ t = t' + 1 by omega) with rfl | rfl
        · refine ⟨P.length - 1 - (t + 1), by omega, ?_, ?_⟩
          · have e : fq P x (P.length - 1 - (t + 1) + 1) = P[t] := by rw [hq]; congr 1; omega
            exact e ▸ mem_block_q₁
          · have e : fq P x (P.length - 1 - (t + 1)) = P[t + 1] := by rw [hq]; congr 1; omega
            exact e ▸ mem_block_q
        · refine ⟨P.length - 1 - (t' + 1), by omega, ?_, ?_⟩
          · have e : fq P x (P.length - 1 - (t' + 1)) = P[t' + 1] := by rw [hq]; congr 1; omega
            exact e ▸ mem_block_q
          · have e : fq P x (P.length - 1 - (t' + 1) + 1) = P[t'] := by rw [hq]; congr 1; omega
            exact e ▸ mem_block_q₁
      · exact hPo u v huv huP ⟨hv.1, fun h' => h'.elim hvP hvy, hv.2⟩
    · have huo : u ∈ outer G S y ℓ P := ⟨hu.1, fun h' => h'.elim huP huy, hu.2⟩
      by_cases hvP : v ∈ P
      · obtain ⟨i, hi, h1, h2⟩ := hPo v u huv.symm hvP huo
        exact ⟨i, hi, h2, h1⟩
      · -- two outer vertices: the same component of `G - P - y`
        have hvo : v ∈ outer G S y ℓ P := ⟨hv.1, fun h' => h'.elim hvP hvy, hv.2⟩
        have hreach : (restrict G (S \ {u | u ∈ P ∨ u = y})).Reachable u v :=
          Adj.reachable ⟨huv, ⟨huo.1, huo.2.1⟩, ⟨hvo.1, hvo.2.1⟩⟩
        have hZ : compOf G S {u | u ∈ P ∨ u = y} v = compOf G S {u | u ∈ P ∨ u = y} u := by
          ext w
          exact ⟨fun hw => hreach.trans hw, fun hw => hreach.symm.trans hw⟩
        refine ⟨_, by have := (hc.window huo).1; omega, mem_block_K ⟨huo, rfl⟩,
          mem_block_K ⟨hvo, ?_⟩⟩
        rw [hZ]
  · -- `P` is induced in the fan
    rintro u hu v hv ⟨huv, i, hi, hui, hvi⟩
    have hPb : ∀ w ∈ P, w ∈ fanBlock y (fq P x) (fK G S x y ℓ P) i →
        w = fq P x i ∨ w = fq P x (i + 1) := fun w hw hwi => by
      rcases mem_block_cases hwi with rfl | h' | h' | h'
      · exact absurd hw hyP
      · exact Or.inl h'
      · exact Or.inr h'
      · exact absurd hw (hoP h'.1)
    have he : IsListEdge P (fq P x (i + 1)) (fq P x i) := by
      have e1 : fq P x (i + 1) = P[P.length - 1 - (i + 1)]'(by omega) := hq _
      have e2 : fq P x i = P[P.length - 1 - (i + 1) + 1]'(by omega) := by rw [hq]; congr 1; omega
      rw [e1, e2]
      exact isListEdge_getElem P _ (by omega)
    rcases hPb u hu hui with rfl | rfl <;> rcases hPb v hv hvi with rfl | rfl
    · exact absurd rfl huv
    · exact he.symm
    · exact he
    · exact absurd rfl huv

end Case2

end GraphMinor.HP25
