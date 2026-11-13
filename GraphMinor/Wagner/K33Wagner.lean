module

public import GraphMinor.Wagner.K33Model
public import GraphMinor.Wagner.K33TypeI
public import GraphMinor.Wagner.TV8Iso
public import GraphMinor.Wagner.PlanarNoK33

/-!
# An internally `4`-connected graph with no `K_5` minor and a subdivision of `K_{3,3}` contains a
subdivision of `V_8`

Let `S` be a subdivision of `K_{3,3}` in an internally `4`-connected graph `K` with no `K_5` minor.
By `K33Sub.exists_linkA` and `K33Sub.exists_linkB` there are two links whose inner vertices avoid
`S`: a link `Q_A` between the sets `X i` and `X j` around `a i` and `a j`, and a link `Q_B` between
the sets `Y k` and `Y l` around `b k` and `b l`. If either link joins inner vertices of paths that
share no end, we get a subdivision of `V_8` by `K33Sub.tv8_of_cross`. Otherwise we find a `K_5`
minor, which is impossible.

* If some path of `S` holds an end of `Q_A` and an end of `Q_B` (`hub_case`), we leave that path
  out of a `K_{3,3}` model. Its inner part together with the inner parts of both links is a
  connected set that touches four sets of the model, and `K33M.hasK5_hub` applies.
* Otherwise each inner part of `S` can go to the side whose link ends on it. If the two links share
  an inner vertex, their inner parts form a hub as above. If not, the model has an extra link on
  each side, and `K33M.hasK5_two_links` applies.
-/

@[expose] public section

namespace GraphMinor.Wagner

open Set Function SimpleGraph

variable {γ : Type*} {K : SimpleGraph γ}

theorem chain_mid {u v : γ} {mid : List γ} (h : (u :: mid ++ [v]).IsChain K.Adj) :
    mid.IsChain K.Adj :=
  (K33Sub.path_chain_right h).left_of_append

theorem exists_mem_adj_head {u v : γ} {l : List γ} (hl : l ≠ [])
    (h : (u :: l ++ [v]).IsChain K.Adj) : ∃ w ∈ l, K.Adj u w := by
  obtain ⟨w, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  exact ⟨w, List.mem_cons_self, (List.isChain_cons_cons.mp h).1⟩

theorem exists_last_adj {u v : γ} {l : List γ} (h : (u :: l ++ [v]).IsChain K.Adj) :
    ∃ w ∈ u :: l, K.Adj w v := by
  have hne : u :: l ≠ [] := List.cons_ne_nil _ _
  have e : u :: l ++ [v] = (u :: l) ++ [v] := rfl
  rw [e] at h
  exact ⟨_, List.getLast_mem hne, (List.isChain_append.mp h).2.2 _
    (by rw [List.getLast?_eq_some_getLast hne]; rfl) v rfl⟩

theorem exists_mem_adj_last {u v : γ} {l : List γ} (hl : l ≠ [])
    (h : (u :: l ++ [v]).IsChain K.Adj) : ∃ w ∈ l, K.Adj w v := by
  have h' := isChain_reverse_path h
  obtain ⟨w, hw, hadj⟩ := exists_mem_adj_head (by simpa using hl) h'
  exact ⟨w, List.mem_reverse.mp hw, hadj.symm⟩

namespace K33Sub

variable (S : K33Sub K)

theorem m_sub_X {i k : Fin 3} {x : γ} (h : x ∈ S.m i k) : x ∈ S.X i := Or.inr ⟨k, h⟩

theorem m_sub_Y {i k : Fin 3} {x : γ} (h : x ∈ S.m i k) : x ∈ S.Y k := Or.inr ⟨i, h⟩

theorem X_unique {i j k : Fin 3} {x : γ} (hx : x ∈ S.X j) (h : x ∈ S.m i k) : i = j := by
  by_contra hij
  exact disjoint_left.mp (S.X_disj i j hij) (S.m_sub_X h) hx

theorem Y_unique {i k l : Fin 3} {x : γ} (hx : x ∈ S.Y l) (h : x ∈ S.m i k) : k = l := by
  by_contra hkl
  have hd := S.transpose.X_disj k l hkl
  rw [transpose_X, transpose_X] at hd
  exact disjoint_left.mp hd (S.m_sub_Y h) hx

/-- No link whose inner vertices avoid `S` joins inner vertices of two paths with no common end. -/
def NoCross (S : K33Sub K) : Prop :=
  ∀ ⦃i j k l : Fin 3⦄ ⦃x y : γ⦄ ⦃mid : List γ⦄, i ≠ j → k ≠ l → x ∈ S.m i k → y ∈ S.m j l →
    (x :: mid ++ [y]).Nodup → (x :: mid ++ [y]).IsChain K.Adj → (∀ z ∈ mid, ¬ S.InH z) → False

/-- **A path holding ends of both links.** The path from `a i₀` to `b k₀` holds an end `s` of a link
to `X j` and an end `t` of a link to `Y l`. Then `K` has a `K_5` minor. -/
theorem hub_case (hno : S.NoCross) {i₀ k₀ j l : Fin 3} {s y t y' : γ} {midA midB : List γ}
    (hs : s ∈ S.m i₀ k₀) (ht : t ∈ S.m i₀ k₀) (hy : y ∈ S.X j) (hj : j ≠ i₀) (hy' : y' ∈ S.Y l)
    (hl : l ≠ k₀) (hndA : (s :: midA ++ [y]).Nodup) (hchA : (s :: midA ++ [y]).IsChain K.Adj)
    (hmidA : ∀ z ∈ midA, ¬ S.InH z) (hchB : (t :: midB ++ [y']).IsChain K.Adj)
    (hmidB : ∀ z ∈ midB, ¬ S.InH z) : HasK5MinorSimple K := by
  classical
  let toA : Fin 3 → Fin 3 → Prop := fun i k => ∃ z, (z = s ∨ z = y) ∧ z ∈ S.m i k
  let ex : Fin 3 → Fin 3 → Prop := fun i k => (i, k) = (i₀, k₀)
  let M := S.cutModel toA ex
  have hyA : y ∈ M.A j := by
    rcases hy with h | ⟨k, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, ⟨y, Or.inr rfl, h⟩, fun e => hj (Prod.mk.inj e).1, h⟩
  have hyB : y' ∈ M.B l := by
    rcases hy' with h | ⟨i, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨i, ?_, fun e => hl (Prod.mk.inj e).2, h⟩
      rintro ⟨z, rfl | rfl, hz⟩
      · exact hl (S.m_disj i l i₀ k₀ (fun e => hl (Prod.mk.inj e).2) z hz hs).elim
      · have hij : i = j := S.X_unique hy hz
        subst hij
        exact hno (Ne.symm hj) (Ne.symm hl) hs hz hndA hchA hmidA
  let P : Set γ := {z | z ∈ S.m i₀ k₀}
  let ZA : Set γ := {z | z ∈ s :: midA}
  let ZB : Set γ := {z | z ∈ t :: midB}
  have hmne : S.m i₀ k₀ ≠ [] := List.ne_nil_of_mem hs
  have hpcP : (K.induce P).Preconnected := pc_of_isChain (chain_mid (S.path i₀ k₀).2)
  have hpc : (K.induce ((P ∪ ZA) ∪ ZB)).Preconnected :=
    pc_union_mem (pc_union_mem hpcP (pc_of_isChain hchA.left_of_append) (x := s) hs
      List.mem_cons_self) (pc_of_isChain hchB.left_of_append) (x := t) (Or.inl ht)
      List.mem_cons_self
  have hZ : ∀ z ∈ (P ∪ ZA) ∪ ZB, z ∈ P ∨ ¬ S.InH z := by
    rintro z ((hz | hz) | hz)
    · exact Or.inl hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl hs
      · exact Or.inr (hmidA z hz)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inl ht
      · exact Or.inr (hmidB z hz)
  have dZA : ∀ i, Disjoint ((P ∪ ZA) ∪ ZB) (M.A i) := fun i =>
    disjoint_left.mpr fun z hz hzA => by
      rcases hZ z hz with h | h
      · exact disjoint_left.mp (S.disj_ex_cutA (toA := toA) (i₀ := i₀) (k₀ := k₀) i) h hzA
      · exact h (S.cutA_inH hzA)
  have dZB : ∀ k, Disjoint ((P ∪ ZA) ∪ ZB) (M.B k) := fun k =>
    disjoint_left.mpr fun z hz hzB => by
      rcases hZ z hz with h | h
      · exact disjoint_left.mp (S.disj_ex_cutB (toA := toA) (i₀ := i₀) (k₀ := k₀) k) h hzB
      · exact h (S.cutB_inH hzB)
  obtain ⟨w₁, hw₁, h₁⟩ := exists_mem_adj_head hmne (S.path i₀ k₀).2
  obtain ⟨w₃, hw₃, h₃⟩ := exists_mem_adj_last hmne (S.path i₀ k₀).2
  obtain ⟨w₂, hw₂, h₂⟩ := exists_last_adj hchA
  obtain ⟨w₄, hw₄, h₄⟩ := exists_last_adj hchB
  exact M.hasK5_hub (i₀ := i₀) (k₀ := k₀) (fun i k h => S.cutModel_touch toA ex i k h) hj hl
    ⟨s, Or.inl (Or.inl hs)⟩ hpc dZA dZB ⟨w₁, Or.inl (Or.inl hw₁), _, Or.inl rfl, h₁.symm⟩
    ⟨w₂, Or.inl (Or.inr hw₂), y, hyA, h₂⟩ ⟨w₃, Or.inl (Or.inl hw₃), _, Or.inl rfl, h₃⟩
    ⟨w₄, Or.inr hw₄, y', hyB, h₄⟩

end K33Sub

variable {N : ℕ} {K : SimpleGraph (Fin N)}

namespace K33Sub

/-- **A subdivision of `K_{3,3}` gives a subdivision of `V_8`** in an internally `4`-connected graph
with no `K_5` minor. -/
theorem tv8 (hi : IsInternally4ConnFin K) (hK5 : ¬ HasK5MinorSimple K) (S : K33Sub K) :
    Nonempty (TV8 K) := by
  classical
  by_contra hno
  have hnc : S.NoCross := fun i j k l x y mid hij hkl hx hy hnd hch hmid =>
    hno (S.tv8_of_cross hij hkl hx hy hnd hch hmid)
  obtain ⟨i, j, x, y, midA, hij, hx, hy, hndA, hchA, hmidA⟩ := S.exists_linkA hi
  obtain ⟨k, l, x', y', midB, hkl, hx', hy', hndB, hchB, hmidB⟩ := S.exists_linkB hi
  by_cases hb : ∃ i₀ k₀ s t, (s = x ∨ s = y) ∧ (t = x' ∨ t = y') ∧ s ∈ S.m i₀ k₀ ∧ t ∈ S.m i₀ k₀
  · -- Some path holds an end of each link.
    obtain ⟨i₀, k₀, s, t, hs, ht, hsm, htm⟩ := hb
    have hA : ∃ y₁ j₁ mid₁, y₁ ∈ S.X j₁ ∧ j₁ ≠ i₀ ∧ (s :: mid₁ ++ [y₁]).Nodup ∧
        (s :: mid₁ ++ [y₁]).IsChain K.Adj ∧ ∀ z ∈ mid₁, ¬ S.InH z := by
      rcases hs with rfl | rfl
      · have e : i₀ = i := S.X_unique hx hsm
        exact ⟨y, j, midA, hy, fun h => hij (e.symm.trans h.symm), hndA, hchA, hmidA⟩
      · have e : i₀ = j := S.X_unique hy hsm
        refine ⟨x, i, midA.reverse, hx, fun h => hij (h.trans e), ?_, isChain_reverse_path hchA,
          fun z hz => hmidA z (List.mem_reverse.mp hz)⟩
        have e' : s :: midA.reverse ++ [x] = (x :: midA ++ [s]).reverse := by simp
        rw [e']
        exact List.nodup_reverse.mpr hndA
    have hB : ∃ y₁ l₁ mid₁, y₁ ∈ S.Y l₁ ∧ l₁ ≠ k₀ ∧ (t :: mid₁ ++ [y₁]).IsChain K.Adj ∧
        ∀ z ∈ mid₁, ¬ S.InH z := by
      rcases ht with rfl | rfl
      · have e : k₀ = k := S.Y_unique hx' htm
        exact ⟨y', l, midB, hy', fun h => hkl (e.symm.trans h.symm), hchB, hmidB⟩
      · have e : k₀ = l := S.Y_unique hy' htm
        exact ⟨x', k, midB.reverse, hx', fun h => hkl (h.trans e), isChain_reverse_path hchB,
          fun z hz => hmidB z (List.mem_reverse.mp hz)⟩
    obtain ⟨y₁, j₁, mid₁, hy₁, hj₁, hnd₁, hch₁, hmid₁⟩ := hA
    obtain ⟨y₂, l₂, mid₂, hy₂, hl₂, hch₂, hmid₂⟩ := hB
    exact hK5 (S.hub_case hnc hsm htm hy₁ hj₁ hy₂ hl₂ hnd₁ hch₁ hmid₁ hch₂ hmid₂)
  -- Each inner part goes to the side whose link ends on it.
  let toA : Fin 3 → Fin 3 → Prop := fun i k => ∃ z, (z = x ∨ z = y) ∧ z ∈ S.m i k
  let ex : Fin 3 → Fin 3 → Prop := fun _ _ => False
  let M := S.cutModel toA ex
  have hAend : ∀ {z : Fin N} {t : Fin 3}, z ∈ S.X t → (z = x ∨ z = y) → z ∈ M.A t := by
    rintro z t (h | ⟨k₁, h⟩) hz
    · exact Or.inl h
    · exact Or.inr ⟨k₁, ⟨z, hz, h⟩, not_false, h⟩
  have hBend : ∀ {z : Fin N} {t : Fin 3}, z ∈ S.Y t → (z = x' ∨ z = y') → z ∈ M.B t := by
    rintro z t (h | ⟨i₁, h⟩) hz
    · exact Or.inl h
    · refine Or.inr ⟨i₁, ?_, not_false, h⟩
      rintro ⟨z', hz', h'⟩
      exact hb ⟨i₁, t, z', z, hz', hz, h', h⟩
  have hxA := hAend hx (Or.inl rfl)
  have hyA := hAend hy (Or.inr rfl)
  have hxB := hBend hx' (Or.inl rfl)
  have hyB := hBend hy' (Or.inr rfl)
  have ht : ∀ i k, Touch K (M.A i) (M.B k) := fun i k => S.cutModel_touch toA ex i k not_false
  by_cases hint : ∃ z, z ∈ midA ∧ z ∈ midB
  · -- The two links meet, and their inner parts form a hub.
    obtain ⟨z, hzA, hzB⟩ := hint
    have hZ : ∀ z ∈ {z | z ∈ midA} ∪ {z | z ∈ midB}, ¬ S.InH z := by
      rintro z (h | h)
      · exact hmidA z h
      · exact hmidB z h
    obtain ⟨w₁, hw₁, h₁⟩ := exists_mem_adj_head (List.ne_nil_of_mem hzA) hchA
    obtain ⟨w₂, hw₂, h₂⟩ := exists_mem_adj_last (List.ne_nil_of_mem hzA) hchA
    obtain ⟨w₃, hw₃, h₃⟩ := exists_mem_adj_head (List.ne_nil_of_mem hzB) hchB
    obtain ⟨w₄, hw₄, h₄⟩ := exists_mem_adj_last (List.ne_nil_of_mem hzB) hchB
    exact hK5 (M.hasK5_hub (i₀ := i) (k₀ := k) (fun i k _ => ht i k) (Ne.symm hij) (Ne.symm hkl)
      ⟨z, Or.inl hzA⟩ (pc_union_mem (pc_of_isChain (chain_mid hchA))
        (pc_of_isChain (chain_mid hchB)) (x := z) hzA hzB) (S.disj_cutA hZ toA ex)
      (S.disj_cutB hZ toA ex) ⟨w₁, Or.inl hw₁, x, hxA, h₁.symm⟩ ⟨w₂, Or.inl hw₂, y, hyA, h₂⟩
      ⟨w₃, Or.inr hw₃, x', hxB, h₃.symm⟩ ⟨w₄, Or.inr hw₄, y', hyB, h₄⟩)
  · -- The two links are disjoint, and they are extra links on the two sides.
    have hpc : ∀ {X : Set (Fin N)} {u v : Fin N} {mid : List (Fin N)}, (K.induce X).Preconnected →
        u ∈ X → (u :: mid ++ [v]).IsChain K.Adj →
        (K.induce (X ∪ {z | z ∈ mid})).Preconnected := by
      intro X u v mid hX hu hch
      refine pc_congr ?_ (pc_union_mem hX (pc_of_isChain hch.left_of_append) (x := u) hu
        List.mem_cons_self)
      ext z
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hu
          · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    have htouch : ∀ {X Y : Set (Fin N)} {u v : Fin N} {mid : List (Fin N)}, u ∈ X → v ∈ Y →
        (u :: mid ++ [v]).IsChain K.Adj → Touch K (X ∪ {z | z ∈ mid}) Y := by
      intro X Y u v mid hu hv hch
      obtain ⟨w, hw, h⟩ := exists_last_adj hch
      refine ⟨w, ?_, v, hv, h⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inl hu
      · exact Or.inr hw
    exact hK5 (M.hasK5_two_links ht hij hkl (hpc (M.pcA i) hxA hchA) (hpc (M.pcB k) hxB hchB)
      (htouch hxA hyA hchA) (htouch hxB hyB hchB) (S.disj_cutA (Z := {z | z ∈ midA}) hmidA toA ex)
      (S.disj_cutB (Z := {z | z ∈ midA}) hmidA toA ex)
      (S.disj_cutA (Z := {z | z ∈ midB}) hmidB toA ex)
      (S.disj_cutB (Z := {z | z ∈ midB}) hmidB toA ex)
      (disjoint_left.mpr fun z hzA hzB => hint ⟨z, hzA, hzB⟩))

end K33Sub

/-- **Wagner's theorem for internally `4`-connected graphs.** An internally `4`-connected simple
graph with no `K_5` minor is planar or isomorphic to `V_8`. -/
theorem planar_or_v8_of_internally4Conn (hi : IsInternally4ConnFin K)
    (hK5 : ¬ HasK5MinorSimple K) :
    Nonempty (HP25.PlaneEmbedding K Set.univ) ∨
      Nonempty (Iso (Graph.ofSimpleGraph K) GM16.wagnerGraphV8) := by
  by_cases h33 : HasK33Subdiv K
  · obtain ⟨S⟩ := K33Sub.nonempty_of_hasK33Subdiv h33
    obtain ⟨T⟩ := S.tv8 hi hK5
    exact Or.inr (T.iso hi.2.1 hK5)
  · exact Or.inl (planar_of_noK33 hi hK5 h33)

end GraphMinor.Wagner
