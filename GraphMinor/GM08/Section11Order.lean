module

public import GraphMinor.GM08.Section11Disc
import GraphMinor.GM11.NiceStatements
import GraphMinor.Surface.Crossing

/-!
# A sleeve drawn in the disc, and the order of its radial paths

`SleeveDraw` is a sleeve given by sequences (`SleeveSeq`) together with its drawing: the
circuits `C_j` as subdrawings bounding nested closed discs `Δ_j`, and the paths `P_i ∩ C_j`.
We prove that two radial paths consecutive on `C_j` are consecutive on `C_{j + 1}`
(`SleeveDraw.adj_step`), by the crossing argument described in
`GraphMinor/GM08/Section11Disc.lean`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Graph Surface GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- A sleeve given by sequences, with its drawing. The circuit `C j` bounds the closed disc
`Δ j`, the discs are nested, every radial path starts on `C_1`, and `Q i j` is the path
`P_i ∩ C_j`. -/
structure SleeveDraw (D₀ : Drawing S) (W : Set S) (r s : ℕ) extends
    SleeveSeq (D₀.toGraph.induce W) r s where
  W_sub : W ⊆ D₀.V
  ε_mod : ∀ j x, ε j (x % n j) = ε j x
  ε_inj : ∀ j x y, x < n j → y < n j → ε j x = ε j y → x = y
  /-- The circuit `C_j` as a subdrawing. -/
  C : Fin s → Drawing S
  C_sub : ∀ j, (C j).IsSubdrawing D₀
  C_V : ∀ j u, u ∈ (C j).V ↔ ∃ x, c j x = u
  C_E : ∀ j e, e ∈ (C j).E ↔ ∃ x, ε j x = e
  /-- The closed disc bounded by `C_j`. -/
  Δ : Fin s → Set S
  Δ_disc : ∀ j, IsClosedDisc (Δ j)
  Δ_bd : ∀ j, discBd (Δ j) = (C j).U
  Δ_lt : ∀ j j', j < j' → Δ j ⊆ discInt (Δ j')
  d_start : ∀ i j, j.1 = 0 → ∃ x, d i 0 = c j x
  /-- The path `P_i ∩ C_j`. -/
  Q : Fin r → Fin s → Drawing S
  Q_sub : ∀ i j, (Q i j).IsSubdrawing D₀
  Q_V : ∀ i j u, u ∈ (Q i j).V ↔ (∃ k ≤ len i, d i k = u) ∧ ∃ x, c j x = u
  Q_E : ∀ i j, (Q i j).E ⊆ (C j).E
  Q_path : ∀ i j, ∃ a b, (Q i j).IsPathBetween a b

namespace SleeveDraw

variable {D₀ : Drawing S} {W : Set S} {r s : ℕ} (L : SleeveDraw D₀ W r s)

/-- The stretch `c j p, …, c j (p + ℓ)` of the circuit `C_j`, as a walk of `D₀`. -/
@[expose] def cw (j : Fin s) (p ℓ : ℕ) : GraphWalk D₀.toGraph (L.c j p) (L.c j (p + ℓ)) :=
  seqWalk (L.c j) (L.ε j) p (L.c_link j p).1.left_mem ℓ fun k _ => (L.c_link j (p + k)).1

/-- The start `d i 0, …, d i ℓ` of the radial path `P_i`, as a walk of `D₀`. -/
@[expose] def dw (i : Fin r) (ℓ : ℕ) (hℓ : ℓ ≤ L.len i) :
    GraphWalk D₀.toGraph (L.d i 0) (L.d i (0 + ℓ)) :=
  seqWalk (L.d i) (L.δ i) 0
    (show L.d i 0 ∈ V(D₀.toGraph) from L.W_sub (L.d_mem i 0 (Nat.zero_le _))) ℓ
    fun k hk => (L.d_link i (0 + k) (by omega)).1

variable {L}
variable [T2Space S]

theorem mem_cw_V {j : Fin s} {p ℓ : ℕ} {u : S} :
    u ∈ (walkDrawing D₀ (L.cw j p ℓ)).V ↔ ∃ k ≤ ℓ, L.c j (p + k) = u := by
  rw [walkDrawing_V]
  exact mem_seqWalk_support

theorem mem_dw_V {i : Fin r} {ℓ : ℕ} {hℓ : ℓ ≤ L.len i} {u : S} :
    u ∈ (walkDrawing D₀ (L.dw i ℓ hℓ)).V ↔ ∃ k ≤ ℓ, L.d i k = u := by
  rw [walkDrawing_V]
  exact mem_seqWalk_support.trans (by simp only [Nat.zero_add])

theorem cw_U_subset (j : Fin s) (p ℓ : ℕ) : (walkDrawing D₀ (L.cw j p ℓ)).U ⊆ (L.C j).U :=
  walkDrawing_U_subset _ (fun x hx => (L.C_V j x).mpr (by
      obtain ⟨k, -, hk⟩ := mem_seqWalk_support.mp hx
      exact ⟨_, hk⟩))
    (fun e he => (L.C_E j e).mpr (by
      obtain ⟨k, -, hk⟩ := mem_seqWalk_edges.mp he
      exact ⟨_, hk⟩))

omit [T2Space S] in
theorem eps_eq_window {j : Fin s} {x₀ a b : ℕ} (ha : a < L.n j) (hb : b < L.n j)
    (h : L.ε j (x₀ + a) = L.ε j (x₀ + b)) : a = b := by
  have hn := L.n_pos j
  have h1 : (x₀ + a) % L.n j = (x₀ + b) % L.n j :=
    L.ε_inj j _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by rw [L.ε_mod, L.ε_mod, h])
  have h2 : a ≡ b [MOD L.n j] := Nat.ModEq.add_left_cancel' x₀ h1
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

omit [T2Space S] in
/-- Every position of `C_j` has the same vertex and edge as one in a given window. -/
theorem exists_offset' (j : Fin s) (x₀ x : ℕ) :
    ∃ y, y < L.n j ∧ L.c j (x₀ + y) = L.c j x ∧ L.ε j (x₀ + y) = L.ε j x := by
  obtain ⟨y, hy, hyx⟩ := L.toSleeveSeq.exists_offset j x₀ x
  refine ⟨y, hy, hyx, ?_⟩
  rw [← L.ε_mod j (x₀ + y), ← L.ε_mod j x, L.mod_eq_of_c_eq hyx]

/-- A vertex of `P_i` and its start lie in the disc bounded by a later circuit `C_{j'}` up to the
first vertex of `P_i` on `C_{j'}`. -/
theorem dw_U_subset_disc (hS : IsClosedDisc (univ : Set S)) (i : Fin r) {j' : Fin s}
    (hj' : 0 < j'.1) : (walkDrawing D₀ (L.dw i (L.hit i j') (L.hit_le i j'))).U ⊆ L.Δ j' := by
  have hs : 0 < s := Nat.zero_lt_of_lt j'.2
  have h0 : L.d i 0 ∈ L.Δ j' := by
    obtain ⟨x, hx⟩ := L.d_start i ⟨0, hs⟩ rfl
    have hU : L.d i 0 ∈ discBd (L.Δ ⟨0, hs⟩) := by
      rw [L.Δ_bd]
      exact (L.C _).V_subset_U ((L.C_V _ _).mpr ⟨x, hx.symm⟩)
    exact discInt_subset _ (L.Δ_lt ⟨0, hs⟩ j' (Fin.lt_def.mpr hj') (Surface.discBd_subset _ hU))
  have key := seq_mem_disc hS (L.C_sub j') (L.Δ_disc j') (L.Δ_bd j') (L.d i) (L.δ i) (L.hit i j')
    (fun k hk => (L.d_link i k (by have := L.hit_le i j'; omega)).1) h0
    (fun k hk hC => by
      obtain ⟨x, hx⟩ := (L.C_V j' _).mp hC
      exact L.hit_min i j' k hk x hx)
  intro x hx
  rcases (mem_walkDrawing_U D₀ _).mp hx with hx | ⟨e, he, hxe⟩
  · obtain ⟨k, hk, rfl⟩ := mem_seqWalk_support.mp hx
    simpa using (key k (by omega)).1
  · obtain ⟨k, hk, rfl⟩ := mem_seqWalk_edges.mp he
    simp only [Nat.zero_add] at hxe ⊢
    exact (key k hk.le).2 hk hxe

omit [T2Space S] in
theorem adj_comm {j : Fin s} {a b : Fin r} : L.Adj j a b ↔ L.Adj j b a :=
  exists_congr fun _ => Or.comm

omit [T2Space S] in
/-- `P_i ∩ C_j` is a subdrawing of `C_j`. -/
theorem Q_isSubdrawing_C (i : Fin r) (j : Fin s) : (L.Q i j).IsSubdrawing (L.C j) :=
  ⟨fun u hu => (L.C_V j u).mpr ((L.Q_V i j u).mp hu).2, L.Q_E i j⟩

omit [T2Space S] in
theorem c_ne_window {j : Fin s} {p a b : ℕ} (ha : a < L.n j) (hb : b < L.n j) (hab : a ≠ b) :
    L.c j (p + a) ≠ L.c j (p + b) :=
  fun h => hab (L.eq_of_c_eq_window ha hb h)

/-- **Four positions in cyclic order on `C_j` cross on the boundary of `Δ_j`.** Going around
`C_j` from `c j p`, we meet `c j (p + t)`, then `c j (p + y)`, then `c j (p + u)`. -/
theorem pairsCrossOn_circuit (j : Fin s) (p : ℕ) {t y u : ℕ} (ht : 0 < t) (hty : t < y)
    (hyu : y < u) (hu : u < L.n j) :
    PairsCrossOn (discBd (L.Δ j)) (L.c j p) (L.c j (p + y)) (L.c j (p + t)) (L.c j (p + u)) := by
  have hn := L.n_pos j
  have hp0 : L.c j p = L.c j (p + 0) := rfl
  have hpn : L.c j (p + y + (L.n j - y)) = L.c j (p + 0) := by
    rw [show p + y + (L.n j - y) = p + L.n j by omega, L.c_add]
    rfl
  set W₁ := L.cw j p y
  set W₂ := L.cw j (p + y) (L.n j - y)
  have hcov : discBd (L.Δ j) = (walkDrawing D₀ W₁).U ∪ (walkDrawing D₀ W₂).U := by
    rw [L.Δ_bd]
    refine subset_antisymm ?_ (union_subset (L.cw_U_subset _ _ _) (L.cw_U_subset _ _ _))
    intro z hz
    rw [(L.C j).U_eq] at hz
    rcases hz with hz | hz
    · obtain ⟨x, rfl⟩ := (L.C_V j z).mp hz
      obtain ⟨o, ho, hox, -⟩ := L.exists_offset' j p x
      rw [← hox]
      by_cases hoy : o ≤ y
      · exact Or.inl ((walkDrawing D₀ W₁).V_subset_U (mem_cw_V.mpr ⟨o, hoy, rfl⟩))
      · exact Or.inr ((walkDrawing D₀ W₂).V_subset_U (mem_cw_V.mpr ⟨o - y, by omega, by
          rw [show p + y + (o - y) = p + o by omega]⟩))
    · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hz
      obtain ⟨x, rfl⟩ := (L.C_E j e).mp he
      obtain ⟨o, ho, -, hox⟩ := L.exists_offset' j p x
      rw [← hox] at hze
      by_cases hoy : o < y
      · exact Or.inl ((mem_walkDrawing_U D₀ W₁).mpr
          (Or.inr ⟨_, mem_seqWalk_edges.mpr ⟨o, hoy, rfl⟩, hze⟩))
      · exact Or.inr ((mem_walkDrawing_U D₀ W₂).mpr (Or.inr ⟨_, mem_seqWalk_edges.mpr
          ⟨o - y, by omega, by rw [show p + y + (o - y) = p + o by omega]⟩, hze⟩))
  have hE : Disjoint (walkDrawing D₀ W₁).E (walkDrawing D₀ W₂).E := by
    rw [walkDrawing_E, walkDrawing_E]
    refine Set.disjoint_left.mpr fun e he he' => ?_
    obtain ⟨k, hk, rfl⟩ := mem_seqWalk_edges.mp he
    obtain ⟨k', hk', hkk⟩ := mem_seqWalk_edges.mp he'
    rw [add_assoc] at hkk
    have := L.eps_eq_window (show y + k' < L.n j by omega) (show k < L.n j by omega) hkk
    omega
  have hint : (walkDrawing D₀ W₁).U ∩ (walkDrawing D₀ W₂).U ⊆
      {L.c j p, L.c j (p + y)} := by
    intro z hz
    obtain ⟨h1, h2⟩ := inter_U_subset_V (walkDrawing_isSubdrawing D₀ W₁)
      (walkDrawing_isSubdrawing D₀ W₂) hE hz
    obtain ⟨k, hk, rfl⟩ := mem_cw_V.mp h1
    obtain ⟨k', hk', hkk⟩ := mem_cw_V.mp h2
    by_cases hk'n : k' = L.n j - y
    · subst hk'n
      rw [hpn] at hkk
      have := L.eq_of_c_eq_window (show 0 < L.n j from hn) (show k < L.n j by omega) hkk
      subst this
      exact Or.inl rfl
    · rw [add_assoc] at hkk
      have := L.eq_of_c_eq_window (show y + k' < L.n j by omega) (show k < L.n j by omega) hkk
      have hk0 : k' = 0 := by omega
      subst hk0
      have : k = y := by omega
      subst this
      exact Or.inr rfl
  have hmem₁ : ∀ o ≤ y, L.c j (p + o) ∈ (walkDrawing D₀ W₁).U := fun o ho =>
    (walkDrawing D₀ W₁).V_subset_U (mem_cw_V.mpr ⟨o, ho, rfl⟩)
  have hmem₂ : ∀ o, y ≤ o → o ≤ L.n j → L.c j (p + o) ∈ (walkDrawing D₀ W₂).U := fun o h1 h2 =>
    (walkDrawing D₀ W₂).V_subset_U (mem_cw_V.mpr ⟨o - y, by omega, by
      rw [show p + y + (o - y) = p + o by omega]⟩)
  have hnot : ∀ o, 0 < o → o < L.n j → o ≠ y → L.c j (p + o) ∉ ({L.c j p, L.c j (p + y)} : Set S) := by
    rintro o h0 hon hoy (h | h)
    · exact L.c_ne_window hon hn (by omega) (h.trans hp0)
    · exact L.c_ne_window hon (by omega : y < L.n j) hoy h
  exact pairsCrossOn_of_closed_cover hcov (walkDrawing D₀ W₁).isClosed_U
    (walkDrawing D₀ W₂).isClosed_U hint (hcov ▸ Or.inl (hmem₁ 0 (Nat.zero_le _)))
    (hcov ▸ Or.inl (hmem₁ y le_rfl))
    (fun h => L.c_ne_window hn (by omega : y < L.n j) (by omega) (hp0.symm.trans h))
    (L.c_ne_window (by omega) hu (by omega)) (hmem₁ t hty.le) (hnot t ht (by omega) (by omega))
    (hmem₂ u hyu.le hu.le) (hnot u (by omega) hu (by omega))

/-! ## The two sides of `C_j` -/

omit [T2Space S] in
/-- If the owner of `C_j` changes from `P_a` at `x` to `P_b` at `x + 1`, then `c j (x + 1)` is on
`P_b`, some `c j (x + 1 + g)` with `0 < g < n j` is on `P_a`, and no position strictly between
`x + 1 + g` and `x + 1 + n j` is on a radial path. -/
theorem exists_gap {j : Fin s} {x : ℕ} {a b : Fin r} (hab : a ≠ b)
    (ha : L.owner j x = some a) (hb : L.owner j (x + 1) = some b) :
    ∃ g, 0 < g ∧ g < L.n j ∧ L.OnSpoke b (L.c j (x + 1)) ∧ L.OnSpoke a (L.c j (x + 1 + g)) ∧
      ∀ o, g < o → o < L.n j → L.c j (x + 1 + o) ∉ L.marked := by
  have hr : 0 < r := a.pos
  have hn := L.n_pos j
  have hK := SleeveSeq.exists_marked hr (L := L.toSleeveSeq) j
  obtain ⟨hlt, -, hmin⟩ := backIdx_spec hn (L.c_mod j) hK x
  have hbsp : L.OnSpoke b (L.c j (x + 1)) :=
    SleeveSeq.onSpoke_of_owner_ne hr (by rw [ha, hb]; exact fun h => hab (Option.some.inj h)) hb
  have hasp : L.OnSpoke a (L.c j (x + L.n j - backIdx (L.n j) (L.c j) L.marked x)) := by
    apply SleeveSeq.onSpoke_of_lab
    rw [← ha]
    rfl
  have hg : backIdx (L.n j) (L.c j) L.marked x + 1 < L.n j := by
    by_contra h
    rw [show x + L.n j - backIdx (L.n j) (L.c j) L.marked x = x + 1 by omega] at hasp
    exact hab (hasp.eq hbsp)
  refine ⟨L.n j - backIdx (L.n j) (L.c j) L.marked x - 1, by omega, by omega, hbsp, ?_,
    fun o h1 h2 => ?_⟩
  · rwa [show x + 1 + (L.n j - backIdx (L.n j) (L.c j) L.marked x - 1) =
      x + L.n j - backIdx (L.n j) (L.c j) L.marked x by omega]
  · have := hmin (L.n j - 1 - o) (by omega)
    rwa [show x + L.n j - (L.n j - 1 - o) = x + 1 + o by omega] at this

omit [T2Space S] in
/-- In the situation of `exists_gap`, every other radial path meets `C_j` strictly between
`c j q` and `c j (q + g)`. -/
theorem exists_pos_between {j : Fin s} {q g : ℕ} {a b e : Fin r}
    (hb : L.OnSpoke b (L.c j q)) (ha : L.OnSpoke a (L.c j (q + g)))
    (hm : ∀ o, g < o → o < L.n j → L.c j (q + o) ∉ L.marked) (hea : e ≠ a) (heb : e ≠ b) :
    ∃ o, 0 < o ∧ o < g ∧ L.OnSpoke e (L.c j (q + o)) := by
  obtain ⟨x, hx⟩ := L.hit_mem e j
  obtain ⟨o, ho, hox, -⟩ := L.exists_offset' j q x
  have he : L.OnSpoke e (L.c j (q + o)) := ⟨_, L.hit_le e j, (hox.trans hx).symm⟩
  refine ⟨o, Nat.pos_of_ne_zero fun h => heb (he.eq (by rw [h]; exact hb)), ?_, he⟩
  by_contra h
  rcases eq_or_lt_of_le (not_lt.mp h) with h | h
  · subst h
    exact hea (he.eq ha)
  · exact hm o h ho ⟨e, he⟩

omit [T2Space S] in
/-- If `P_i` misses the positions `q + o₁` and `q + o₂` of `C_j` but meets a position outside
them, it misses every position strictly between them, because `P_i ∩ C_j` is an interval. -/
theorem not_onSpoke_between {j : Fin s} {i : Fin r} {q o₁ o₂ w : ℕ} (ho₂ : o₂ < L.n j)
    (h₁ : ¬ L.OnSpoke i (L.c j (q + o₁))) (h₂ : ¬ L.OnSpoke i (L.c j (q + o₂)))
    (hw : w < L.n j) (hwo : w < o₁ ∨ o₂ < w) (hi : L.OnSpoke i (L.c j (q + w)))
    {o : ℕ} (h1 : o₁ < o) (h2 : o < o₂) : ¬ L.OnSpoke i (L.c j (q + o)) := by
  rintro ⟨k, hk, hko⟩
  obtain ⟨k', hk', hkw⟩ := hi
  obtain ⟨x'', hz, hy, hx''⟩ := L.arc i j (q + o₁) (q + o₂) (by omega)
    (fun k hk h => h₁ ⟨k, hk, h⟩) (fun k hk h => h₂ ⟨k, hk, h⟩) (q + o) (by omega) (by omega)
    ⟨k, hk, hko⟩ (q + w) k' hk' hkw
  have := L.eq_of_c_eq_window (show x'' - q < L.n j by omega) hw
    (by rw [show q + (x'' - q) = x'' by omega]; exact hx'')
  omega

/-- The stretch of `C_j` between two radial paths `P_e, P_{e'}` met strictly between `c j q`
(on `P_b`) and `c j (q + g)` (on `P_a`) misses `P_a` and `P_b`. -/
theorem exists_arc [ConnectedSpace S] {j : Fin s} {q g : ℕ} {a b e e' : Fin r} (hg : g < L.n j)
    (hb : L.OnSpoke b (L.c j q)) (ha : L.OnSpoke a (L.c j (q + g)))
    (hea : e ≠ a) (heb : e ≠ b) (he'a : e' ≠ a) (he'b : e' ≠ b) {o₁ o₂ : ℕ}
    (h₁ : 0 < o₁) (h₁' : o₁ < g) (h₂ : 0 < o₂) (h₂' : o₂ < g)
    (he : L.OnSpoke e (L.c j (q + o₁))) (he' : L.OnSpoke e' (L.c j (q + o₂))) :
    ∃ D : Drawing S, D.IsSubdrawing D₀ ∧ IsPathConnected D.U ∧ D.U ⊆ (L.C j).U ∧
      L.c j (q + o₁) ∈ D.U ∧ L.c j (q + o₂) ∈ D.U ∧
      ∀ u ∈ D.V, ∃ o, 0 < o ∧ o < g ∧ ¬ L.OnSpoke a (L.c j (q + o)) ∧
        ¬ L.OnSpoke b (L.c j (q + o)) ∧ L.c j (q + o) = u := by
  wlog h : o₁ ≤ o₂ generalizing o₁ o₂ e e'
  · obtain ⟨D, h1, h2, h3, h4, h5, h6⟩ := this he'a he'b hea heb h₂ h₂' h₁ h₁' he' he (by omega)
    exact ⟨D, h1, h2, h3, h5, h4, h6⟩
  refine ⟨walkDrawing D₀ (L.cw j (q + o₁) (o₂ - o₁)), walkDrawing_isSubdrawing _ _,
    isPathConnected_walkDrawing _ _, L.cw_U_subset _ _ _,
    (walkDrawing D₀ _).V_subset_U (mem_cw_V.mpr ⟨0, Nat.zero_le _, rfl⟩),
    (walkDrawing D₀ _).V_subset_U (mem_cw_V.mpr ⟨o₂ - o₁, le_rfl, by
      rw [show q + o₁ + (o₂ - o₁) = q + o₂ by omega]⟩), fun u hu => ?_⟩
  obtain ⟨k, hk, rfl⟩ := mem_cw_V.mp hu
  have hna₁ : ¬ L.OnSpoke a (L.c j (q + o₁)) := fun h => hea (he.eq h)
  have hnb₁ : ¬ L.OnSpoke b (L.c j (q + o₁)) := fun h => heb (he.eq h)
  have hna₂ : ¬ L.OnSpoke a (L.c j (q + o₂)) := fun h => he'a (he'.eq h)
  have hnb₂ : ¬ L.OnSpoke b (L.c j (q + o₂)) := fun h => he'b (he'.eq h)
  refine ⟨o₁ + k, by omega, by omega, ?_, ?_, by rw [add_assoc]⟩
  all_goals
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · assumption
    rcases eq_or_lt_of_le hk with rfl | hk1
    · rwa [show o₁ + (o₂ - o₁) = o₂ by omega]
  · exact L.not_onSpoke_between (by omega) hna₁ hna₂ hg (Or.inr h₂') ha (by omega) (by omega)
  · exact L.not_onSpoke_between (w := 0) (by omega) hnb₁ hnb₂ (L.n_pos j) (Or.inl h₁) hb
      (by omega) (by omega)

/-! ## Two consecutive radial paths stay consecutive -/

omit [T2Space S] in
/-- Two subdrawings of `D₀` whose vertices satisfy incompatible properties have disjoint point
sets. -/
theorem disjoint_U_of_pred {D₁ D₂ : Drawing S} (h₁ : D₁.IsSubdrawing D₀)
    (h₂ : D₂.IsSubdrawing D₀) {P₁ P₂ : S → Prop} (hP : ∀ u, P₁ u → P₂ u → False)
    (hV₁ : ∀ u ∈ D₁.V, P₁ u) (hV₂ : ∀ u ∈ D₂.V, P₂ u) : Disjoint D₁.U D₂.U :=
  GM08.disjoint_U_of_disjoint_V h₁ h₂
    (Set.disjoint_left.mpr fun u hu hu' => hP u (hV₁ u hu) (hV₂ u hu'))

/-- A vertex of `P_i` on an earlier circuit lies on the start of `P_i` before `C_{j'}`. -/
theorem mem_dw_U_of_onSpoke {i : Fin r} {j j' : Fin s} (hjj' : j < j') {y : ℕ}
    (h : L.OnSpoke i (L.c j y)) :
    L.c j y ∈ (walkDrawing D₀ (L.dw i (L.hit i j') (L.hit_le i j'))).U := by
  obtain ⟨k, hk, hky⟩ := h
  exact (walkDrawing D₀ _).V_subset_U (mem_dw_V.mpr ⟨k, (L.level i j j' k y hk hky hjj').le, hky⟩)

theorem hit_mem_dw_U (i : Fin r) (j' : Fin s) :
    L.d i (L.hit i j') ∈ (walkDrawing D₀ (L.dw i (L.hit i j') (L.hit_le i j'))).U :=
  (walkDrawing D₀ _).V_subset_U (mem_dw_V.mpr ⟨_, le_rfl, rfl⟩)

omit [T2Space S] in
theorem hit_mem_Q_U (i : Fin r) (j' : Fin s) : L.d i (L.hit i j') ∈ (L.Q i j').U :=
  (L.Q i j').V_subset_U ((L.Q_V i j' _).mpr ⟨⟨_, L.hit_le i j', rfl⟩, L.hit_mem i j'⟩)

/-- The oriented case of `adj_step`. -/
theorem adj_step_aux (hS : IsClosedDisc (univ : Set S)) {j : Fin s} (hj : j.1 + 1 < s) {x : ℕ}
    {a b : Fin r} (hab : a ≠ b) (ha : L.owner j x = some a) (hb : L.owner j (x + 1) = some b) :
    L.Adj ⟨j.1 + 1, hj⟩ a b := by
  classical
  have : ConnectedSpace S := connectedSpace_iff_univ.mpr hS.isPathConnected.isConnected
  have hr : 0 < r := a.pos
  set j' : Fin s := ⟨j.1 + 1, hj⟩ with hj'def
  have hjj' : j < j' := Fin.lt_def.mpr (Nat.lt_succ_self _)
  have hj'0 : 0 < j'.1 := Nat.succ_pos _
  by_contra hnot
  -- An owner change on `C_{j'}` happens at a vertex of the new owner.
  have hchange : ∀ y {i i' : Fin r}, i ≠ i' → L.owner j' y = some i → L.owner j' (y + 1) = some i' →
      L.OnSpoke i' (L.c j' (y + 1)) := fun y i i' hii' h1 h2 =>
    SleeveSeq.onSpoke_of_owner_ne hr (by rw [h1, h2]; exact fun h => hii' (Option.some.inj h)) h2
  -- Going around `C_{j'}` from `P_a` to `P_b` and back meets `P_e` and `P_{e'}`.
  obtain ⟨pa, hpa⟩ := L.hit_mem a j'
  obtain ⟨xb, hxb⟩ := L.hit_mem b j'
  obtain ⟨yb, hyb, hyxb, -⟩ := L.exists_offset' j' pa xb
  have hn' := L.n_pos j'
  have hoa : L.owner j' pa = some a :=
    SleeveSeq.owner_of_onSpoke hr ⟨_, L.hit_le a j', hpa.symm⟩
  have hob : L.owner j' (pa + yb) = some b :=
    SleeveSeq.owner_of_onSpoke hr ⟨_, L.hit_le b j', (hyxb.trans hxb).symm⟩
  have hex₁ : ∃ t, L.owner j' (pa + t) ≠ some a :=
    ⟨yb, by rw [hob]; exact fun h => hab (Option.some.inj h).symm⟩
  have ht₁ : L.owner j' (pa + Nat.find hex₁) ≠ some a := Nat.find_spec hex₁
  have ht₁0 : 0 < Nat.find hex₁ := Nat.pos_of_ne_zero fun h => ht₁ (by rw [h]; exact hoa)
  have ht₁' : L.owner j' (pa + (Nat.find hex₁ - 1)) = some a :=
    not_not.mp (Nat.find_min hex₁ (by omega))
  obtain ⟨e, he⟩ := SleeveSeq.owner_isSome hr (L := L.toSleeveSeq) j' (pa + Nat.find hex₁)
  have hea : e ≠ a := fun h => ht₁ (h ▸ he)
  have hsucc₁ : pa + (Nat.find hex₁ - 1) + 1 = pa + Nat.find hex₁ := by omega
  have heb : e ≠ b := by
    rintro rfl
    exact hnot ⟨pa + (Nat.find hex₁ - 1), Or.inl ⟨ht₁', by rw [hsucc₁]; exact he⟩⟩
  have ht₁yb : Nat.find hex₁ < yb := by
    have h := Nat.find_min' hex₁ (show L.owner j' (pa + yb) ≠ some a by
      rw [hob]; exact fun h => hab (Option.some.inj h).symm)
    rcases eq_or_lt_of_le h with h | h
    · rw [h, hob] at he
      exact absurd (Option.some.inj he) heb.symm
    · exact h
  have hsp₁ : L.OnSpoke e (L.c j' (pa + Nat.find hex₁)) := by
    have := hchange _ hea.symm ht₁' (by rw [hsucc₁]; exact he)
    rwa [hsucc₁] at this
  have hoa' : L.owner j' (pa + yb + (L.n j' - yb)) = some a := by
    rw [show pa + yb + (L.n j' - yb) = pa + L.n j' by omega,
      SleeveSeq.owner_eq_of_c_eq hr (L.c_add j' pa), hoa]
  have hex₂ : ∃ t, L.owner j' (pa + yb + t) ≠ some b :=
    ⟨L.n j' - yb, by rw [hoa']; exact fun h => hab (Option.some.inj h)⟩
  have ht₂ : L.owner j' (pa + yb + Nat.find hex₂) ≠ some b := Nat.find_spec hex₂
  have ht₂0 : 0 < Nat.find hex₂ := Nat.pos_of_ne_zero fun h => ht₂ (by rw [h]; exact hob)
  have ht₂' : L.owner j' (pa + yb + (Nat.find hex₂ - 1)) = some b :=
    not_not.mp (Nat.find_min hex₂ (by omega))
  obtain ⟨e', he'⟩ := SleeveSeq.owner_isSome hr (L := L.toSleeveSeq) j' (pa + yb + Nat.find hex₂)
  have he'b : e' ≠ b := fun h => ht₂ (h ▸ he')
  have hsucc₂ : pa + yb + (Nat.find hex₂ - 1) + 1 = pa + yb + Nat.find hex₂ := by omega
  have he'a : e' ≠ a := by
    rintro rfl
    exact hnot ⟨pa + yb + (Nat.find hex₂ - 1), Or.inr ⟨ht₂', by rw [hsucc₂]; exact he'⟩⟩
  have ht₂n : Nat.find hex₂ < L.n j' - yb := by
    have h := Nat.find_min' hex₂ (show L.owner j' (pa + yb + (L.n j' - yb)) ≠ some b by
      rw [hoa']; exact fun h => hab (Option.some.inj h))
    rcases eq_or_lt_of_le h with h | h
    · rw [h, hoa'] at he'
      exact absurd (Option.some.inj he') he'a.symm
    · exact h
  have hsp₂ : L.OnSpoke e' (L.c j' (pa + (yb + Nat.find hex₂))) := by
    have := hchange _ he'b.symm ht₂' (by rw [hsucc₂]; exact he')
    rwa [hsucc₂, add_assoc] at this
  have hcross := L.pairsCrossOn_circuit j' pa ht₁0 ht₁yb (Nat.lt_add_of_pos_right ht₂0)
    (by omega)
  -- The two sides of `C_j`.
  obtain ⟨g, hg0, hgn, hbq, haq, hm⟩ := L.exists_gap hab ha hb
  obtain ⟨oe, hoe0, hoeg, hoe⟩ := L.exists_pos_between hbq haq hm hea heb
  obtain ⟨oe', hoe'0, hoe'g, hoe'⟩ := L.exists_pos_between hbq haq hm he'a he'b
  obtain ⟨Darc, hDarc, hDarcP, hDarcC, hDarc₁, hDarc₂, hDarcV⟩ :=
    L.exists_arc hgn hbq haq hea heb he'a he'b hoe0 hoeg hoe'0 hoe'g hoe hoe'
  -- The vertices of the stretch of `C_j` from `P_a` to `P_b` are on no other radial path.
  have hγend : L.c j (x + 1 + g + (L.n j - g)) = L.c j (x + 1) := by
    rw [show x + 1 + g + (L.n j - g) = x + 1 + L.n j by omega, L.c_add]
  have hγ : ∀ k ≤ L.n j - g, ∀ i, L.OnSpoke i (L.c j (x + 1 + g + k)) → i = a ∨ i = b := by
    intro k hk i hi
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl (hi.eq haq)
    rcases eq_or_lt_of_le hk with rfl | hk1
    · rw [hγend] at hi
      exact Or.inr (hi.eq hbq)
    · exact absurd ⟨i, by rwa [add_assoc] at hi⟩ (hm (g + k) (by omega) (by omega))
  -- The two connected sets.
  let VA : S → Prop := fun u => L.OnSpoke a u ∨ (∃ k ≤ L.n j - g, L.c j (x + 1 + g + k) = u) ∨
    L.OnSpoke b u
  let VB : S → Prop := fun u => L.OnSpoke e u ∨ (∃ o, 0 < o ∧ o < g ∧
    ¬ L.OnSpoke a (L.c j (x + 1 + o)) ∧ ¬ L.OnSpoke b (L.c j (x + 1 + o)) ∧
      L.c j (x + 1 + o) = u) ∨ L.OnSpoke e' u
  have hdis : ∀ u, VA u → VB u → False := by
    rintro u (hA | ⟨k, hk, rfl⟩ | hA) (hB | ⟨o, ho0, hog, hna, hnb, hou⟩ | hB)
    · exact hea (hB.eq hA)
    · exact hna (hou ▸ hA)
    · exact he'a (hB.eq hA)
    · rcases hγ k hk e hB with h | h
      · exact hea h
      · exact heb h
    · rcases eq_or_lt_of_le hk with rfl | hk1
      · rw [hγend] at hou
        exact L.c_ne_window (p := x + 1) (show o < L.n j by omega) (L.n_pos j) (by omega) hou
      · rw [show x + 1 + g + k = x + 1 + (g + k) by omega] at hou
        exact L.c_ne_window (show o < L.n j by omega) (show g + k < L.n j by omega) (by omega) hou
    · rcases hγ k hk e' hB with h | h
      · exact he'a h
      · exact he'b h
    · exact heb (hB.eq hA)
    · exact hnb (hou ▸ hA)
    · exact he'b (hB.eq hA)
  have hspV : ∀ (i : Fin r) (P : S → Prop), (∀ u, L.OnSpoke i u → P u) →
      (∀ u ∈ (walkDrawing D₀ (L.dw i (L.hit i j') (L.hit_le i j'))).V, P u) ∧
        ∀ u ∈ (L.Q i j').V, P u := fun i P hP =>
    ⟨fun u hu => hP u (by
        obtain ⟨k, hk, rfl⟩ := mem_dw_V.mp hu
        exact ⟨k, hk.trans (L.hit_le i j'), rfl⟩),
      fun u hu => hP u ((L.Q_V i j' u).mp hu).1⟩
  obtain ⟨hVA₁, -⟩ := hspV a VA fun u h => Or.inl h
  obtain ⟨hVA₃, -⟩ := hspV b VA fun u h => Or.inr (Or.inr h)
  have hVA₂ : ∀ u ∈ (walkDrawing D₀ (L.cw j (x + 1 + g) (L.n j - g))).V, VA u :=
    fun u hu => Or.inr (Or.inl (mem_cw_V.mp hu))
  obtain ⟨hVB₁, hVB₂⟩ := hspV e VB fun u h => Or.inl h
  obtain ⟨hVB₄, hVB₅⟩ := hspV e' VB fun u h => Or.inr (Or.inr h)
  have hVB₃ : ∀ u ∈ Darc.V, VB u := fun u hu => Or.inr (Or.inl (hDarcV u hu))
  have hfin : ∀ {D₁ D₂ : Drawing S} {z : S}, z ∈ D₁.U → z ∈ D₂.U → D₁.IsSubdrawing D₀ →
      D₂.IsSubdrawing D₀ → (∀ u ∈ D₁.V, VA u) → (∀ u ∈ D₂.V, VB u) → False :=
    fun h h' h₁ h₂ hV₁ hV₂ => Set.disjoint_left.mp (disjoint_U_of_pred h₁ h₂ hdis hV₁ hV₂) h h'
  -- Path-connectedness.
  obtain ⟨_, _, hQe⟩ := L.Q_path e j'
  obtain ⟨_, _, hQe'⟩ := L.Q_path e' j'
  have hA : IsPathConnected
      ((walkDrawing D₀ (L.dw a (L.hit a j') (L.hit_le a j'))).U ∪
        (walkDrawing D₀ (L.cw j (x + 1 + g) (L.n j - g))).U ∪
        (walkDrawing D₀ (L.dw b (L.hit b j') (L.hit_le b j'))).U) := by
    refine ((isPathConnected_walkDrawing _ _).union (isPathConnected_walkDrawing _ _)
      ⟨_, L.mem_dw_U_of_onSpoke hjj' haq,
        (walkDrawing D₀ _).V_subset_U (mem_cw_V.mpr ⟨0, Nat.zero_le _, rfl⟩)⟩).union
      (isPathConnected_walkDrawing _ _) ⟨L.c j (x + 1), Or.inr ?_,
        L.mem_dw_U_of_onSpoke hjj' hbq⟩
    rw [← hγend]
    exact (walkDrawing D₀ _).V_subset_U (mem_cw_V.mpr ⟨_, le_rfl, rfl⟩)
  have hB : IsPathConnected
      ((walkDrawing D₀ (L.dw e (L.hit e j') (L.hit_le e j'))).U ∪ (L.Q e j').U ∪ Darc.U ∪
        (walkDrawing D₀ (L.dw e' (L.hit e' j') (L.hit_le e' j'))).U ∪ (L.Q e' j').U) := by
    refine ((((isPathConnected_walkDrawing _ _).union
      (GraphMinor.GM08.Drawing.IsPathBetween.isPathConnected_U hQe)
      ⟨_, L.hit_mem_dw_U e j', L.hit_mem_Q_U e j'⟩).union hDarcP
      ⟨_, Or.inl (L.mem_dw_U_of_onSpoke hjj' hoe), hDarc₁⟩).union
      (isPathConnected_walkDrawing _ _) ⟨_, Or.inr hDarc₂, L.mem_dw_U_of_onSpoke hjj' hoe'⟩).union
      (GraphMinor.GM08.Drawing.IsPathBetween.isPathConnected_U hQe')
      ⟨_, Or.inr (L.hit_mem_dw_U e' j'), L.hit_mem_Q_U e' j'⟩
  -- Both sets lie in `Δ_{j'}`.
  have hCj : (L.C j).U ⊆ L.Δ j' := fun z hz =>
    discInt_subset _ (L.Δ_lt j j' hjj' (Surface.discBd_subset _ ((L.Δ_bd j).symm ▸ hz)))
  have hQΔ : ∀ i, (L.Q i j').U ⊆ L.Δ j' := fun i z hz =>
    Surface.discBd_subset _ ((L.Δ_bd j').symm ▸ (L.Q_isSubdrawing_C i j').U_subset hz)
  have hdΔ := fun i => L.dw_U_subset_disc hS i hj'0
  have hAΔ := union_subset (union_subset (hdΔ a) ((L.cw_U_subset j (x + 1 + g) (L.n j - g)).trans hCj)) (hdΔ b)
  have hBΔ := union_subset (union_subset (union_subset (union_subset (hdΔ e) (hQΔ e))
    (hDarcC.trans hCj)) (hdΔ e')) (hQΔ e')
  -- The ends.
  have hQmem : ∀ {i : Fin r} {y : ℕ}, L.OnSpoke i (L.c j' y) → L.c j' y ∈ (L.Q i j').U :=
    fun h => (L.Q _ j').V_subset_U ((L.Q_V _ j' _).mpr ⟨h, _, rfl⟩)
  obtain ⟨z, hzA, hzB⟩ := DiscCrossingStatement.of_isPathConnected disc_crossing (L.Δ j') _ _
    _ _ _ _ (L.Δ_disc j') hAΔ hBΔ hA hB
    (Or.inl (Or.inl (by rw [hpa]; exact L.hit_mem_dw_U a j')))
    (Or.inr (by rw [hyxb, hxb]; exact L.hit_mem_dw_U b j'))
    (Or.inl (Or.inl (Or.inl (Or.inr (hQmem hsp₁))))) (Or.inr (hQmem hsp₂)) hcross
  rcases hzA with (h | h) | h <;>
    rcases hzB with (((h' | h') | h') | h') | h' <;>
    exact hfin h h' (walkDrawing_isSubdrawing _ _)
      (by first | exact walkDrawing_isSubdrawing _ _ | exact L.Q_sub _ _ | assumption)
      (by assumption) (by assumption)

/-- **Two radial paths consecutive on `C_j` are consecutive on `C_{j + 1}`.** -/
theorem adj_step (hS : IsClosedDisc (univ : Set S)) (j : Fin s) (hj : j.1 + 1 < s) (a b : Fin r)
    (hab : a ≠ b) (h : L.Adj j a b) : L.Adj ⟨j.1 + 1, hj⟩ a b := by
  obtain ⟨x, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · exact L.adj_step_aux hS hj hab h1 h2
  · exact adj_comm.mpr (L.adj_step_aux hS hj (Ne.symm hab) h1 h2)

end SleeveDraw

end GM08
end GraphMinor
