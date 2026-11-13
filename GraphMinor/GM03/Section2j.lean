module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2g
public import GraphMinor.GM03.Section2h
public import GraphMinor.GM03.Section2i

/-!
# Graph Minors III, Section 2j: Base and Inductive Shell Gluing into $N(d, \lambda)$ (for (2.3))

This file proves the base (`d = 1`) and inductive (`d ↦ d + 1`) combinatorial shell-gluing
embeddings for `(2.3)` (page 55) of N. Robertson and P. D. Seymour,
*Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984), 49–64:
1. `exists_graphN1_empty_inner` and `exists_graphN1_cyclic_model`: embedding the innermost circuit
   `C_d` together with the inner tree `T` and monotone attachment edges into `graphN 1 lam`;
2. `exists_graphN_succ_cyclic_model`: shifting an inner cyclic model in `graphN d lam` inward by one
   cylinder ring and attaching the next outer shell circuit and monotone radial edges in
   `graphN (d + 1) lam`.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

/-! ## 1. Base Shell `d = 1`: Embedding `(T, C₀, E_att)` into `graphN 1 lam` -/

/-- Base case `V(F) = ∅`: embed a single simple circuit `C₀` directly into `graphN 1 lam` with
`HasCyclicModel`. -/
theorem exists_graphN1_empty_inner {α : Type u} {β : Type v}
    (C₀ : Graph α β) (hSimple : C₀.Simple) {p : ℕ} (cyc : CircuitCycle C₀ p) :
    ∃ lam : ℕ, HasCyclicModel C₀ C₀ cyc 1 lam := by
  classical
  let lam := p + 2
  have hlam : 1 ≤ lam := by omega
  have hp_lt_pow : p < 3 * 2 ^ (lam - 1) := by
    have h1 : p + 1 < 2 ^ (p + 1) := Nat.lt_two_pow_self
    change p < 3 * 2 ^ (p + 1); omega
  let b : Fin p → ℕ := fun t => t.1 + 1
  have hb_bd : ∀ t : Fin p, 1 ≤ b t ∧ b t < 3 * 2 ^ (lam - 1) :=
    fun t => ⟨by dsimp only [b]; omega, by dsimp only [b]; have := t.2; omega⟩
  have hb_mono : StrictMono b := fun t₁ t₂ hlt => by
    have := Fin.lt_def.mp hlt; dsimp only [b]; omega
  let ηv : α → Set (GraphNVertex 1 lam) := fun v =>
    if hv : ∃ t : Fin p, cyc.u t = v then
      circle0ArcSet 1 lam cyc.hp b hv.choose
    else ∅
  let ηe : β → GraphNEdge 1 lam := fun e =>
    if he : ∃ t : Fin p, cyc.ce t = e then
      circle0Edge 1 lam ⟨b he.choose - 1, by have := (hb_bd he.choose).2; omega⟩
    else circle0Edge 1 lam ⟨0, by omega⟩
  have hηv_u : ∀ t : Fin p, ηv (cyc.u t) = circle0ArcSet 1 lam cyc.hp b t := by
    intro t
    dsimp only [ηv]
    split_ifs with hex
    · exact congrArg _ (cyc.u_inj hex.choose_spec)
    · exact (hex ⟨t, rfl⟩).elim
  have hηe_ce : ∀ t : Fin p,
      ηe (cyc.ce t) = circle0Edge 1 lam ⟨b t - 1, by have := (hb_bd t).2; omega⟩ := by
    intro t
    dsimp only [ηe]
    split_ifs with hex
    · congr 1; apply Fin.ext; dsimp only; rw [cyc.ce_inj hex.choose_spec]
    · exact (hex ⟨t, rfl⟩).elim
  refine ⟨lam, le_rfl, hlam, le_rfl, ηv, ηe, b, ?_, hb_bd, hb_mono,
    fun t => by rw [hηv_u t]⟩
  refine isMinorModel_of_loopless_link
    (fun e _ u hl => hSimple.not_isLoopAt e u hl)
    (fun v hv => ?_)
    (fun _ _ => subset_univ _)
    (fun v₁ hv₁ v₂ hv₂ hne => ?_)
    (fun e₁ he₁ e₂ he₂ heq => ?_)
    (fun e u v hl => ?_)
    (fun v hv x hx y hy => ?_)
  · obtain ⟨t, rfl⟩ := cyc.vertexSet_eq ▸ hv
    rw [hηv_u t]
    exact circle0ArcSet_nonempty cyc.hp hb_bd hb_mono t
  · obtain ⟨t₁, rfl⟩ := cyc.vertexSet_eq ▸ hv₁
    obtain ⟨t₂, rfl⟩ := cyc.vertexSet_eq ▸ hv₂
    rw [hηv_u t₁, hηv_u t₂]
    exact circle0ArcSet_disjoint cyc.hp hb_mono (fun h => hne (congrArg cyc.u h))
  · obtain ⟨t₁, rfl⟩ := cyc.edgeSet_eq ▸ he₁
    obtain ⟨t₂, rfl⟩ := cyc.edgeSet_eq ▸ he₂
    rw [hηe_ce t₁, hηe_ce t₂] at heq
    have hidx := Fin.mk.inj (circle0Edge_inj heq)
    dsimp only [b] at hidx
    exact congrArg cyc.ce (Fin.ext (by omega))
  · obtain ⟨t, rfl⟩ := cyc.edgeSet_eq ▸ hl.edge_mem
    have hl_t := cyc.isLink_ce t
    obtain ⟨hL, hR⟩ := circle0_divider_endpoints (d := 1) (lam := lam) cyc.hp hb_bd hb_mono t
    have hlink := graphN_isLink_circle0 (d := 1) (lam := lam) le_rfl
      ⟨b t - 1, by have := (hb_bd t).2; omega⟩
    rw [hηe_ce t]
    rcases hl.left_eq_or_eq hl_t with rfl | rfl
    · rw [hl.right_unique hl_t, hηv_u t, hηv_u (nextSpoke t)]
      exact ⟨_, hL, _, hR, hlink⟩
    · rw [hl.right_unique hl_t.symm, hηv_u (nextSpoke t), hηv_u t]
      exact ⟨_, hR, _, hL, hlink.symm⟩
  · obtain ⟨t, rfl⟩ := cyc.vertexSet_eq ▸ hv
    rw [hηv_u t] at hx hy ⊢
    refine circle0ArcSet_connected le_rfl cyc.hp hb_bd hb_mono t subset_rfl ?_ hx hy
    intro i hi_nd ⟨e, he, heq⟩
    obtain ⟨s, rfl⟩ := cyc.edgeSet_eq ▸ he
    rw [hηe_ce s] at heq
    exact hi_nd s (Fin.mk.inj (circle0Edge_inj heq)).symm

open Classical in
/-- Embed a simple graph `G₁` partitioned into an inner tree `T` (with tour walk `W`), an outer
circuit `C₀` (`cyc : CircuitCycle C₀ p`), and `m` attachment edges `attE r` (`Monotone g`,
`Monotone f`) into `graphN 1 lam` satisfying `HasCyclicModel`. -/
theorem exists_graphN1_cyclic_model {α : Type u} {β : Type v}
    (G₁ T C₀ : Graph α β) (hSimple : G₁.Simple)
    (hT_le : T ≤ G₁) (hC₀_le : C₀ ≤ G₁) (hDisj_V : Disjoint V(T) V(C₀))
    (hVT : V(T).Finite) (hET : E(T).Finite)
    (hNoCirc : ∀ C' ≤ T, ¬ IsGraphCircuit T C')
    {v₀ : α} (hv₀ : v₀ ∈ V(T))
    (hConn : ∀ z ∈ V(T), Relation.ReflTransGen T.Adj v₀ z)
    (W : GraphWalk T v₀ v₀) (hCount : ∀ e ∈ E(T), W.edges.count e = 2)
    {p : ℕ} (cyc : CircuitCycle C₀ p)
    {m : ℕ} (attE : Fin m → β) (hatt_inj : Injective attE)
    (g : Fin m → Fin W.support.length)
    (f : Fin m → Fin (p + 1))
    (hg_mono : Monotone g) (hf_mono : Monotone f)
    (hVG₁ : V(G₁) = V(T) ∪ V(C₀))
    (hEG₁ : E(G₁) = E(T) ∪ E(C₀) ∪ range attE)
    (hatt_link : ∀ r : Fin m,
      G₁.IsLink (attE r) (W.support[g r])
        (cyc.u ⟨(f r).1 % p, Nat.mod_lt _ (by have := cyc.hp; omega)⟩)) :
    ∃ lam : ℕ, HasCyclicModel G₁ C₀ cyc 1 lam := by
  classical
  have hT_simple : T.Simple := Simple.mono hSimple hT_le
  have hW_mem : ∀ k : Fin W.support.length, W.support[k] ∈ V(T) := by
    intro k
    have hsup : ∀ {a b : α} (Q : GraphWalk T a b), a ∈ V(T) → ∀ x ∈ Q.support, x ∈ V(T) := by
      intro a b Q; induction Q with
      | nil ha =>
        intro _ x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ha
        · cases hmem
      | cons hl rest ih =>
        intro ha x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ha
        · exact ih hl.right_mem x hmem
    exact hsup W hv₀ W.support[k] (List.getElem_mem _)
  obtain ⟨h, ηvT₀, ηeT, l, hh, hmT₀, _, hl_spec, hl_mono⟩ :=
    exists_binWord_tour_model T hT_simple hVT hET hNoCirc hv₀ hConn W hCount
  let κ := p + m + 2
  have hκ : 1 ≤ κ := by dsimp only [κ]; omega
  obtain ⟨ηvT, hmT, hcone⟩ :=
    cone_extend_binWord_tour hT_simple hW_mem hh κ hκ hmT₀ hl_spec hl_mono
  let lam := h + κ + 1
  have hlam : 1 ≤ lam := by dsimp only [lam]; omega
  let R := 3 * 2 ^ (lam - 1)
  have hsup_len : W.support.length = W.length + 1 := by
    have hlen : ∀ {a b : α} (Q : GraphWalk T a b), Q.support.length = Q.length + 1 := by
      intro a b Q; induction Q with
      | nil _ => rfl
      | cons _ _ ih => simp only [GraphWalk.support, List.length_cons, ih, GraphWalk.length_cons]
    exact hlen W
  let q := W.length
  let castIdx : Fin (q + 1) → Fin W.support.length := Fin.cast hsup_len.symm
  let a : Fin (q + 1) → ℕ := fun s => 2 ^ (κ + 1) * subVal (l (castIdx s))
  let d_hi : Fin (q + 1) → ℕ := fun s => 2 ^ (κ + 1) * (subVal (l (castIdx s)) + 1)
  have hpow_κ : p + m + 2 ≤ 2 ^ (κ + 1) := by
    have hlt : κ + 1 < 2 ^ (κ + 1) := Nat.lt_two_pow_self
    dsimp only [κ] at hlt ⊢; omega
  have hd_le_R : ∀ s : Fin (q + 1), d_hi s ≤ R := by
    intro s
    have hlt_l : subVal (l (castIdx s)) < 2 ^ (h - 1) := by
      have := subVal_lt_pow (l (castIdx s))
      rwa [(hl_spec (castIdx s)).1] at this
    have hmul : 2 ^ (κ + 1) * (subVal (l (castIdx s)) + 1) ≤ 2 ^ (κ + 1) * 2 ^ (h - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : 2 ^ (κ + 1) * 2 ^ (h - 1) = 2 ^ (lam - 1) := by
      rw [← pow_add]; congr 1; dsimp only [lam]; omega
    dsimp only [d_hi, R]; omega
  let g' : Fin m → Fin (q + 1) := fun r => Fin.cast hsup_len (g r)
  have hg'_mono : Monotone g' := fun r₁ r₂ hle => hg_mono hle
  obtain ⟨b, spk, hb_bd, hb_mono, hspk_bd, hspk_mono, hsep⟩ :=
    exists_monotone_dividers_and_spokes a d_hi g' f
      (fun s => by dsimp only [a, d_hi]; rw [Nat.mul_add, Nat.mul_one]; omega)
      (fun s₁ s₂ hle => by
        dsimp only [a]
        exact Nat.mul_le_mul_left _ (hl_mono.monotone hle))
      hd_le_R hg'_mono hf_mono
  have hspk_lt_R : ∀ r : Fin m, spk r < R :=
    fun r => lt_of_lt_of_le (hspk_bd r).2.2 (hd_le_R (g' r))
  -- Disjointness of `E(T)`, `E(C₀)`, and `range attE`
  have hET_disj_EC₀ : Disjoint E(T) E(C₀) := by
    rw [Set.disjoint_left]
    intro e heT heC
    obtain ⟨u₁, v₁, hl₁⟩ := T.exists_isLink_of_mem_edgeSet heT
    obtain ⟨u₂, v₂, hl₂⟩ := C₀.exists_isLink_of_mem_edgeSet heC
    rcases (hl₁.mono hT_le).left_eq_or_eq (hl₂.mono hC₀_le) with rfl | rfl
    · exact Set.disjoint_left.mp hDisj_V hl₁.left_mem hl₂.left_mem
    · exact Set.disjoint_left.mp hDisj_V hl₁.left_mem hl₂.right_mem
  have hET_disj_att : Disjoint E(T) (range attE) := by
    rw [Set.disjoint_left]
    rintro e heT ⟨r, rfl⟩
    obtain ⟨u₁, v₁, hl₁⟩ := T.exists_isLink_of_mem_edgeSet heT
    have hl₂ := hatt_link r
    have hC_mem : cyc.u ⟨(f r).1 % p, Nat.mod_lt _ (by have := cyc.hp; omega)⟩ ∈ V(C₀) :=
      cyc.vertexSet_eq ▸ mem_range_self _
    rcases (hl₁.mono hT_le).left_eq_or_eq hl₂ with heq | heq
    · have hv₁ : v₁ = cyc.u _ := (hl₁.mono hT_le).right_unique (heq ▸ hl₂)
      exact Set.disjoint_left.mp hDisj_V hl₁.right_mem (hv₁ ▸ hC_mem)
    · exact Set.disjoint_left.mp hDisj_V (heq ▸ hl₁.left_mem) hC_mem
  have hEC₀_disj_att : Disjoint E(C₀) (range attE) := by
    rw [Set.disjoint_left]
    rintro e heC ⟨r, rfl⟩
    obtain ⟨u₁, v₁, hl₁⟩ := C₀.exists_isLink_of_mem_edgeSet heC
    have hl₂ := hatt_link r
    have hT_mem : W.support[g r] ∈ V(T) := hW_mem (g r)
    rcases (hl₁.mono hC₀_le).left_eq_or_eq hl₂ with heq | heq
    · exact Set.disjoint_left.mp hDisj_V (heq ▸ hT_mem) hl₁.left_mem
    · have hv₁ : v₁ = W.support[g r] := (hl₁.mono hC₀_le).right_unique (heq ▸ hl₂.symm)
      exact Set.disjoint_left.mp hDisj_V (hv₁ ▸ hT_mem) hl₁.right_mem
  let φv : α → Set (GraphNVertex 1 lam) := fun v =>
    if v ∈ V(T) then
      {z | ∃ (w : List Bool) (hw : w.length < h + κ),
        w ∈ ηvT v ∧ z = Sum.inl (binNodeOfWord (h + κ) w hw)}
    else if hvC : ∃ t : Fin p, cyc.u t = v then
      circle0ArcSet 1 lam cyc.hp b hvC.choose
    else ∅
  let φe : β → GraphNEdge 1 lam := fun e =>
    if e ∈ E(T) then
      if he : (ηeT e).length < h + κ then Sum.inl (Sum.inl (binNodeOfWord (h + κ) (ηeT e) he))
      else Sum.inl (Sum.inl none)
    else if heC : ∃ t : Fin p, cyc.ce t = e then
      circle0Edge 1 lam ⟨b heC.choose - 1, by have := (hb_bd heC.choose).2; omega⟩
    else if heA : ∃ r : Fin m, attE r = e then
      Sum.inl (Sum.inr ⟨spk heA.choose, hspk_lt_R heA.choose⟩)
    else circle0Edge 1 lam ⟨0, by have := three_pow_ge_three lam; omega⟩
  have hφv_T : ∀ v ∈ V(T), φv v = {z | ∃ (w : List Bool) (hw : w.length < h + κ),
      w ∈ ηvT v ∧ z = Sum.inl (binNodeOfWord (h + κ) w hw)} := by
    intro v hv; dsimp only [φv]; split_ifs; rfl
  have hφv_C : ∀ t : Fin p, φv (cyc.u t) = circle0ArcSet 1 lam cyc.hp b t := by
    intro t
    have hnotT : cyc.u t ∉ V(T) :=
      Set.disjoint_right.mp hDisj_V (cyc.vertexSet_eq ▸ mem_range_self t)
    dsimp only [φv]
    split_ifs with hex
    · exact congrArg _ (cyc.u_inj hex.choose_spec)
    · exact (hex ⟨t, rfl⟩).elim
  have hφe_T : ∀ e ∈ E(T), ∀ (hlt : (ηeT e).length < h + κ),
      φe e = Sum.inl (Sum.inl (binNodeOfWord (h + κ) (ηeT e) hlt)) := by
    intro e he hlt; dsimp only [φe]; split_ifs; rfl
  have hφe_C : ∀ t : Fin p,
      φe (cyc.ce t) = circle0Edge 1 lam ⟨b t - 1, by have := (hb_bd t).2; omega⟩ := by
    intro t
    have hnotT : cyc.ce t ∉ E(T) :=
      Set.disjoint_right.mp hET_disj_EC₀ (cyc.edgeSet_eq ▸ mem_range_self t)
    dsimp only [φe]
    split_ifs with hex
    · congr 1; apply Fin.ext; dsimp only; rw [cyc.ce_inj hex.choose_spec]
    · exact (hex ⟨t, rfl⟩).elim
    · exact (hex ⟨t, rfl⟩).elim
  have hφe_att : ∀ r : Fin m,
      φe (attE r) = Sum.inl (Sum.inr ⟨spk r, hspk_lt_R r⟩) := by
    intro r
    have hnotT : attE r ∉ E(T) := Set.disjoint_right.mp hET_disj_att (mem_range_self r)
    have hnotC : ¬ ∃ t : Fin p, cyc.ce t = attE r := by
      rintro ⟨t, ht⟩
      exact Set.disjoint_left.mp hEC₀_disj_att (ht ▸ cyc.edgeSet_eq ▸ mem_range_self t)
        (mem_range_self r)
    dsimp only [φe]
    split_ifs with hex
    · congr 2; apply Fin.ext; dsimp only; rw [hatt_inj hex.choose_spec]
    · exact (hex ⟨r, rfl⟩).elim
  refine ⟨lam, le_rfl, hlam, hC₀_le, φv, φe, b, ?_, hb_bd, hb_mono,
    fun t => by rw [hφv_C t]⟩
  refine isMinorModel_of_loopless_link
    (fun e _ u hl => hSimple.not_isLoopAt e u hl)
    (fun v hv => ?_)
    (fun _ _ => subset_univ _)
    (fun v₁ hv₁ v₂ hv₂ hne => ?_)
    (fun e₁ he₁ e₂ he₂ heq => ?_)
    (fun e u v hl => ?_)
    (fun u hu x hx y hy => ?_)
  · rcases hVG₁ ▸ hv with hvT | hvC
    · rw [hφv_T v hvT]
      obtain ⟨w, hw⟩ := hmT.vertex_nonempty v hvT
      exact ⟨_, w, hmT.vertex_subset v hvT hw, hw, rfl⟩
    · obtain ⟨t, rfl⟩ := cyc.vertexSet_eq ▸ hvC
      rw [hφv_C t]
      exact circle0ArcSet_nonempty cyc.hp hb_bd hb_mono t
  · have hT_not_C : ∀ z, (∃ (w : List Bool) (hw : w.length < h + κ),
        z = Sum.inl (binNodeOfWord (h + κ) w hw)) →
        ∀ t : Fin p, z ∉ circle0ArcSet 1 lam cyc.hp b t := by
      rintro _ ⟨_, _, rfl⟩ t hzC
      unfold circle0ArcSet at hzC
      split_ifs at hzC
      · obtain ⟨_, _, heq⟩ := hzC; cases heq
      · obtain ⟨_, _, _, heq⟩ := hzC; cases heq
    rcases hVG₁ ▸ hv₁ with h1T | h1C <;> rcases hVG₁ ▸ hv₂ with h2T | h2C
    · rw [hφv_T v₁ h1T, hφv_T v₂ h2T, Set.disjoint_left]
      rintro _ ⟨w₁, hw₁_lt, hw₁, rfl⟩ ⟨w₂, hw₂_lt, hw₂, heq⟩
      injection heq with h'
      exact Set.disjoint_left.mp (hmT.vertex_disjoint v₁ h1T v₂ h2T hne)
        hw₁ ((binNodeOfWord_inj hw₁_lt hw₂_lt h') ▸ hw₂)
    · obtain ⟨t₂, rfl⟩ := cyc.vertexSet_eq ▸ h2C
      rw [hφv_T v₁ h1T, hφv_C t₂, Set.disjoint_left]
      rintro z ⟨w₁, hw₁_lt, _, rfl⟩ hzC
      exact hT_not_C _ ⟨w₁, hw₁_lt, rfl⟩ t₂ hzC
    · obtain ⟨t₁, rfl⟩ := cyc.vertexSet_eq ▸ h1C
      rw [hφv_C t₁, hφv_T v₂ h2T, Set.disjoint_left]
      rintro z hzC ⟨w₂, hw₂_lt, _, rfl⟩
      exact hT_not_C _ ⟨w₂, hw₂_lt, rfl⟩ t₁ hzC
    · obtain ⟨t₁, rfl⟩ := cyc.vertexSet_eq ▸ h1C
      obtain ⟨t₂, rfl⟩ := cyc.vertexSet_eq ▸ h2C
      rw [hφv_C t₁, hφv_C t₂]
      exact circle0ArcSet_disjoint cyc.hp hb_mono (fun h => hne (congrArg cyc.u h))
  · rcases hEG₁ ▸ he₁ with (h1T | h1C) | ⟨r₁, rfl⟩ <;>
      rcases hEG₁ ▸ he₂ with (h2T | h2C) | ⟨r₂, rfl⟩
    · have hlt₁ := (hmT.edge_mem e₁ h1T).2
      have hlt₂ := (hmT.edge_mem e₂ h2T).2
      rw [hφe_T e₁ h1T hlt₁, hφe_T e₂ h2T hlt₂] at heq
      injection heq with h1; injection h1 with h2
      exact hmT.edge_injOn h1T h2T (binNodeOfWord_inj hlt₁ hlt₂ h2)
    · obtain ⟨t₂, rfl⟩ := cyc.edgeSet_eq ▸ h2C
      rw [hφe_T e₁ h1T (hmT.edge_mem e₁ h1T).2, hφe_C t₂] at heq; cases heq
    · rw [hφe_T e₁ h1T (hmT.edge_mem e₁ h1T).2, hφe_att r₂] at heq; cases heq
    · obtain ⟨t₁, rfl⟩ := cyc.edgeSet_eq ▸ h1C
      rw [hφe_C t₁, hφe_T e₂ h2T (hmT.edge_mem e₂ h2T).2] at heq; cases heq
    · obtain ⟨t₁, rfl⟩ := cyc.edgeSet_eq ▸ h1C
      obtain ⟨t₂, rfl⟩ := cyc.edgeSet_eq ▸ h2C
      rw [hφe_C t₁, hφe_C t₂] at heq
      have hidx := Fin.mk.inj (circle0Edge_inj heq)
      have hbt₁ : b t₁ = b t₂ := by
        have := (hb_bd t₁).1; have := (hb_bd t₂).1; omega
      exact congrArg cyc.ce (hb_mono.injective hbt₁)
    · obtain ⟨t₁, rfl⟩ := cyc.edgeSet_eq ▸ h1C
      rw [hφe_C t₁, hφe_att r₂] at heq; cases heq
    · rw [hφe_att r₁, hφe_T e₂ h2T (hmT.edge_mem e₂ h2T).2] at heq; cases heq
    · obtain ⟨t₂, rfl⟩ := cyc.edgeSet_eq ▸ h2C
      rw [hφe_att r₁, hφe_C t₂] at heq; cases heq
    · rw [hφe_att r₁, hφe_att r₂] at heq
      injection heq with h1; injection h1 with h2
      exact congrArg attE (hspk_mono.injective (Fin.mk.inj h2))
  · rcases hEG₁ ▸ hl.edge_mem with (heT | heC) | ⟨r, rfl⟩
    · obtain ⟨u', v', hl_T⟩ := T.exists_isLink_of_mem_edgeSet heT
      have hl_uv : T.IsLink e u v := by
        rcases hl.left_eq_or_eq (hl_T.mono hT_le) with rfl | rfl
        · rwa [hl.right_unique (hl_T.mono hT_le)]
        · rw [hl.right_unique (hl_T.mono hT_le).symm]; exact hl_T.symm
      have huv : u ≠ v := fun h => hSimple.not_isLoopAt e u (h ▸ hl)
      obtain ⟨x', hx'u, y', hy'v, hne_e, hlt_e, hends⟩ :=
        exists_isLink_of_isMinorModel hmT hl_uv huv
      have hsnoc : ηeT e = (ηeT e).dropLast ++ [(ηeT e).getLast hne_e] :=
        (List.dropLast_append_getLast hne_e).symm
      have hsnoc_lt : ((ηeT e).dropLast ++ [(ηeT e).getLast hne_e]).length < h + κ :=
        hsnoc ▸ hlt_e
      have hl_N := graphN_isLink_binNode_snoc 1 (ηeT e).dropLast ((ηeT e).getLast hne_e) hsnoc_lt
      have hnode_eq : binNodeOfWord (h + κ) ((ηeT e).dropLast ++ [(ηeT e).getLast hne_e]) hsnoc_lt =
          binNodeOfWord (h + κ) (ηeT e) hlt_e := by congr 1; exact hsnoc.symm
      rw [hnode_eq] at hl_N
      have hx_lt := hmT.vertex_subset u hl_uv.left_mem hx'u
      have hy_lt := hmT.vertex_subset v hl_uv.right_mem hy'v
      rw [hφe_T e heT hlt_e, hφv_T u hl_uv.left_mem, hφv_T v hl_uv.right_mem]
      refine ⟨_, ⟨x', hx_lt, hx'u, rfl⟩, _, ⟨y', hy_lt, hy'v, rfl⟩, ?_⟩
      rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hl_N
      · exact hl_N.symm
    · obtain ⟨t, rfl⟩ := cyc.edgeSet_eq ▸ heC
      have hl_C := (cyc.isLink_ce t).mono hC₀_le
      obtain ⟨hL, hR⟩ := circle0_divider_endpoints (d := 1) (lam := lam) cyc.hp hb_bd hb_mono t
      have hlink := graphN_isLink_circle0 (d := 1) (lam := lam) le_rfl
        ⟨b t - 1, by have := (hb_bd t).2; omega⟩
      rw [hφe_C t]
      rcases hl.left_eq_or_eq hl_C with rfl | rfl
      · rw [hl.right_unique hl_C, hφv_C t, hφv_C (nextSpoke t)]
        exact ⟨_, hL, _, hR, hlink⟩
      · rw [hl.right_unique hl_C.symm, hφv_C (nextSpoke t), hφv_C t]
        exact ⟨_, hR, _, hL, hlink.symm⟩
    · have hl_r := hatt_link r
      let ir : Fin R := ⟨spk r, hspk_lt_R r⟩
      have hcast_g : castIdx (g' r) = g r := by apply Fin.ext; rfl
      have hlo : 2 ^ (κ + 1) * subVal (l (g r)) ≤ ir.1 := by
        have := (hspk_bd r).2.1; dsimp only [a] at this; rwa [hcast_g] at this
      have hhi : ir.1 < 2 ^ (κ + 1) * (subVal (l (g r)) + 1) := by
        have := (hspk_bd r).2.2; dsimp only [d_hi] at this; rwa [hcast_g] at this
      obtain ⟨w, hw_lt, hw_mem, hleaf_eq⟩ := hcone (g r) ir hlo hhi
      let tr : Fin p := ⟨(f r).1 % p, Nat.mod_lt _ (by have := cyc.hp; omega)⟩
      have hmem_T : Sum.inl (treeYLeafParent lam ir) ∈ φv (W.support[g r]) := by
        rw [hφv_T _ (hW_mem (g r))]
        exact ⟨w, hw_lt, hw_mem, congrArg Sum.inl hleaf_eq⟩
      have hmem_C : circle0Vert 1 lam ir ∈ φv (cyc.u tr) := by
        rw [hφv_C tr]
        exact mem_circle0ArcSet_of_sep cyc.hp (hspk_lt_R r) (f r) (hsep r)
      have hl_leaf : (graphN 1 lam).IsLink (Sum.inl (Sum.inr ir))
          (Sum.inl (treeYLeafParent lam ir)) (circle0Vert 1 lam ir) :=
        Or.inl ⟨rfl, rfl⟩
      rw [hφe_att r]
      rcases hl.left_eq_or_eq hl_r with rfl | rfl
      · rw [hl.right_unique hl_r]
        exact ⟨_, hmem_T, _, hmem_C, hl_leaf⟩
      · rw [hl.right_unique hl_r.symm]
        exact ⟨_, hmem_C, _, hmem_T, hl_leaf.symm⟩
  · rcases hVG₁ ▸ hu with huT | huC
    · rw [hφv_T u huT] at hx hy
      obtain ⟨w₁, hw₁_lt, hw₁, rfl⟩ := hx
      obtain ⟨w₂, hw₂_lt, hw₂, rfl⟩ := hy
      obtain ⟨K, hK_le, hVK, hK_conn⟩ := hmT.connected u huT
      have hsub_u := hmT.vertex_subset u huT
      have hrel := hK_conn.2 w₁ (hVK ▸ hw₁) w₂ (hVK ▸ hw₂)
      revert hw₂_lt hw₂
      induction hrel with
      | refl => intro _ _; exact Relation.ReflTransGen.refl
      | @tail a₀ b₀ _ hstep ih_step =>
        intro _ _
        obtain ⟨f₀, hlf⟩ := hstep
        have hlf_del : ((binWordTree (h + κ)).deleteEdges (ηeT '' E(T))).IsLink f₀ a₀ b₀ :=
          hlf.mono hK_le
        rw [Graph.deleteEdges_isLink] at hlf_del
        obtain ⟨⟨hf_ne, hf_lt, hf_ends⟩, hf_not_img⟩ := hlf_del
        have ha_u : a₀ ∈ ηvT u := hVK ▸ hlf.left_mem
        have hb_u : b₀ ∈ ηvT u := hVK ▸ hlf.right_mem
        have ha_lt := hsub_u ha_u
        have hb_lt := hsub_u hb_u
        refine Relation.ReflTransGen.tail (ih_step ha_lt ha_u) ?_
        have hsnoc : f₀ = f₀.dropLast ++ [f₀.getLast hf_ne] :=
          (List.dropLast_append_getLast hf_ne).symm
        have hsnoc_lt : (f₀.dropLast ++ [f₀.getLast hf_ne]).length < h + κ := hsnoc ▸ hf_lt
        have hl_f := graphN_isLink_binNode_snoc 1 f₀.dropLast (f₀.getLast hf_ne) hsnoc_lt
        have hnode_eq : binNodeOfWord (h + κ) (f₀.dropLast ++ [f₀.getLast hf_ne]) hsnoc_lt =
            binNodeOfWord (h + κ) f₀ hf_lt := by congr 1; exact hsnoc.symm
        rw [hnode_eq] at hl_f
        refine ⟨Sum.inl (Sum.inl (binNodeOfWord (h + κ) f₀ hf_lt)), ?_⟩
        rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · rcases hf_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hl_f
          · exact hl_f.symm
        · rintro ⟨e, he, heq⟩
          rcases hEG₁ ▸ he with (heT | heC) | ⟨r, rfl⟩
          · have he_lt := (hmT.edge_mem e heT).2
            rw [hφe_T e heT he_lt] at heq
            injection heq with h1; injection h1 with h2
            exact hf_not_img ⟨e, heT, binNodeOfWord_inj he_lt hf_lt h2⟩
          · obtain ⟨t, rfl⟩ := cyc.edgeSet_eq ▸ heC
            rw [hφe_C t] at heq; cases heq
          · rw [hφe_att r] at heq; cases heq
        · rw [hφv_T u huT]; exact ⟨a₀, ha_lt, ha_u, rfl⟩
        · rw [hφv_T u huT]; exact ⟨b₀, hb_lt, hb_u, rfl⟩
    · obtain ⟨t, rfl⟩ := cyc.vertexSet_eq ▸ huC
      rw [hφv_C t] at hx hy ⊢
      refine circle0ArcSet_connected le_rfl cyc.hp hb_bd hb_mono t subset_rfl ?_ hx hy
      intro i hi_nd ⟨e, he, heq⟩
      rcases hEG₁ ▸ he with (heT | heC) | ⟨r, rfl⟩
      · rw [hφe_T e heT (hmT.edge_mem e heT).2] at heq; cases heq
      · obtain ⟨s, rfl⟩ := cyc.edgeSet_eq ▸ heC
        rw [hφe_C s] at heq
        exact hi_nd s (Fin.mk.inj (circle0Edge_inj heq)).symm
      · rw [hφe_att r] at heq; cases heq

/-! ## 2. Inductive Shell Step `d ↦ d + 1`: Shifting Inner Model and Adding Outer Ring -/

/-- Given a cyclic minor model of `G_in` in `graphN d lam₀` (`1 ≤ d`, `1 ≤ lam₀`) with boundary
circuit `C_in` (`cyc_in : CircuitCycle C_in p_in`), an outer circuit `C_out`
(`cyc_out : CircuitCycle C_out p_out`) vertex-disjoint from `G_in`, and `m` monotone radial edges
`attE r` between `C_in` and `C_out`, construct a cyclic minor model of `G_out` in
`graphN (d + 1) lam` for some `lam ≥ lam₀`. -/
theorem exists_graphN_succ_cyclic_model {α : Type u} {β : Type v}
    (G_out G_in C_in C_out : Graph α β) (hSimple : G_out.Simple)
    (hGin_le : G_in ≤ G_out) (hCout_le : C_out ≤ G_out)
    (hDisj_V : Disjoint V(G_in) V(C_out))
    {p_in p_out : ℕ} (cyc_in : CircuitCycle C_in p_in) (cyc_out : CircuitCycle C_out p_out)
    {d lam₀ : ℕ} (hcyc_in : HasCyclicModel G_in C_in cyc_in d lam₀)
    {m : ℕ} (attE : Fin m → β) (hatt_inj : Injective attE)
    (g : Fin m → Fin (p_in + 1)) (f : Fin m → Fin (p_out + 1))
    (hg_mono : Monotone g) (hf_mono : Monotone f)
    (hVG_out : V(G_out) = V(G_in) ∪ V(C_out))
    (hEG_out : E(G_out) = E(G_in) ∪ E(C_out) ∪ range attE)
    (hatt_link : ∀ r : Fin m,
      G_out.IsLink (attE r)
        (cyc_in.u ⟨(g r).1 % p_in, Nat.mod_lt _ (by have := cyc_in.hp; omega)⟩)
        (cyc_out.u ⟨(f r).1 % p_out, Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩)) :
    ∃ lam : ℕ, lam₀ ≤ lam ∧ HasCyclicModel G_out C_out cyc_out (d + 1) lam := by
  classical
  have hd : 1 ≤ d := hcyc_in.1
  have hlam₀ : 1 ≤ lam₀ := hcyc_in.2.1
  have hCin_le : C_in ≤ G_in := hcyc_in.2.2.1
  let κ := p_out + m + 2
  have hpow_κ : p_out + m + 2 ≤ 2 ^ κ := le_of_lt Nat.lt_two_pow_self
  obtain ⟨ηv_in, ηe_in, b_in, hm_in, hbin_bd, hbin_gap, hbin_mono, harc_in⟩ :=
    iterate_double_cyclic_model (Simple.mono hSimple hGin_le) hcyc_in κ
  let lam := lam₀ + κ
  have hlam : 1 ≤ lam := by omega
  let R := 3 * 2 ^ (lam - 1)
  have hp_in2 := cyc_in.hp
  let a : Fin (p_in + 1) → ℕ := fun s =>
    if hs : s.1 = 0 then 0 else b_in ⟨s.1 - 1, by have := s.2; omega⟩
  let d_hi : Fin (p_in + 1) → ℕ := fun s =>
    if hs : s.1 < p_in then b_in ⟨s.1, hs⟩ else R
  have hslot_len : ∀ s : Fin (p_in + 1), a s + (p_out + m + 2) ≤ d_hi s := by
    intro s
    dsimp only [a, d_hi]
    split_ifs with hs0 hslt hslt'
    · have := (hbin_bd ⟨0, by omega⟩).1
      have h0eq : (⟨s.1, hslt⟩ : Fin p_in) = ⟨0, by omega⟩ := Fin.ext hs0
      rw [h0eq]; omega
    · omega
    · have hg := hbin_gap ⟨s.1 - 1, by omega⟩ ⟨s.1, hslt'⟩ (Fin.lt_def.mpr (by dsimp only; omega))
      omega
    · have := (hbin_bd ⟨p_in - 1, by omega⟩).2
      have hpred : (⟨s.1 - 1, by have := s.2; omega⟩ : Fin p_in) = ⟨p_in - 1, by omega⟩ :=
        Fin.ext (by dsimp only; have := s.2; omega)
      rw [hpred]; dsimp only [R, lam]; omega
  have ha_mono : ∀ s₁ s₂ : Fin (p_in + 1), s₁ ≤ s₂ → a s₁ ≤ a s₂ := by
    intro s₁ s₂ hle
    have hle' := Fin.le_def.mp hle
    dsimp only [a]
    split_ifs with h1 h2 h2'
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact hbin_mono.monotone (Fin.le_def.mpr (by dsimp only; omega))
  have hd_le_R : ∀ s : Fin (p_in + 1), d_hi s ≤ R := by
    intro s; dsimp only [d_hi]; split_ifs with hs
    · have := (hbin_bd ⟨s.1, hs⟩).2; have : 1 ≤ 2 ^ κ := Nat.one_le_pow _ _ (by omega)
      dsimp only [R, lam]; omega
    · exact le_rfl
  obtain ⟨b_out, spk, hbout_bd, hbout_mono, hspk_bd, hspk_mono, hsep⟩ :=
    exists_monotone_dividers_and_spokes a d_hi g f hslot_len ha_mono hd_le_R hg_mono hf_mono
  have hspk_lt_R : ∀ r : Fin m, spk r < R :=
    fun r => lt_of_lt_of_le (hspk_bd r).2.2 (hd_le_R (g r))
  -- Every spoke in `[a s, d_hi s)` lies in `circle0ArcSet d lam cyc_in.hp b_in ⟨s.1 % p_in, _⟩`
  have hslot_mem_in : ∀ (s : Fin (p_in + 1)) (k : ℕ) (hk : k < R),
      a s ≤ k → k < d_hi s →
      circle0Vert d lam ⟨k, hk⟩ ∈
        circle0ArcSet d lam cyc_in.hp b_in ⟨s.1 % p_in, Nat.mod_lt _ (by omega)⟩ := by
    intro s k hk hlo hhi
    dsimp only [a, d_hi] at hlo hhi
    unfold circle0ArcSet
    split_ifs with hmod0
    · by_cases hs0 : s.1 = 0
      · have hhi' : k < b_in ⟨0, by omega⟩ := by
          split_ifs at hhi with hslt
          · have h0eq : (⟨s.1, hslt⟩ : Fin p_in) = ⟨0, by omega⟩ := Fin.ext hs0
            rwa [h0eq] at hhi
          · omega
        exact ⟨⟨k, hk⟩, Or.inl hhi', rfl⟩
      · have hslt : ¬ s.1 < p_in := by
          intro hlt
          exact hs0 (by dsimp only at hmod0; rwa [Nat.mod_eq_of_lt hlt] at hmod0)
        have hseq : s.1 = p_in := by have := s.2; omega
        have hlo' : b_in ⟨p_in - 1, by omega⟩ ≤ k := by
          split_ifs at hlo
          have hpred : (⟨s.1 - 1, by have := s.2; omega⟩ : Fin p_in) = ⟨p_in - 1, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rwa [hpred] at hlo
        exact ⟨⟨k, hk⟩, Or.inr hlo', rfl⟩
    · have hs0 : ¬ s.1 = 0 := fun h => hmod0 (by dsimp only; rw [h, Nat.zero_mod])
      have hslt : s.1 < p_in := by
        by_contra hge
        have hseq : s.1 = p_in := by have := s.2; omega
        exact hmod0 (by dsimp only; rw [hseq, Nat.mod_self])
      have hmod : s.1 % p_in = s.1 := Nat.mod_eq_of_lt hslt
      have hlo' : b_in ⟨(⟨s.1 % p_in, Nat.mod_lt _ (by omega)⟩ : Fin p_in).1 - 1, by omega⟩ ≤ k := by
        split_ifs at hlo
        have h1 : (⟨(⟨s.1 % p_in, Nat.mod_lt _ (by omega)⟩ : Fin p_in).1 - 1, by omega⟩ :
            Fin p_in) = ⟨s.1 - 1, by have := s.2; omega⟩ :=
          Fin.ext (by dsimp only; rw [hmod])
        rwa [h1]
      have hhi' : k < b_in ⟨s.1 % p_in, Nat.mod_lt _ (by omega)⟩ := by
        split_ifs at hhi
        have h2 : (⟨s.1 % p_in, Nat.mod_lt _ (by omega)⟩ : Fin p_in) = ⟨s.1, hslt⟩ :=
          Fin.ext hmod
        rwa [h2]
      exact ⟨⟨k, hk⟩, hlo', hhi', rfl⟩
  -- Disjointness of `E(G_in)`, `E(C_out)`, and `range attE`
  have hEGin_disj_ECout : Disjoint E(G_in) E(C_out) := by
    rw [Set.disjoint_left]
    intro e heIn heOut
    obtain ⟨u₁, v₁, hl₁⟩ := G_in.exists_isLink_of_mem_edgeSet heIn
    obtain ⟨u₂, v₂, hl₂⟩ := C_out.exists_isLink_of_mem_edgeSet heOut
    rcases (hl₁.mono hGin_le).left_eq_or_eq (hl₂.mono hCout_le) with rfl | rfl
    · exact Set.disjoint_left.mp hDisj_V hl₁.left_mem hl₂.left_mem
    · exact Set.disjoint_left.mp hDisj_V hl₁.left_mem hl₂.right_mem
  have hEGin_disj_att : Disjoint E(G_in) (range attE) := by
    rw [Set.disjoint_left]
    rintro e heIn ⟨r, rfl⟩
    obtain ⟨u₁, v₁, hl₁⟩ := G_in.exists_isLink_of_mem_edgeSet heIn
    have hl₂ := hatt_link r
    have hOut_mem : cyc_out.u ⟨(f r).1 % p_out, Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ ∈
        V(C_out) := cyc_out.vertexSet_eq ▸ mem_range_self _
    rcases (hl₁.mono hGin_le).left_eq_or_eq hl₂ with heq | heq
    · have hv₁ : v₁ = cyc_out.u _ := (hl₁.mono hGin_le).right_unique (heq ▸ hl₂)
      exact Set.disjoint_left.mp hDisj_V hl₁.right_mem (hv₁ ▸ hOut_mem)
    · exact Set.disjoint_left.mp hDisj_V (heq ▸ hl₁.left_mem) hOut_mem
  have hECout_disj_att : Disjoint E(C_out) (range attE) := by
    rw [Set.disjoint_left]
    rintro e heOut ⟨r, rfl⟩
    obtain ⟨u₁, v₁, hl₁⟩ := C_out.exists_isLink_of_mem_edgeSet heOut
    have hl₂ := hatt_link r
    have hIn_mem : cyc_in.u ⟨(g r).1 % p_in, Nat.mod_lt _ (by have := cyc_in.hp; omega)⟩ ∈
        V(G_in) := hCin_le.vertexSet_mono (cyc_in.vertexSet_eq ▸ mem_range_self _)
    rcases (hl₁.mono hCout_le).left_eq_or_eq hl₂ with heq | heq
    · exact Set.disjoint_left.mp hDisj_V (heq ▸ hIn_mem) hl₁.left_mem
    · have hv₁ : v₁ = cyc_in.u _ := (hl₁.mono hCout_le).right_unique (heq ▸ hl₂.symm)
      exact Set.disjoint_left.mp hDisj_V (hv₁ ▸ hIn_mem) hl₁.right_mem
  -- Shift `graphN d lam` (`1 ≤ d`) to circles `1 .. d` of `graphN (d + 1) lam`
  let shiftVert : GraphNVertex d lam → GraphNVertex (d + 1) lam
    | Sum.inl t => Sum.inl t
    | Sum.inr (i, j) => Sum.inr (i, ⟨j.1 + 1, by have := j.2; omega⟩)
  let shiftEdge : GraphNEdge d lam → GraphNEdge (d + 1) lam
    | Sum.inl e => Sum.inl e
    | Sum.inr (Sum.inl (i, j)) => Sum.inr (Sum.inl (i, ⟨j.1 + 1, by have := j.2; omega⟩))
    | Sum.inr (Sum.inr (i, j)) => Sum.inr (Sum.inr (i, ⟨j.1 + 1, by have := j.2; omega⟩))
  have hshiftVert_inj : Injective shiftVert := by
    rintro (t₁ | ⟨i₁, j₁⟩) (t₂ | ⟨i₂, j₂⟩) h
    · injection h with h'; rw [h']
    · cases h
    · cases h
    · injection h with hp
      obtain ⟨rfl, hj⟩ := Prod.mk.inj hp
      have hj' : j₁ = j₂ := Fin.ext (by have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val hj; omega)
      rw [hj']
  have hshiftEdge_inj : Injective shiftEdge := by
    rintro (e₁ | (⟨i₁, j₁⟩ | ⟨i₁, j₁⟩)) (e₂ | (⟨i₂, j₂⟩ | ⟨i₂, j₂⟩)) h
    · injection h with h'; rw [h']
    · cases h
    · cases h
    · cases h
    · injection h with h1; injection h1 with hp
      obtain ⟨rfl, hj⟩ := Prod.mk.inj hp
      have hj' : j₁ = j₂ := Fin.ext (by have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val hj; omega)
      rw [hj']
    · cases h
    · cases h
    · cases h
    · injection h with h1; injection h1 with hp
      obtain ⟨rfl, hj⟩ := Prod.mk.inj hp
      have hj' : j₁ = j₂ := Fin.ext (by have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val hj; omega)
      rw [hj']
  have hshift_link : ∀ {f₀ : GraphNEdge d lam} {x y : GraphNVertex d lam},
      (graphN d lam).IsLink f₀ x y →
      (graphN (d + 1) lam).IsLink (shiftEdge f₀) (shiftVert x) (shiftVert y) := by
    intro f₀ x y hlf
    rcases f₀ with (t | i) | (⟨i, j⟩ | ⟨i, j⟩)
    · obtain ⟨ht_ne, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hlf
      · exact ⟨ht_ne, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨ht_ne, Or.inr ⟨rfl, rfl⟩⟩
    · have hcIdx : (⟨(⟨max d 1 - 1, by omega⟩ : Fin (max d 1)).1 + 1, by omega⟩ :
          Fin (max (d + 1) 1)) = ⟨max (d + 1) 1 - 1, by omega⟩ :=
        Fin.ext (by dsimp only; omega)
      rcases hlf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, by dsimp only [shiftVert]; rw [hcIdx]⟩
      · exact Or.inr ⟨rfl, by dsimp only [shiftVert]; rw [hcIdx]⟩
    · obtain ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hlf
      · exact ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨by omega, Or.inr ⟨rfl, rfl⟩⟩
    · obtain ⟨_, hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hlf
      · have hs' : j.1 + 1 < max d 1 := hs
        exact ⟨by omega, show j.1 + 1 + 1 < max (d + 1) 1 by omega, Or.inl ⟨rfl, rfl⟩⟩
      · have hs' : j.1 + 1 < max d 1 := hs
        exact ⟨by omega, show j.1 + 1 + 1 < max (d + 1) 1 by omega, Or.inr ⟨rfl, rfl⟩⟩
  have hd1 : 1 ≤ d + 1 := by omega
  let φv : α → Set (GraphNVertex (d + 1) lam) := fun v =>
    if v ∈ V(G_in) then shiftVert '' ηv_in v
    else if hvC : ∃ t : Fin p_out, cyc_out.u t = v then
      circle0ArcSet (d + 1) lam cyc_out.hp b_out hvC.choose
    else ∅
  let φe : β → GraphNEdge (d + 1) lam := fun e =>
    if e ∈ E(G_in) then shiftEdge (ηe_in e)
    else if heC : ∃ t : Fin p_out, cyc_out.ce t = e then
      circle0Edge (d + 1) lam ⟨b_out heC.choose - 1, by have := (hbout_bd heC.choose).2; omega⟩
    else if heA : ∃ r : Fin m, attE r = e then
      Sum.inr (Sum.inr (⟨spk heA.choose, hspk_lt_R heA.choose⟩, ⟨0, by omega⟩))
    else circle0Edge (d + 1) lam ⟨0, by have := three_pow_ge_three lam; omega⟩
  have hφv_in : ∀ v ∈ V(G_in), φv v = shiftVert '' ηv_in v := by
    intro v hv; dsimp only [φv]; split_ifs; rfl
  have hφv_out : ∀ t : Fin p_out,
      φv (cyc_out.u t) = circle0ArcSet (d + 1) lam cyc_out.hp b_out t := by
    intro t
    have hnotIn : cyc_out.u t ∉ V(G_in) :=
      Set.disjoint_right.mp hDisj_V (cyc_out.vertexSet_eq ▸ mem_range_self t)
    dsimp only [φv]
    split_ifs with hex
    · exact congrArg _ (cyc_out.u_inj hex.choose_spec)
    · exact (hex ⟨t, rfl⟩).elim
  have hφe_in : ∀ e ∈ E(G_in), φe e = shiftEdge (ηe_in e) := by
    intro e he; dsimp only [φe]; split_ifs; rfl
  have hφe_out : ∀ t : Fin p_out,
      φe (cyc_out.ce t) = circle0Edge (d + 1) lam ⟨b_out t - 1, by have := (hbout_bd t).2; omega⟩ := by
    intro t
    have hnotIn : cyc_out.ce t ∉ E(G_in) :=
      Set.disjoint_right.mp hEGin_disj_ECout (cyc_out.edgeSet_eq ▸ mem_range_self t)
    dsimp only [φe]
    split_ifs with hex
    · congr 1; apply Fin.ext; dsimp only; rw [cyc_out.ce_inj hex.choose_spec]
    · exact (hex ⟨t, rfl⟩).elim
    · exact (hex ⟨t, rfl⟩).elim
  have hφe_att : ∀ r : Fin m,
      φe (attE r) = Sum.inr (Sum.inr (⟨spk r, hspk_lt_R r⟩, ⟨0, by omega⟩)) := by
    intro r
    have hnotIn : attE r ∉ E(G_in) := Set.disjoint_right.mp hEGin_disj_att (mem_range_self r)
    have hnotOut : ¬ ∃ t : Fin p_out, cyc_out.ce t = attE r := by
      rintro ⟨t, ht⟩
      exact Set.disjoint_left.mp hECout_disj_att
        (ht ▸ cyc_out.edgeSet_eq ▸ mem_range_self t) (mem_range_self r)
    dsimp only [φe]
    split_ifs with hex
    · congr 3; apply Fin.ext; dsimp only; rw [hatt_inj hex.choose_spec]
    · exact (hex ⟨r, rfl⟩).elim
  have hshift_not_c0Vert : ∀ (z : GraphNVertex d lam) (t : Fin p_out),
      shiftVert z ∉ circle0ArcSet (d + 1) lam cyc_out.hp b_out t := by
    intro z t hzC
    have hne_c0 : ∀ w : Fin R, shiftVert z ≠ circle0Vert (d + 1) lam w := by
      rcases z with t₀ | ⟨i₀, j₀⟩ <;> intro w heq <;> unfold circle0Vert at heq <;> cases heq
    unfold circle0ArcSet at hzC
    split_ifs at hzC
    · obtain ⟨w, _, heq⟩ := hzC; exact hne_c0 w heq
    · obtain ⟨w, _, _, heq⟩ := hzC; exact hne_c0 w heq
  have hshift_not_c0Edge : ∀ (f₀ : GraphNEdge d lam) (i : Fin R),
      shiftEdge f₀ ≠ circle0Edge (d + 1) lam i := by
    rintro (e₀ | (⟨i₀, j₀⟩ | ⟨i₀, j₀⟩)) i heq <;> unfold circle0Edge at heq <;> cases heq
  have hshift_not_rad0 : ∀ (f₀ : GraphNEdge d lam) (i : Fin R),
      shiftEdge f₀ ≠ Sum.inr (Sum.inr (i, ⟨0, by omega⟩)) := by
    rintro (e₀ | (⟨i₀, j₀⟩ | ⟨i₀, j₀⟩)) i heq <;> cases heq
  refine ⟨lam, Nat.le_add_right lam₀ κ, hd1, hlam, hCout_le, φv, φe, b_out, ?_,
    hbout_bd, hbout_mono, fun t => by rw [hφv_out t]⟩
  refine isMinorModel_of_loopless_link
    (fun e _ u hl => hSimple.not_isLoopAt e u hl)
    (fun v hv => ?_)
    (fun _ _ => subset_univ _)
    (fun v₁ hv₁ v₂ hv₂ hne => ?_)
    (fun e₁ he₁ e₂ he₂ heq => ?_)
    (fun e u v hl => ?_)
    (fun u hu x hx y hy => ?_)
  · rcases hVG_out ▸ hv with hvIn | hvOut
    · rw [hφv_in v hvIn]
      exact (hm_in.vertex_nonempty v hvIn).image _
    · obtain ⟨t, rfl⟩ := cyc_out.vertexSet_eq ▸ hvOut
      rw [hφv_out t]
      exact circle0ArcSet_nonempty cyc_out.hp hbout_bd hbout_mono t
  · rcases hVG_out ▸ hv₁ with h1In | h1Out <;> rcases hVG_out ▸ hv₂ with h2In | h2Out
    · rw [hφv_in v₁ h1In, hφv_in v₂ h2In, Set.disjoint_left]
      rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
      exact Set.disjoint_left.mp (hm_in.vertex_disjoint v₁ h1In v₂ h2In hne)
        hz₁ ((hshiftVert_inj heq) ▸ hz₂)
    · obtain ⟨t₂, rfl⟩ := cyc_out.vertexSet_eq ▸ h2Out
      rw [hφv_in v₁ h1In, hφv_out t₂, Set.disjoint_left]
      rintro _ ⟨z₁, _, rfl⟩ hzC
      exact hshift_not_c0Vert z₁ t₂ hzC
    · obtain ⟨t₁, rfl⟩ := cyc_out.vertexSet_eq ▸ h1Out
      rw [hφv_out t₁, hφv_in v₂ h2In, Set.disjoint_left]
      rintro _ hzC ⟨z₂, _, rfl⟩
      exact hshift_not_c0Vert z₂ t₁ hzC
    · obtain ⟨t₁, rfl⟩ := cyc_out.vertexSet_eq ▸ h1Out
      obtain ⟨t₂, rfl⟩ := cyc_out.vertexSet_eq ▸ h2Out
      rw [hφv_out t₁, hφv_out t₂]
      exact circle0ArcSet_disjoint cyc_out.hp hbout_mono (fun h => hne (congrArg cyc_out.u h))
  · rcases hEG_out ▸ he₁ with (h1In | h1Out) | ⟨r₁, rfl⟩ <;>
      rcases hEG_out ▸ he₂ with (h2In | h2Out) | ⟨r₂, rfl⟩
    · rw [hφe_in e₁ h1In, hφe_in e₂ h2In] at heq
      exact hm_in.edge_injOn h1In h2In (hshiftEdge_inj heq)
    · obtain ⟨t₂, rfl⟩ := cyc_out.edgeSet_eq ▸ h2Out
      rw [hφe_in e₁ h1In, hφe_out t₂] at heq
      exact (hshift_not_c0Edge _ _ heq).elim
    · rw [hφe_in e₁ h1In, hφe_att r₂] at heq
      exact (hshift_not_rad0 _ _ heq).elim
    · obtain ⟨t₁, rfl⟩ := cyc_out.edgeSet_eq ▸ h1Out
      rw [hφe_out t₁, hφe_in e₂ h2In] at heq
      exact (hshift_not_c0Edge _ _ heq.symm).elim
    · obtain ⟨t₁, rfl⟩ := cyc_out.edgeSet_eq ▸ h1Out
      obtain ⟨t₂, rfl⟩ := cyc_out.edgeSet_eq ▸ h2Out
      rw [hφe_out t₁, hφe_out t₂] at heq
      have hidx := Fin.mk.inj (circle0Edge_inj heq)
      have hbt : b_out t₁ = b_out t₂ := by
        have := (hbout_bd t₁).1; have := (hbout_bd t₂).1; omega
      exact congrArg cyc_out.ce (hbout_mono.injective hbt)
    · obtain ⟨t₁, rfl⟩ := cyc_out.edgeSet_eq ▸ h1Out
      rw [hφe_out t₁, hφe_att r₂] at heq; unfold circle0Edge at heq; cases heq
    · rw [hφe_att r₁, hφe_in e₂ h2In] at heq
      exact (hshift_not_rad0 _ _ heq.symm).elim
    · obtain ⟨t₂, rfl⟩ := cyc_out.edgeSet_eq ▸ h2Out
      rw [hφe_att r₁, hφe_out t₂] at heq; unfold circle0Edge at heq; cases heq
    · rw [hφe_att r₁, hφe_att r₂] at heq
      injection heq with h1; injection h1 with hp
      exact congrArg attE (hspk_mono.injective (Fin.mk.inj (Prod.mk.inj hp).1))
  · rcases hEG_out ▸ hl.edge_mem with (heIn | heOut) | ⟨r, rfl⟩
    · obtain ⟨u', v', hl_in⟩ := G_in.exists_isLink_of_mem_edgeSet heIn
      have hl_uv : G_in.IsLink e u v := by
        rcases hl.left_eq_or_eq (hl_in.mono hGin_le) with rfl | rfl
        · rwa [hl.right_unique (hl_in.mono hGin_le)]
        · rw [hl.right_unique (hl_in.mono hGin_le).symm]; exact hl_in.symm
      have huv : u ≠ v := fun h => hSimple.not_isLoopAt e u (h ▸ hl)
      obtain ⟨x₀, hx₀, y₀, hy₀, hlf₀⟩ := exists_isLink_of_isMinorModel hm_in hl_uv huv
      rw [hφe_in e heIn, hφv_in u hl_uv.left_mem, hφv_in v hl_uv.right_mem]
      exact ⟨shiftVert x₀, mem_image_of_mem _ hx₀, shiftVert y₀, mem_image_of_mem _ hy₀,
        hshift_link hlf₀⟩
    · obtain ⟨t, rfl⟩ := cyc_out.edgeSet_eq ▸ heOut
      have hl_C := (cyc_out.isLink_ce t).mono hCout_le
      obtain ⟨hL, hR⟩ :=
        circle0_divider_endpoints (d := d + 1) (lam := lam) cyc_out.hp hbout_bd hbout_mono t
      have hlink := graphN_isLink_circle0 (d := d + 1) (lam := lam) hd1
        ⟨b_out t - 1, by have := (hbout_bd t).2; omega⟩
      rw [hφe_out t]
      rcases hl.left_eq_or_eq hl_C with rfl | rfl
      · rw [hl.right_unique hl_C, hφv_out t, hφv_out (nextSpoke t)]
        exact ⟨_, hL, _, hR, hlink⟩
      · rw [hl.right_unique hl_C.symm, hφv_out (nextSpoke t), hφv_out t]
        exact ⟨_, hR, _, hL, hlink.symm⟩
    · have hl_r := hatt_link r
      let ir : Fin R := ⟨spk r, hspk_lt_R r⟩
      let s_in : Fin p_in := ⟨(g r).1 % p_in, Nat.mod_lt _ (by have := cyc_in.hp; omega)⟩
      let t_out : Fin p_out := ⟨(f r).1 % p_out, Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩
      have hu_in_mem : cyc_in.u s_in ∈ V(G_in) :=
        hCin_le.vertexSet_mono (cyc_in.vertexSet_eq ▸ mem_range_self s_in)
      have hc0_in : circle0Vert d lam ir ∈ ηv_in (cyc_in.u s_in) :=
        harc_in s_in (hslot_mem_in (g r) (spk r) (hspk_lt_R r) (hspk_bd r).2.1 (hspk_bd r).2.2)
      have hmem_in : Sum.inr (ir, ⟨1, by omega⟩) ∈ φv (cyc_in.u s_in) := by
        rw [hφv_in _ hu_in_mem]
        exact ⟨circle0Vert d lam ir, hc0_in, rfl⟩
      have hmem_out : circle0Vert (d + 1) lam ir ∈ φv (cyc_out.u t_out) := by
        rw [hφv_out t_out]
        exact mem_circle0ArcSet_of_sep cyc_out.hp (hspk_lt_R r) (f r) (hsep r)
      have hl_rad : (graphN (d + 1) lam).IsLink (Sum.inr (Sum.inr (ir, ⟨0, by omega⟩)))
          (circle0Vert (d + 1) lam ir) (Sum.inr (ir, ⟨1, by omega⟩)) :=
        ⟨by omega, by dsimp only; omega, Or.inl ⟨rfl, rfl⟩⟩
      rw [hφe_att r]
      rcases hl.left_eq_or_eq hl_r with rfl | rfl
      · rw [hl.right_unique hl_r]
        exact ⟨_, hmem_in, _, hmem_out, hl_rad.symm⟩
      · rw [hl.right_unique hl_r.symm]
        exact ⟨_, hmem_out, _, hmem_in, hl_rad⟩
  · rcases hVG_out ▸ hu with huIn | huOut
    · rw [hφv_in u huIn] at hx hy ⊢
      obtain ⟨z₁, hz₁, rfl⟩ := hx
      obtain ⟨z₂, hz₂, rfl⟩ := hy
      obtain ⟨K, hK_le, hVK, hK_conn⟩ := hm_in.connected u huIn
      have hrel := hK_conn.2 z₁ (hVK.symm ▸ hz₁) z₂ (hVK.symm ▸ hz₂); clear hz₂
      induction hrel with
      | refl => exact Relation.ReflTransGen.refl
      | @tail a₀ b₀ _ hstep ih_step =>
        obtain ⟨f₀, hlf⟩ := hstep
        have hlf_del : ((graphN d lam).deleteEdges (ηe_in '' E(G_in))).IsLink f₀ a₀ b₀ :=
          hlf.mono hK_le
        rw [Graph.deleteEdges_isLink] at hlf_del
        obtain ⟨hlf_N, hf_not_img⟩ := hlf_del
        have ha_u : a₀ ∈ ηv_in u := hVK ▸ hlf.left_mem
        have hb_u : b₀ ∈ ηv_in u := hVK ▸ hlf.right_mem
        refine Relation.ReflTransGen.tail ih_step ⟨shiftEdge f₀, ?_⟩
        rw [Graph.induce_isLink, Graph.deleteEdges_isLink]
        refine ⟨⟨hshift_link hlf_N, ?_⟩, mem_image_of_mem _ ha_u, mem_image_of_mem _ hb_u⟩
        rintro ⟨e, he, heq⟩
        rcases hEG_out ▸ he with (heIn | heOut) | ⟨r, rfl⟩
        · rw [hφe_in e heIn] at heq
          exact hf_not_img ⟨e, heIn, hshiftEdge_inj heq⟩
        · obtain ⟨t, rfl⟩ := cyc_out.edgeSet_eq ▸ heOut
          rw [hφe_out t] at heq
          exact hshift_not_c0Edge f₀ _ heq.symm
        · rw [hφe_att r] at heq
          exact hshift_not_rad0 f₀ _ heq.symm
    · obtain ⟨t, rfl⟩ := cyc_out.vertexSet_eq ▸ huOut
      rw [hφv_out t] at hx hy ⊢
      refine circle0ArcSet_connected hd1 cyc_out.hp hbout_bd hbout_mono t subset_rfl ?_ hx hy
      intro i hi_nd ⟨e, he, heq⟩
      rcases hEG_out ▸ he with (heIn | heOut) | ⟨r, rfl⟩
      · rw [hφe_in e heIn] at heq
        exact hshift_not_c0Edge _ i heq
      · obtain ⟨s, rfl⟩ := cyc_out.edgeSet_eq ▸ heOut
        rw [hφe_out s] at heq
        exact hi_nd s (Fin.mk.inj (circle0Edge_inj heq)).symm
      · rw [hφe_att r] at heq; unfold circle0Edge at heq; cases heq

end GraphMinor.GM03
