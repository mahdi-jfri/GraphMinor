module

public import GraphMinor.GM08.Section11Order
public import GraphMinor.GM08.Section11Inside
import GraphMinor.GM08.Section9
import GraphMinor.GM11.Walks
import GraphMinor.GM16.DrawingGraphPaths

/-!
# A sleeve of a drawing as sequences

Here we write a sleeve `C_1 ∪ … ∪ C_s ∪ P_1 ∪ … ∪ P_r` for an O-arc `F` of a drawing `Γ*` in the
disc as a `SleeveDraw` (`SleeveData.exists_sleeveDraw`), so that the contraction onto the cylinder
of `GraphMinor/GM08/Section11Contract.lean` applies to it.

The circuits and the radial paths become sequences of vertices and edges. Two facts need a
proof.

* `P_i` meets `C_j` before it meets a later circuit `C_{j'}` (`SleeveSeq.level`). After its first
  vertex on `C_{j'}`, the path `P_i` stays on `C_{j'}` for a while, since `P_i ∩ C_{j'}` is a path,
  and after that it never comes back to `C_{j'}`. So from then on it stays on one side of
  `C_{j'}`, the side of its end on `F`, which is outside `C_{j'}`. But `C_j` is inside `C_{j'}`.
* `P_i ∩ C_j` is an interval of `C_j` (`SleeveSeq.arc`), since it is a path of `C_j`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Graph Surface GM11 GM06

universe u

variable {S : Type u} [TopologicalSpace S]

/-- No point of `F` is inside `F`. -/
theorem not_insideOArc_self {Δ F : Set S} {x : S} (hx : x ∈ F) : ¬ InsideOArc Δ F x := by
  rintro ⟨D, hD, hxD⟩
  exact hxD.2 (hD.2.2.1 ▸ hx)

/-- A drawing path is connected as a graph. -/
theorem Drawing.IsPathBetween.isGraphConnected {P : Drawing S} {a b : S}
    (h : P.IsPathBetween a b) : IsGraphConnected P.toGraph :=
  (GM16.graphPath_of_drawingPath (H := P) ⟨subset_rfl, subset_rfl⟩ h).isGraphConnected

/-! ## Circuits and paths as sequences -/

/-- A link of a subdrawing with both ends in `W` is a link of the graph of `D₀` induced on `W`. -/
theorem isLink_induce_of_sub {C D₀ : Drawing S} (hsub : C.IsSubdrawing D₀) {W : Set S}
    (hW : C.V ⊆ W) {e : Set S} {x y : S} (h : C.toGraph.IsLink e x y) :
    (D₀.toGraph.induce W).IsLink e x y :=
  ⟨(hsub.isLink_iff h.edge_mem).mp h, hW h.left_mem, hW h.right_mem⟩

/-- A circuit is a sequence of vertices and edges of period `n`. -/
theorem exists_circuit_seq {C D₀ : Drawing S} (hC : C.IsCircuit) (hsub : C.IsSubdrawing D₀)
    {W : Set S} (hW : C.V ⊆ W) :
    ∃ (n : ℕ) (c : ℕ → S) (ε : ℕ → Set S), 0 < n ∧ (∀ x, c (x % n) = c x) ∧
      (∀ x, ε (x % n) = ε x) ∧ (∀ x, (D₀.toGraph.induce W).IsLink (ε x) (c x) (c (x + 1))) ∧
      (∀ x y, x < n → y < n → c x = c y → x = y) ∧ (∀ x y, x < n → y < n → ε x = ε y → x = y) ∧
      (∀ u, u ∈ C.V ↔ ∃ x, c x = u) ∧ (∀ e, e ∈ C.E ↔ ∃ x, ε x = e) := by
  obtain ⟨u, Wk, ⟨htail, hedge⟩, hpos, hV, hE⟩ := hC
  obtain ⟨c', ε', hc0, hcn, hlink, hsupp, hedges, htinj, -, heinj⟩ := GraphWalk.exists_seq Wk
  have hcn' : c' Wk.length = c' 0 := hcn.trans hc0.symm
  refine ⟨Wk.length, fun x => c' (x % Wk.length), fun x => ε' (x % Wk.length), hpos,
    fun x => by simp only [Nat.mod_mod], fun x => by simp only [Nat.mod_mod], fun x => ?_,
    fun x y hx hy h => ?_, fun x y hx hy h => ?_, fun v => ?_, fun e => ?_⟩
  · have hk := Nat.mod_lt x hpos
    have hl := hlink (x % Wk.length) hk
    have hsucc : c' (x % Wk.length + 1) = c' ((x + 1) % Wk.length) := by
      rw [← Nat.mod_add_mod]
      rcases Nat.lt_or_ge (x % Wk.length + 1) Wk.length with h | h
      · rw [Nat.mod_eq_of_lt h]
      · rw [show x % Wk.length + 1 = Wk.length by omega, Nat.mod_self, hcn']
    show (D₀.toGraph.induce W).IsLink (ε' (x % Wk.length)) (c' (x % Wk.length))
      (c' ((x + 1) % Wk.length))
    rw [← hsucc]
    exact isLink_induce_of_sub hsub hW hl
  · simp only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
    -- Moving the position `0` to `n` does not change the vertex.
    have hfc : ∀ z, c' (if z = 0 then Wk.length else z) = c' z := fun z => by
      split_ifs with h0
      · rw [h0, hcn']
      · rfl
    have := htinj htail (if x = 0 then Wk.length else x) (if y = 0 then Wk.length else y)
      (by split_ifs <;> omega) (by split_ifs <;> omega) (by split_ifs <;> omega)
      (by split_ifs <;> omega) (by rw [hfc, hfc, h])
    split_ifs at this <;> omega
  · simp only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
    exact heinj hedge x y hx hy h
  · rw [hV]
    show v ∈ Wk.support ↔ _
    rw [hsupp]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases eq_or_lt_of_le hk with h | h
      · exact ⟨0, by show c' (0 % Wk.length) = _; rw [Nat.zero_mod, h, hcn']⟩
      · exact ⟨k, by show c' (k % Wk.length) = _; rw [Nat.mod_eq_of_lt h]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (Nat.mod_lt x hpos).le, rfl⟩
  · rw [hE]
    show e ∈ Wk.edges ↔ _
    rw [hedges]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, by show ε' (k % Wk.length) = _; rw [Nat.mod_eq_of_lt hk]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, Nat.mod_lt x hpos, rfl⟩

/-- A path is a sequence of distinct vertices with edges between consecutive ones. -/
theorem exists_path_seq {P D₀ : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hsub : P.IsSubdrawing D₀) {W : Set S} (hW : P.V ⊆ W) :
    ∃ (len : ℕ) (d : ℕ → S) (δ : ℕ → Set S), d 0 = a ∧ d len = b ∧
      (∀ k < len, (D₀.toGraph.induce W).IsLink (δ k) (d k) (d (k + 1))) ∧
      (∀ k k', k ≤ len → k' ≤ len → d k = d k' → k = k') ∧
      (∀ u, u ∈ P.V ↔ ∃ k ≤ len, d k = u) ∧ (∀ e, e ∈ P.E ↔ ∃ k < len, δ k = e) := by
  obtain ⟨Wk, hsimp, hV, hE⟩ := hP
  obtain ⟨d, δ, hd0, hdn, hlink, hsupp, hedges, -, hinj, -⟩ := GraphWalk.exists_seq Wk
  refine ⟨Wk.length, d, δ, hd0, hdn, fun k hk => isLink_induce_of_sub hsub hW (hlink k hk),
    hinj hsimp, fun u => ?_, fun e => ?_⟩
  · rw [hV]
    exact hsupp u
  · rw [hE]
    exact hedges e

/-! ## Paths of a path and of a circuit are intervals -/

/-- A connected subdrawing `Q` whose edges are edges of a path `d 0, …, d len` has its vertices at
consecutive positions of the path. -/
theorem mem_of_between_path {D₀ Q : Drawing S} (hQ : Q.IsSubdrawing D₀)
    (hQc : IsGraphConnected Q.toGraph) {len : ℕ} {d : ℕ → S} {δ : ℕ → Set S}
    (hlink : ∀ k < len, D₀.toGraph.IsLink (δ k) (d k) (d (k + 1)))
    (hinj : ∀ k k', k ≤ len → k' ≤ len → d k = d k' → k = k')
    (hQE : ∀ e ∈ Q.E, ∃ k < len, δ k = e)
    {h k m : ℕ} (hhk : h < k) (hkm : k < m) (hm : m ≤ len) (hh : d h ∈ Q.V) (hmQ : d m ∈ Q.V) :
    d k ∈ Q.V := by
  by_contra hk
  obtain ⟨W⟩ := hQc.2 _ hmQ _ hh
  have hstep : ∀ e a a' x, Q.toGraph.IsLink e a a' → (x ≤ len ∧ d x = a) →
      (x + 1 ≤ len ∧ d (x + 1) = a') ∨ (0 < x ∧ (x - 1 ≤ len ∧ d (x - 1) = a')) := by
    rintro e a a' x hl ⟨hx, hxa⟩
    have he : e ∈ Q.E := hl.edge_mem
    obtain ⟨m', hm', rfl⟩ := hQE e he
    have hl' := (hQ.isLink_iff he).mp hl
    rcases hl'.eq_and_eq_or_eq_and_eq (hlink m' hm') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hinj x m' hx hm'.le (hxa.trans h1)
      subst this
      exact Or.inl ⟨by omega, h2.symm⟩
    · have := hinj x (m' + 1) hx (by omega) (hxa.trans h1)
      subst this
      exact Or.inr ⟨by omega, by omega, by simpa using h2.symm⟩
  obtain ⟨x', h1, -, h2, h3⟩ := exists_pos_of_walk (Q := Q.toGraph)
    (fun x a => x ≤ len ∧ d x = a) hstep (z := k) (y := len + 1)
    (fun a ha h => hk (h.2 ▸ ha)) (fun a _ h => by have := h.1; omega) W hkm (by omega) ⟨hm, rfl⟩
  have := hinj _ _ h2 (by omega) h3
  omega

/-- A connected subdrawing `Q` whose edges are edges of a circuit `c` (of period `n`) is an
interval of the circuit: if it has a vertex at a position strictly between two positions `z < y`
that carry no vertex of `Q`, then every vertex of `Q` is at a position strictly between them. -/
theorem exists_between_circuit {D₀ Q : Drawing S} (hQ : Q.IsSubdrawing D₀)
    (hQc : IsGraphConnected Q.toGraph) {n : ℕ} {c : ℕ → S} {ε : ℕ → Set S} (hn : 0 < n)
    (hper : ∀ x, c (x % n) = c x) (hlink : ∀ x, D₀.toGraph.IsLink (ε x) (c x) (c (x + 1)))
    (hinj : ∀ x y, x < n → y < n → c x = c y → x = y) (hQE : ∀ e ∈ Q.E, ∃ x, ε x = e)
    {z y : ℕ} (hz : c z ∉ Q.V) (hy : c y ∉ Q.V) {x : ℕ} (hzx : z < x) (hxy : x < y)
    (hx : c x ∈ Q.V) {u : S} (hu : u ∈ Q.V) : ∃ x'', z < x'' ∧ x'' < y ∧ c x'' = u := by
  obtain ⟨W⟩ := hQc.2 _ hx _ hu
  have hstep : ∀ e a a' x', Q.toGraph.IsLink e a a' → (z < x' ∧ c x' = a) →
      (z < x' + 1 ∧ c (x' + 1) = a') ∨ (0 < x' ∧ (z < x' - 1 ∧ c (x' - 1) = a')) := by
    rintro e a a' x' hl ⟨hzx', hxa⟩
    have he : e ∈ Q.E := hl.edge_mem
    obtain ⟨w, rfl⟩ := hQE e he
    have hl' := (hQ.isLink_iff he).mp hl
    rcases hl'.eq_and_eq_or_eq_and_eq (hlink w) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hm : x' % n = w % n := seq_mod_eq_of_eq hn hper hinj (hxa.trans h1)
      exact Or.inl ⟨by omega, (seq_mod_eq hper (Nat.ModEq.add_right 1 hm)).trans h2.symm⟩
    · have hm : (x' - 1 + 1) % n = (w + 1) % n := by
        rw [show x' - 1 + 1 = x' by omega]
        exact seq_mod_eq_of_eq hn hper hinj (hxa.trans h1)
      have hc : c (x' - 1) = a' :=
        (seq_mod_eq hper (Nat.ModEq.add_right_cancel' 1 hm)).trans h2.symm
      refine Or.inr ⟨by omega, ?_, hc⟩
      by_contra hle
      have : x' - 1 = z := by omega
      rw [this] at hc
      exact hz (hc ▸ hl.right_mem)
  obtain ⟨x'', h1, h2, -, h3⟩ := exists_pos_of_walk (Q := Q.toGraph)
    (fun x a => z < x ∧ c x = a) hstep (z := z) (y := y) (fun a _ h => by have := h.1; omega)
    (fun a ha h => hy (h.2 ▸ ha)) W hzx hxy ⟨hzx, rfl⟩
  exact ⟨x'', h1, h2, h3⟩

/-! ## A path from inside a circuit to outside it -/

/-- Let `C` bound a closed disc `Δ` of the disc `S`, and let `Q` be the part of a path
`d 0, …, d len` on `C`, connected. If the path ends outside `Δ`, then a vertex `d k` inside `Δ`
comes before every vertex `d h` on `C`. The reason: after `d h` the path stays on `C` for a while,
and once it leaves `C` it does not come back, so it stays on the side of its end. -/
theorem lt_of_mem_discInt [T2Space S] (hS : IsClosedDisc (univ : Set S)) {D₀ C Q : Drawing S}
    (hC : C.IsSubdrawing D₀) {Δ : Set S} (hΔ : IsClosedDisc Δ) (hbd : discBd Δ = C.U)
    (hQ : Q.IsSubdrawing D₀) (hQc : IsGraphConnected Q.toGraph) {len : ℕ} {d : ℕ → S}
    {δ : ℕ → Set S} (hlink : ∀ k < len, D₀.toGraph.IsLink (δ k) (d k) (d (k + 1)))
    (hinj : ∀ k k', k ≤ len → k' ≤ len → d k = d k' → k = k')
    (hQV : ∀ k ≤ len, d k ∈ C.V → d k ∈ Q.V) (hQC : Q.V ⊆ C.V)
    (hQE : ∀ e ∈ Q.E, ∃ k < len, δ k = e) (hend : d len ∉ Δ) {h k : ℕ} (hh : h ≤ len)
    (hhC : d h ∈ C.V) (hk : k ≤ len) (hkin : d k ∈ discInt Δ) : k < h := by
  have hkC : d k ∉ C.V := fun h' => hkin.2 (hbd ▸ C.V_subset_U h')
  by_contra hkh
  have hhk : h < k := by
    rcases eq_or_lt_of_le (not_lt.mp hkh) with h' | h'
    · exact absurd (h' ▸ hhC) hkC
    · exact h'
  by_cases hex : ∃ m, k < m ∧ m ≤ len ∧ d m ∈ C.V
  · obtain ⟨m, hkm, hm, hmC⟩ := hex
    exact hkC (hQC (mem_of_between_path hQ hQc hlink hinj hQE hhk hkm hm (hQV h hh hhC)
      (hQV m hm hmC)))
  · push Not at hex
    have key := seq_mem_disc hS hC hΔ hbd (fun m => d (k + m)) (fun m => δ (k + m)) (len - k)
      (fun m hm => hlink (k + m) (by omega)) hkin.1 (fun m hm => by
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · exact hkC
        · exact hex (k + m) (by omega) (by omega))
    have := (key (len - k) le_rfl).1
    simp only [show k + (len - k) = len by omega] at this
    exact hend this

/-! ## The discs of the circuits of a sleeve -/

/-- Every point of the disc bounded by a circuit of a sleeve for `F` is inside `F`. -/
theorem SleeveData.insideOArc_of_mem_ins (hS : IsClosedDisc (univ : Set S)) {Γ : Drawing S}
    {F : Set S} (sd : SleeveData Γ univ F) (j : Fin (((Γ.V ∩ F).ncard + 1) / 2)) {x : S}
    (hx : x ∈ (sd.nest.circuit j).ins) : InsideOArc univ F x := by
  have hins := (sd.nest.circuit j).isInside
  by_cases hb : x ∈ discBd (sd.nest.circuit j).ins
  · exact sd.circuit_inside j x (hins.2.2.1 ▸ hb)
  · obtain ⟨e⟩ := (sd.nest.circuit j).isOArc_U
    obtain ⟨DF, hDF, -⟩ := sd.circuit_inside j _ (e 1).2
    have := (insideDisc_subset_of_oArcEncloses hS hDF hins
      (fun z hz => sd.circuit_inside j z hz.1)).2 ⟨hx, hb⟩
    exact ⟨DF, hDF, this⟩

/-! ## The sleeve as a `SleeveDraw` -/

/-- **A sleeve of a drawing in the disc, written as sequences.** Let `Γ*` contain a sleeve for `F`
whose vertices are in a set `W` of vertices of `Γ*`. Then the sleeve gives a `SleeveDraw` in the
graph of `Γ*` induced on `W`, whose radial paths and circuits are those of the sleeve. -/
theorem SleeveData.exists_sleeveDraw [T2Space S] (hS : IsClosedDisc (univ : Set S))
    {Γ Dstar : Drawing S} {F : Set S} (sd : SleeveData Γ univ F)
    (hcirc : ∀ j, (sd.circuitDraw j).IsSubdrawing Dstar)
    (hspoke : ∀ i, (sd.spoke i).IsSubdrawing Dstar) {W : Set S} (hWD : W ⊆ Dstar.V)
    (hsW : ∀ x ∈ (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V), x ∈ W) :
    ∃ L : SleeveDraw Dstar W (Γ.V ∩ F).ncard (((Γ.V ∩ F).ncard + 1) / 2),
      (∀ i k, k ≤ L.len i → L.d i k ∈ (sd.spoke i).V) ∧ (∀ i, L.d i (L.len i) ∈ Γ.V ∩ F) ∧
      (∀ i k, k < L.len i → L.d i k ∉ F) ∧ (∀ j x, L.c j x ∈ (sd.circuitDraw j).V) := by
  classical
  have hcircW : ∀ j, (sd.circuitDraw j).V ⊆ W := fun j x hx =>
    hsW x (Or.inl (mem_iUnion.mpr ⟨j, hx⟩))
  have hspokeW : ∀ i, (sd.spoke i).V ⊆ W := fun i x hx =>
    hsW x (Or.inr (mem_iUnion.mpr ⟨i, hx⟩))
  choose n c ε hn hcper hεper hclink hcinj hεinj hCV hCE using fun j =>
    exists_circuit_seq (sd.isCircuit_draw j).2.1 (hcirc j) (hcircW j)
  choose hs u v hsub hu hvF hpath henc hVF using sd.isPath_spoke
  choose len d δ hd0 hdl hdlink hdinj hPV hPE using fun i =>
    exists_path_seq (hpath i) (hspoke i) (hspokeW i)
  choose Q qa qb hQsub hQV hQE hQpath using sd.inter_isPath
  -- The circuits are pairwise disjoint.
  have hCdisj : ∀ j j', j ≠ j' → Disjoint (sd.circuitDraw j).V (sd.circuitDraw j').V := by
    have key : ∀ j j', j < j' → Disjoint (sd.circuitDraw j).V (sd.circuitDraw j').V := by
      intro j j' hlt
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      have hxU : x ∈ (sd.nest.circuit j).U :=
        (sd.isCircuit_draw j).2.2 ▸ (sd.circuitDraw j).V_subset_U hx
      have hxU' : x ∈ (sd.nest.circuit j').U :=
        (sd.isCircuit_draw j').2.2 ▸ (sd.circuitDraw j').V_subset_U hx'
      exact not_insideOArc_self hxU' (sd.nest.inside_of_lt hlt x hxU)
    intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' h
    · exact (key j' j h).symm
  have hcmem : ∀ j x, c j x ∈ (sd.circuitDraw j).V := fun j x => (hCV j _).mpr ⟨x, rfl⟩
  have hdmem : ∀ i k, k ≤ len i → d i k ∈ (sd.spoke i).V := fun i k hk =>
    (hPV i _).mpr ⟨k, hk, rfl⟩
  have hQsub' : ∀ i j, (Q i j).IsSubdrawing Dstar := fun i j =>
    ⟨fun x hx => (hspoke i).1 ((hQV i j).subset hx).1,
      fun e he => (hspoke i).2 ((hQE i j).subset he).1⟩
  have hQc : ∀ i j, IsGraphConnected (Q i j).toGraph := fun i j =>
    Drawing.IsPathBetween.isGraphConnected (hQpath i j)
  have hQmem : ∀ i j u, u ∈ (Q i j).V ↔ u ∈ (sd.spoke i).V ∧ u ∈ (sd.circuitDraw j).V :=
    fun i j u => by rw [hQV i j]; rfl
  -- Every radial path meets every circuit.
  have hex : ∀ i j, ∃ k, k ≤ len i ∧ ∃ x, c j x = d i k := by
    intro i j
    obtain ⟨Wq, -, hVq, -⟩ := hQpath i j
    have hq : qa i j ∈ (Q i j).V := hVq ▸ Wq.start_mem_support
    obtain ⟨h1, h2⟩ := (hQmem i j _).mp hq
    obtain ⟨k, hk, hkq⟩ := (hPV i _).mp h1
    obtain ⟨x, hx⟩ := (hCV j _).mp h2
    exact ⟨k, hk, x, hx.trans hkq.symm⟩
  -- The discs of the circuits.
  have hΔbd : ∀ j, discBd (sd.nest.circuit j).ins = (sd.circuitDraw j).U := fun j =>
    (sd.nest.circuit j).isInside.2.2.1.trans (sd.isCircuit_draw j).2.2.symm
  have hΔlt : ∀ j j', j < j' → (sd.nest.circuit j).ins ⊆ discInt (sd.nest.circuit j').ins :=
    fun j j' h => DrawingNest.insideDisc_subset_discInt_of_lt hS sd.nest h
  have hend : ∀ i j, d i (len i) ∉ (sd.nest.circuit j).ins := fun i j h =>
    not_insideOArc_self (by rw [hdl]; exact hvF i) (sd.insideOArc_of_mem_ins hS j h)
  have hvd : ∀ i, d i (len i) ∈ (sd.spoke i).V ∩ F := fun i => by
    rw [hVF i, hdl]
    rfl
  refine ⟨{
    n := n
    n_pos := hn
    c := c
    ε := ε
    c_mod := hcper
    c_link := hclink
    c_inj := hcinj
    c_disj := fun j j' x y hne h =>
      Set.disjoint_left.mp (hCdisj j j' hne) (hcmem j x) (h ▸ hcmem j' y)
    len := len
    d := d
    δ := δ
    d_mem := fun i k hk => hspokeW i (hdmem i k hk)
    d_link := hdlink
    d_inj := hdinj
    d_disj := fun i i' k k' hne hk hk' h =>
      Set.disjoint_left.mp (sd.pairwise_disjoint_spokes hne) (hdmem i k hk) (h ▸ hdmem i' k' hk')
    hit := fun i j => Nat.find (hex i j)
    hit_le := fun i j => (Nat.find_spec (hex i j)).1
    hit_mem := fun i j => (Nat.find_spec (hex i j)).2
    hit_min := fun i j k hk x hx =>
      Nat.find_min (hex i j) hk ⟨hk.le.trans (Nat.find_spec (hex i j)).1, x, hx⟩
    level := fun i j j' k x hk hkx hjj' => by
      obtain ⟨hh, x', hx'⟩ := Nat.find_spec (hex i j')
      refine lt_of_mem_discInt hS (hcirc j') (sd.nest.circuit j').isInside.2.1 (hΔbd j')
        (hQsub' i j') (hQc i j') (fun k hk => (hdlink i k hk).1) (hdinj i)
        (fun k hk hkC => (hQmem i j' _).mpr ⟨hdmem i k hk, hkC⟩)
        (fun u hu => ((hQmem i j' u).mp hu).2)
        (fun e he => (hPE i e).mp ((hQE i j').subset he).1) (hend i j') hh
        (hx' ▸ hcmem j' x') hk ?_
      have hU : d i k ∈ discBd (sd.nest.circuit j).ins := by
        rw [hΔbd, hkx]
        exact (sd.circuitDraw j).V_subset_U (hcmem j x)
      exact hΔlt j j' hjj' (Surface.discBd_subset _ hU)
    arc := fun i j z y hzy hz hy x hzx hxy hx x' k' hk' hk'x => by
      have hnot : ∀ w, (∀ k ≤ len i, d i k ≠ c j w) → c j w ∉ (Q i j).V := by
        intro w hw hwQ
        obtain ⟨k, hk, hkw⟩ := (hPV i _).mp ((hQmem i j _).mp hwQ).1
        exact hw k hk hkw
      have hin : ∀ w, (∃ k ≤ len i, d i k = c j w) → c j w ∈ (Q i j).V := by
        rintro w ⟨k, hk, hkw⟩
        exact (hQmem i j _).mpr ⟨hkw ▸ hdmem i k hk, hcmem j w⟩
      exact exists_between_circuit (hQsub' i j) (hQc i j) (hn j) (hcper j)
        (fun x => (hclink j x).1) (hcinj j)
        (fun e he => (hCE j e).mp ((hQE i j).subset he).2) (hnot z hz) (hnot y hy) hzx hxy
        (hin x hx) (hin x' ⟨k', hk', hk'x⟩)
    W_sub := hWD
    ε_mod := hεper
    ε_inj := hεinj
    C := sd.circuitDraw
    C_sub := hcirc
    C_V := hCV
    C_E := hCE
    Δ := fun j => (sd.nest.circuit j).ins
    Δ_disc := fun j => (sd.nest.circuit j).isInside.2.1
    Δ_bd := hΔbd
    Δ_lt := hΔlt
    d_start := fun i j hj => by
      have hj' : j = ⟨0, hs i⟩ := Fin.ext hj
      subst hj'
      have hd0V : d i 0 ∈ (sd.spoke i).V := hdmem i 0 (Nat.zero_le _)
      have hU : d i 0 ∈ (sd.circuitDraw ⟨0, hs i⟩).U := by
        rw [(sd.isCircuit_draw _).2.2, hd0]
        exact hu i
      obtain ⟨x, hx⟩ := (hCV _ _).mp (mem_V_of_mem_U (hcirc _) hU ((hspoke i).1 hd0V))
      exact ⟨x, hx.symm⟩
    Q := Q
    Q_sub := hQsub'
    Q_V := fun i j u => (hQmem i j u).trans (and_congr (hPV i u) (hCV j u))
    Q_E := fun i j e he => ((hQE i j).subset he).2
    Q_path := fun i j => ⟨_, _, hQpath i j⟩ }, hdmem, fun i => ?_, fun i k hk hkF => ?_, hcmem⟩
  · exact ⟨(hsub i).1 (hvd i).1, (hvd i).2⟩
  · replace hk : k < len i := hk
    have hk' : d i k ∈ (sd.spoke i).V ∩ F := ⟨hdmem i k hk.le, hkF⟩
    rw [hVF i] at hk'
    have hk'' : d i k = d i (len i) := by rw [hdl]; exact hk'
    have := hdinj i k (len i) hk.le le_rfl hk''
    omega

end GM08
end GraphMinor
