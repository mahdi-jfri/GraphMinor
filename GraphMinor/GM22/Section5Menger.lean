module

public import GraphMinor.GM07.SideDisc
public import GraphMinor.GM07.CylinderPaths
public import GraphMinor.GM07.CuffGrid
public import GraphMinor.GM22.Section4Sleeve

/-!
# Menger's Theorem Across a Disc with Circuit Outer Boundary (GM22 Section 5)

In Graph Minors XXII, (5.3) Claim (5) (page 541), Menger's theorem is applied to the cylinder
`S_i \ discInt (ins(F_i))` inside a closed disc `S_i ⊆ Σ` bounded by a circuit `C_i` of `Γ`, where
`F_i = discBd (ins(F_i))` is a `Γ`-normal `O`-arc. Here we adapt `GM07.exists_disc_of_side`,
`GM07.exists_cylinder_paths`, and `GM07.exists_disc_grid` so that the separator disc `B` in the
sphere satisfies `discBd B ∩ D₂ ⊆ X ⊆ Γ.V`, ensuring that `discBd (ρ '' B)` meets `subBd S_i = C_i.U`
only at vertices of `Γ` and is therefore `Γ`-normal on all of `Σ`.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.deprecated false

namespace GraphMinor.GM22

open Set Topology Metric Function Graph GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11

local notation "I" => unitInterval

variable {T : Type} [TopologicalSpace T] [T2Space T]

/-- `GM07.exists_disc_of_side` together with `discBd B ∩ E₀ ⊆ X` (from `hbdY` in the proof of
`GM07.exists_disc_of_side`). -/
theorem exists_disc_of_side_with_bd (hS : IsClosedSurface T) (hsph : IsSphere T) (Γ : Drawing T)
    {B₀ E₀ X K : Set T} (hB₀ : IsClosedDisc B₀) (hE₀ : IsClosedDisc E₀) (hd : Disjoint B₀ E₀)
    (hbd : Γ.U ∩ discBd B₀ ⊆ Γ.V) (hint : Disjoint Γ.U (discInt B₀))
    (hEU : Γ.U ∩ E₀ ⊆ Γ.V) (hEint : Disjoint Γ.U (discInt E₀))
    (hKV : K ⊆ Γ.V) (hXV : X ⊆ Γ.V) (hXK : Disjoint X K)
    (hcuff : Γ.V ∩ discBd B₀ ⊆ K ∪ X) (hKE : Disjoint K E₀)
    (hedge : ∀ e ∈ Γ.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ Γ.V, w ∈ closure e → w ∈ K ∪ X)
    {ρ : T → ℕ}
    (hreach : ∀ u ∈ K, u ∉ discBd B₀ →
      ∃ e ∈ Γ.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e ∧ (w ∉ discBd B₀ → ρ w < ρ u)) :
    ∃ B, IsClosedDisc B ∧ B₀ ⊆ B ∧ Disjoint (discInt E₀) B ∧
      discBd B ∩ Γ.U ⊆ X ∧ discBd B ∩ E₀ ⊆ X := by
  classical
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  by_cases hA : (Γ.V ∩ discBd B₀).Nonempty
  swap
  · refine ⟨B₀, hB₀, Subset.rfl, hd.symm.mono_left fun x hx => hx.1, fun x hx => ?_, fun x hx => ?_⟩
    · exact absurd ⟨x, hbd ⟨hx.2, hx.1⟩, hx.1⟩ hA
    · exact (disjoint_left.mp hd (Surface.discBd_subset B₀ hx.1) hx.2).elim
  obtain ⟨D, hDU, hDV⟩ :=
    exists_drawing_on_oArc hB₀.isOArc_discBd (Γ.finite_V.subset inter_subset_left) hA inter_subset_right
  have hmeet : Γ.U ∩ D.U ⊆ Γ.V ∩ D.V := fun x hx => by
    have hx2 : x ∈ discBd B₀ := hDU ▸ hx.2
    have hxV := hbd ⟨hx.1, hx2⟩
    exact ⟨hxV, hDV ▸ ⟨hxV, hx2⟩⟩
  have hE₁ : Γ.E ⊆ (Γ.glue D hmeet).E := by
    rw [Drawing.glue_E]
    exact subset_union_left
  have hD₁ : D.E ⊆ (Γ.glue D hmeet).E := by
    rw [Drawing.glue_E]
    exact subset_union_right
  have hV₁ : Γ.V ⊆ (Γ.glue D hmeet).V := subset_union_left
  have hDV₁ : D.V ⊆ (Γ.glue D hmeet).V := subset_union_right
  have hB₀V : ∀ x ∈ Γ.U, x ∈ B₀ → x ∈ discBd B₀ ∧ x ∈ Γ.V := fun x hx h => by
    have h1 : x ∈ discBd B₀ := by
      by_contra hn
      exact disjoint_left.mp hint hx ⟨h, hn⟩
    exact ⟨h1, hbd ⟨hx, h1⟩⟩
  have hclV : ∀ g ∈ Γ.E, ∀ x ∈ closure g, x ∉ Γ.V → x ∈ g := fun g hg x hx hn => by
    obtain ⟨c, h1, h2, h3, h4, h5⟩ := exists_edge_param Γ hg
    have hc : EdgeParam Γ g c := ⟨h1, h2, h3, h4, h5⟩
    rw [hc.closure_eq] at hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨h6, h7⟩ := hc.pos_of_ne hg hn
    exact hc.mem_edge h6 h7
  have hclU : ∀ g ∈ Γ.E, closure g ⊆ Γ.U :=
    fun g hg => closure_minimal (fun x hx => (hg.2.1 hx).1) Γ.isClosed_U
  let 𝓔 : Set (Set T) := {e ∈ Γ.E | ∃ u ∈ K, u ∈ closure e}
  have h𝓔 : 𝓔.Finite := Γ.finite_edges.subset (sep_subset _ _)
  have hor : ∀ e ∈ 𝓔, ∃ c, EdgeParam Γ e c ∧ c 0 ∈ K := fun e he => by
    obtain ⟨u, hu, huc⟩ := he.2
    obtain ⟨c, h1, h2⟩ := EdgeParam.exists_orient he.1 huc (hKV hu)
    exact ⟨c, h1, h2 ▸ hu⟩
  haveI : Nonempty (I → T) := ⟨fun _ => hA.some⟩
  choose! γ hγ hγK using hor
  have hzex : ∀ v : T, ∃ z ∈ discBd B₀, z ≠ v := fun v => hB₀.isOArc_discBd.exists_ne v
  choose z hz hzv using hzex
  have hq1 : quarter₂ < (1 : I) := unitInterval.lt_one_iff_ne_one.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [quarter₂] at h1
  have hq0 : (0 : I) < quarter₂ := unitInterval.pos_iff_ne_zero.mpr fun e => by
    have h1 := congrArg Subtype.val e
    norm_num [quarter₂] at h1
  let P : T → Set T := fun v =>
    (Γ.V \ {v}) ∪ (⋃ e ∈ {e ∈ Γ.E | v ∉ closure e}, closure e) ∪
      ((fun e => γ e quarter₂) '' 𝓔) ∪ E₀ ∪ (if v ∈ discBd B₀ then {z v} else B₀)
  have hPc : ∀ v ∈ K, IsClosed (P v) := fun v _ => by
    refine (((((Γ.finite_V.subset sdiff_subset).isClosed).union
      ((Γ.finite_edges.subset (sep_subset _ _)).isClosed_biUnion fun e _ => isClosed_closure)).union
      (h𝓔.image _).isClosed).union hE₀.isClosed).union ?_
    split_ifs
    · exact isClosed_singleton
    · exact hB₀.isClosed
  have hvP : ∀ v ∈ K, v ∉ P v := fun v hv => by
    rintro ((((h | h) | ⟨e, he, h⟩) | h) | h)
    · exact h.2 rfl
    · obtain ⟨e, he, h1⟩ := mem_iUnion₂.mp h
      exact he.2 h1
    · have h' : γ e quarter₂ = v := h
      exact (hγ e he).not_V he.1 hq0 hq1 (h'.symm ▸ hKV hv)
    · exact disjoint_left.mp hKE hv h
    · split_ifs at h with h2
      · exact hzv v h.symm
      · exact h2 (hB₀V v (Γ.V_subset_U (hKV hv)) h).1
  obtain ⟨R, hR, hRd⟩ := exists_star_family hS (Γ.glue D hmeet) (hKV.trans hV₁) hPc hvP
  have hRP : ∀ v ∈ K, ∀ x ∈ R v, x ∉ P v :=
    fun v hv x hx h => disjoint_left.mp (hR v hv).2 hx h
  have hoffV : ∀ v ∈ K, ∀ w ∈ Γ.V, w ≠ v → w ∉ R v :=
    fun v hv w hw hne h => hRP v hv w h (.inl (.inl (.inl (.inl ⟨hw, hne⟩))))
  have hcloff : ∀ v ∈ K, ∀ e ∈ Γ.E, v ∉ closure e → Disjoint (R v) (closure e) :=
    fun v hv e he hn => disjoint_left.mpr fun x hx h =>
      hRP v hv x hx (.inl (.inl (.inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hn⟩, h⟩)))))
  have hRE : ∀ v ∈ K, Disjoint (R v) E₀ :=
    fun v hv => disjoint_left.mpr fun x hx h => hRP v hv x hx (.inl (.inr h))
  have hRB₀ : ∀ v ∈ K, v ∉ discBd B₀ → Disjoint (R v) B₀ :=
    fun v hv hn => disjoint_left.mpr fun x hx h => hRP v hv x hx (.inr (by rwa [if_neg hn]))
  have hpiece : ∀ e ∈ 𝓔, ∃ L a b, IsPiece Γ K X R e L a b (γ e 0) (γ e 1) := fun e he =>
    exists_piece hman hE₁ hV₁ hKV (fun v hv => (hR v hv).1) (hγ e he) he.1 (hγK e he)
      (fun v hv h => hRP v hv _ h (.inl (.inl (.inr ⟨e, he, rfl⟩))))
      hoffV (fun v hv ⟨y, h1, h2⟩ => by
        by_contra hn
        exact disjoint_left.mp (hcloff v hv e he.1 hn) h1 h2)
      (hedge e he.1 _ (hγK e he) ((hγ e he).closure_eq ▸ mem_range_self _) _
        (hγ e he).mem1 ((hγ e he).closure_eq ▸ mem_range_self _)) hXK
  haveI : Nonempty T := ⟨hA.some⟩
  choose! L a b hL using hpiece
  have hLU : ∀ e ∈ 𝓔, L e ⊆ Γ.U := fun e he x hx => hclU e he.1 ((hL e he).sub hx)
  have hLVmem : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Γ.V → x = b e ∧ b e ∈ X :=
    fun e he x hx hv => (hL e he).vertex x hx hv
  have hmeetV : ∀ e ∈ 𝓔, ∀ f ∈ 𝓔, e ≠ f → ∀ x ∈ L e, x ∈ L f → x ∈ Γ.V :=
    fun e he f hf hef x hx hy => by
      rcases (hL e he).onEdge x hx with h1 | h1
      · rcases (hL f hf).onEdge x hy with h2 | h2
        · exact absurd h2 (disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.1 hf.1 hef) h1)
        · exact h2
      · exact h1
  have hKfin : K.Finite := Γ.finite_V.subset hKV
  have hchord : ∀ v ∈ K ∩ discBd B₀, ∃ F y₁ y₂,
      IsLineWithEnds F y₁ y₂ ∧ y₁ ≠ y₂ ∧ F ⊆ R v ∧ F ∩ discBd (R v) = {y₁, y₂} ∧
      R v ∩ discBd B₀ = F ∧ v ∈ F := fun v hv => by
    have hst := (hR v hv.1).1
    refine exists_star_chord hB₀.isOArc_discBd hv.2 hst.disc (hst.disc.isOpen_discInt hman)
      hst.mem (hz v) (fun h => ?_) (fun y hy => ?_)
    · exact hRP v hv.1 _ h (.inr (by rw [if_pos hv.2]; exact rfl))
    · exact hst.star _ hB₀.isOArc_discBd.isCompact.isClosed (hDU ▸ isGammaNice_of_U hD₁ hDV₁) y hy
  choose! F y₁ y₂ hF₁ hF₂ hF₃ hF₄ hF₅ hF₆ using hchord
  have hK₀ : (K ∩ discBd B₀).Finite := hKfin.subset inter_subset_left
  have hmemK₀ : ∀ {v}, v ∈ hK₀.toFinset → v ∈ K ∩ discBd B₀ := fun {v} h => hK₀.mem_toFinset.mp h
  obtain ⟨B₁, hB₁, h1a, h1b, h1c, h1d, h1e, h1f, h1g⟩ :=
    exists_blob (R := R) (F := F) (y₁ := y₁) (y₂ := y₂) (v := id) hS hB₀ hK₀.toFinset
      (fun v hv => (hR v (hmemK₀ hv).1).1.disc)
      (fun v hv => hF₁ v (hmemK₀ hv)) (fun v hv => hF₂ v (hmemK₀ hv))
      (fun v hv => hF₃ v (hmemK₀ hv)) (fun v hv => hF₄ v (hmemK₀ hv))
      (fun v hv => hF₅ v (hmemK₀ hv)) (fun v hv => hF₆ v (hmemK₀ hv))
      (fun v hv => (hR v (hmemK₀ hv).1).1.mem)
      (fun u hu v hv huv => hRd u (hmemK₀ hu).1 v (hmemK₀ hv).1 huv)
  have hB₁cases : ∀ x ∈ B₁, x ∈ B₀ ∨ ∃ v ∈ K, v ∈ discBd B₀ ∧ x ∈ R v := fun x hx => by
    rcases h1c hx with h | h
    · exact .inl h
    · obtain ⟨v, hv, h2⟩ := mem_iUnion₂.mp h
      exact .inr ⟨v, (hmemK₀ hv).1, (hmemK₀ hv).2, h2⟩
  have hbB₁ : ∀ v ∈ K, v ∈ discBd B₀ → ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → x ∈ discBd B₁ :=
    fun v hv hvb x hx h2 h3 =>
      h1f v (hK₀.mem_toFinset.mpr ⟨hv, hvb⟩) ⟨hx, fun h => h2 (hB₀V x h3 h).2⟩
  have hintR : ∀ v ∈ K, v ∈ discBd B₀ → discInt (R v) ⊆ discInt B₁ := fun v hv hvb x hx => by
    have hm := hK₀.mem_toFinset.mpr ⟨hv, hvb⟩
    exact ⟨h1b v hm hx.1, fun h => disjoint_left.mp (h1e v hm) h hx⟩
  have hLB₁ : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ B₁ → x = a e ∨ x = b e := fun e he x hx hxB => by
    rcases hB₁cases x hxB with h | ⟨v, hv, -, h⟩
    · exact .inr (hLVmem e he x hx (hB₀V x (hLU e he hx) h).2).1
    · exact (hL e he).disc v hv x hx h
  have hvert : ∀ e ∈ 𝓔, ∀ x ∈ closure e, x ∈ Γ.V → x = γ e 0 ∨ x = γ e 1 :=
    fun e he x hx hv => by
      rw [(hγ e he).closure_eq] at hx
      obtain ⟨y, rfl⟩ := hx
      by_contra hn
      push Not at hn
      have h1 : 0 < y := unitInterval.pos_iff_ne_zero.mpr fun e' => hn.1 (by rw [e'])
      have h2 : y < 1 := unitInterval.lt_one_iff_ne_one.mpr fun e' => hn.2 (by rw [e'])
      exact (hγ e he).not_V he.1 h1 h2 hv
  have hnoV : ∀ e ∈ 𝓔, γ e 1 ∈ K → ∀ x ∈ L e, x ∉ Γ.V := fun e he h1 x hx hv => by
    obtain ⟨-, h2⟩ := hLVmem e he x hx hv
    rcases (hL e he).b_mem with ⟨-, -, h3⟩ | ⟨h3, -⟩
    · exact h3 (hXV h2)
    · exact h3 h1
  have hbK : ∀ e ∈ 𝓔, γ e 1 ∈ K → b e ∈ discBd (R (γ e 1)) ∧ b e ∉ Γ.V := fun e he h1 => by
    rcases (hL e he).b_mem with ⟨-, h3, h4⟩ | ⟨h3, -⟩
    · exact ⟨h3, h4⟩
    · exact absurd h1 h3
  let N : Type := ↥(K \ discBd B₀)
  have htree : ∀ u : N, ∃ e ∈ 𝓔, ∃ w ∈ K, w ≠ u.1 ∧ u.1 ∈ closure e ∧ w ∈ closure e ∧
      (w ∉ discBd B₀ → ρ w < ρ u.1) := fun u => by
    obtain ⟨e, he, w, hw, h1, h2, h3, h4⟩ := hreach u.1 u.2.1 u.2.2
    exact ⟨e, ⟨he, u.1, u.2.1, h2⟩, w, hw, h1, h2, h3, h4⟩
  choose eT heT wT hwT hwne huc hwc hrk using htree
  have hTends : ∀ u : N,
      (γ (eT u) 0 = u.1 ∧ γ (eT u) 1 = wT u) ∨ (γ (eT u) 0 = wT u ∧ γ (eT u) 1 = u.1) :=
    fun u => by
      rcases hvert _ (heT u) _ (huc u) (hKV u.2.1) with h1 | h1 <;>
        rcases hvert _ (heT u) _ (hwc u) (hKV (hwT u)) with h2 | h2
      · exact absurd (h2.trans h1.symm) (hwne u)
      · exact .inl ⟨h1.symm, h2.symm⟩
      · exact .inr ⟨h2.symm, h1.symm⟩
      · exact absurd (h2.trans h1.symm) (hwne u)
  have hT1 : ∀ u : N, γ (eT u) 1 ∈ K := fun u => by
    rcases hTends u with ⟨-, h⟩ | ⟨-, h⟩
    · exact h ▸ hwT u
    · exact h ▸ u.2.1
  have hpq : ∀ u : N, ∃ p q, IsLineWithEnds (L (eT u)) p q ∧
      p ∈ discBd (R u.1) ∧ q ∈ discBd (R (wT u)) ∧
      ({p, q} : Set T) = {a (eT u), b (eT u)} := fun u => by
    have hP := hL _ (heT u)
    have hb' := (hbK _ (heT u) (hT1 u)).1
    rcases hTends u with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a _, b _, hP.line, h1 ▸ hP.a_bd, h2 ▸ hb', rfl⟩
    · exact ⟨b _, a _, hP.line.symm, h2 ▸ hb', h1 ▸ hP.a_bd, pair_comm _ _⟩
  choose p q hpql hpb hqb hpq_ends using hpq
  let par : N → Option N := fun u => if h : wT u ∉ discBd B₀ then some ⟨wT u, hwT u, h⟩ else none
  let c₀ : Option N → Set T := fun n => n.elim B₁ fun u => R u.1
  have hRB₁ : ∀ u : N, Disjoint (R u.1) B₁ := fun u => disjoint_left.mpr fun x hx h => by
    rcases hB₁cases x h with h1 | ⟨v, hv, hvb, h1⟩
    · exact disjoint_left.mp (hRB₀ u.1 u.2.1 u.2.2) hx h1
    · exact disjoint_left.mp (hRd u.1 u.2.1 v hv fun e => u.2.2 (e ▸ hvb)) hx h1
  have hd' : ∀ n, IsClosedDisc (c₀ n) := fun n => by
    cases n with
    | none => exact hB₁
    | some u => exact (hR u.1 u.2.1).1.disc
  have hdj' : ∀ m n, m ≠ n → Disjoint (c₀ m) (c₀ n) := fun m n hmn => by
    cases m with
    | none =>
      cases n with
      | none => exact absurd rfl hmn
      | some u => exact (hRB₁ u).symm
    | some u =>
      cases n with
      | none => exact hRB₁ u
      | some v => exact hRd u.1 u.2.1 v.1 v.2.1 fun e => hmn (congrArg some (Subtype.ext e))
  have hρ' : ∀ u v, par u = some v → ρ v.1 < ρ u.1 := fun u v h => by
    by_cases h1 : wT u ∉ discBd B₀
    · have h2 : par u = some ⟨wT u, hwT u, h1⟩ := dif_pos h1
      rw [h2] at h
      obtain rfl := Option.some.inj h
      exact hrk u h1
    · have h2 : par u = none := dif_neg h1
      rw [h2] at h
      exact absurd h (by simp)
  have hq' : ∀ u, q u ∈ discBd (c₀ (par u)) := fun u => by
    have hqU : q u ∈ L (eT u) := (hpql u).right_mem
    by_cases h1 : wT u ∉ discBd B₀
    · have h2 : par u = some ⟨wT u, hwT u, h1⟩ := dif_pos h1
      rw [h2]
      exact hqb u
    · have h2 : par u = none := dif_neg h1
      rw [h2]
      exact hbB₁ _ (hwT u) (not_not.mp h1) _ (hqb u)
        (hnoV _ (heT u) (hT1 u) _ hqU) (hLU _ (heT u) hqU)
  have hLc' : ∀ u n, L (eT u) ∩ c₀ n ⊆ {p u, q u} := fun u n x hx => by
    rw [hpq_ends u]
    cases n with
    | none => exact hLB₁ _ (heT u) x hx.1 hx.2
    | some v => exact (hL _ (heT u)).disc v.1 v.2.1 x hx.1 hx.2
  have hLL' : ∀ u v, u ≠ v → Disjoint (L (eT u)) (L (eT v)) := fun u v huv => by
    have hne : eT u ≠ eT v := fun he => by
      have hvu : u.1 ≠ v.1 := fun e => huv (Subtype.ext e)
      have h1 := hvert _ (heT u) _ (huc u) (hKV u.2.1)
      have h2 := hvert _ (heT u) _ (hwc u) (hKV (hwT u))
      have h3 := hvert _ (heT u) _ (he ▸ huc v) (hKV v.2.1)
      have h4 := hvert _ (heT u) _ (he ▸ hwc v) (hKV (hwT v))
      have hw1 : wT u = v.1 := by
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
        · exact absurd (h2.trans h1.symm) (hwne u)
        · exact absurd (h2.trans h1.symm) (hwne u)
        · exact absurd (h1.trans h3.symm) hvu
        · exact h2.trans h3.symm
        · exact h2.trans h3.symm
        · exact absurd (h1.trans h3.symm) hvu
        · exact absurd (h2.trans h1.symm) (hwne u)
        · exact absurd (h2.trans h1.symm) (hwne u)
      have hw2 : wT v = u.1 := by
        rcases h1 with h1 | h1 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
        · exact absurd (h1.trans h3.symm) hvu
        · exact absurd (h1.trans h3.symm) hvu
        · exact h4.trans h1.symm
        · exact absurd (h4.trans h3.symm) (hwne v)
        · exact absurd (h4.trans h3.symm) (hwne v)
        · exact h4.trans h1.symm
        · exact absurd (h1.trans h3.symm) hvu
        · exact absurd (h1.trans h3.symm) hvu
      have h5 := hrk u (hw1 ▸ v.2.2)
      have h6 := hrk v (hw2 ▸ u.2.2)
      rw [hw1] at h5
      rw [hw2] at h6
      omega
    refine disjoint_left.mpr fun x hx hy => ?_
    exact hnoV _ (heT u) (hT1 u) x hx (hmeetV _ (heT u) _ (heT v) hne x hx hy)
  have hfin : (𝓔 \ range eT).Finite := h𝓔.subset sdiff_subset
  set s := hfin.toFinset with hs
  have hmem : ∀ {e}, e ∈ s → e ∈ 𝓔 ∧ ∀ u, eT u ≠ e := fun {e} h => by
    obtain ⟨h1, h2⟩ := hfin.mem_toFinset.mp h
    exact ⟨h1, fun u hu => h2 ⟨u, hu⟩⟩
  have hXfin : X.Finite := Γ.finite_V.subset hXV
  set Y : Set T := X ∪ (Γ.V \ K) ∪ (⋃ f ∈ Γ.E \ 𝓔, closure f) ∪ E₀
  have hYc : IsClosed Y :=
    ((hXfin.isClosed.union (Γ.finite_V.subset sdiff_subset).isClosed).union
      ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)).union
      hE₀.isClosed
  have hclf : ∀ f ∈ Γ.E \ 𝓔, ∀ v ∈ K, v ∉ closure f := fun f hf v hv h => hf.2 ⟨hf.1, v, hv, h⟩
  have hYR : ∀ v ∈ K, ∀ x ∈ R v, x ∉ Y := fun v hv x hx => by
    rintro (((h | h) | h) | h)
    · exact hoffV v hv x (hXV h) (fun e => disjoint_left.mp hXK h (e ▸ hv)) hx
    · exact hoffV v hv x h.1 (fun e => h.2 (e ▸ hv)) hx
    · obtain ⟨f, hf, h1⟩ := mem_iUnion₂.mp h
      exact disjoint_left.mp (hcloff v hv f hf.1 (hclf f hf v hv)) hx h1
    · exact disjoint_left.mp (hRE v hv) hx h
  have hYL : ∀ e ∈ 𝓔, ∀ x ∈ L e, x ∈ Y → x ∈ Γ.V := fun e he x hx => by
    rintro (((h | h) | h) | h)
    · exact hXV h
    · exact h.1
    · obtain ⟨f, hf, h1⟩ := mem_iUnion₂.mp h
      by_contra hn
      have h2 := hclV f hf.1 x h1 hn
      rcases (hL e he).onEdge x hx with h3 | h3
      · have hef : e = f := by
          by_contra hne
          exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.1 hf.1 hne) h3 h2
        exact hf.2 (hef ▸ he)
      · exact hn h3
    · exact hEU ⟨hLU e he hx, h⟩
  have hint' : IsPreconnected (discInt E₀) := hE₀.isPreconnected_discInt
  have hYne : (discInt E₀).Nonempty := hE₀.nonempty_discInt
  have hXY : Disjoint X (discInt E₀) :=
    disjoint_left.mpr fun x hx h => disjoint_left.mp hEint (Γ.V_subset_U (hXV hx)) h
  have hY₀Y : discInt E₀ ⊆ Y := fun _ hx => .inr hx.1
  have hLY' : ∀ u, Disjoint (L (eT u)) Y := fun u => disjoint_left.mpr fun x hx h =>
    hnoV _ (heT u) (hT1 u) x hx (hYL _ (heT u) x hx h)
  have hLℓ : ∀ u, ∀ e ∈ s, Disjoint (L (eT u)) (L e) := fun u e he =>
    disjoint_left.mpr fun x hx h =>
      hnoV _ (heT u) (hT1 u) x hx (hmeetV _ (heT u) _ (hmem he).1 ((hmem he).2 u) x hx h)
  have hcY₀ : ∀ n, Disjoint (discInt E₀) (c₀ n) := fun n => by
    cases n with
    | none =>
      refine disjoint_left.mpr fun x hx h => ?_
      rcases hB₁cases x h with h1 | ⟨v, hv, -, h1⟩
      · exact disjoint_left.mp hd h1 hx.1
      · exact disjoint_left.mp (hRE v hv) h1 hx.1
    | some u => exact ((hRE u.1 u.2.1).mono_right fun _ hx => hx.1).symm
  have hbY : ∀ n, discBd (c₀ n) ∩ Y ⊆ X := fun n => by
    cases n with
    | none =>
      rintro x ⟨hx, hy⟩
      rcases h1d hx with h | h
      · have hxB := h
        rcases hy with ((h1 | h1) | h1) | h1
        · exact h1
        · rcases h1 with ⟨h2, h3⟩
          exact (hcuff ⟨h2, hxB⟩).resolve_left h3
        · obtain ⟨f, hf, h2⟩ := mem_iUnion₂.mp h1
          have h3 := hbd ⟨hclU f hf.1 h2, hxB⟩
          rcases hcuff ⟨h3, hxB⟩ with h4 | h4
          · exact absurd h2 (hclf f hf x h4)
          · exact h4
        · exact absurd h1 (disjoint_left.mp hd (GM11.discBd_subset _ hxB))
      · obtain ⟨v, hv, h2⟩ := mem_iUnion₂.mp h
        exact absurd hy (hYR v (hmemK₀ hv).1 x (GM11.discBd_subset _ h2))
    | some u =>
      rintro x ⟨hx, hy⟩
      exact absurd hy (hYR u.1 u.2.1 x (GM11.discBd_subset _ hx))
  have hbon : ∀ v ∈ K, ∀ x ∈ discBd (R v), x ∉ Γ.V → x ∈ Γ.U → ∃ n, x ∈ discBd (c₀ n) :=
    fun v hv x hx h2 h3 => by
      by_cases h1 : v ∈ discBd B₀
      · exact ⟨none, hbB₁ v hv h1 x hx h2 h3⟩
      · exact ⟨some ⟨v, hv, h1⟩, hx⟩
  haveI : Finite N := (hKfin.subset sdiff_subset).to_subtype
  obtain ⟨B, hB, hc, hLint, hY₀B, hbdY, hbdL⟩ :=
    exists_disc_of_tree hS hsph (c₀ := c₀) (L := fun u => L (eT u)) (p := p) (q := q)
      (par := par) (ρ := fun u => ρ u.1) hd' hdj' hρ' hpql hpb hq' hLc' hLL'
      s L a b (X := X) (Y := Y) (Y₀ := discInt E₀)
      hint' hYne hXY hYc hY₀Y hLY' hLℓ hcY₀ hbY
      (fun e he => (hL e (hmem he).1).line) (fun e he => (hL e (hmem he).1).ne)
      (fun e he h => (hL e (hmem he).1).a_notV (hXV h))
      (fun e he => hbon _ (hγK e (hmem he).1) _ (hL e (hmem he).1).a_bd
        (hL e (hmem he).1).a_notV (hLU e (hmem he).1 (hL e (hmem he).1).line.left_mem))
      (fun e he => by
        have h𝓔e := (hmem he).1
        rcases (hL e h𝓔e).b_mem with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
        · exact .inl (hbon _ h1 _ h2 h3 (hLU e h𝓔e (hL e h𝓔e).line.right_mem))
        · have hbU := hLU e h𝓔e (hL e h𝓔e).line.right_mem
          have hbR : ∀ v ∈ K, b e ∉ R v := fun v hv h => hYR v hv _ h (.inl (.inl (.inl h2)))
          by_cases h3 : b e ∈ discBd B₀
          · refine .inl ⟨none, h1g ⟨h3, fun h => ?_⟩⟩
            obtain ⟨v, hv, h4⟩ := mem_iUnion₂.mp h
            exact hbR v (hmemK₀ hv).1 h4
          · refine .inr ⟨h2, fun n h => ?_⟩
            cases n with
            | none =>
              rcases hB₁cases _ h with h4 | ⟨v, hv, -, h4⟩
              · exact h3 (hB₀V _ hbU h4).1
              · exact hbR v hv h4
            | some u => exact hbR u.1 u.2.1 h)
      (fun e he n x hx => by
        have h𝓔e := (hmem he).1
        cases n with
        | none => exact hLB₁ e h𝓔e x hx.1 hx.2
        | some v => exact (hL e h𝓔e).disc v.1 v.2.1 x hx.1 hx.2)
      (fun e he x hx =>
        (hLVmem e (hmem he).1 x hx.1 (hYL e (hmem he).1 x hx.1 hx.2)).1 ▸
          (hLVmem e (hmem he).1 x hx.1 (hYL e (hmem he).1 x hx.1 hx.2)).2)
      (fun e he =>
        disjoint_left.mpr fun x hx h => hx.2 (.inr (hLVmem e (hmem he).1 x hx.1 (hXV h)).1))
      (fun e he f hf hef x hx => by
        have h2 := hmeetV e (hmem he).1 f (hmem hf).1 hef x hx.1 hx.2
        have h3 := hLVmem e (hmem he).1 x hx.1 h2
        exact h3.1 ▸ h3.2)
  have hRint : ∀ v ∈ K, discInt (R v) ⊆ discInt B := fun v hv x hx => by
    by_cases h1 : v ∈ discBd B₀
    · exact (hc none).2 (hintR v hv h1 hx)
    · exact (hc (some ⟨v, hv, h1⟩)).2 hx
  refine ⟨B, hB, h1a.trans (hc none).1, hY₀B, ?_, fun x hx => hbdY ⟨hx.1, .inr hx.2⟩⟩
  rintro x ⟨hx, hU⟩
  have hnotint : x ∉ discInt B := fun h => h.2 hx
  by_cases hV : x ∈ Γ.V
  · by_cases hK : x ∈ K
    · exact absurd (hRint x hK (hR x hK).1.mem) hnotint
    · exact hbdY ⟨hx, .inl (.inl (.inr ⟨hV, hK⟩))⟩
  obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hU hV
  by_cases h𝓔e : e ∈ 𝓔
  · by_cases hxL : x ∈ L e
    · by_cases hmemT : e ∈ range eT
      · obtain ⟨u, rfl⟩ := hmemT
        exact absurd (hLint u hxL) hnotint
      · exact hbdL e (hfin.mem_toFinset.mpr ⟨h𝓔e, hmemT⟩) ⟨hx, hxL⟩
    · obtain ⟨w, hw, h1⟩ := (hL e h𝓔e).rest x hxe hxL
      exact absurd (hRint w hw h1) hnotint
  · exact hbdY ⟨hx, .inl (.inr (mem_iUnion₂.mpr ⟨e, ⟨he, h𝓔e⟩, subset_closure hxe⟩))⟩

/-- `GM07.exists_cylinder_paths` with the extra guarantee `discBd B ∩ D₂ ⊆ Γ.V` in `hi`. -/
theorem exists_cylinder_paths_with_bd (hS : IsClosedSurface T) (hsph : IsSphere T) (Γ : Drawing T)
    {D₁ D₂ : Set T} (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂) (hd : Disjoint D₁ D₂)
    (hU₁ : Γ.U ∩ D₁ ⊆ Γ.V) (hi₁ : Disjoint Γ.U (discInt D₁))
    (hU₂ : Γ.U ∩ D₂ ⊆ Γ.V) (hi₂ : Disjoint Γ.U (discInt D₂)) {r : ℕ}
    (hi : ∀ B, IsClosedDisc B → D₁ ⊆ B → Disjoint (discInt D₂) B →
      discBd B ∩ Γ.U ⊆ Γ.V → discBd B ∩ D₂ ⊆ Γ.V → r ≤ (discBd B ∩ Γ.U).ncard) :
    ∃ (P : Fin r → Drawing T) (u v : Fin r → T),
      (∀ i, (P i).IsSubdrawing Γ ∧ u i ∈ D₁ ∧ v i ∈ D₂ ∧ (P i).IsPathBetween (u i) (v i)) ∧
      ∀ i i', i ≠ i' → Disjoint (P i).V (P i').V := by
  classical
  set Z₁ := Γ.V ∩ D₁
  set Z₂ := Γ.V ∩ D₂
  have hZ₁V : Z₁ ⊆ Γ.toHypergraph.vertexSet := inter_subset_left
  have hZ₂V : Z₂ ⊆ Γ.toHypergraph.vertexSet := inter_subset_left
  by_cases hp : HasDisjointPaths Γ.toHypergraph.skeleton Z₁ Z₂ r
  · obtain ⟨Q, hQ⟩ := hp
    have hex : ∀ i, ∃ P : Drawing T,
        P.IsPathBetween (Q i).first (Q i).last ∧ P.IsSubdrawing Γ ∧
        P.V = {x | x ∈ (Q i).walk.support} := fun i =>
      GraphMinor.GM16.drawing_path_of_skeleton_path (Q i).first_mem.1 (Q i).walk (Q i).isPath
    choose P hP hPs hPV using hex
    refine ⟨P, fun i => (Q i).first, fun i => (Q i).last,
      fun i => ⟨hPs i, (Q i).first_mem.2, (Q i).last_mem.2, hP i⟩, fun i i' hne => ?_⟩
    rw [hPV, hPV]
    exact hQ hne
  · exfalso
    obtain ⟨X, hsep, hlt⟩ :=
      Thomas.exists_separates_lt_of_not_hasDisjointPaths Γ.toHypergraph hZ₁V hZ₂V hp
    set K₀ := Γ.toHypergraph.skeleton
    set K := Thomas.sepCompLeft K₀ Γ.V X Z₁
    have hXV : X ⊆ Γ.V := hsep.1
    let P : T → ℕ → Prop := fun u n =>
      ∃ z ∈ Z₁ \ X, ∃ p : K₀.Walk z u, (∀ w ∈ p.support, w ∈ Γ.V \ X) ∧ p.length = n
    have hne : ∀ u ∈ K, ∃ n, P u n := fun u ⟨_, z, hz, p, hp⟩ => ⟨_, z, hz, p, hp, rfl⟩
    let ρ : T → ℕ := fun u => sInf {n | P u n}
    have hρ : ∀ u ∈ K, P u (ρ u) := fun u hu => Nat.sInf_mem (hne u hu)
    have hKsub : K ⊆ Γ.V \ X := Thomas.sepCompLeft_subset_sdiff _ _ _ _
    have hedge : ∀ e ∈ Γ.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ Γ.V, w ∈ closure e → w ∈ K ∪ X :=
      fun e he u hu hue w hw hwe => by
        by_cases huw : u = w
        · exact .inl (huw ▸ hu)
        by_contra hn
        have hw' : w ∈ Thomas.sepCompRight K₀ Γ.V X Z₁ :=
          ⟨⟨hw, fun h => hn (.inr h)⟩, fun h => hn (.inl h)⟩
        exact Thomas.not_adj_sepCompLeft_sepCompRight hu hw'
          ⟨huw, e, ⟨he, (hKsub hu).1, hue⟩, ⟨he, hw, hwe⟩⟩
    have hZbd : ∀ {z}, z ∈ Z₁ → z ∈ discBd D₁ := fun {z} hz => by
      by_contra hn
      exact disjoint_left.mp hi₁ (Γ.V_subset_U hz.1) ⟨hz.2, hn⟩
    have hreach : ∀ u ∈ K, u ∉ discBd D₁ →
        ∃ e ∈ Γ.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e ∧
          (w ∉ discBd D₁ → ρ w < ρ u) := fun u hu hub => by
      obtain ⟨z, hz, p, hp, hl⟩ := hρ u hu
      have huz : u ≠ z := fun h => hub (h ▸ hZbd hz.1)
      obtain ⟨w, hadj, q, hq⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huz p.reverse
      obtain ⟨huw, e, h1, h2⟩ := hadj
      have hsup : ∀ y ∈ q.support, y ∈ Γ.V \ X := fun y hy => hp y (by
        have : y ∈ p.reverse.support := by
          rw [hq]
          exact List.mem_cons_of_mem _ hy
        rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)
      have hsup' : ∀ y ∈ q.reverse.support, y ∈ Γ.V \ X :=
        fun y hy => hsup y (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy)
      have hw : w ∈ K := ⟨hsup w q.start_mem_support, z, hz, q.reverse, hsup'⟩
      refine ⟨e, h1.1, w, hw, huw.symm, h1.2.2, h2.2.2, fun _ => ?_⟩
      have hle : ρ w ≤ q.reverse.length := Nat.sInf_le ⟨z, hz, q.reverse, hsup', rfl⟩
      have hlen : q.length + 1 = p.length := by
        have h3 : p.reverse.length = q.length + 1 := by rw [hq]; rfl
        rw [SimpleGraph.Walk.length_reverse] at h3
        exact h3.symm
      rw [SimpleGraph.Walk.length_reverse] at hle
      omega
    have hc : Γ.V ∩ discBd D₁ ⊆ K ∪ X := fun x hx => by
      by_cases hxX : x ∈ X
      · exact .inr hxX
      · have hz : x ∈ Z₁ := ⟨hx.1, Surface.discBd_subset _ hx.2⟩
        exact .inl ⟨⟨hx.1, hxX⟩, x, ⟨hz, hxX⟩, SimpleGraph.Walk.nil, fun w hw => by
          rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
          exact hw ▸ ⟨hx.1, hxX⟩⟩
    have hke : Disjoint K D₂ := disjoint_left.mpr fun u hu hu₂ => by
      obtain ⟨hV, z, hz, p, hp⟩ := hu
      obtain ⟨x, hx, hxX⟩ := hsep.2 hz.1 (⟨hV.1, hu₂⟩ : u ∈ Z₂) p (fun w hw => (hp w hw).1)
      exact (hp x hx).2 hxX
    obtain ⟨B, hB, hsub, hdis, hbdB, hbdE⟩ :=
      exists_disc_of_side_with_bd (K := K) (X := X) (ρ := ρ) hS hsph Γ h₁ h₂ hd
        (fun x hx => hU₁ ⟨hx.1, Surface.discBd_subset _ hx.2⟩) hi₁ hU₂ hi₂
        (fun x hx => (hKsub hx).1) hXV (Thomas.disjoint_sepCompLeft_sep _ _ _ _).symm
        hc hke hedge hreach
    have hle := hi B hB hsub hdis (hbdB.trans hXV) (hbdE.trans hXV)
    have := Set.ncard_le_ncard hbdB (Γ.finite_V.subset hXV)
    omega

universe u

/-- Menger's theorem between an inner closed disc `D₁` with `Γ`-normal boundary and an outer closed
disc `Δ₂` bounded by a subdrawing `C` of `Γ`. -/
theorem exists_disc_paths_of_circuit_bd {S : Type u} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Γ C : Drawing S} {D₁ Δ₂ : Set S}
    (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc Δ₂) (hin : D₁ ⊆ Δ₂ \ discBd Δ₂)
    (hC : C.IsSubdrawing Γ) (hCU : discBd Δ₂ = C.U) (hn₁ : Γ.IsNormal (discBd D₁)) {r : ℕ}
    (hi : ∀ B, IsClosedDisc B → D₁ ⊆ B → B ⊆ Δ₂ → Γ.IsNormal (discBd B) →
      r ≤ (Γ.V ∩ discBd B).ncard) :
    ∃ (P : Fin r → Drawing S) (u v : Fin r → S),
      (∀ i, (P i).IsSubdrawing Γ ∧ u i ∈ discBd D₁ ∧ v i ∈ discBd Δ₂ ∧
        (P i).IsPathBetween (u i) (v i) ∧ (P i).U ⊆ Δ₂ \ discInt D₁) ∧
      ∀ i i', i ≠ i' → Disjoint (P i).V (P i').V := by
  classical
  have hT : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hint : ∀ x ∈ discBd Δ₂, IsInteriorPoint x := fun x _ => hS.2.2 x
  let G : Drawing S := Γ.span Γ.V (Γ.E \ C.E)
  have hG_sub : G.IsSubdrawing Γ := Γ.span_isSubdrawing _ _
  have hGE : G.E = (Γ.E \ C.E) ∩ Γ.E := Γ.span_E _ _
  have hGV : G.V = Γ.V :=
    Subset.antisymm hG_sub.1 (fun x hx => .inl ⟨hx, hx⟩)
  have hn₁_G : G.IsNormal (discBd D₁) := fun x hx =>
    hGV.symm ▸ hn₁ ⟨hx.1, hG_sub.U_subset hx.2⟩
  have hn₂_G : G.IsNormal (discBd Δ₂) := by
    rintro x ⟨hxbd, hxU⟩
    by_contra hxV
    obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hxU hxV
    rw [hGE] at he
    have hxC : x ∈ C.U := hCU ▸ hxbd
    by_cases hxCV : x ∈ C.V
    · exact hxV (hGV.symm ▸ hC.1 hxCV)
    · obtain ⟨f, hf, hxf⟩ := C.exists_edge_of_mem hxC hxCV
      have hef : e = f := by
        by_contra hne
        exact disjoint_left.mp (GM06.disjoint_edges_of_ne Γ he.2 (hC.2 hf) hne) hxe hxf
      exact he.1.2 (hef ▸ hf)
  have hGU_add : ∀ x ∈ Γ.U, x ∉ discBd Δ₂ → x ∈ G.U := by
    intro x hxU hxnot
    by_cases hxV : x ∈ Γ.V
    · exact G.V_subset_U (hGV.symm ▸ hxV)
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
      have he_notC : e ∉ C.E := fun heC =>
        hxnot (hCU.symm ▸ C.closure_subset_U heC (subset_closure hxe))
      have heG : e ∈ G.E := by
        rw [hGE]
        exact ⟨⟨he, he_notC⟩, he⟩
      exact G.closure_subset_U heG (subset_closure hxe)
  obtain ⟨E, hE, hΔE, -⟩ := Surface.exists_disc_around hT h₂ hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := h₂.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hm, hm', hl, hr', hcE, hcb, -⟩ := exists_disc_collar h₂ hE hΔE p
  obtain ⟨R, tR, ι, hR2, hRc, hRs, hιc, hιi⟩ := exists_sphere_chart
  let τ : S → R := ι ∘ c'
  have hτc : ContinuousOn τ E := hιc.comp_continuousOn hcc'
  have hτi : InjOn τ E := fun x hx y hy h => by
    have h1 : c' x = c' y := hιi h
    rw [← hr' hx, ← hr' hy, h1]
  have hΔ₂E : Δ₂ ⊆ E := fun x hx => (hΔE hx).1
  have hD₁E : D₁ ⊆ E := fun x hx => hΔ₂E (hin hx).1
  let A : Set S := Δ₂ \ discInt D₁
  have hAc : IsClosed A := h₂.isClosed.inter (h₁.isOpen_discInt hT).isClosed_compl
  let Gi : Drawing S := G.span A {e | e ⊆ A}
  have hGiE : Gi.E = {e | e ⊆ A} ∩ G.E := G.span_E _ _
  have hclA : ∀ {e : Set S}, e ⊆ A → closure e ⊆ A := fun {e} he => closure_minimal he hAc
  have hGiV : Gi.V ⊆ G.V ∩ A := by
    rintro x (hx | hx)
    · exact ⟨hx.2, hx.1⟩
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact ⟨hxe.2, hclA he.1 hxe.1⟩
  have hGiU : Gi.U ⊆ A := by
    rintro x (hx | hx)
    · exact (hGiV hx).2
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact hclA he.1 hxe
  have hGiUU : Gi.U ⊆ G.U := (Drawing.span_isSubdrawing G _ _).U_subset
  have hinV : ∀ y ∈ G.V, y ∈ A → y ∈ Gi.V := fun y hy h => .inl ⟨h, hy⟩
  have hmemU : ∀ x ∈ G.U, x ∈ A → x ∈ Gi.U := fun x hx hA => by
    by_cases hxV : x ∈ G.V
    · exact Gi.V_subset_U (hinV x hxV hA)
    obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hx hxV
    have hpc : IsPreconnected e := he.2.2.1.isConnected.isPreconnected
    have hoff : ∀ {Y : Set S}, G.IsNormal Y → Disjoint e Y := fun {Y} hY => by
      rw [disjoint_left]
      intro z hz hzb
      exact (he.2.1 hz).2 (hY ⟨hzb, (he.2.1 hz).1⟩)
    have hsub : e ⊆ A := by
      have h3 := inside_or_off hpc h₁.isClosed ((hoff hn₁_G).mono_right (frontier_disc_subset hT h₁))
      have h4 := inside_or_off hpc h₂.isClosed ((hoff hn₂_G).mono_right (frontier_disc_subset hT h₂))
      have h5 : e ⊆ (D₁)ᶜ := h3.resolve_left fun h =>
        hA.2 ⟨interior_subset (h hxe), disjoint_left.mp (hoff hn₁_G) hxe⟩
      have h6 : e ⊆ interior Δ₂ := h4.resolve_right fun h => h hxe hA.1
      exact fun z hz => ⟨interior_subset (h6 hz), fun h7 => h5 hz h7.1⟩
    have hmem : e ∈ Gi.E := by
      rw [hGiE]
      exact ⟨hsub, he⟩
    exact Gi.closure_subset_U hmem (subset_closure hxe)
  have hKc : IsCompact E := hE.isCompact
  have hAE : A ⊆ E := fun x hx => hΔ₂E hx.1
  have hGiK : Gi.U ⊆ E := hGiU.trans hAE
  have hAne : E.Nonempty := by
    obtain ⟨z, hz⟩ := (isConnected_of_isOArc h₂.isOArc_discBd).nonempty
    exact ⟨z, hΔ₂E (Surface.discBd_subset _ hz)⟩
  have : Nonempty S := ⟨hAne.some⟩
  obtain ⟨Γ_R, hΓU, hΓV, hΓE⟩ := exists_transport hKc hAne hτc hτi Gi hGiK
  obtain ⟨ρ, hρc, hρl⟩ := Surface.exists_inv_of_compactOn hKc hτc hτi
  have hτρ : ∀ y ∈ τ '' E, τ (ρ y) = y := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hρl hx]
  have hRman : ∀ x : R, IsManifoldPoint x := fun x => (hRc.2.2 x).isManifoldPoint
  obtain ⟨hD₁', hD₁b⟩ := isClosedDisc_image h₁ (hτc.mono hD₁E) (hτi.mono hD₁E)
  obtain ⟨hΔ', hΔb⟩ := isClosedDisc_image h₂ (hτc.mono hΔ₂E) (hτi.mono hΔ₂E)
  obtain ⟨hD₂', hD₂b⟩ := GM12.isClosedDisc_closure_compl_of_sphere hRc hRs hΔ'
  set Δ' := τ '' Δ₂
  set D₂' := closure (univ \ Δ')
  have hoffD : ∀ {x}, x ∉ Δ' → x ∈ discInt D₂' := fun {x} hx =>
    ⟨subset_closure ⟨mem_univ x, hx⟩, fun hb => hx (Surface.discBd_subset Δ' (hD₂b ▸ hb))⟩
  have hnotΔ : ∀ {x}, x ∈ discInt Δ' → x ∉ D₂' := fun {x} hx h => by
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h _ (hΔ'.isOpen_discInt hRman) hx
    exact hw2.2 hw1.1
  have hint₂ : ∀ {x}, x ∈ discInt D₂' → x ∉ Δ' := fun {x} hx h => by
    refine hnotΔ ⟨h, fun hb => hx.2 ?_⟩ hx.1
    rw [hD₂b]
    exact hb
  have hτint : ∀ {z}, z ∈ Δ₂ → z ∉ discBd Δ₂ → τ z ∈ discInt Δ' :=
    fun {z} hz hb => ⟨mem_image_of_mem τ hz, fun h => by
      rw [hΔb] at h
      obtain ⟨w, hw, he⟩ := h
      exact hb ((hτi (hΔ₂E (Surface.discBd_subset _ hw)) (hΔ₂E hz) he) ▸ hw)⟩
  have hd : Disjoint (τ '' D₁) D₂' := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ h
    exact hnotΔ (hτint (hin hz).1 (hin hz).2) h
  have hbdV : ∀ {y : S}, y ∈ Gi.U → y ∈ discBd D₁ ∪ discBd Δ₂ → y ∈ Gi.V := fun {y} hy h => by
    refine hinV y ?_ (hGiU hy)
    rcases h with h | h
    · exact hn₁_G ⟨h, hGiUU hy⟩
    · exact hn₂_G ⟨h, hGiUU hy⟩
  have hκD₁ : ∀ {y : S}, y ∈ Gi.U → τ y ∈ τ '' D₁ → y ∈ discBd D₁ := fun {y} hy h => by
    obtain ⟨z, hz, he⟩ := h
    have h3 : z = y := hτi (hD₁E hz) (hGiK hy) he
    by_contra hb
    exact (hGiU hy).2 ⟨h3 ▸ hz, hb⟩
  have hκD₂ : ∀ {y : S}, y ∈ Gi.U → τ y ∈ D₂' → y ∈ discBd Δ₂ := fun {y} hy h => by
    by_contra hb
    exact hnotΔ (hτint (hGiU hy).1 hb) h
  have hU₁ : Γ_R.U ∩ τ '' D₁ ⊆ Γ_R.V := by
    rintro _ ⟨hx, hb⟩
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hΓV]
    exact ⟨y, hbdV hy (.inl (hκD₁ hy hb)), rfl⟩
  have hi₁ : Disjoint Γ_R.U (discInt (τ '' D₁)) := by
    rw [disjoint_left]
    intro x hx hi
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have h3 := hκD₁ hy hi.1
    exact hi.2 (hD₁b ▸ ⟨y, h3, rfl⟩)
  have hU₂ : Γ_R.U ∩ D₂' ⊆ Γ_R.V := by
    rintro _ ⟨hx, hb⟩
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hΓV]
    exact ⟨y, hbdV hy (.inr (hκD₂ hy hb)), rfl⟩
  have hi₂ : Disjoint Γ_R.U (discInt D₂') := by
    rw [disjoint_left]
    intro x hx hi
    rw [hΓU] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hint₂ hi (mem_image_of_mem τ (hGiU hy).1)
  have hτint₁ : ∀ {z}, z ∈ discInt D₁ → τ z ∈ discInt (τ '' D₁) :=
    fun {z} hz => ⟨mem_image_of_mem τ hz.1, fun hb => hz.2 (by
      rw [hD₁b] at hb
      obtain ⟨w, hw, he⟩ := hb
      exact hτi (hD₁E (Surface.discBd_subset _ hw)) (hD₁E hz.1) he ▸ hw)⟩
  have hΔ'E : Δ' ⊆ τ '' E := image_mono hΔ₂E
  have hnormal_G : ∀ {X : Set S}, X ⊆ A → τ '' X ∩ Γ_R.U ⊆ Γ_R.V → G.IsNormal X :=
    fun {X} hXA h => by
      rintro x ⟨hx, hxU⟩
      have hy := hmemU x hxU (hXA hx)
      have h3 : τ x ∈ τ '' X ∩ Γ_R.U :=
        ⟨mem_image_of_mem τ hx, hΓU ▸ mem_image_of_mem τ hy⟩
      have h4 := h h3
      rw [hΓV] at h4
      obtain ⟨y, hy', he⟩ := h4
      rw [← hτi (hGiK (Gi.V_subset_U hy')) (hGiK hy) he]
      exact (hGiV hy').1
  have hcount : ∀ {X : Set S}, X ⊆ A → τ '' X ∩ Γ_R.U ⊆ Γ_R.V →
      (Γ.V ∩ X).ncard ≤ (τ '' X ∩ Γ_R.U).ncard := fun {X} hXA h => by
    have hsub : τ '' (Γ.V ∩ X) ⊆ τ '' X ∩ Γ_R.U := by
      rintro _ ⟨y, ⟨hy, hyX⟩, rfl⟩
      exact ⟨mem_image_of_mem τ hyX,
        hΓU ▸ mem_image_of_mem τ (Gi.V_subset_U (hinV y (hGV.symm ▸ hy) (hXA hyX)))⟩
    have hi' : InjOn τ (Γ.V ∩ X) := hτi.mono fun y hy => hΔ₂E (hXA hy.2).1
    rw [← hi'.ncard_image]
    exact ncard_le_ncard hsub (Γ_R.finite_V.subset h)
  have hA₁ : ∀ {B : Set R}, Disjoint (discInt D₂') B → B ⊆ Δ' := fun {B} h x hx => by
    by_contra hn
    exact disjoint_left.mp h (hoffD hn) hx
  have hρimg : ∀ {B : Set R}, B ⊆ Δ' → τ '' (ρ '' B) = B := fun {B} h => by
    rw [image_image]
    exact (image_congr fun y hy => hτρ y (hΔ'E (h hy))).trans (image_id' B)
  have hρin : ∀ {B : Set R}, B ⊆ Δ' → ρ '' B ⊆ Δ₂ := fun {B} h => by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := h hy
    rw [hρl (hΔ₂E hz)]
    exact hz
  have hρcon : ∀ {B : Set R}, B ⊆ Δ' → ContinuousOn ρ B :=
    fun {B} h => hρc.mono (h.trans hΔ'E)
  have hρinj : ∀ {B : Set R}, B ⊆ Δ' → InjOn ρ B :=
    fun {B} h x hx y hy e => by rw [← hτρ x (hΔ'E (h hx)), ← hτρ y (hΔ'E (h hy)), e]
  have hhi : ∀ B, IsClosedDisc B → τ '' D₁ ⊆ B → Disjoint (discInt D₂') B →
      discBd B ∩ Γ_R.U ⊆ Γ_R.V → discBd B ∩ D₂' ⊆ Γ_R.V → r ≤ (discBd B ∩ Γ_R.U).ncard :=
    fun B hB h3 h4 h5 h5_bd => by
      have hBΔ := hA₁ h4
      obtain ⟨hB₀, hB₀b⟩ := isClosedDisc_image hB (hρcon hBΔ) (hρinj hBΔ)
      have hD₁B : D₁ ⊆ ρ '' B :=
        fun z hz => ⟨τ z, h3 (mem_image_of_mem τ hz), hρl (hD₁E hz)⟩
      have hbA : discBd (ρ '' B) ⊆ A := fun x hx => by
        refine ⟨hρin hBΔ (Surface.discBd_subset _ hx), fun h6 => ?_⟩
        have h7 : τ x ∈ discInt (τ '' D₁) := hτint₁ h6
        have h8 : τ x ∈ interior B :=
          interior_maximal (fun z hz => h3 hz.1) (hD₁'.isOpen_discInt hRman) h7
        have h9 : τ x ∈ discBd B := by
          rw [hB₀b] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [hτρ y (hΔ'E (hBΔ (Surface.discBd_subset _ hy)))]
          exact hy
        rw [← IsClosedDisc.frontier_eq_discBd hRc hB] at h9
        exact h9.2 h8
      have hτb : τ '' discBd (ρ '' B) = discBd B := by
        rw [hB₀b]
        exact hρimg ((Surface.discBd_subset B).trans hBΔ)
      have h6 : τ '' discBd (ρ '' B) ∩ Γ_R.U ⊆ Γ_R.V := by rwa [hτb]
      have hG_norm : G.IsNormal (discBd (ρ '' B)) := hnormal_G hbA h6
      have hΓ_norm : Γ.IsNormal (discBd (ρ '' B)) := by
        rintro x ⟨hx_bd, hx_U⟩
        by_cases hx_Δ₂ : x ∈ discBd Δ₂
        · have hτx_bd : τ x ∈ discBd B := hτb ▸ mem_image_of_mem τ hx_bd
          have hτx_D₂ : τ x ∈ D₂' :=
            Surface.discBd_subset D₂' (hD₂b.symm ▸ hΔb.symm ▸ mem_image_of_mem τ hx_Δ₂)
          have hτx_V : τ x ∈ Γ_R.V := h5_bd ⟨hτx_bd, hτx_D₂⟩
          rw [hΓV] at hτx_V
          obtain ⟨y, hy', he⟩ := hτx_V
          have hyx : y = x := hτi (hGiK (Gi.V_subset_U hy')) (hAE (hbA hx_bd)) he
          exact hGV ▸ hyx ▸ (hGiV hy').1
        · exact hGV ▸ hG_norm ⟨hx_bd, hGU_add x hx_U hx_Δ₂⟩
      have h7 := hi _ hB₀ hD₁B (hρin hBΔ) hΓ_norm
      have h8 := hcount hbA h6
      rw [hτb] at h8
      exact h7.trans h8
  have : CompactSpace R := hRc.1
  obtain ⟨P', u', v', hP, hPd⟩ :=
    exists_cylinder_paths_with_bd hRc hRs Γ_R hD₁' hD₂' hd hU₁ hi₁ hU₂ hi₂ hhi
  have hρθ : ∀ {x}, x ∈ Gi.U → ρ (τ x) = x := fun {x} hx => hρl (hGiK hx)
  have hΓK : Γ_R.U ⊆ τ '' E := by
    rw [hΓU]
    exact image_mono hGiK
  have hτρ' : ∀ {y}, y ∈ Γ_R.U → τ (ρ y) = y := fun {y} hy => by
    rw [hΓU] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hρθ hx]
  have hpull : ∀ D' : Drawing R, D'.IsSubdrawing Γ_R → D'.U.Nonempty →
      ∃ D : Drawing S, D.IsSubdrawing G ∧ τ '' D.U = D'.U ∧ τ '' D.V = D'.V ∧
        D.U ⊆ Gi.U ∧ D.U = ρ '' D'.U ∧ D.V = ρ '' D'.V ∧ D.E = image ρ '' D'.E :=
    fun D' hD' hne => by
      have hDU := hD'.U_subset
      have hc : ContinuousOn ρ D'.U := hρc.mono (hDU.trans hΓK)
      have hin' : InjOn ρ D'.U :=
        fun x hx y hy e => by rw [← hτρ' (hDU hx), ← hτρ' (hDU hy), e]
      obtain ⟨D, h3, h4, h5⟩ :=
        exists_transport D'.isClosed_U.isCompact hne hc hin' D' subset_rfl
      have hDΓ : D.U ⊆ Gi.U := by
        rw [h3]
        rintro _ ⟨y, hy, rfl⟩
        have h6 := hDU hy
        rw [hΓU] at h6
        obtain ⟨x, hx, rfl⟩ := h6
        rwa [hρθ hx]
      have hsubV : D.V ⊆ G.V := by
        rw [h4]
        rintro _ ⟨y, hy, rfl⟩
        have h6 := hD'.1 hy
        rw [hΓV] at h6
        obtain ⟨x, hx, rfl⟩ := h6
        rw [hρθ (Gi.V_subset_U hx)]
        exact (hGiV hx).1
      have hsubE : D.E ⊆ G.E := by
        rw [h5]
        rintro _ ⟨f, hf, rfl⟩
        have h6 := hD'.2 hf
        rw [hΓE] at h6
        obtain ⟨e, he, rfl⟩ := h6
        have hee : e ⊆ Gi.U := fun z hz => Gi.closure_subset_U he (subset_closure hz)
        have h7 : image ρ (image τ e) = e := by
          rw [image_image]
          exact (image_congr fun z hz => hρθ (hee hz)).trans (image_id' e)
        rw [h7]
        rw [hGiE] at he
        exact he.2
      have himg : ∀ {W : Set R}, W ⊆ D'.U → τ '' (ρ '' W) = W := fun {W} hW => by
        rw [image_image]
        exact (image_congr fun y hy => hτρ' (hDU (hW hy))).trans (image_id' W)
      refine ⟨D, ⟨hsubV, hsubE⟩, ?_, ?_, hDΓ, h3, h4, h5⟩
      · rw [h3]; exact himg subset_rfl
      · rw [h4]; exact himg D'.V_subset_U
  have hnonU : ∀ {X : Drawing R} {a b : R}, X.IsPathBetween a b → X.U.Nonempty :=
    fun {X a _} h => by
      obtain ⟨W, -, hV, -⟩ := h
      exact ⟨a, X.V_subset_U (by rw [hV]; exact W.start_mem_support)⟩
  have hthe : ∀ {D' : Drawing R}, D'.IsSubdrawing Γ_R → InjOn ρ D'.U :=
    fun {D'} hD' x hx y hy e => by rw [← hτρ' (hD'.U_subset hx), ← hτρ' (hD'.U_subset hy), e]
  have hcthe : ∀ {D' : Drawing R}, D'.IsSubdrawing Γ_R → ContinuousOn ρ D'.U :=
    fun {D'} hD' => hρc.mono (hD'.U_subset.trans hΓK)
  have hPex : ∀ i, ∃ (D : Drawing S),
      D.IsSubdrawing G ∧ τ '' D.U = (P' i).U ∧ τ '' D.V = (P' i).V ∧
      D.U ⊆ Gi.U ∧ D.IsPathBetween (ρ (u' i)) (ρ (v' i)) := fun i => by
    obtain ⟨c1, -, -, c4⟩ := hP i
    obtain ⟨D, h3, h4, h5, h6, h7, h8, h9⟩ := hpull _ c1 (hnonU c4)
    exact ⟨D, h3, h4, h5, h6,
      transport_isPathBetween (P' i).isClosed_U.isCompact (hcthe c1) (hthe c1) h8 h9 c4⟩
  choose P hPs hPU hPV hPG hPp using hPex
  have hstart : ∀ i, u' i ∈ (P' i).V ∧ v' i ∈ (P' i).V := fun i => by
    obtain ⟨-, -, -, W, -, hV, -⟩ := hP i
    exact ⟨by rw [hV]; exact W.start_mem_support, by rw [hV]; exact W.end_mem_support⟩
  have hΓmem : ∀ {y}, y ∈ Γ_R.V → ρ y ∈ Gi.V := fun {y} hy => by
    rw [hΓV] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rwa [hρθ (Gi.V_subset_U hx)]
  refine ⟨P, fun i => ρ (u' i), fun i => ρ (v' i),
    fun i => ⟨(hPs i).trans hG_sub, ?_, ?_, hPp i, (hPG i).trans hGiU⟩,
    fun i i' hne => ?_⟩
  · have h3 := hΓmem ((hP i).1.1 (hstart i).1)
    refine hκD₁ (Gi.V_subset_U h3) ?_
    rw [hτρ' ((hP i).1.U_subset ((P' i).V_subset_U (hstart i).1))]
    exact (hP i).2.1
  · have h3 := hΓmem ((hP i).1.1 (hstart i).2)
    refine hκD₂ (Gi.V_subset_U h3) ?_
    rw [hτρ' ((hP i).1.U_subset ((P' i).V_subset_U (hstart i).2))]
    exact (hP i).2.2.1
  · rw [disjoint_left]
    intro x h3 h4
    exact disjoint_left.mp (hPd i i' hne)
      (hPV i ▸ mem_image_of_mem τ h3) (hPV i' ▸ mem_image_of_mem τ h4)

private theorem arcComponentsIn_empty {X : Type*} [TopologicalSpace X] :
    arcComponentsIn (∅ : Set X) = ∅ := by
  ext C
  simp only [arcComponentsIn, mem_ofPred_eq, subset_empty_iff, mem_empty_iff_false, iff_false]
  rintro ⟨hne, hC, _, _⟩
  exact hne.ne_empty hC

/-- Pullback of a drawing `P : Drawing S` with `P.U ⊆ X` along `Subtype.val : ↥X → S` for a closed
subset `X ⊆ S`. -/
noncomputable def drawingPullSubtype {S : Type*} [TopologicalSpace S] [T2Space S]
    (P : Surface.Drawing S) {X : Set S} (hX : IsClosed X) (hU : P.U ⊆ X) :
    Surface.Drawing ↥X :=
  let f : ↥X → S := Subtype.val
  have hf : IsClosedEmbedding f := hX.isClosedEmbedding_subtypeVal
  have hf_img : ∀ {A : Set S}, A ⊆ X → f '' (f ⁻¹' A) = A := fun {A} hA => by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨⟨x, hA hx⟩, hx, rfl⟩⟩
  have hf_img_U : f '' (f ⁻¹' P.U) = P.U := hf_img hU
  have hf_img_V : f '' (f ⁻¹' P.V) = P.V := hf_img (P.V_subset_U.trans hU)
  have hf_img_diff : f '' (f ⁻¹' P.U \ f ⁻¹' P.V) = P.U \ P.V := by
    rw [image_sdiff hf.injective, hf_img_U, hf_img_V]
  have harc_img : arcComponentsIn (P.U \ P.V) = image f '' arcComponentsIn (f ⁻¹' P.U \ f ⁻¹' P.V) := by
    rw [← hf_img_diff]
    rcases (f ⁻¹' P.U \ f ⁻¹' P.V).eq_empty_or_nonempty with h_emp | ⟨x₀, _⟩
    · rw [h_emp, image_empty, arcComponentsIn_empty, arcComponentsIn_empty, image_empty]
    · have : Nonempty ↥X := ⟨x₀⟩
      have hl : Function.LeftInverse (Function.invFun f) f :=
        Function.leftInverse_invFun hf.injective
      refine GM11.arcComponentsIn_image hf.continuous.continuousOn ?_ fun x _ => hl x
      rw [hf.isInducing.continuousOn_iff]
      refine continuousOn_id.congr ?_
      rintro _ ⟨x, -, rfl⟩
      simp [hl x]
  have harc : arcComponentsIn (f ⁻¹' P.U \ f ⁻¹' P.V) = preimage f '' P.E := by
    change arcComponentsIn (f ⁻¹' P.U \ f ⁻¹' P.V) = preimage f '' arcComponentsIn (P.U \ P.V)
    rw [harc_img, image_image]
    ext e'
    simp only [mem_image]
    constructor
    · intro he'
      exact ⟨e', he', preimage_image_eq e' hf.injective⟩
    · rintro ⟨e₀, he₀, rfl⟩
      rwa [preimage_image_eq e₀ hf.injective]
  have hcl_pre : ∀ {e : Set S}, e ∈ P.E → f '' closure (f ⁻¹' e) = closure e := fun {e} he => by
    have heX : e ⊆ X := fun x hx => hU (he.2.1 hx).1
    exact (hf.closure_image_eq (f ⁻¹' e)).symm.trans (congrArg closure (hf_img heX))
  have hcap_pre : ∀ {e : Set S}, e ∈ P.E →
      closure (f ⁻¹' e) ∩ (f ⁻¹' P.V) = f ⁻¹' (closure e ∩ P.V) := fun {e} he => by
    apply image_injective.mpr hf.injective
    have hclX : closure e ∩ P.V ⊆ X :=
      inter_subset_right.trans (P.V_subset_U.trans hU)
    rw [image_inter hf.injective, hcl_pre he, hf_img_V, hf_img hclX]
  { U := f ⁻¹' P.U
    V := f ⁻¹' P.V
    V_subset_U := preimage_mono P.V_subset_U
    isClosed_U := P.isClosed_U.preimage continuous_subtype_val
    finite_V := P.finite_V.preimage hf.injective.injOn
    finite_edges := by
      rw [harc]
      exact P.finite_edges.image _
    edge_cond := by
      rw [harc]
      rintro _ ⟨e, he, rfl⟩
      let hhomeo : closure (f ⁻¹' e) ≃ₜ closure e :=
        (hf.isEmbedding.homeomorphImage (closure (f ⁻¹' e))).trans
          (Homeomorph.setCongr (hcl_pre he))
      have hhomeo_val : ∀ z : closure (f ⁻¹' e), (hhomeo z).1 = z.1.1 := fun ⟨z, hz⟩ => rfl
      rcases P.edge_cond e he with ⟨u, v, h1, h2, ⟨φ_line, h0, h1_end⟩⟩ | ⟨u, h2, ⟨φ_cir⟩⟩
      · have huX : u ∈ X := hU (P.V_subset_U ((h2 ▸ mem_insert u {v}).2))
        have hvX : v ∈ X := hU (P.V_subset_U ((h2 ▸ mem_insert_of_mem u (mem_singleton v)).2))
        let u' : ↥X := ⟨u, huX⟩
        let v' : ↥X := ⟨v, hvX⟩
        have hpair : f ⁻¹' {u, v} = ({u', v'} : Set ↥X) := by
          ext z
          simp [f, u', v', Subtype.ext_iff]
        refine Or.inl ⟨u', v', fun h => h1 (congrArg Subtype.val h),
          by rw [hcap_pre he, h2, hpair], ⟨φ_line.trans hhomeo.symm, ?_, ?_⟩⟩
        · apply Subtype.ext
          change (hhomeo.symm (φ_line 0)).1.1 = u
          rw [← hhomeo_val (hhomeo.symm (φ_line 0)), Homeomorph.apply_symm_apply, h0]
        · apply Subtype.ext
          change (hhomeo.symm (φ_line 1)).1.1 = v
          rw [← hhomeo_val (hhomeo.symm (φ_line 1)), Homeomorph.apply_symm_apply, h1_end]
      · have huX : u ∈ X := hU (P.V_subset_U ((h2 ▸ mem_singleton u).2))
        let u' : ↥X := ⟨u, huX⟩
        have hsing : f ⁻¹' {u} = ({u'} : Set ↥X) := by
          ext z
          simp [f, u', Subtype.ext_iff]
        exact Or.inr ⟨u', by rw [hcap_pre he, h2, hsing], ⟨φ_cir.trans hhomeo.symm⟩⟩ }

theorem drawingMapEmb_drawingPullSubtype {S : Type*} [TopologicalSpace S] [T2Space S]
    (P : Surface.Drawing S) {X : Set S} (hX : IsClosed X) (hU : P.U ⊆ X) :
    drawingMapEmb (drawingPullSubtype P hX hU) hX.isClosedEmbedding_subtypeVal = P := by
  have hU_eq : Subtype.val '' (drawingPullSubtype P hX hU).U = P.U := by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨⟨x, hU hx⟩, hx, rfl⟩⟩
  have hV_eq : Subtype.val '' (drawingPullSubtype P hX hU).V = P.V := by
    ext x
    exact ⟨by rintro ⟨y, hy, rfl⟩; exact hy, fun hx => ⟨⟨x, hU (P.V_subset_U hx)⟩, hx, rfl⟩⟩
  exact Surface.Drawing.ext_of_V_E hV_eq (by
    rw [drawingMapEmb_E]
    have hdiff :
        Subtype.val '' ((drawingPullSubtype P hX hU).U \ (drawingPullSubtype P hX hU).V) =
          P.U \ P.V := by
      rw [image_sdiff Subtype.val_injective, hU_eq, hV_eq]
    change image Subtype.val ''
      arcComponentsIn ((drawingPullSubtype P hX hU).U \ (drawingPullSubtype P hX hU).V) =
      arcComponentsIn (P.U \ P.V)
    rw [← hdiff]
    rcases ((drawingPullSubtype P hX hU).U \ (drawingPullSubtype P hX hU).V).eq_empty_or_nonempty
      with h_emp | ⟨x₀, _⟩
    · rw [h_emp, image_empty, arcComponentsIn_empty, arcComponentsIn_empty, image_empty]
    · have : Nonempty ↥X := ⟨x₀⟩
      have hf : IsClosedEmbedding (Subtype.val : ↥X → S) := hX.isClosedEmbedding_subtypeVal
      have hl : Function.LeftInverse (Function.invFun (Subtype.val : ↥X → S)) Subtype.val :=
        Function.leftInverse_invFun hf.injective
      refine (GM11.arcComponentsIn_image hf.continuous.continuousOn ?_ fun x _ => hl x).symm
      rw [hf.isInducing.continuousOn_iff]
      refine continuousOn_id.congr ?_
      rintro _ ⟨x, -, rfl⟩
      simp [hl x])

theorem toEmbeddedGraph_drawingPullSubtype {S : Type*} [TopologicalSpace S] [T2Space S]
    {α : Type*} {β : Type*}
    (P : Surface.Drawing S) {X : Set S} (hX : IsClosed X) (hU : P.U ⊆ X)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    let embV : ↥X ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
    let embE : Set ↥X ↪ Set S := ⟨image Subtype.val, image_injective.mpr Subtype.val_injective⟩
    (drawingPullSubtype P hX hU).toEmbeddedGraph (embV.trans ιV) (embE.trans ιE) =
      P.toEmbeddedGraph ιV ιE := by
  intro embV embE
  have hmap := drawingMapEmb_toGraph_eq (drawingPullSubtype P hX hU) hX.isClosedEmbedding_subtypeVal
  rw [drawingMapEmb_drawingPullSubtype P hX hU] at hmap
  have hlink_iff : ∀ e₀ x₀ y₀,
      P.toGraph.IsLink e₀ x₀ y₀ ↔
        ((drawingPullSubtype P hX hU).toGraph.mapEmbed embV embE).IsLink e₀ x₀ y₀ := by
    intro e₀ x₀ y₀
    exact ⟨fun h => hmap ▸ h, fun h => hmap.symm ▸ h⟩
  refine Graph.ext ?_ fun e x y => ?_
  · change (embV.trans ιV) '' (drawingPullSubtype P hX hU).V = ιV '' P.V
    ext v
    constructor
    · rintro ⟨⟨x, hxX⟩, hxV, rfl⟩
      exact ⟨x, hxV, rfl⟩
    · rintro ⟨x, hxV, rfl⟩
      exact ⟨⟨x, hU (P.V_subset_U hxV)⟩, hxV, rfl⟩
  · constructor
    · rintro ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
      refine ⟨embE e₀, embV x₀, embV y₀, ?_, rfl, rfl, rfl⟩
      rw [hlink_iff]
      exact ⟨e₀, x₀, y₀, hl, rfl, rfl, rfl⟩
    · rintro ⟨e₁, x₁, y₁, hl, rfl, rfl, rfl⟩
      rw [hlink_iff] at hl
      rcases hl with ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
      exact ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩

theorem isGraphPathWithEnds_comapEmbed {α₁ : Type*} {β₁ : Type*} {α₂ : Type*} {β₂ : Type*}
    (ιV : α₁ ↪ α₂) (ιE : β₁ ↪ β₂) {H : Graph α₁ β₁} {P' : Graph α₂ β₂} {u v : α₁}
    (hP' : IsGraphPathWithEnds (H.mapEmbed ιV ιE) P' (ιV u) (ιV v)) :
    IsGraphPathWithEnds H (P'.comapEmbed ιV ιE) u v := by
  obtain ⟨hle', W', hW'_simp, hVW', hEW'⟩ := hP'
  obtain ⟨hmap, hle⟩ := mapEmbed_comapEmbed_of_le ιV ιE hle'
  obtain ⟨W, hs, he⟩ := comapEmbed_walk ιV ιE (W'.mono hmap.ge)
  rw [GraphWalk.support_mono] at hs
  rw [GraphWalk.edges_mono] at he
  refine ⟨hle, W, ?_, ?_, ?_⟩
  · unfold GraphWalk.IsSimple at hW'_simp ⊢
    exact (List.nodup_map_iff ιV.injective).mp (hs ▸ hW'_simp)
  · ext x
    change ιV x ∈ V(P') ↔ x ∈ W.support
    rw [hVW', mem_ofPred_eq, hs, List.mem_map_of_injective ιV.injective]
  · ext e
    rw [← ιE.injective.mem_set_image, show ιE '' E(P'.comapEmbed ιV ιE) = E(P') from
      congrArg Graph.edgeSet hmap, hEW', mem_ofPred_eq, he, List.mem_map_of_injective ιE.injective]
    rfl

theorem exists_disc_paths_pull_of_circuit_bd {S : Type*} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {Γ C : Drawing S} {D₁ Δ₂ X : Set S}
    (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc Δ₂) (hin : D₁ ⊆ Δ₂ \ discBd Δ₂)
    (hC : C.IsSubdrawing Γ) (hCU : discBd Δ₂ = C.U) (hn₁ : Γ.IsNormal (discBd D₁))
    (hX : IsClosed X) (hsubX : Δ₂ \ discInt D₁ ⊆ X)
    (hi : ∀ B, IsClosedDisc B → D₁ ⊆ B → B ⊆ Δ₂ → Γ.IsNormal (discBd B) →
      (Γ.V ∩ discBd D₁).ncard ≤ (Γ.V ∩ discBd B).ncard) :
    let D_pull := drawingPullSubtype (Γ.interSet X) hX (GM11.interSet_U_subset hX)
    let C_pull : Set ↥X := Subtype.val ⁻¹' discBd D₁
    ∃ P : ↑(D_pull.V ∩ C_pull) → Graph ↥X (Set ↥X),
      (∀ x : ↑(D_pull.V ∩ C_pull),
        ∃ y ∈ D_pull.V ∩ Subtype.val ⁻¹' subBd Δ₂,
          IsGraphPathWithEnds D_pull.toGraph (P x) x.1 y) ∧
      Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂)) := by
  classical
  intro D_pull C_pull
  set r := (Γ.V ∩ discBd D₁).ncard
  obtain ⟨P₀, u, v, hP₀, hP₀d⟩ :=
    exists_disc_paths_of_circuit_bd hS h₁ h₂ hin hC hCU hn₁ hi
  have hu_mem_P : ∀ i : Fin r, u i ∈ (P₀ i).V := fun i => by
    obtain ⟨W, -, hV, -⟩ := (hP₀ i).2.2.2.1
    rw [hV]
    exact W.start_mem_support
  have hv_mem_P : ∀ i : Fin r, v i ∈ (P₀ i).V := fun i => by
    obtain ⟨W, -, hV, -⟩ := (hP₀ i).2.2.2.1
    rw [hV]
    exact W.end_mem_support
  have hP₀_sub_X : ∀ i : Fin r, (P₀ i).IsSubdrawing (Γ.interSet X) := fun i => by
    have hUX : (P₀ i).U ⊆ X := (hP₀ i).2.2.2.2.trans hsubX
    refine ⟨fun x hx => ?_, fun e he => ?_⟩
    · rw [GM11.mem_interSet_V_iff hX]
      exact ⟨(hP₀ i).1.1 hx, hUX ((P₀ i).V_subset_U hx)⟩
    · rw [GM11.mem_interSet_E_iff]
      exact ⟨(hP₀ i).1.2 he, fun z hz => hUX ((he.2.1 hz).1)⟩
  have hD₁_sub_X : discBd D₁ ⊆ X := fun x hx =>
    hsubX ⟨(hin (Surface.discBd_subset D₁ hx)).1, fun h => h.2 hx⟩
  have hV_eq : Subtype.val '' (D_pull.V ∩ C_pull) = Γ.V ∩ discBd D₁ := by
    ext x
    constructor
    · rintro ⟨⟨z, hzX⟩, ⟨hzV, hzC⟩, rfl⟩
      have hzV' : z ∈ (Γ.interSet X).V := hzV
      rw [GM11.mem_interSet_V_iff hX] at hzV'
      exact ⟨hzV'.1, hzC⟩
    · rintro ⟨hxV, hxD₁⟩
      have hxX : x ∈ X := hD₁_sub_X hxD₁
      refine ⟨⟨x, hxX⟩, ⟨?_, hxD₁⟩, rfl⟩
      change x ∈ (Γ.interSet X).V
      rw [GM11.mem_interSet_V_iff hX]
      exact ⟨hxV, hxX⟩
  let u_sub : Fin r → ↑(D_pull.V ∩ C_pull) := fun i =>
    ⟨⟨u i, (hP₀_sub_X i).U_subset ((P₀ i).V_subset_U (hu_mem_P i)) |>
      GM11.interSet_U_subset hX⟩,
      ⟨(hP₀_sub_X i).1 (hu_mem_P i), (hP₀ i).2.1⟩⟩
  have hu_inj : Function.Injective u_sub := by
    intro i j hij
    by_contra hne
    have hueq : u i = u j := congrArg (fun z : ↑(D_pull.V ∩ C_pull) => z.1.1) hij
    exact disjoint_left.mp (hP₀d i j hne) (hu_mem_P i) (hueq ▸ hu_mem_P j)
  have hfin_set : (D_pull.V ∩ C_pull).Finite := D_pull.finite_V.subset inter_subset_left
  letI : Fintype ↑(D_pull.V ∩ C_pull) := hfin_set.fintype
  have hcard_eq : Fintype.card (Fin r) = Fintype.card ↑(D_pull.V ∩ C_pull) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq]
    change (Γ.V ∩ discBd D₁).ncard = (D_pull.V ∩ C_pull).ncard
    rw [← hV_eq, ncard_image_of_injective _ Subtype.val_injective]
  have hu_bij : Function.Bijective u_sub :=
    (Fintype.bijective_iff_injective_and_card u_sub).mpr ⟨hu_inj, hcard_eq⟩
  let e_u : Fin r ≃ ↑(D_pull.V ∩ C_pull) := Equiv.ofBijective u_sub hu_bij
  let embV : ↥X ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
  let embE : Set ↥X ↪ Set S := ⟨image Subtype.val, image_injective.mpr Subtype.val_injective⟩
  have hmap_D : (Γ.interSet X).toGraph = D_pull.toGraph.mapEmbed embV embE := by
    have hmap := drawingMapEmb_toGraph_eq D_pull hX.isClosedEmbedding_subtypeVal
    rwa [drawingMapEmb_drawingPullSubtype (Γ.interSet X) hX (GM11.interSet_U_subset hX)] at hmap
  refine ⟨fun x => (P₀ (e_u.symm x)).toGraph.comapEmbed embV embE, fun x => ?_, fun x₁ x₂ hne => ?_⟩
  · set i := e_u.symm x
    have hui : (u_sub i).1 = x.1 := congrArg Subtype.val (e_u.apply_symm_apply x)
    have hvi_X : v i ∈ X :=
      GM11.interSet_U_subset hX ((hP₀_sub_X i).U_subset ((P₀ i).V_subset_U (hv_mem_P i)))
    let y : ↥X := ⟨v i, hvi_X⟩
    have hy_mem : y ∈ D_pull.V ∩ Subtype.val ⁻¹' subBd Δ₂ := by
      refine ⟨(hP₀_sub_X i).1 (hv_mem_P i), ?_⟩
      change v i ∈ subBd Δ₂
      rw [subBd_eq_frontier, IsClosedDisc.frontier_eq_discBd hS h₂]
      exact (hP₀ i).2.2.1
    refine ⟨y, hy_mem, ?_⟩
    obtain ⟨W, hW, hVW, hEW⟩ := (hP₀ i).2.2.2.1
    have hpath_S : IsGraphPathWithEnds (D_pull.toGraph.mapEmbed embV embE)
        (P₀ i).toGraph (embV x.1) (embV y) := by
      have hx_eq : embV x.1 = u i := by
        change x.1.1 = u i
        exact (congrArg Subtype.val hui).symm
      rw [← hmap_D, hx_eq]
      exact ⟨(hP₀_sub_X i).toGraph_le, W, hW, hVW, hEW⟩
    exact isGraphPathWithEnds_comapEmbed embV embE hpath_S
  · have hne_i : e_u.symm x₁ ≠ e_u.symm x₂ := fun h => hne (e_u.symm.injective h)
    refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
    exact disjoint_left.mp (hP₀d (e_u.symm x₁) (e_u.symm x₂) hne_i) hz₁ hz₂

end GraphMinor.GM22
