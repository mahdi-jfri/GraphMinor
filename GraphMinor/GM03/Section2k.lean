module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2f
public import GraphMinor.GM11.ForestRegions

/-!
# Graph Minors III, Section 2k: Planar Shell Edge Classification and Inner Forest Connection (for
(2.3))

This file establishes the first two surface-topology ingredients for `(2.3)` (page 55) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
1. `ShellDiscData`, `exists_shellDiscData_of_isDShell`, and `ShellDiscData.edge_classification`:
   surface disc structure for a `d`-shell and the 4-bucket classification of all edges of `D`;
2. `exists_connected_innerDraw`: adding chords in `interior (Δ_{d-1})` to turn a nonempty acyclic
   inner drawing `innerDraw D d C` into a connected tree while preserving `ShellDiscData` and
   simplicity.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u v

/-! ## 1. Surface Shell Disc Data and 4-Bucket Edge Classification -/

/-- Surface-level `d`-shell disc data on `D : Drawing S` (without the region chain). -/
structure ShellDiscData {S : Type*} [TopologicalSpace S] (D : Drawing S) (d : ℕ)
    (C : Fin d → Drawing S) (Δ : Fin d → Set S) : Prop where
  isSubdrawing : ∀ j : Fin d, (C j).IsSubdrawing D
  isCircuit : ∀ j : Fin d, (C j).IsCircuit
  isClosedDisc : ∀ j : Fin d, IsClosedDisc (Δ j)
  discBd_eq : ∀ j : Fin d, discBd (Δ j) = (C j).U
  disjoint_V : ∀ ⦃j j' : Fin d⦄, j < j' → Disjoint (C j).V (C j').V
  disc_subset_interior : ∀ ⦃j j' : Fin d⦄, j < j' → Δ j' ⊆ interior (Δ j)
  vertex_in_or_inside : ∀ (hd : 0 < d), ∀ v ∈ D.V,
    (∃ j : Fin d, v ∈ (C j).V) ∨ v ∈ interior (Δ ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩)
  edge_induced : ∀ (j : Fin d) ⦃e : Set S⦄ ⦃u v : S⦄,
    D.toGraph.IsLink e u v → u ∈ (C j).V → v ∈ (C j).V → e ∈ (C j).E

section ShellClassification

variable {S : Type} [TopologicalSpace S]

theorem ShellDiscData.disjoint_V_ne {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S}
    {Δ : Fin d → Set S} (hSh : ShellDiscData D d C Δ) {j j' : Fin d} (hne : j ≠ j') :
    Disjoint (C j).V (C j').V := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hSh.disjoint_V hlt
  · exact (hSh.disjoint_V hgt).symm

theorem ShellDiscData.subdrawing_toGraph_le [T2Space S] {D : Drawing S} {d : ℕ}
    {C : Fin d → Drawing S} {Δ : Fin d → Set S} (hSh : ShellDiscData D d C Δ) (j : Fin d) :
    (C j).toGraph ≤ D.toGraph := by
  refine ⟨(hSh.isSubdrawing j).1, fun e u v hl => ?_⟩
  exact ⟨(hSh.isSubdrawing j).2 hl.1, (hSh.isSubdrawing j).1 hl.2.1,
    (hSh.isSubdrawing j).1 hl.2.2.1, by
      rw [← (hSh.isSubdrawing j).closure_inter_V hl.1]
      exact hl.2.2.2⟩

theorem ShellDiscData.mem_disc_and_interior_of_circuit_V (hS : IsClosedSurface S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) {j m : Fin d} {w : S} (hw : w ∈ (C j).V) :
    (w ∈ Δ m ↔ m ≤ j) ∧ (w ∈ interior (Δ m) ↔ m < j) := by
  have : T2Space S := hS.2.1
  have hw_bd_j : w ∈ discBd (Δ j) := (hSh.discBd_eq j).symm ▸ (C j).V_subset_U hw
  have hw_Δ_j : w ∈ Δ j := GM11.discBd_subset (Δ j) hw_bd_j
  have hw_not_int_j : w ∉ interior (Δ j) := by
    intro hint
    rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j)] at hint
    exact hint.2 hw_bd_j
  constructor
  · constructor
    · intro hw_m
      by_contra hnot
      have hlt : j < m := not_le.mp hnot
      exact hw_not_int_j (hSh.disc_subset_interior hlt hw_m)
    · intro hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hw_Δ_j
      · exact interior_subset (hSh.disc_subset_interior hlt hw_Δ_j)
  · constructor
    · intro hw_int_m
      by_contra hnot
      rcases eq_or_lt_of_le (not_lt.mp hnot) with rfl | hlt
      · exact hw_not_int_j hw_int_m
      · exact hw_not_int_j (hSh.disc_subset_interior hlt (interior_subset hw_int_m))
    · intro hlt
      exact hSh.disc_subset_interior hlt hw_Δ_j

theorem ShellDiscData.mem_interior_of_inner_V (hS : IsClosedSurface S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) (hd : 0 < d)
    {w : S} (hw : haveI : T2Space S := hS.2.1; w ∈ (innerDraw D d C).V) (m : Fin d) :
    w ∈ interior (Δ m) := by
  have : T2Space S := hS.2.1
  obtain ⟨_, hNV, _, _⟩ := innerDraw_spec D d C
  rw [hNV] at hw
  rcases hSh.vertex_in_or_inside hd w hw.1 with ⟨j, hwj⟩ | hw_int
  · exact (hw.2 (mem_iUnion.mpr ⟨j, hwj⟩)).elim
  · let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
    by_cases hm : m = j_last
    · exact hm ▸ hw_int
    · have hlt : m < j_last := lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt m.2)) hm
      exact hSh.disc_subset_interior hlt (interior_subset hw_int)

theorem ShellDiscData.innerDraw_V_disjoint_circuit_V [T2Space S]
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (_hSh : ShellDiscData D d C Δ) (j : Fin d) :
    Disjoint (innerDraw D d C).V (C j).V := by
  obtain ⟨_, hNV, _, _⟩ := innerDraw_spec D d C
  rw [hNV, Set.disjoint_left]
  exact fun _ hv hvj => hv.2 (mem_iUnion.mpr ⟨j, hvj⟩)

/-- For any edge `e ∈ D.E` (`D.toGraph.IsLink e u v`) and `m : Fin d` with `e ∉ (C m).E`, either
`e ⊆ interior (Δ m)` (with `u, v ∈ Δ m`) or `Disjoint e (Δ m)` (with `u, v ∉ interior (Δ m)`). -/
theorem ShellDiscData.edge_inside_or_disjoint_of_notMem (hS : IsClosedSurface S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) {m : Fin d} {e : Set S} {u v : S}
    (hl : D.toGraph.IsLink e u v) (he_not : e ∉ (C m).E) :
    (e ⊆ interior (Δ m) ∧ u ∈ Δ m ∧ v ∈ Δ m) ∨
      (Disjoint e (Δ m) ∧ u ∉ interior (Δ m) ∧ v ∉ interior (Δ m)) := by
  have : T2Space S := hS.2.1
  have heD : e ∈ D.E := hl.1
  have he_pre : IsPreconnected e := hl.1.2.2.1.isConnected.isPreconnected
  have hfr_m : frontier (Δ m) = (C m).U :=
    (GM11.IsClosedDisc.frontier_eq_discBd hS (hSh.isClosedDisc m)).trans (hSh.discBd_eq m)
  have hdisj_fr : Disjoint e (frontier (Δ m)) := by
    rw [hfr_m, Set.disjoint_left]
    intro x hxe hxU
    have hx_not_DV : x ∉ D.V := (heD.2.1 hxe).2
    have hx_not_CV : x ∉ (C m).V := fun h => hx_not_DV ((hSh.isSubdrawing m).1 h)
    obtain ⟨f, hfC, hxf⟩ := (C m).exists_edge_of_mem hxU hx_not_CV
    have hef : e = f := D.edge_eq_of_mem heD ((hSh.isSubdrawing m).2 hfC) hxe hxf
    exact he_not (hef ▸ hfC)
  have hu_cl : u ∈ closure e := (hl.2.2.2.symm ▸ mem_insert u {v}).1
  have hv_cl : v ∈ closure e := (hl.2.2.2.symm ▸ mem_insert_of_mem u (mem_singleton v)).1
  rcases GM11.subset_or_disjoint_of_frontier (hSh.isClosedDisc m).isClosed he_pre hdisj_fr with
    hsub | hdisj
  · have hcl_sub : closure e ⊆ Δ m := closure_minimal hsub (hSh.isClosedDisc m).isClosed
    refine Or.inl ⟨fun x hxe => ?_, hcl_sub hu_cl, hcl_sub hv_cl⟩
    by_contra hx_ni
    exact Set.disjoint_left.mp hdisj_fr hxe ⟨subset_closure (hsub hxe), hx_ni⟩
  · have hdisj_int : Disjoint (closure e) (interior (Δ m)) :=
      (hdisj.mono_right interior_subset).closure_left isOpen_interior
    exact Or.inr ⟨hdisj, fun hu_int => Set.disjoint_left.mp hdisj_int hu_cl hu_int,
      fun hv_int => Set.disjoint_left.mp hdisj_int hv_cl hv_int⟩

theorem ShellDiscData.innerDraw_U_subset_interior (hS : IsClosedSurface S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) (hd : 0 < d) :
    haveI : T2Space S := hS.2.1
    (innerDraw D d C).U ⊆ interior (Δ ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩) := by
  have : T2Space S := hS.2.1
  let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
  obtain ⟨_, hNV, hNE, _⟩ := innerDraw_spec D d C
  rw [(innerDraw D d C).U_eq]
  refine union_subset (fun v hv => hSh.mem_interior_of_inner_V hS hd hv j_last)
    (iUnion₂_subset fun e heN => ?_)
  have heD : e ∈ D.E := (hNE ▸ heN).1
  have he_not_C : e ∉ (C j_last).E := by
    intro heC
    rcases (C j_last).edge_cond e heC with ⟨a, b, -, hcap, -⟩ | ⟨a, hcap, -⟩
    · have haC : a ∈ (C j_last).V := (hcap ▸ mem_insert a {b}).2
      have ha_cl : a ∈ closure e ∩ D.V :=
        ⟨(hcap ▸ mem_insert a {b}).1, (hSh.isSubdrawing j_last).1 haC⟩
      exact ((hNE ▸ heN).2 ha_cl).2 (mem_iUnion.mpr ⟨j_last, haC⟩)
    · have haC : a ∈ (C j_last).V := (hcap ▸ mem_singleton a).2
      have ha_cl : a ∈ closure e ∩ D.V :=
        ⟨(hcap ▸ mem_singleton a).1, (hSh.isSubdrawing j_last).1 haC⟩
      exact ((hNE ▸ heN).2 ha_cl).2 (mem_iUnion.mpr ⟨j_last, haC⟩)
  have he_int : e ⊆ interior (Δ j_last) := by
    rcases D.edge_cond e heD with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
    · have huD : u ∈ D.V := (hcap ▸ mem_insert u {v}).2
      have hvD : v ∈ D.V := (hcap ▸ mem_insert_of_mem u (mem_singleton v)).2
      have hl : D.toGraph.IsLink e u v := ⟨heD, huD, hvD, hcap⟩
      have huN : u ∈ (innerDraw D d C).V := hNV.symm ▸ (hNE ▸ heN).2 (hcap ▸ mem_insert u {v})
      rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_C with ⟨hsub, _, _⟩ | ⟨_, hni, _⟩
      · exact hsub
      · exact (hni (hSh.mem_interior_of_inner_V hS hd huN j_last)).elim
    · have huD : u ∈ D.V := (hcap ▸ mem_singleton u).2
      have hl : D.toGraph.IsLink e u u := ⟨heD, huD, huD, hcap.trans (pair_eq_singleton u).symm⟩
      have huN : u ∈ (innerDraw D d C).V := hNV.symm ▸ (hNE ▸ heN).2 (hcap ▸ mem_singleton u)
      rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_C with ⟨hsub, _, _⟩ | ⟨_, hni, _⟩
      · exact hsub
      · exact (hni (hSh.mem_interior_of_inner_V hS hd huN j_last)).elim
  intro x hxcl
  by_cases hxV : x ∈ D.V
  · exact hSh.mem_interior_of_inner_V hS hd (hNV.symm ▸ (hNE ▸ heN).2 ⟨hxcl, hxV⟩) j_last
  · exact he_int ((D.closure_diff_V heD).subset ⟨hxcl, hxV⟩)

/-- **4-Bucket Planar Shell Edge Classification:**
Under `ShellDiscData D d C Δ` (`0 < d`), every edge `e ∈ D.E` with `D.toGraph.IsLink e u v` falls
into one of four buckets:
1. `e ∈ (innerDraw D d C).E` (both endpoints in `(innerDraw D d C).V`);
2. `e ∈ (C j).E` for some `j : Fin d` (both endpoints in `(C j).V`);
3. Attachment edge between `(innerDraw D d C).V` and `(C ⟨d - 1, _⟩).V` with
   `e ⊆ interior (Δ ⟨d - 1, _⟩) \ (innerDraw D d C).U`;
4. Radial edge between `(C ⟨j + 1, _⟩).V` and `(C j).V` (`j + 1 < d`) with
   `e ⊆ interior (Δ j) \ Δ ⟨j + 1, _⟩`. -/
theorem ShellDiscData.edge_classification (hS : IsClosedSurface S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hSh : ShellDiscData D d C Δ) (hd : 0 < d)
    {e : Set S} {u v : S} (hl : D.toGraph.IsLink e u v) :
    haveI : T2Space S := hS.2.1
    let N := innerDraw D d C
    let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
    e ∈ N.E ∨
    (∃ j : Fin d, e ∈ (C j).E) ∨
    (((u ∈ N.V ∧ v ∈ (C j_last).V) ∨ (u ∈ (C j_last).V ∧ v ∈ N.V)) ∧
      e ⊆ interior (Δ j_last) \ N.U) ∨
    (∃ (j : ℕ) (hj : j + 1 < d),
      ((u ∈ (C ⟨j + 1, hj⟩).V ∧ v ∈ (C ⟨j, Nat.lt_of_succ_lt hj⟩).V) ∨
        (u ∈ (C ⟨j, Nat.lt_of_succ_lt hj⟩).V ∧ v ∈ (C ⟨j + 1, hj⟩).V)) ∧
      e ⊆ interior (Δ ⟨j, Nat.lt_of_succ_lt hj⟩) \ Δ ⟨j + 1, hj⟩) := by
  classical
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let N := innerDraw D d C
  let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
  obtain ⟨hNs, hNV, hNE, _⟩ := innerDraw_spec D d C
  have hpart : ∀ w ∈ D.V, w ∈ N.V ∨ ∃ j : Fin d, w ∈ (C j).V := by
    intro w hw
    by_cases h : ∃ j : Fin d, w ∈ (C j).V
    · exact Or.inr h
    · refine Or.inl (hNV.symm ▸ ⟨hw, ?_⟩)
      rintro hw_un
      obtain ⟨j, hwj⟩ := mem_iUnion.mp hw_un
      exact h ⟨j, hwj⟩
  have he_not_Cm_of_not_Vm : ∀ (m : Fin d), (u ∉ (C m).V ∨ v ∉ (C m).V) → e ∉ (C m).E := by
    intro m hnot heC
    have hcap_m : closure e ∩ (C m).V = closure e ∩ D.V :=
      (hSh.isSubdrawing m).closure_inter_V heC
    rw [hl.2.2.2] at hcap_m
    rcases hnot with hu_not | hv_not
    · exact hu_not (hcap_m.symm ▸ mem_insert u {v}).2
    · exact hv_not (hcap_m.symm ▸ mem_insert_of_mem u (mem_singleton v)).2
  have he_disj_NU : e ∉ N.E → Disjoint e N.U := by
    intro he_not_NE
    rw [Set.disjoint_left]
    intro x hxe hxNU
    have hx_not_DV : x ∉ D.V := (hl.1.2.1 hxe).2
    have hx_not_NV : x ∉ N.V := fun h => hx_not_DV (hNs.1 h)
    obtain ⟨f, hfN, hxf⟩ := N.exists_edge_of_mem hxNU hx_not_NV
    exact he_not_NE (D.edge_eq_of_mem hl.1 (hNs.2 hfN) hxe hxf ▸ hfN)
  rcases hpart u hl.2.1 with huN | ⟨ju, huC⟩ <;> rcases hpart v hl.2.2.1 with hvN | ⟨jv, hvC⟩
  · refine Or.inl (hNE.symm ▸ ⟨hl.1, ?_⟩)
    rw [hl.2.2.2, ← hNV]
    rintro z (rfl | rfl)
    · exact huN
    · exact hvN
  · have hjv_eq : jv = j_last := by
      by_contra hne
      have hlt : jv < j_last := lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt jv.2)) hne
      have he_not : e ∉ (C j_last).E := he_not_Cm_of_not_Vm j_last
        (Or.inl (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_last) huN))
      rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not with ⟨_, _, hv_Δ⟩ | ⟨_, hu_ni, _⟩
      · exact not_le_of_gt hlt ((hSh.mem_disc_and_interior_of_circuit_V hS hvC).1.mp hv_Δ)
      · exact hu_ni (hSh.mem_interior_of_inner_V hS hd huN j_last)
    subst hjv_eq
    have he_not_C : e ∉ (C j_last).E := he_not_Cm_of_not_Vm j_last
      (Or.inl (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_last) huN))
    have he_not_N : e ∉ N.E := by
      intro heN
      have hv_in : v ∈ closure e ∩ D.V := hl.2.2.2.symm ▸ mem_insert_of_mem u rfl
      exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_last)
        (hNV.symm ▸ (hNE ▸ heN).2 hv_in) hvC
    have he_int : e ⊆ interior (Δ j_last) := by
      rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_C with ⟨hsub, _, _⟩ | ⟨_, hu_ni, _⟩
      · exact hsub
      · exact (hu_ni (hSh.mem_interior_of_inner_V hS hd huN j_last)).elim
    exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨huN, hvC⟩,
      subset_sdiff.mpr ⟨he_int, he_disj_NU he_not_N⟩⟩))
  · have hju_eq : ju = j_last := by
      by_contra hne
      have hlt : ju < j_last := lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt ju.2)) hne
      have he_not : e ∉ (C j_last).E := he_not_Cm_of_not_Vm j_last
        (Or.inr (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_last) hvN))
      rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not with ⟨_, hu_Δ, _⟩ | ⟨_, _, hv_ni⟩
      · exact not_le_of_gt hlt ((hSh.mem_disc_and_interior_of_circuit_V hS huC).1.mp hu_Δ)
      · exact hv_ni (hSh.mem_interior_of_inner_V hS hd hvN j_last)
    subst hju_eq
    have he_not_C : e ∉ (C j_last).E := he_not_Cm_of_not_Vm j_last
      (Or.inr (Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_last) hvN))
    have he_not_N : e ∉ N.E := by
      intro heN
      have hu_in : u ∈ closure e ∩ D.V := hl.2.2.2.symm ▸ mem_insert u {v}
      exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j_last)
        (hNV.symm ▸ (hNE ▸ heN).2 hu_in) huC
    have he_int : e ⊆ interior (Δ j_last) := by
      rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_C with ⟨hsub, _, _⟩ | ⟨_, _, hv_ni⟩
      · exact hsub
      · exact (hv_ni (hSh.mem_interior_of_inner_V hS hd hvN j_last)).elim
    exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨huC, hvN⟩,
      subset_sdiff.mpr ⟨he_int, he_disj_NU he_not_N⟩⟩))
  · rcases lt_trichotomy ju jv with hlt | rfl | hgt
    · have hsucc : jv.1 = ju.1 + 1 := by
        by_contra hne
        have hlt2 : ju.1 + 1 < jv.1 := by have := Fin.lt_def.mp hlt; omega
        let m : Fin d := ⟨ju.1 + 1, by omega⟩
        have he_not : e ∉ (C m).E := he_not_Cm_of_not_Vm m (Or.inl
          (Set.disjoint_left.mp (hSh.disjoint_V_ne
            (Fin.ne_of_lt (Fin.lt_def.mpr (by dsimp only [m]; omega)))) huC))
        rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not with ⟨_, hu_Δ, _⟩ | ⟨_, _, hv_ni⟩
        · have := Fin.le_def.mp ((hSh.mem_disc_and_interior_of_circuit_V hS huC (m := m)).1.mp hu_Δ)
          dsimp only [m] at this; omega
        · exact hv_ni ((hSh.mem_disc_and_interior_of_circuit_V hS hvC (m := m)).2.mpr
            (Fin.lt_def.mpr hlt2))
      have hjv_lt : ju.1 + 1 < d := hsucc ▸ jv.2
      have hjv_fin : jv = ⟨ju.1 + 1, hjv_lt⟩ := Fin.ext hsucc
      rw [hjv_fin] at hvC hlt
      have he_not_ju : e ∉ (C ju).E := he_not_Cm_of_not_Vm ju
        (Or.inr (Set.disjoint_right.mp (hSh.disjoint_V hlt) hvC))
      have he_not_jv : e ∉ (C ⟨ju.1 + 1, hjv_lt⟩).E := he_not_Cm_of_not_Vm _
        (Or.inl (Set.disjoint_left.mp (hSh.disjoint_V hlt) huC))
      have he_int : e ⊆ interior (Δ ju) := by
        rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_ju with ⟨hsub, _, _⟩ | ⟨_, _, hv_ni⟩
        · exact hsub
        · exact (hv_ni ((hSh.mem_disc_and_interior_of_circuit_V hS hvC (m := ju)).2.mpr hlt)).elim
      have he_disj : Disjoint e (Δ ⟨ju.1 + 1, hjv_lt⟩) := by
        rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_jv with ⟨_, hu_Δ, _⟩ | ⟨hdisj, _, _⟩
        · exact (not_le_of_gt hlt
            ((hSh.mem_disc_and_interior_of_circuit_V hS huC).1.mp hu_Δ)).elim
        · exact hdisj
      exact Or.inr (Or.inr (Or.inr ⟨ju.1, hjv_lt, Or.inr ⟨huC, hvC⟩,
        subset_sdiff.mpr ⟨he_int, he_disj⟩⟩))
    · exact Or.inr (Or.inl ⟨ju, hSh.edge_induced ju hl huC hvC⟩)
    · have hsucc : ju.1 = jv.1 + 1 := by
        by_contra hne
        have hlt2 : jv.1 + 1 < ju.1 := by have := Fin.lt_def.mp hgt; omega
        let m : Fin d := ⟨jv.1 + 1, by omega⟩
        have he_not : e ∉ (C m).E := he_not_Cm_of_not_Vm m (Or.inr
          (Set.disjoint_left.mp (hSh.disjoint_V_ne
            (Fin.ne_of_lt (Fin.lt_def.mpr (by dsimp only [m]; omega)))) hvC))
        rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not with ⟨_, _, hv_Δ⟩ | ⟨_, hu_ni, _⟩
        · have := Fin.le_def.mp ((hSh.mem_disc_and_interior_of_circuit_V hS hvC (m := m)).1.mp hv_Δ)
          dsimp only [m] at this; omega
        · exact hu_ni ((hSh.mem_disc_and_interior_of_circuit_V hS huC (m := m)).2.mpr
            (Fin.lt_def.mpr hlt2))
      have hju_lt : jv.1 + 1 < d := hsucc ▸ ju.2
      have hju_fin : ju = ⟨jv.1 + 1, hju_lt⟩ := Fin.ext hsucc
      rw [hju_fin] at huC hgt
      have he_not_jv : e ∉ (C jv).E := he_not_Cm_of_not_Vm jv
        (Or.inl (Set.disjoint_right.mp (hSh.disjoint_V hgt) huC))
      have he_not_ju : e ∉ (C ⟨jv.1 + 1, hju_lt⟩).E := he_not_Cm_of_not_Vm _
        (Or.inr (Set.disjoint_left.mp (hSh.disjoint_V hgt) hvC))
      have he_int : e ⊆ interior (Δ jv) := by
        rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_jv with ⟨hsub, _, _⟩ | ⟨_, hu_ni, _⟩
        · exact hsub
        · exact (hu_ni ((hSh.mem_disc_and_interior_of_circuit_V hS huC (m := jv)).2.mpr hgt)).elim
      have he_disj : Disjoint e (Δ ⟨jv.1 + 1, hju_lt⟩) := by
        rcases hSh.edge_inside_or_disjoint_of_notMem hS hl he_not_ju with ⟨_, _, hv_Δ⟩ | ⟨hdisj, _, _⟩
        · exact (not_le_of_gt hgt
            ((hSh.mem_disc_and_interior_of_circuit_V hS hvC).1.mp hv_Δ)).elim
        · exact hdisj
      exact Or.inr (Or.inr (Or.inr ⟨jv.1, hju_lt, Or.inl ⟨huC, hvC⟩,
        subset_sdiff.mpr ⟨he_int, he_disj⟩⟩))

/-- Translate `(G, M, C)` (`G.Simple`, `HasDrawingRadiusLE M d`, `IsDShell M d C`) to surface
`ShellDiscData M.drawing d C_D Δ` on `M.S` with acyclic `innerDraw M.drawing d C_D`. -/
theorem exists_shellDiscData_of_isDShell {α : Type u} {β : Type v}
    {G : Graph α β} {M : PlanarDrawing G} {d : ℕ} {C : Fin d → Graph α β}
    (hSimple : G.Simple) (hrad : HasDrawingRadiusLE M d) (hShell : IsDShell M d C) :
    haveI : T2Space M.S := M.isClosedSurface.2.1
    ∃ (C_D : Fin d → Drawing M.S) (Δ : Fin d → Set M.S),
      M.drawing.toGraph.Simple ∧
      IsIsoMinor G M.drawing.toGraph ∧
      ShellDiscData M.drawing d C_D Δ ∧
      (∀ C' ≤ (innerDraw M.drawing d C_D).toGraph,
        ¬ IsGraphCircuit (innerDraw M.drawing d C_D).toGraph C') := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have hSph : IsSphere M.S := M.isSphere
  have : T2Space M.S := hS.2.1
  have : LocallyConnectedSpace M.S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let D : Drawing M.S := M.drawing
  have hIso : Iso G D.toGraph := M.graphDrawing.iso
  have hSimpleD : D.toGraph.Simple :=
    { not_isLoopAt := fun e x hloop => by
        obtain ⟨u, hu⟩ := hIso.vertexEquiv.surjective ⟨x, hloop.left_mem⟩
        obtain ⟨f, hf⟩ := hIso.edgeEquiv.surjective ⟨e, hloop.edge_mem⟩
        have hlG : G.IsLink f u.1 u.1 :=
          (hIso.isLink_iff f u u).mpr (by rw [hf, hu]; exact hloop)
        exact hSimple.not_isLoopAt f u.1 hlG
      eq_of_isLink := fun e₁ e₂ x y hl₁ hl₂ => by
        obtain ⟨u, hu⟩ := hIso.vertexEquiv.surjective ⟨x, hl₁.left_mem⟩
        obtain ⟨v, hv⟩ := hIso.vertexEquiv.surjective ⟨y, hl₁.right_mem⟩
        obtain ⟨f₁, hf₁⟩ := hIso.edgeEquiv.surjective ⟨e₁, hl₁.edge_mem⟩
        obtain ⟨f₂, hf₂⟩ := hIso.edgeEquiv.surjective ⟨e₂, hl₂.edge_mem⟩
        have hlG₁ : G.IsLink f₁ u.1 v.1 :=
          (hIso.isLink_iff f₁ u v).mpr (by rw [hf₁, hu, hv]; exact hl₁)
        have hlG₂ : G.IsLink f₂ u.1 v.1 :=
          (hIso.isLink_iff f₂ u v).mpr (by rw [hf₂, hu, hv]; exact hl₂)
        have hfeq : f₁ = f₂ := Subtype.ext (hSimple.eq_of_isLink hlG₁ hlG₂)
        exact Subtype.ext_iff.mp (hf₁.symm.trans (congrArg hIso.edgeEquiv hfeq |>.trans hf₂)) }
  let C_D : Fin d → Drawing M.S := fun j => subdrawingOfSubgraph M (C j)
  have hex_Δ : ∀ j : Fin d, ∃ Δ : Set M.S, IsInsideDisc M (C j) Δ :=
    fun j => (exists_unique_insideDisc M (hShell.isNested.1 j)).1
  choose Δ hΔ using hex_Δ
  let m := gmap_fwd_of_planarDrawing M
  have hCD_spec : ∀ j : Fin d,
      (C_D j).IsSubdrawing D ∧ (C_D j).IsCircuit ∧
      (C_D j).V = drawingFwdV M '' V(C j) ∧ (C_D j).E = drawingFwdE M '' E(C j) ∧
      discBd (Δ j) = (C_D j).U := by
    intro j
    obtain ⟨hSub, hV, hE, _, hU⟩ := subdrawingOfSubgraph_spec M (hShell.isNested.1 j).1
    obtain ⟨hCirc, _, _⟩ := isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 j)
    exact ⟨hSub, hCirc, hV, hE, (hΔ j).2.1.trans hU⟩
  have hSh : ShellDiscData D d C_D Δ :=
    { isSubdrawing := fun j => (hCD_spec j).1
      isCircuit := fun j => (hCD_spec j).2.1
      isClosedDisc := fun j => (hΔ j).1
      discBd_eq := fun j => (hCD_spec j).2.2.2.2
      disjoint_V := fun j j' hlt => by
        obtain ⟨hdisj, _, _, _, _, _⟩ := hShell.isNested.2 hlt
        rw [(hCD_spec j).2.2.1, (hCD_spec j').2.2.1, Set.disjoint_left]
        rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
        have heq := m.bijV.injOn ((hShell.isNested.1 j).1.vertexSet_mono hu)
          ((hShell.isNested.1 j').1.vertexSet_mono hv) huv.symm
        exact Set.disjoint_left.mp hdisj hu (heq ▸ hv)
      disc_subset_interior := fun j j' hlt => by
        obtain ⟨hdisj, D_j', D_j, hDj', hDj, hsubD⟩ := hShell.isNested.2 hlt
        have heq_j' : Δ j' = D_j' :=
          (exists_unique_insideDisc M (hShell.isNested.1 j')).2 _ _ (hΔ j') hDj'
        have heq_j : Δ j = D_j :=
          (exists_unique_insideDisc M (hShell.isNested.1 j)).2 _ _ (hΔ j) hDj
        exact insideDisc_subset_interior_of_disjoint M
          (hShell.isNested.1 j) (hShell.isNested.1 j') hdisj (hΔ j) (hΔ j')
          (heq_j'.symm ▸ heq_j.symm ▸ hsubD)
      vertex_in_or_inside := fun hd x hx => by
        obtain ⟨v, hv, rfl⟩ := m.bijV.surjOn hx
        rcases hShell.vertex_in_or_inside hd v hv with ⟨j, hvj⟩ | ⟨⟨_, hv_not_last⟩, Δ₀, hΔ₀, hsub₀⟩
        · exact Or.inl ⟨j, (hCD_spec j).2.2.1 ▸ mem_image_of_mem _ hvj⟩
        · refine Or.inr ?_
          let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
          have heq_last : Δ j_last = Δ₀ :=
            (exists_unique_insideDisc M (hShell.isNested.1 j_last)).2 _ _ (hΔ j_last) hΔ₀
          have hx_Δ : drawingFwdV M v ∈ Δ j_last := by
            rw [heq_last]
            exact hsub₀ (graphDrawingVertexSet_eq_singleton M hv ▸ mem_singleton _)
          rw [← discInt_eq_interior_of_isClosedDisc hS (hΔ j_last).1]
          refine ⟨hx_Δ, fun hx_bd => ?_⟩
          rw [(hCD_spec j_last).2.2.2.2] at hx_bd
          by_cases hx_CV : drawingFwdV M v ∈ (C_D j_last).V
          · rw [(hCD_spec j_last).2.2.1] at hx_CV
            obtain ⟨w, hw, hwv⟩ := hx_CV
            exact hv_not_last
              (m.bijV.injOn ((hShell.isNested.1 j_last).1.vertexSet_mono hw) hv hwv ▸ hw)
          · obtain ⟨e, heC, hxe⟩ := (C_D j_last).exists_edge_of_mem hx_bd hx_CV
            exact (((hCD_spec j_last).1.2 heC).2.1 hxe).2 hx
      edge_induced := fun j e x y hl hx hy => by
        rw [(hCD_spec j).2.2.1] at hx hy
        obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨v, hv, rfl⟩ := hy
        obtain ⟨f, hf, rfl⟩ := m.bijE.surjOn hl.edge_mem
        have hlG : G.IsLink f u v :=
          (m.link hf ((hShell.isNested.1 j).1.vertexSet_mono hu)
            ((hShell.isNested.1 j).1.vertexSet_mono hv)).mpr hl
        rw [(hCD_spec j).2.2.2.1]
        exact mem_image_of_mem _ (hShell.edge_induced j hlG hu hv) }
  -- Use `M' = planarDrawingOfDrawing hS hSph D M.infRegion M.infRegion_mem` directly for acyclicity
  let M' := planarDrawingOfDrawing hS hSph D M.infRegion M.infRegion_mem
  have hFwdV : ∀ v ∈ D.V, drawingFwdV M' v = v := fun v hv => by
    have hv' : v ∈ V(D.toGraph) := hv
    simp [drawingFwdV, M', planarDrawingOfDrawing, hv']
    rfl
  have hFwdE : ∀ e ∈ D.E, drawingFwdE M' e = e := fun e he => by
    have he' : e ∈ E(D.toGraph) := he
    simp [drawingFwdE, M', planarDrawingOfDrawing, he']
    rfl
  have hSubdraw_U : ∀ j : Fin d, (subdrawingOfSubgraph M' (C_D j).toGraph).U = (C_D j).U := by
    intro j
    obtain ⟨_, hVj_s, hEj_s, _, _⟩ := subdrawingOfSubgraph_spec M' (hSh.subdrawing_toGraph_le j)
    have hVj : (subdrawingOfSubgraph M' (C_D j).toGraph).V = (C_D j).V := by
      rw [hVj_s]
      ext x
      exact ⟨fun ⟨v, hv, hvx⟩ => by rw [← hvx, hFwdV v ((hSh.isSubdrawing j).1 hv)]; exact hv,
        fun hx => ⟨x, hx, hFwdV x ((hSh.isSubdrawing j).1 hx)⟩⟩
    have hEj : (subdrawingOfSubgraph M' (C_D j).toGraph).E = (C_D j).E := by
      rw [hEj_s]
      ext e
      exact ⟨fun ⟨f, hf, hfe⟩ => by rw [← hfe, hFwdE f ((hSh.isSubdrawing j).2 hf)]; exact hf,
        fun he => ⟨e, he, hFwdE e ((hSh.isSubdrawing j).2 he)⟩⟩
    rw [(subdrawingOfSubgraph M' (C_D j).toGraph).U_eq, (C_D j).U_eq, hVj, hEj]
    rfl
  have hInside' : ∀ j : Fin d, IsInsideDisc M' (C_D j).toGraph (Δ j) := fun j => by
    obtain ⟨_, _, _, _, hUj⟩ := subdrawingOfSubgraph_spec M' (hSh.subdrawing_toGraph_le j)
    rw [hSubdraw_U j] at hUj
    exact ⟨(hΔ j).1, (hSh.discBd_eq j).trans hUj.symm, (hΔ j).2.2⟩
  have hShell' : IsDShell M' d (fun j => (C_D j).toGraph) := by
    refine ⟨⟨fun j => ?_, fun j j' hlt => ⟨hSh.disjoint_V hlt, Δ j', Δ j,
        hInside' j', hInside' j, (hSh.disc_subset_interior hlt).trans interior_subset⟩⟩, ?_, ?_⟩
    · obtain ⟨u, W, hCyc, hPos, hV, hE⟩ := hSh.isCircuit j
      exact ⟨hSh.subdrawing_toGraph_le j, u, W, hCyc, hPos, hV, hE⟩
    · intro hd v hv
      rcases hSh.vertex_in_or_inside hd v hv with ⟨j, hvj⟩ | hv_int
      · exact Or.inl ⟨j, hvj⟩
      · let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
        refine Or.inr ⟨⟨hv, fun hvC => ?_⟩, Δ j_last, hInside' j_last, fun x hx => ?_⟩
        · have hv_bd : v ∈ discBd (Δ j_last) := (hSh.discBd_eq j_last).symm ▸ (C_D j_last).V_subset_U hvC
          rw [← discInt_eq_interior_of_isClosedDisc hS (hΔ j_last).1] at hv_int
          exact hv_int.2 hv_bd
        · rw [graphDrawingVertexSet_eq_singleton M' hv, hFwdV v hv] at hx
          exact mem_singleton_iff.mp hx ▸ interior_subset hv_int
    · exact fun j e u v hl hu hv => hSh.edge_induced j hl hu hv
  obtain ⟨_, hNV, hNE, hN_le⟩ := innerDraw_spec D d C_D
  refine ⟨C_D, Δ, hSimpleD, hIso.isIsoMinor_left (IsIsoMinor.refl _), hSh, ?_⟩
  intro C' hC'_le hCirc
  have hCircD : IsGraphCircuit D.toGraph C' := by
    obtain ⟨_, u, W, hCyc, hPos, hV, hE⟩ := hCirc
    exact ⟨hC'_le.trans hN_le, u, W, hCyc, hPos, hV, hE⟩
  have hC'_del : C' ≤ GM09.deleteVertices D.toGraph (⋃ j : Fin d, V((C_D j).toGraph)) := by
    refine ⟨fun v hv => ?_, fun e u v hl => ?_⟩
    · have hvN : v ∈ (innerDraw D d C_D).V := hC'_le.vertexSet_mono hv
      rw [hNV] at hvN
      exact hvN
    · have hlN := hl.mono hC'_le
      have huN : u ∈ (innerDraw D d C_D).V := hlN.left_mem
      have hvN : v ∈ (innerDraw D d C_D).V := hlN.right_mem
      rw [hNV] at huN hvN
      exact ⟨hlN.mono hN_le, huN, hvN⟩
  obtain ⟨R, hR, hno_chain⟩ :=
    exists_region_no_chain_of_circuit_delete_shell hShell' C' hC'_del hCircD
  obtain ⟨k, hkd, hchain⟩ := hrad R hR
  exact hno_chain k hkd hchain

end ShellClassification

/-! ## 2. Connecting the Inner Forest `innerDraw D d C` into a Single Tree -/

section ConnectInnerForest

variable {S : Type} [TopologicalSpace S]

/-- Adding a single chord `e_new` between `compSubdraw N v₀` and `restSubdraw N v₀` inside a region
`q ∈ D.R` (`q ⊆ interior (Δ ⟨d - 1, _⟩)`) preserves `ShellDiscData`, simplicity, and acyclicity of
`innerDraw`, while increasing `E(innerDraw).ncard` by `1`. -/
theorem connect_innerDraw_step [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hd : 0 < d) (hSimple : D.toGraph.Simple) (hSh : ShellDiscData D d C Δ)
    (hNoCirc : haveI : T2Space S := hS.2.1
      ∀ C' ≤ (innerDraw D d C).toGraph, ¬ IsGraphCircuit (innerDraw D d C).toGraph C')
    {v₀ : S} (hv₀ : haveI : T2Space S := hS.2.1; v₀ ∈ (innerDraw D d C).V)
    (hRest : haveI : T2Space S := hS.2.1; (restSubdraw (innerDraw D d C) v₀).V.Nonempty) :
    haveI : T2Space S := hS.2.1
    ∃ D' : Drawing S,
      D'.toGraph.Simple ∧
      D.toGraph ≤ D'.toGraph ∧
      ShellDiscData D' d C Δ ∧
      (innerDraw D' d C).V = (innerDraw D d C).V ∧
      (innerDraw D' d C).E.ncard = (innerDraw D d C).E.ncard + 1 ∧
      (∀ C' ≤ (innerDraw D' d C).toGraph, ¬ IsGraphCircuit (innerDraw D' d C).toGraph C') := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let N := innerDraw D d C
  let j_last : Fin d := ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩
  let C_last := C j_last
  let Δ_last := Δ j_last
  obtain ⟨hNs, hNV, hNE, hN_le⟩ := innerDraw_spec D d C
  -- `N` has no circuit subdrawings, hence `R_N = univ \ N.U ∈ N.R` with `closure R_N = univ`
  have hno_draw : ∀ C₀ : Drawing S, C₀.IsCircuit → C₀.IsSubdrawing N → False := by
    intro C₀ hC₀ hSub₀
    have hC₀_le : C₀.toGraph ≤ N.toGraph := by
      refine ⟨hSub₀.1, fun e u v hl => ⟨hSub₀.2 hl.1, hSub₀.1 hl.2.1, hSub₀.1 hl.2.2.1, ?_⟩⟩
      rw [← hSub₀.closure_inter_V hl.1]
      exact hl.2.2.2
    obtain ⟨u, W, hCyc, hPos, hV, hE⟩ := hC₀
    exact hNoCirc C₀.toGraph hC₀_le ⟨hC₀_le, u, W, hCyc, hPos, hV, hE⟩
  have hPre_compl : IsPreconnected N.Uᶜ := GM11.isPreconnected_compl_of_noCircuit hS N hno_draw
  obtain ⟨p₀, -, hp₀_not_NU⟩ := GM11.exists_notMem_U (Γ := N) hS isOpen_univ univ_nonempty
  let R_N : Set S := univ \ N.U
  have hRN : R_N ∈ N.R := by
    rw [GM11.mem_R_iff]
    refine ⟨p₀, hp₀_not_NU, ?_⟩
    refine Subset.antisymm ?_ (connectedComponentIn_subset _ _)
    exact (compl_eq_univ_sdiff N.U ▸ hPre_compl).subset_connectedComponentIn
      ⟨mem_univ p₀, hp₀_not_NU⟩ subset_rfl
  have hcl_RN_univ : closure R_N = univ := by
    refine eq_univ_of_forall fun x => mem_closure_iff.mpr fun O hO hxO => ?_
    obtain ⟨z, hzO, hz_not_NU⟩ := GM11.exists_notMem_U (Γ := N) hS hO ⟨x, hxO⟩
    exact ⟨z, hzO, mem_univ z, hz_not_NU⟩
  let N₁ := compSubdraw N v₀
  let N₂ := restSubdraw N v₀
  obtain ⟨hN₁s, hN₂s, hN₁V, hN₂V, _, _, hv₀_N₁, hNU_union, hNU_disj, _⟩ := compSubdraw_spec N hv₀
  obtain ⟨w₀, hw₀_N₂⟩ := hRest
  -- Form `N_plus = N.glue C_last` and its annular-like region `Ω = R_N ∩ interior Δ_last`
  have hNU_int : N.U ⊆ interior Δ_last := hSh.innerDraw_U_subset_interior hS hd
  have hbd_eq : discBd Δ_last = C_last.U := hSh.discBd_eq j_last
  have hfr_Δ : frontier Δ_last = C_last.U :=
    (GM11.IsClosedDisc.frontier_eq_discBd hS (hSh.isClosedDisc j_last)).trans hbd_eq
  have hdisj_NC : Disjoint N.U C_last.U := by
    refine Set.disjoint_left.mpr fun z hzN hzC => ?_
    have hz_int := hNU_int hzN
    rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_last)] at hz_int
    exact hz_int.2 (hbd_eq.symm ▸ hzC)
  let N_plus := N.glue C_last
    (by rw [Set.disjoint_iff_inter_eq_empty.mp hdisj_NC]; exact empty_subset _)
  have hNp_E : N_plus.E = N.E ∪ C_last.E := by
    change (N.glue C_last _).E = N.E ∪ C_last.E
    rw [Drawing.glue_E]
  have hNp_sub : N_plus.IsSubdrawing D :=
    ⟨union_subset hNs.1 (hSh.isSubdrawing j_last).1,
      hNp_E ▸ union_subset hNs.2 (hSh.isSubdrawing j_last).2⟩
  let Ω : Set S := R_N ∩ interior Δ_last
  have hv₀_cl_Ω : v₀ ∈ closure Ω := by
    rw [mem_closure_iff]
    intro O hO hv₀O
    have hv₀_int : v₀ ∈ interior Δ_last := hNU_int (hN₁s.U_subset (N₁.V_subset_U hv₀_N₁))
    obtain ⟨w, ⟨hwO, hw_int⟩, hwRN⟩ :=
      mem_closure_iff.mp (hcl_RN_univ ▸ mem_univ v₀) (O ∩ interior Δ_last)
        (hO.inter isOpen_interior) ⟨hv₀O, hv₀_int⟩
    exact ⟨w, hwO, hwRN, hw_int⟩
  have hw₀_cl_Ω : w₀ ∈ closure Ω := by
    rw [mem_closure_iff]
    intro O hO hw₀O
    have hw₀_int : w₀ ∈ interior Δ_last := hNU_int (hN₂s.U_subset (N₂.V_subset_U hw₀_N₂))
    obtain ⟨w, ⟨hwO, hw_int⟩, hwRN⟩ :=
      mem_closure_iff.mp (hcl_RN_univ ▸ mem_univ w₀) (O ∩ interior Δ_last)
        (hO.inter isOpen_interior) ⟨hw₀O, hw₀_int⟩
    exact ⟨w, hwO, hwRN, hw_int⟩
  obtain ⟨p₁, -, hp₁_Ω⟩ := mem_closure_iff.mp hv₀_cl_Ω univ isOpen_univ (mem_univ v₀)
  have hp₁_not_Np : p₁ ∉ N_plus.U := by
    rintro (hpN | hpC)
    · exact GM11.region_subset hRN hp₁_Ω.1 hpN
    · have hp_int := hp₁_Ω.2
      rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_last)] at hp_int
      exact hp_int.2 (hbd_eq.symm ▸ hpC)
  obtain ⟨Ω', hΩ', hp₁_Ω'⟩ := GM11.exists_region_of_notMem hp₁_not_Np
  have hΩ'_sub_Ω : Ω' ⊆ Ω := by
    have hsub_RN : Ω' ⊆ R_N :=
      GM11.subset_region hRN (GM11.region_isPreconnected hΩ')
        (Set.disjoint_left.mpr fun z hzΩ' hzN => GM11.region_subset hΩ' hzΩ' (Or.inl hzN))
        hp₁_Ω' hp₁_Ω.1
    have hdisj_C : Disjoint Ω' C_last.U :=
      Set.disjoint_left.mpr fun z hzΩ' hzC => GM11.region_subset hΩ' hzΩ' (Or.inr hzC)
    have hsub_Δ : Ω' ⊆ Δ_last := by
      rcases GM11.subset_or_disjoint_of_frontier (hSh.isClosedDisc j_last).isClosed
          (GM11.region_isPreconnected hΩ') (hfr_Δ.symm ▸ hdisj_C) with hsub | hdisj
      · exact hsub
      · exact (Set.disjoint_left.mp hdisj hp₁_Ω' (interior_subset hp₁_Ω.2)).elim
    intro z hzΩ'
    refine ⟨hsub_RN hzΩ', ?_⟩
    rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_last)]
    exact ⟨hsub_Δ hzΩ', fun hz_bd => Set.disjoint_left.mp hdisj_C hzΩ' (hbd_eq ▸ hz_bd)⟩
  have hΩ_sub_Ω' : Ω ⊆ Ω' := by
    intro y hyΩ
    let Q_out : Set S := Ωᶜ
    have hp₁_not_Q : p₁ ∉ Q_out := not_not.mpr hp₁_Ω
    have hy_not_Q : y ∉ Q_out := not_not.mpr hyΩ
    have hNp_Q : N_plus.U ⊆ Q_out := by
      rintro z (hzN | hzC) hzΩ
      · exact GM11.region_subset hRN hzΩ.1 hzN
      · have hz_int := hzΩ.2
        rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_last)] at hz_int
        exact hz_int.2 (hbd_eq.symm ▸ hzC)
    obtain ⟨r_same, hr_same, hp₁_same, hy_same⟩ :=
      GM11.same_region_of_discs hS hSph hp₁_not_Q hy_not_Q N_plus.E.ncard N_plus rfl hNp_Q
        (fun F hF hF_sub => by
          have hF_split : F ⊆ N.U ∪ C_last.U := hF_sub
          by_cases hFN : (F ∩ N.U).Nonempty
          · have hF_in_N : F ⊆ N.U := by
              intro x hxF
              by_contra hx_not_N
              have hxC : x ∈ C_last.U := (hF_split hxF).resolve_left hx_not_N
              obtain ⟨w, -, hwN, hwC⟩ :=
                isPreconnected_closed_iff.mp hF.isPreconnected N.U C_last.U
                  N.isClosed_U C_last.isClosed_U hF_split hFN ⟨x, hxF, hxC⟩
              exact Set.disjoint_left.mp hdisj_NC hwN hwC
            obtain ⟨Δ_F, hΔ_F, hbd_F, hdisj_F⟩ :=
              GM11.exists_disc_missing hS hSph hF (GM11.region_isPreconnected hRN)
                (Set.disjoint_left.mpr fun x hxRN hxF =>
                  GM11.region_subset hRN hxRN (hF_in_N hxF))
            exact ⟨Δ_F, hΔ_F, fun x hxΔ hxΩ =>
              Set.disjoint_left.mp hdisj_F hxΔ hxΩ.1, hbd_F⟩
          · have hF_in_C : F ⊆ C_last.U := fun x hxF =>
              (hF_split hxF).resolve_left fun hxN => hFN ⟨x, hxF, hxN⟩
            have hint_pre : IsPreconnected (interior Δ_last) := by
              rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc j_last)]
              exact (hSh.isClosedDisc j_last).isPreconnected_discInt
            obtain ⟨Δ_F, hΔ_F, hbd_F, hdisj_F⟩ :=
              GM11.exists_disc_missing hS hSph hF hint_pre
                (Set.disjoint_left.mpr fun x hx_int hxF => by
                  rw [← discInt_eq_interior_of_isClosedDisc hS
                    (hSh.isClosedDisc j_last)] at hx_int
                  exact hx_int.2 (hbd_eq.symm ▸ hF_in_C hxF))
            exact ⟨Δ_F, hΔ_F, fun x hxΔ hxΩ =>
              Set.disjoint_left.mp hdisj_F hxΔ hxΩ.2, hbd_F⟩)
    rwa [← GM11.region_eq_of_mem hr_same hΩ' hp₁_same hp₁_Ω']
  have hΩ_mem : Ω ∈ N_plus.R := Subset.antisymm hΩ'_sub_Ω hΩ_sub_Ω' ▸ hΩ'
  have hcl_Ω_eq := closure_RN_eq_biUnion_closure_regions hS hNp_sub hΩ_mem
  have hv₀_un : v₀ ∈ ⋃ (q ∈ D.R) (_ : q ⊆ Ω), closure q := hcl_Ω_eq ▸ hv₀_cl_Ω
  simp only [mem_iUnion, exists_prop] at hv₀_un
  obtain ⟨r₁, hr₁, hr₁_Ω, hv₀_r₁⟩ := hv₀_un
  have hw₀_un : w₀ ∈ ⋃ (q ∈ D.R) (_ : q ⊆ Ω), closure q := hcl_Ω_eq ▸ hw₀_cl_Ω
  simp only [mem_iUnion, exists_prop] at hw₀_un
  obtain ⟨r₂, hr₂, hr₂_Ω, hw₀_r₂⟩ := hw₀_un
  have h_exists_q : ∃ q ∈ D.R, q ⊆ interior Δ_last ∧
      (closure q ∩ N₁.U).Nonempty ∧ (closure q ∩ N₂.U).Nonempty := by
    let Z : Set (Set S) := {q ∈ D.R | q ⊆ Ω ∧ (closure q ∩ N₁.U).Nonempty}
    have hr₁_Z : r₁ ∈ Z := ⟨hr₁, hr₁_Ω, v₀, hv₀_r₁, N₁.V_subset_U hv₀_N₁⟩
    by_cases hr₂_Z : r₂ ∈ Z
    · exact ⟨r₂, hr₂, hr₂_Ω.trans inter_subset_right, hr₂_Z.2.2,
        w₀, hw₀_r₂, N₂.V_subset_U hw₀_N₂⟩
    · obtain ⟨e, heD, he_not_Np, a, b, haZ, hbZ, ha_Ω, hb_Ω, ⟨_, haR, pa, hpa_e, hpa_a⟩,
          ⟨_, hbR, pb, hpb_e, hpb_b⟩⟩ :=
        GM11.theorem_5_1_proof hS hNp_sub hΩ_mem hr₁ hr₁_Z hr₂ hr₂_Z hr₁_Ω hr₂_Ω
      have he_cl_a : closure e ⊆ closure a :=
        closure_minimal (GM11.edge_subset_closure_of_incident hS heD haR ⟨pa, hpa_e, hpa_a⟩)
          isClosed_closure
      have he_cl_b : closure e ⊆ closure b :=
        closure_minimal (GM11.edge_subset_closure_of_incident hS heD hbR ⟨pb, hpb_e, hpb_b⟩)
          isClosed_closure
      have ha_cl_Δ : closure a ⊆ Δ_last :=
        closure_minimal ((ha_Ω.trans inter_subset_right).trans interior_subset)
          (hSh.isClosedDisc j_last).isClosed
      have hV_in_CN : ∀ w ∈ closure e ∩ D.V, w ∈ C_last.V ∨ w ∈ N.V := by
        intro w ⟨hwe, hwV⟩
        have hw_Δ : w ∈ Δ_last := ha_cl_Δ (he_cl_a hwe)
        rcases hSh.vertex_in_or_inside hd w hwV with ⟨i, hwi⟩ | hw_int
        · by_cases hij : i = j_last
          · exact Or.inl (show w ∈ (C j_last).V from hij ▸ hwi)
          · exfalso
            have hilt : i < j_last :=
              lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
            have hw_int_i : w ∈ interior (Δ i) := hSh.disc_subset_interior hilt hw_Δ
            rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc i)] at hw_int_i
            exact hw_int_i.2 ((hSh.discBd_eq i).symm ▸ (C i).V_subset_U hwi)
        · refine Or.inr (hNV.symm ▸ ⟨hwV, fun h_un => ?_⟩)
          obtain ⟨i, hwi⟩ := mem_iUnion.mp h_un
          have hw_int_i : w ∈ interior (Δ i) := by
            by_cases hij : i = j_last
            · exact hij ▸ hw_int
            · have hilt : i < j_last :=
                lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt i.2)) hij
              exact hSh.disc_subset_interior hilt (interior_subset hw_int)
          rw [← discInt_eq_interior_of_isClosedDisc hS (hSh.isClosedDisc i)] at hw_int_i
          exact hw_int_i.2 ((hSh.discBd_eq i).symm ▸ (C i).V_subset_U hwi)
      have h_has_NV : ∃ w ∈ closure e ∩ D.V, w ∈ N.V := by
        by_contra hno_NV
        push Not at hno_NV
        have hall_C : ∀ w ∈ closure e ∩ D.V, w ∈ C_last.V := fun w hw =>
          (hV_in_CN w hw).resolve_right (hno_NV w hw)
        rcases D.edge_cond e heD with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
        · have hu : u ∈ closure e ∩ D.V := hcap ▸ mem_insert u {v}
          have hv : v ∈ closure e ∩ D.V := hcap ▸ mem_insert_of_mem u rfl
          have heC : e ∈ C_last.E :=
            hSh.edge_induced j_last ⟨heD, hu.2, hv.2, hcap⟩ (hall_C u hu) (hall_C v hv)
          exact he_not_Np (hNp_E ▸ Or.inr heC)
        · have hu : u ∈ closure e ∩ D.V := hcap ▸ mem_singleton u
          exact hSimple.not_isLoopAt e u ⟨heD, hu.2, hu.2, hcap.trans (pair_eq_singleton u).symm⟩
      obtain ⟨w, ⟨hwe, _⟩, hwNV⟩ := h_has_NV
      have hw_not_N₁ : w ∉ N₁.U := fun hw₁ => hbZ ⟨hbR, hb_Ω, w, he_cl_b hwe, hw₁⟩
      have hw_N₂ : w ∈ N₂.U := (hNU_union ▸ N.V_subset_U hwNV).resolve_left hw_not_N₁
      exact ⟨a, haR, ha_Ω.trans inter_subset_right, haZ.2.2, w, he_cl_a hwe, hw_N₂⟩
  obtain ⟨q, hq, _, hq_N₁, hq_N₂⟩ := h_exists_q
  have h_vert_of_cl : ∀ (Γ₀ : Drawing S), Γ₀.IsSubdrawing N →
      (closure q ∩ Γ₀.U).Nonempty → ∃ v ∈ Γ₀.V, v ∈ closure q := by
    intro Γ₀ hΓ₀s ⟨z, hzq, hzΓ₀⟩
    by_cases hzV : z ∈ Γ₀.V
    · exact ⟨z, hzV, hzq⟩
    · obtain ⟨e, heΓ₀, hze⟩ := Γ₀.exists_edge_of_mem hzΓ₀ hzV
      have heD : e ∈ D.E := hNs.2 (hΓ₀s.2 heΓ₀)
      have he_cl : closure e ⊆ closure q :=
        closure_minimal (GM11.edge_subset_closure_of_incident hS heD hq ⟨z, hze, hzq⟩)
          isClosed_closure
      rcases Γ₀.edge_cond e heΓ₀ with ⟨u, v, -, hcap, -⟩ | ⟨u, hcap, -⟩
      · have hu : u ∈ closure e ∩ Γ₀.V := hcap ▸ mem_insert u {v}
        exact ⟨u, hu.2, he_cl hu.1⟩
      · have hu : u ∈ closure e ∩ Γ₀.V := hcap ▸ mem_singleton u
        exact ⟨u, hu.2, he_cl hu.1⟩
  obtain ⟨v₁, hv₁_N₁, hv₁_cl_q⟩ := h_vert_of_cl N₁ hN₁s hq_N₁
  obtain ⟨v₂, hv₂_N₂, hv₂_cl_q⟩ := h_vert_of_cl N₂ hN₂s hq_N₂
  have hv₁_NV : v₁ ∈ N.V := hN₁s.1 hv₁_N₁
  have hv₂_NV : v₂ ∈ N.V := hN₂s.1 hv₂_N₂
  have hv₁_D : v₁ ∈ D.V := hNs.1 hv₁_NV
  have hv₂_D : v₂ ∈ D.V := hNs.1 hv₂_NV
  have hv₁v₂ : v₁ ≠ v₂ := fun heq =>
    Set.disjoint_left.mp hNU_disj (N₁.V_subset_U hv₁_N₁) (heq ▸ N₂.V_subset_U hv₂_N₂)
  have hnotAdj : ¬ D.toGraph.Adj v₁ v₂ := by
    rintro ⟨e, heD, _, _, hcap⟩
    have heN : e ∈ N.E := by
      rw [hNE]
      refine ⟨heD, ?_⟩
      rw [hcap, ← hNV]
      rintro z (rfl | rfl)
      · exact hv₁_NV
      · exact hv₂_NV
    rcases edge_reach_or_rest N heN with h₁ | h₂
    · have hv₂_in : v₂ ∈ closure e ∩ N.V := by
        rw [hNs.closure_inter_V heN, hcap]; exact mem_insert_of_mem v₁ rfl
      exact (hN₂V ▸ hv₂_N₂).2 (h₁ hv₂_in)
    · have hv₁_in : v₁ ∈ closure e ∩ N.V := by
        rw [hNs.closure_inter_V heN, hcap]; exact mem_insert v₁ {v₂}
      exact (h₂ hv₁_in).2 (hN₁V ▸ hv₁_N₁)
  obtain ⟨g₁, hg₁, hg₁0, hg₁t⟩ := GM11.exists_path_into_region hS D hv₁_D hq hv₁_cl_q
  obtain ⟨g₂, hg₂, hg₂0, hg₂t⟩ := GM11.exists_path_into_region hS D hv₂_D hq hv₂_cl_q
  have hq_pc : IsPathConnected q :=
    GM11.isPathConnected_of_isOpen hS (GM11.region_isOpen hq)
      (GM11.region_isPreconnected hq) (GM11.region_nonempty hq)
  have hv₁_not_q : v₁ ∉ q := fun h => GM11.region_subset hq h (D.V_subset_U hv₁_D)
  obtain ⟨γ, hγ_cont, hγ_inj, hγ0, hγ1, hγ_in, -⟩ :=
    GM11.exists_chord hq_pc hv₁v₂ hv₁_not_q hg₁ hg₂ hg₁0 hg₂0 hg₁t hg₂t
  let K : Set S := range γ
  have hK : IsLineWithEnds K v₁ v₂ := hγ0 ▸ hγ1 ▸ GM11.isLine_range hγ_cont hγ_inj
  have hKq : K \ {v₁, v₂} ⊆ q := by
    rintro _ ⟨⟨t, rfl⟩, hnot⟩
    exact hγ_in t (fun h => hnot (Or.inl (h ▸ hγ0))) (fun h => hnot (Or.inr (h ▸ hγ1)))
  let hmeet := lineDrawing_meet_of_subset_region hq hv₁_D hv₂_D hK hv₁v₂ hKq
  let D' := D.glue (GM11.lineDrawing hK hv₁v₂) hmeet
  let N' := innerDraw D' d C
  let e_new : Set S := K \ {v₁, v₂}
  obtain ⟨hN's, hN'V, hN'E, hN'_le⟩ := innerDraw_spec D' d C
  have hV_sub_L : (GM11.lineDrawing hK hv₁v₂).V ⊆ D.V := by
    rintro z (rfl | rfl)
    · exact hv₁_D
    · exact hv₂_D
  have hD'V : D'.V = D.V := union_eq_left.mpr hV_sub_L
  have hD'E : D'.E = insert e_new D.E := by
    change (D.glue (GM11.lineDrawing hK hv₁v₂) hmeet).E = insert e_new D.E
    rw [Drawing.glue_E, GM11.lineDrawing_E, union_singleton]
  have hcl_enew : closure e_new = K := GM11.closure_sdiff_pair hK
  have hcap_enew : closure e_new ∩ D'.V = {v₁, v₂} := by
    rw [hcl_enew, hD'V]
    refine Subset.antisymm (fun z ⟨hzK, hzV⟩ => ?_) ?_
    · by_contra hnot
      exact GM11.region_subset hq (hKq ⟨hzK, hnot⟩) (D.V_subset_U hzV)
    · rintro z (rfl | rfl)
      · exact ⟨(GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inl rfl), hv₁_D⟩
      · exact ⟨(GM11.lineDrawing hK hv₁v₂).V_subset_U (Or.inr rfl), hv₂_D⟩
  have he_new_not_DE : e_new ∉ D.E := by
    intro heD
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : 𝕀, t₀ ≠ 0 ∧ t₀ ≠ 1 :=
      ⟨⟨1 / 2, by norm_num, by norm_num⟩,
        fun h => by have := congrArg Subtype.val h; norm_num at this,
        fun h => by have := congrArg Subtype.val h; norm_num at this⟩
    have hx_e : γ t₀ ∈ e_new :=
      ⟨⟨t₀, rfl⟩, fun h => by
        rcases h with h | h
        · exact ht₀.1 (hγ_inj (h.trans hγ0.symm))
        · exact ht₀.2 (hγ_inj ((mem_singleton_iff.mp h).trans hγ1.symm))⟩
    exact GM11.region_subset hq (hKq hx_e) (D.closure_subset_U heD (subset_closure hx_e))
  have hD_le_D' : D.toGraph ≤ D'.toGraph := by
    refine ⟨hD'V.symm.subset, fun e u v hl => ?_⟩
    exact ⟨hD'E ▸ mem_insert_of_mem e_new hl.1, hD'V ▸ hl.2.1, hD'V ▸ hl.2.2.1,
      hD'V ▸ hl.2.2.2⟩
  have hSimpleD' : D'.toGraph.Simple :=
    { not_isLoopAt := fun e x hloop => by
        rcases hD'E ▸ hloop.1 with rfl | heD
        · have hpair := hcap_enew.symm.trans hloop.2.2.2
          have hv1_eq : v₁ = x := by
            have : v₁ ∈ ({x, x} : Set S) := hpair ▸ mem_insert v₁ {v₂}
            rcases this with rfl | h <;> simp_all
          have hv2_eq : v₂ = x := by
            have : v₂ ∈ ({x, x} : Set S) := hpair ▸ mem_insert_of_mem v₁ rfl
            rcases this with rfl | h <;> simp_all
          exact hv₁v₂ (hv1_eq.trans hv2_eq.symm)
        · exact hSimple.not_isLoopAt e x ⟨heD, hD'V ▸ hloop.2.1, hD'V ▸ hloop.2.2.1,
            hD'V ▸ hloop.2.2.2⟩
      eq_of_isLink := fun e₁ e₂ x y hl₁ hl₂ => by
        rcases hD'E ▸ hl₁.1 with rfl | he₁ <;> rcases hD'E ▸ hl₂.1 with rfl | he₂
        · rfl
        · exfalso
          have hpair : ({x, y} : Set S) = {v₁, v₂} := hl₁.2.2.2.symm.trans hcap_enew
          exact hnotAdj ⟨e₂, he₂, hv₁_D, hv₂_D, (hD'V ▸ hl₂.2.2.2).trans hpair⟩
        · exfalso
          have hpair : ({x, y} : Set S) = {v₁, v₂} := hl₂.2.2.2.symm.trans hcap_enew
          exact hnotAdj ⟨e₁, he₁, hv₁_D, hv₂_D, (hD'V ▸ hl₁.2.2.2).trans hpair⟩
        · exact hSimple.eq_of_isLink
            ⟨he₁, hD'V ▸ hl₁.2.1, hD'V ▸ hl₁.2.2.1, hD'V ▸ hl₁.2.2.2⟩
            ⟨he₂, hD'V ▸ hl₂.2.1, hD'V ▸ hl₂.2.2.1, hD'V ▸ hl₂.2.2.2⟩ }
  have hSh' : ShellDiscData D' d C Δ :=
    { isSubdrawing := fun j =>
        ⟨hD'V ▸ (hSh.isSubdrawing j).1,
          fun e he => hD'E ▸ mem_insert_of_mem e_new ((hSh.isSubdrawing j).2 he)⟩
      isCircuit := hSh.isCircuit
      isClosedDisc := hSh.isClosedDisc
      discBd_eq := hSh.discBd_eq
      disjoint_V := hSh.disjoint_V
      disc_subset_interior := hSh.disc_subset_interior
      vertex_in_or_inside := fun hd' v hv => hSh.vertex_in_or_inside hd' v (hD'V ▸ hv)
      edge_induced := fun j e u v hl hu hv => by
        rcases hD'E ▸ hl.1 with rfl | heD
        · exfalso
          have hu_in : u ∈ ({v₁, v₂} : Set S) := hcap_enew ▸ hl.2.2.2.symm ▸ mem_insert u {v}
          rcases hu_in with rfl | rfl
          · exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j) hv₁_NV hu
          · exact Set.disjoint_left.mp (hSh.innerDraw_V_disjoint_circuit_V j) hv₂_NV hu
        · exact hSh.edge_induced j ⟨heD, hD'V ▸ hl.2.1, hD'V ▸ hl.2.2.1, hD'V ▸ hl.2.2.2⟩ hu hv }
  have hN'V_eq : N'.V = N.V := by rw [hN'V, hNV, hD'V]
  have hN'E_eq : N'.E = insert e_new N.E := by
    rw [hN'E, hNE, hD'E, hD'V]
    ext e
    simp only [mem_ofPred_eq, mem_insert_iff]
    constructor
    · rintro ⟨rfl | heD, hsub⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨heD, hsub⟩
    · rintro (rfl | ⟨heD, hsub⟩)
      · refine ⟨Or.inl rfl, ?_⟩
        rw [← hNV, ← hD'V, hcap_enew]
        rintro z (rfl | rfl)
        · exact hv₁_NV
        · exact hv₂_NV
      · exact ⟨Or.inr heD, hsub⟩
  have he_new_not_NE : e_new ∉ N.E := fun h => he_new_not_DE (hNs.2 h)
  have hN'E_card : N'.E.ncard = N.E.ncard + 1 := by
    rw [hN'E_eq, ncard_insert_of_notMem he_new_not_NE N.finite_edges]
  -- `N'` remains acyclic because `e_new` is a bridge between `N₁` and `N₂`
  have hN_le_N' : N.toGraph ≤ N'.toGraph := by
    refine ⟨hN'V_eq.symm.subset, fun e u v hl => ?_⟩
    refine ⟨hN'E_eq ▸ mem_insert_of_mem e_new hl.1, hN'V_eq ▸ hl.2.1, hN'V_eq ▸ hl.2.2.1, ?_⟩
    rw [hN's.closure_inter_V (hN'E_eq ▸ mem_insert_of_mem e_new hl.1), hD'V,
      ← hNs.closure_inter_V hl.1]
    exact hl.2.2.2
  have hl_enew_N' : N'.toGraph.IsLink e_new v₁ v₂ :=
    ⟨hN'E_eq ▸ mem_insert e_new N.E, hN'V_eq ▸ hv₁_NV, hN'V_eq ▸ hv₂_NV,
      (hN's.closure_inter_V (hN'E_eq ▸ mem_insert e_new N.E)).trans hcap_enew⟩
  have hNoCirc' : ∀ C' ≤ N'.toGraph, ¬ IsGraphCircuit N'.toGraph C' := by
    intro C' hC'_le ⟨_, u₀, W, hCyc, hPos, hVC', hEC'⟩
    by_cases he_mem : e_new ∈ W.edges
    · -- Split `W` (`W.edges.Nodup`) at `e_new` to obtain a walk in `N.toGraph` between `v₁` and `v₂`
      have hsplit : ∀ {a b : S} (Q : GraphWalk C' a b),
          Q.edges.Nodup → e_new ∈ Q.edges →
          ∃ (x y : S) (Q₁ : GraphWalk C' a x) (Q₂ : GraphWalk C' y b),
            C'.IsLink e_new x y ∧ e_new ∉ Q₁.edges ∧ e_new ∉ Q₂.edges := by
        intro a b Q
        induction Q with
        | nil _ => intro _ h; cases h
        | @cons p q r f hlf rest ih =>
          intro hnd hmem
          have hnd_cons := List.nodup_cons.mp hnd
          rcases List.mem_cons.mp hmem with rfl | hrest
          · exact ⟨p, q, .nil hlf.left_mem, rest, hlf, by simp, hnd_cons.1⟩
          · obtain ⟨x, y, Q₁, Q₂, hl_xy, hn₁, hn₂⟩ := ih hnd_cons.2 hrest
            have hfp : f ≠ e_new := fun h => hnd_cons.1 (h ▸ hrest)
            exact ⟨x, y, .cons hlf Q₁, Q₂, hl_xy,
              fun h => (List.mem_cons.mp h).elim (fun h' => hfp h'.symm) hn₁, hn₂⟩
      obtain ⟨x, y, Q₁, Q₂, hl_xy, hn₁, hn₂⟩ := hsplit W hCyc.2 he_mem
      have hto_N : ∀ {a b : S} (Q : GraphWalk C' a b), a ∈ V(C') → e_new ∉ Q.edges →
          Nonempty (GraphWalk N.toGraph a b) := by
        intro a b Q
        induction Q with
        | @nil p hp =>
          intro _ _
          have hpN' : p ∈ N'.V := hC'_le.vertexSet_mono hp
          rw [hN'V_eq] at hpN'
          exact ⟨.nil hpN'⟩
        | @cons p q r f hlf rest ih =>
          intro hp hn
          have hfn : f ≠ e_new := fun h => hn (h ▸ List.mem_cons_self)
          have hnr : e_new ∉ rest.edges := fun h => hn (List.mem_cons_of_mem _ h)
          obtain ⟨Q_rest⟩ := ih hlf.right_mem hnr
          have hlf_N' : N'.toGraph.IsLink f p q := hlf.mono hC'_le
          have hf_NE : f ∈ N.E := (hN'E_eq ▸ hlf_N'.1).resolve_left hfn
          have hlf_N : N.toGraph.IsLink f p q :=
            ⟨hf_NE, hN'V_eq ▸ hlf_N'.2.1, hN'V_eq ▸ hlf_N'.2.2.1, by
              rw [hNs.closure_inter_V hf_NE, ← hD'V, ← hN's.closure_inter_V hlf_N'.1]
              exact hlf_N'.2.2.2⟩
          exact ⟨.cons hlf_N Q_rest⟩
      have hu₀_C' : u₀ ∈ V(C') := by
        cases W with
        | nil h => exact h
        | cons hlf _ => exact hlf.left_mem
      obtain ⟨P₁⟩ := hto_N Q₁ hu₀_C' hn₁
      obtain ⟨P₂⟩ := hto_N Q₂ hl_xy.right_mem hn₂
      have P_yx : GraphWalk N.toGraph y x := P₂.append P₁
      obtain ⟨W_v₁⟩ := (hN₁V ▸ hv₁_N₁).2
      have hl_xy_N' : N'.toGraph.IsLink e_new x y := hl_xy.mono hC'_le
      rcases hl_xy_N'.left_eq_or_eq hl_enew_N' with rfl | rfl
      · rw [hl_xy_N'.right_unique hl_enew_N'] at P_yx
        exact (hN₂V ▸ hv₂_N₂).2 ⟨hv₂_NV, ⟨W_v₁.append P_yx.reverse⟩⟩
      · rw [hl_xy_N'.right_unique hl_enew_N'.symm] at P_yx
        exact (hN₂V ▸ hv₂_N₂).2 ⟨hv₂_NV, ⟨W_v₁.append P_yx⟩⟩
    · have hC'_le_N : C' ≤ N.toGraph := by
        refine ⟨fun v hv => ?_, fun e u v hl => ?_⟩
        · have hvN' : v ∈ N'.V := hC'_le.vertexSet_mono hv
          rwa [hN'V_eq] at hvN'
        · have he_W : e ∈ W.edges := by
            have heC' : e ∈ E(C') := hl.edge_mem
            rwa [hEC'] at heC'
          have he_ne : e ≠ e_new := fun h => he_mem (h ▸ he_W)
          have hl_N' := hl.mono hC'_le
          have he_NE : e ∈ N.E := (hN'E_eq ▸ hl_N'.1).resolve_left he_ne
          exact ⟨he_NE, hN'V_eq ▸ hl_N'.2.1, hN'V_eq ▸ hl_N'.2.2.1, by
            rw [hNs.closure_inter_V he_NE, ← hD'V, ← hN's.closure_inter_V hl_N'.1]
            exact hl_N'.2.2.2⟩
      exact hNoCirc C' hC'_le_N ⟨hC'_le_N, u₀, W, hCyc, hPos, hVC', hEC'⟩
  exact ⟨D', hSimpleD', hD_le_D', hSh', hN'V_eq, hN'E_card, hNoCirc'⟩

/-- Iterate `connect_innerDraw_step` until `innerDraw D' d C` is a single connected acyclic tree. -/
theorem exists_connected_innerDraw [ConnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {d : ℕ} {C : Fin d → Drawing S} {Δ : Fin d → Set S}
    (hd : 0 < d) (hSimple : D.toGraph.Simple) (hSh : ShellDiscData D d C Δ)
    (hNoCirc : haveI : T2Space S := hS.2.1
      ∀ C' ≤ (innerDraw D d C).toGraph, ¬ IsGraphCircuit (innerDraw D d C).toGraph C')
    (hNe : haveI : T2Space S := hS.2.1; (innerDraw D d C).V.Nonempty) :
    haveI : T2Space S := hS.2.1
    ∃ D' : Drawing S,
      D'.toGraph.Simple ∧
      D.toGraph ≤ D'.toGraph ∧
      ShellDiscData D' d C Δ ∧
      (innerDraw D' d C).V = (innerDraw D d C).V ∧
      IsGraphConnected (innerDraw D' d C).toGraph ∧
      (∀ C' ≤ (innerDraw D' d C).toGraph, ¬ IsGraphCircuit (innerDraw D' d C).toGraph C') := by
  have : T2Space S := hS.2.1
  obtain ⟨v₀, hv₀⟩ := hNe
  let V₀ : Set S := (innerDraw D d C).V
  have hV₀_fin : V₀.Finite := (innerDraw D d C).finite_V
  let bound : ℕ := (V₀ ×ˢ V₀).ncard
  have hE_le_bound : ∀ D₁ : Drawing S, D₁.toGraph.Simple → (innerDraw D₁ d C).V = V₀ →
      (innerDraw D₁ d C).E.ncard ≤ bound := by
    intro D₁ hSim₁ hV₁
    let N₁ := innerDraw D₁ d C
    obtain ⟨_, _, _, hN₁_le⟩ := innerDraw_spec D₁ d C
    have hSimN₁ : N₁.toGraph.Simple := Simple.mono hSim₁ hN₁_le
    classical
    let endPair : Set S → S × S := fun e =>
      if he : ∃ p : S × S, N₁.toGraph.IsLink e p.1 p.2 then he.choose else (v₀, v₀)
    have hmaps : MapsTo endPair N₁.E (V₀ ×ˢ V₀) := by
      intro e he
      obtain ⟨u, v, hl⟩ := N₁.toGraph.exists_isLink_of_mem_edgeSet he
      have hex : ∃ p : S × S, N₁.toGraph.IsLink e p.1 p.2 := ⟨(u, v), hl⟩
      dsimp only [endPair]
      split_ifs
      exact ⟨hV₁ ▸ hex.choose_spec.left_mem, hV₁ ▸ hex.choose_spec.right_mem⟩
    have hinj : InjOn endPair N₁.E := by
      intro e₁ he₁ e₂ he₂ heq
      obtain ⟨u₁, v₁, hl₁⟩ := N₁.toGraph.exists_isLink_of_mem_edgeSet he₁
      obtain ⟨u₂, v₂, hl₂⟩ := N₁.toGraph.exists_isLink_of_mem_edgeSet he₂
      have hex₁ : ∃ p : S × S, N₁.toGraph.IsLink e₁ p.1 p.2 := ⟨(u₁, v₁), hl₁⟩
      have hex₂ : ∃ p : S × S, N₁.toGraph.IsLink e₂ p.1 p.2 := ⟨(u₂, v₂), hl₂⟩
      dsimp only [endPair] at heq
      split_ifs at heq
      have h1 := hex₁.choose_spec
      have h2 := heq ▸ hex₂.choose_spec
      exact hSimN₁.eq_of_isLink h1 h2
    exact Set.ncard_le_ncard_of_injOn endPair hmaps hinj (hV₀_fin.prod hV₀_fin)
  have hrec : ∀ (rem : ℕ) (D₁ : Drawing S),
      bound - (innerDraw D₁ d C).E.ncard ≤ rem →
      D₁.toGraph.Simple →
      D.toGraph ≤ D₁.toGraph →
      ShellDiscData D₁ d C Δ →
      (innerDraw D₁ d C).V = V₀ →
      (∀ C' ≤ (innerDraw D₁ d C).toGraph, ¬ IsGraphCircuit (innerDraw D₁ d C).toGraph C') →
      ∃ D' : Drawing S,
        D'.toGraph.Simple ∧ D.toGraph ≤ D'.toGraph ∧ ShellDiscData D' d C Δ ∧
        (innerDraw D' d C).V = V₀ ∧ IsGraphConnected (innerDraw D' d C).toGraph ∧
        (∀ C' ≤ (innerDraw D' d C).toGraph, ¬ IsGraphCircuit (innerDraw D' d C).toGraph C') := by
    intro rem
    induction rem with
    | zero =>
      intro D₁ hrem hSim₁ hle₁ hSh₁ hV₁ hNo₁
      have hv₀₁ : v₀ ∈ (innerDraw D₁ d C).V := hV₁.symm ▸ hv₀
      by_cases hRest : (restSubdraw (innerDraw D₁ d C) v₀).V.Nonempty
      · obtain ⟨D₂, hSim₂, _, _, hV₂, hE₂, _⟩ :=
          connect_innerDraw_step hS hSph hd hSim₁ hSh₁ hNo₁ hv₀₁ hRest
        have hbd₂ := hE_le_bound D₂ hSim₂ (hV₂.trans hV₁)
        omega
      · refine ⟨D₁, hSim₁, hle₁, hSh₁, hV₁, ?_, hNo₁⟩
        obtain ⟨_, _, _, hN₂V, _, _, _, _, _, _⟩ := compSubdraw_spec (innerDraw D₁ d C) hv₀₁
        have hall : ∀ v ∈ (innerDraw D₁ d C).V, Nonempty (GraphWalk (innerDraw D₁ d C).toGraph v₀ v) := by
          intro v hv
          by_contra hnot
          exact hRest ⟨v, hN₂V.symm ▸ ⟨hv, fun hR => hnot hR.2⟩⟩
        refine ⟨⟨v₀, hv₀₁⟩, fun u hu v hv => ?_⟩
        obtain ⟨Wu⟩ := hall u hu
        obtain ⟨Wv⟩ := hall v hv
        exact ⟨Wu.reverse.append Wv⟩
    | succ rem ih =>
      intro D₁ hrem hSim₁ hle₁ hSh₁ hV₁ hNo₁
      have hv₀₁ : v₀ ∈ (innerDraw D₁ d C).V := hV₁.symm ▸ hv₀
      by_cases hRest : (restSubdraw (innerDraw D₁ d C) v₀).V.Nonempty
      · obtain ⟨D₂, hSim₂, hle₂, hSh₂, hV₂, hE₂, hNo₂⟩ :=
          connect_innerDraw_step hS hSph hd hSim₁ hSh₁ hNo₁ hv₀₁ hRest
        have hbd₂ := hE_le_bound D₂ hSim₂ (hV₂.trans hV₁)
        exact ih D₂ (by omega) hSim₂ (hle₁.trans hle₂) hSh₂ (hV₂.trans hV₁) hNo₂
      · refine ⟨D₁, hSim₁, hle₁, hSh₁, hV₁, ?_, hNo₁⟩
        obtain ⟨_, _, _, hN₂V, _, _, _, _, _, _⟩ := compSubdraw_spec (innerDraw D₁ d C) hv₀₁
        have hall : ∀ v ∈ (innerDraw D₁ d C).V, Nonempty (GraphWalk (innerDraw D₁ d C).toGraph v₀ v) := by
          intro v hv
          by_contra hnot
          exact hRest ⟨v, hN₂V.symm ▸ ⟨hv, fun hR => hnot hR.2⟩⟩
        refine ⟨⟨v₀, hv₀₁⟩, fun u hu v hv => ?_⟩
        obtain ⟨Wu⟩ := hall u hu
        obtain ⟨Wv⟩ := hall v hv
        exact ⟨Wu.reverse.append Wv⟩
  exact hrec (bound - (innerDraw D d C).E.ncard) D le_rfl hSimple (le_refl _) hSh rfl hNoCirc

end ConnectInnerForest

end GraphMinor.GM03
