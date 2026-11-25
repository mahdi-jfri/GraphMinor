module

public import GraphMinor.Surface.OrientModel
public import GraphMinor.Surface.CuffHomeo

/-!
# Crossing cocycle of a proper `I`-arc

Given a cutting `ψ : Y → S` of a connected surface `S` along a proper `I`-arc `F` (with distinct
endpoints `s, t ∈ bd S` and two disjoint lifts `X, X' ⊆ bd Y` covering `F`), we construct the
`ZMod 2` crossing local cocycle `cutCocycle`:
- `cutCocycle` is a local 1-cocycle (`IsCoc`) vanishing locally on `Fᶜ`;
- pulling back along `ψ` yields the coboundary `δ(1_X)` (`pbk_cutCocycle_coboundary`), so
  `CohRel (pbk ψ cutCocycle) 0`;
- any two cuttings of the same proper `I`-arc `F` yield crossing cocycles related by a coboundary
  `δ h` with `h = 0` on `bd S \ {s, t}` (`BdCohRel s t`), defining a canonical class `arcCocycle`;
- if `F` is non-separating (`ConnectedSpace Y`) and `BdCohRel s t (arcCocycle F') (arcCocycle F)`,
  then `F'` is also non-separating (`connected_cut_of_bdCohRel`);
- for a non-separating proper `I`-arc `F`, the cut surface `Y` is orientable iff `CohRel (w1 AS) 0`
  or `CohRel (w1 AS) (cutCocycle F)` (`cut_orientable_iff_cohRel_w1`), with an explicit global
  trivialization `g_S : S → ZMod 2` of `w1 AS - cutCocycle F` matching `h_Y + cutOrientDiff` off `F`
  (`exists_w1_cut_descent`).
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric GraphMinor.Surface

universe u

/-! ### `ZMod 2` and `CohRel` helper lemmas -/

theorem zmod2_neg (a : ZMod 2) : -a = a := by fin_cases a <;> rfl

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> rfl

theorem zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_neg]

theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact .inl rfl
  · exact .inr rfl

/-- Pulling back cohomologous local cocycles along any continuous map preserves `CohRel`. -/
theorem cohRel_pbk_cont {X Y : Type*} {A : Type} [TopologicalSpace X] [TopologicalSpace Y] [AddCommGroup A]
    {f : X → Y} (hf : Continuous f) {φ₁ φ₂ : Y → Y → A} (h : CohRel φ₁ φ₂) :
    CohRel (pbk f φ₁) (pbk f φ₂) := by
  obtain ⟨g, N, hN, hg⟩ := h
  refine ⟨g ∘ f, (fun p : X × X => (f p.1, f p.2)) ⁻¹' N, fun x =>
    ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd)).continuousAt.preimage_mem_nhds (hN (f x)),
    fun x₁ x₂ hx => hg (f x₁) (f x₂) hx⟩

/-! ### Boundary-relative cohomology relation `BdCohRel` -/

section BdCoh

variable {S : Type u} [TopologicalSpace S]

/-- Two `ZMod 2` local cocycles are cohomologous relative to `bd S \ {s, t}`: their difference is
locally a coboundary `h y - h x` with `h x = 0` for all `x ∈ bd S \ {s, t}`. -/
def BdCohRel (s t : S) (α₁ α₂ : S → S → ZMod 2) : Prop :=
  ∃ h : S → ZMod 2, (∀ x ∈ bd S \ {s, t}, h x = 0) ∧
    ∃ N : Set (S × S), NearDiag N ∧ ∀ x y, (x, y) ∈ N → α₁ x y - α₂ x y = h y - h x

theorem bdCohRel_refl (s t : S) (α : S → S → ZMod 2) : BdCohRel s t α α :=
  ⟨fun _ => 0, fun _ _ => rfl, univ, fun _ => Filter.univ_mem, fun _ _ _ => by simp⟩

theorem bdCohRel_symm {s t : S} {α₁ α₂ : S → S → ZMod 2} (h : BdCohRel s t α₁ α₂) :
    BdCohRel s t α₂ α₁ := by
  obtain ⟨f, hf, N, hN, hdiff⟩ := h
  refine ⟨fun x => -f x, fun x hx => by simp [hf x hx], N, hN, fun x y hxy => ?_⟩
  have e := hdiff x y hxy
  linear_combination -e

theorem bdCohRel_trans {s t : S} {α₁ α₂ α₃ : S → S → ZMod 2}
    (h12 : BdCohRel s t α₁ α₂) (h23 : BdCohRel s t α₂ α₃) : BdCohRel s t α₁ α₃ := by
  obtain ⟨f, hf, N₁, hN₁, hd₁⟩ := h12
  obtain ⟨g, hg, N₂, hN₂, hd₂⟩ := h23
  refine ⟨fun x => f x + g x, fun x hx => by simp [hf x hx, hg x hx], N₁ ∩ N₂,
    fun x => Filter.inter_mem (hN₁ x) (hN₂ x), fun x y hxy => ?_⟩
  have e1 := hd₁ x y hxy.1
  have e2 := hd₂ x y hxy.2
  linear_combination e1 + e2

theorem BdCohRel.cohRel {s t : S} {α₁ α₂ : S → S → ZMod 2} (h : BdCohRel s t α₁ α₂) :
    CohRel α₁ α₂ := by
  obtain ⟨f, -, N, hN, hdiff⟩ := h
  exact ⟨f, N, hN, hdiff⟩

end BdCoh

/-! ### Normal separation helpers -/

/-- In a compact Hausdorff space, any closed set inside an open set has a shrunk open neighborhood
whose closure still lies inside the open set. -/
theorem exists_open_closure_subset {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {K U : Set Y} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set Y, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U := by
  have hdis : Disjoint K Uᶜ := disjoint_compl_right_iff_subset.mpr hKU
  obtain ⟨V, W, hVo, hWo, hKV, hUcW, hVW⟩ := normal_separation hK hU.isClosed_compl hdis
  refine ⟨V, hVo, hKV, ?_⟩
  have hcl : closure V ⊆ Wᶜ := closure_minimal hVW.subset_compl_right hWo.isClosed_compl
  exact hcl.trans fun z hz => by_contra fun hzU => hz (hUcW hzU)

/-- In a compact Hausdorff space, two disjoint closed sets have open neighborhoods with disjoint
closures. -/
theorem exists_disjoint_closure_nhds {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {X X' : Set Y} (hX : IsClosed X) (hX' : IsClosed X') (hd : Disjoint X X') :
    ∃ V V' : Set Y, IsOpen V ∧ IsOpen V' ∧ X ⊆ V ∧ X' ⊆ V' ∧ Disjoint (closure V) (closure V') := by
  obtain ⟨U, U', hUo, hU'o, hXU, hX'U', hUU'⟩ := normal_separation hX hX' hd
  obtain ⟨V, hVo, hXV, hclV⟩ := exists_open_closure_subset hX hUo hXU
  obtain ⟨V', hV'o, hX'V', hclV'⟩ := exists_open_closure_subset hX' hU'o hX'U'
  exact ⟨V, V', hVo, hV'o, hXV, hX'V', hUU'.mono hclV hclV'⟩

/-- In a connected topological space, a function that is locally constant on a neighborhood of the
diagonal is globally constant. -/
theorem const_of_nearDiag_eq {X α : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {g : X → α} {N : Set (X × X)} (hN : NearDiag N)
    (hg : ∀ x y, (x, y) ∈ N → g x = g y) :
    ∀ x y : X, g x = g y := by
  have hlc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hN x)
    refine Filter.mem_of_superset (Filter.inter_mem hU hV) fun y hy => ?_
    exact (hg x y (hUV ⟨mem_of_mem_nhds hU, hy.2⟩)).symm
  intro x y
  exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ x) (mem_univ y)

private theorem mem_F_of_left {Y S : Type*} {ψ : Y → S} {F : Set S} {X X' : Set Y}
    (hun : X ∪ X' = ψ ⁻¹' F) {y : Y} (hy : y ∈ X) : ψ y ∈ F := by
  have : y ∈ ψ ⁻¹' F := hun ▸ Or.inl hy
  exact this

private theorem mem_F_of_right {Y S : Type*} {ψ : Y → S} {F : Set S} {X X' : Set Y}
    (hun : X ∪ X' = ψ ⁻¹' F) {y : Y} (hy : y ∈ X') : ψ y ∈ F := by
  have : y ∈ ψ ⁻¹' F := hun ▸ Or.inr hy
  exact this

/-! ### Crossing cocycle from a cutting along a proper `I`-arc -/

section CutCocycleSet

variable {Y S : Type u}

/-- Open neighborhood of `F` induced by open neighborhoods `V_X, V_X'` of its two lifts. -/
def cutNbhd (ψ : Y → S) (V_X V_X' : Set Y) : Set S :=
  (ψ '' (V_X ∪ V_X')ᶜ)ᶜ

/-- Local side indicator on `cutNbhd`: `1` on the `V_X \ X` side, `0` on `F` and the `V_X' \ X'` side. -/
noncomputable def cutSide (ψ : Y → S) (V_X X : Set Y) (x : S) : ZMod 2 :=
  open Classical in if x ∈ ψ '' (V_X \ X) then 1 else 0

/-- The `ZMod 2` crossing cocycle of a cutting `ψ : Y → S` along `F` with lifts `X, X'`. -/
noncomputable def cutCocycle (ψ : Y → S) (V_X V_X' X : Set Y) (x y : S) : ZMod 2 :=
  open Classical in
  if x ∈ cutNbhd ψ V_X V_X' ∧ y ∈ cutNbhd ψ V_X V_X' then
    cutSide ψ V_X X y - cutSide ψ V_X X x
  else 0

theorem preimage_cutNbhd_subset {ψ : Y → S} {V_X V_X' : Set Y} :
    ψ ⁻¹' cutNbhd ψ V_X V_X' ⊆ V_X ∪ V_X' := by
  intro y hy
  by_contra h
  exact hy ⟨y, h, rfl⟩

theorem subset_cutNbhd {ψ : Y → S} {F : Set S} {X X' V_X V_X' : Set Y}
    (hun : X ∪ X' = ψ ⁻¹' F) (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X') :
    F ⊆ cutNbhd ψ V_X V_X' := by
  rintro x hx ⟨y, hyc, rfl⟩
  have hyF : y ∈ X ∪ X' := hun.symm ▸ hx
  exact hyc (hyF.elim (fun h => .inl (hXV h)) (fun h => .inr (hX'V' h)))

theorem cutSide_of_mem_F {ψ : Y → S} {F : Set S} {X X' V_X : Set Y}
    (hun : X ∪ X' = ψ ⁻¹' F) (hdisj : Disjoint V_X X') {x : S} (hx : x ∈ F) :
    cutSide ψ V_X X x = 0 := by
  unfold cutSide
  refine ite_eq_right ?_
  rintro ⟨w, ⟨hwV, hwX⟩, rfl⟩
  have hwF : w ∈ X ∪ X' := hun.symm ▸ hx
  exact Set.disjoint_left.mp hdisj hwV (hwF.resolve_left hwX)

theorem cutSide_of_mem_VX {ψ : Y → S} {V_X X : Set Y} {y : Y} (hy : y ∈ V_X \ X) :
    cutSide ψ V_X X (ψ y) = 1 := by
  unfold cutSide
  exact ite_eq_left ⟨y, hy, rfl⟩

end CutCocycleSet

section CutCocycle

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

theorem isOpen_cutNbhd [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) {V_X V_X' : Set Y} (hVX : IsOpen V_X) (hVX' : IsOpen V_X') :
    IsOpen (cutNbhd ψ V_X V_X') := by
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  exact (hcl _ (hVX.union hVX').isClosed_compl).isOpen_compl

theorem cutSide_of_mem_VX' {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F)
    {X X' V_X V_X' : Set Y} (hun : X ∪ X' = ψ ⁻¹' F) (hdisj : Disjoint V_X V_X')
    (hX'V' : X' ⊆ V_X') {y : Y} (hy : y ∈ V_X') :
    cutSide ψ V_X X (ψ y) = 0 := by
  unfold cutSide
  refine ite_eq_right ?_
  rintro ⟨w, ⟨hwV, hwX⟩, hweq⟩
  by_cases hF : ψ y ∈ F
  · have hwF : w ∈ X ∪ X' := hun.symm ▸ (show ψ w ∈ F by rwa [hweq])
    exact Set.disjoint_left.mp hdisj hwV (hX'V' (hwF.resolve_left hwX))
  · have hwF : ψ w ∉ F := by rwa [hweq]
    have hwy : w = y := hψ.2.2.1 hwF hF hweq
    exact Set.disjoint_left.mp hdisj hwV (hwy ▸ hy)

/-- Helper: `cutCocycle` vanishes on `A₁²` and `A₂²`, where `A₁ = Fᶜ ∩ (ψ '' closure V_X')ᶜ`
and `A₂ = Fᶜ ∩ (ψ '' closure V_X)ᶜ`. -/
private theorem cutCocycle_eq_zero_on_A1 {ψ : Y → S} {F : Set S} (hψ : IsCutting ψ F)
    {X X' V_X V_X' : Set Y} (hun : X ∪ X' = ψ ⁻¹' F)
    {x y : S} (hx : x ∈ Fᶜ ∩ (ψ '' closure V_X')ᶜ) (hy : y ∈ Fᶜ ∩ (ψ '' closure V_X')ᶜ) :
    cutCocycle ψ V_X V_X' X x y = 0 := by
  unfold cutCocycle
  by_cases hU : x ∈ cutNbhd ψ V_X V_X' ∧ y ∈ cutNbhd ψ V_X V_X'
  · rw [ite_eq_left hU]
    have hside : ∀ z ∈ Fᶜ ∩ (ψ '' closure V_X')ᶜ, z ∈ cutNbhd ψ V_X V_X' → cutSide ψ V_X X z = 1 := by
      intro z hz hzU
      obtain ⟨w, rfl⟩ := hψ.2.1 z
      have hw : w ∈ V_X ∪ V_X' := preimage_cutNbhd_subset hzU
      have hwV : w ∈ V_X := hw.resolve_right fun hw' => hz.2 ⟨w, subset_closure hw', rfl⟩
      have hwX : w ∉ X := fun hwX => hz.1 (mem_F_of_left hun hwX)
      exact cutSide_of_mem_VX ⟨hwV, hwX⟩
    rw [hside x hx hU.1, hside y hy hU.2, sub_self]
  · rw [ite_eq_right hU]

omit [TopologicalSpace S] in
private theorem cutCocycle_eq_zero_on_A2 {ψ : Y → S}
    {X V_X V_X' : Set Y}
    {x y : S} (hx : x ∈ (ψ '' closure V_X)ᶜ) (hy : y ∈ (ψ '' closure V_X)ᶜ) :
    cutCocycle ψ V_X V_X' X x y = 0 := by
  unfold cutCocycle
  by_cases hU : x ∈ cutNbhd ψ V_X V_X' ∧ y ∈ cutNbhd ψ V_X V_X'
  · rw [ite_eq_left hU]
    have hside : ∀ z ∈ (ψ '' closure V_X)ᶜ, cutSide ψ V_X X z = 0 := by
      intro z hz
      unfold cutSide
      refine ite_eq_right ?_
      rintro ⟨w, ⟨hwV, -⟩, rfl⟩
      exact hz ⟨w, subset_closure hwV, rfl⟩
    rw [hside x hx, hside y hy, sub_self]
  · rw [ite_eq_right hU]

/-- Away from `F`, `cutCocycle` vanishes identically on a neighborhood of every point. -/
theorem cutCocycle_zero_off [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) {X X' V_X V_X' : Set Y}
    (hun : X ∪ X' = ψ ⁻¹' F) (hclDisj : Disjoint (closure V_X) (closure V_X')) :
    ∀ p ∉ F, ∃ W : Set S, IsOpen W ∧ p ∈ W ∧ W ⊆ Fᶜ ∧
      ∀ x ∈ W, ∀ y ∈ W, cutCocycle ψ V_X V_X' X x y = 0 := by
  intro p hp
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  have hC1 : IsClosed (ψ '' closure V_X) := hcl _ isClosed_closure
  have hC2 : IsClosed (ψ '' closure V_X') := hcl _ isClosed_closure
  have hnot_both : ¬ (p ∈ ψ '' closure V_X ∧ p ∈ ψ '' closure V_X') := by
    rintro ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, hyeq⟩⟩
    have hy2F : ψ y₂ ∉ F := by rwa [hyeq]
    have hy12 : y₁ = y₂ := hψ.2.2.1 hp hy2F hyeq.symm
    exact Set.disjoint_left.mp hclDisj hy₁ (hy12 ▸ hy₂)
  by_cases hp1 : p ∈ ψ '' closure V_X
  · have hp2 : p ∉ ψ '' closure V_X' := fun h => hnot_both ⟨hp1, h⟩
    exact ⟨Fᶜ ∩ (ψ '' closure V_X')ᶜ, hF.isOpen_compl.inter hC2.isOpen_compl, ⟨hp, hp2⟩,
      inter_subset_left, fun x hx y hy => cutCocycle_eq_zero_on_A1 hψ hun hx hy⟩
  · exact ⟨Fᶜ ∩ (ψ '' closure V_X)ᶜ, hF.isOpen_compl.inter hC1.isOpen_compl, ⟨hp, hp1⟩,
      inter_subset_left, fun x hx y hy => cutCocycle_eq_zero_on_A2 hx.2 hy.2⟩

/-- `cutCocycle` is a local 1-cocycle on `S`. -/
theorem isCoc_cutCocycle [CompactSpace Y] [CompactSpace S] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) {X X' V_X V_X' : Set Y}
    (hun : X ∪ X' = ψ ⁻¹' F) (hVX : IsOpen V_X) (hVX' : IsOpen V_X')
    (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X')
    (hclDisj : Disjoint (closure V_X) (closure V_X')) :
    IsCoc (cutCocycle ψ V_X V_X' X) := by
  have hUo : IsOpen (cutNbhd ψ V_X V_X') := isOpen_cutNbhd hψ hVX hVX'
  have hFsub : F ⊆ cutNbhd ψ V_X V_X' := subset_cutNbhd hun hXV hX'V'
  obtain ⟨U₀, hU₀o, hFU₀, hclU₀⟩ := exists_open_closure_subset hF hUo hFsub
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  have hC1 : IsClosed (ψ '' closure V_X) := hcl _ isClosed_closure
  have hC2 : IsClosed (ψ '' closure V_X') := hcl _ isClosed_closure
  let A₁ : Set S := Fᶜ ∩ (ψ '' closure V_X')ᶜ
  let A₂ : Set S := Fᶜ ∩ (ψ '' closure V_X)ᶜ
  have hA₁o : IsOpen A₁ := hF.isOpen_compl.inter hC2.isOpen_compl
  have hA₂o : IsOpen A₂ := hF.isOpen_compl.inter hC1.isOpen_compl
  let W₀ : Set S := U₀
  let W₁ : Set S := cutNbhd ψ V_X V_X' ∩ A₁
  let W₂ : Set S := cutNbhd ψ V_X V_X' ∩ A₂
  let W₃₁ : Set S := (closure U₀)ᶜ ∩ A₁
  let W₃₂ : Set S := (closure U₀)ᶜ ∩ A₂
  have hW₀o : IsOpen W₀ := hU₀o
  have hW₁o : IsOpen W₁ := hUo.inter hA₁o
  have hW₂o : IsOpen W₂ := hUo.inter hA₂o
  have hW₃₁o : IsOpen W₃₁ := isClosed_closure.isOpen_compl.inter hA₁o
  have hW₃₂o : IsOpen W₃₂ := isClosed_closure.isOpen_compl.inter hA₂o
  let N : Set (S × S) := (W₀ ×ˢ W₀) ∪ (W₁ ×ˢ W₁) ∪ (W₂ ×ˢ W₂) ∪ (W₃₁ ×ˢ W₃₁) ∪ (W₃₂ ×ˢ W₃₂)
  have hnot_both : ∀ p ∉ F, p ∈ A₁ ∨ p ∈ A₂ := fun p hp => by
    by_cases hp1 : p ∈ ψ '' closure V_X
    · left
      refine ⟨hp, ?_⟩
      rintro ⟨y₂, hy₂, hyeq⟩
      obtain ⟨y₁, hy₁, hy1eq⟩ := hp1
      have h1F : y₁ ∈ ψ ⁻¹' Fᶜ := by show ψ y₁ ∉ F; rwa [hy1eq]
      have h2F : y₂ ∈ ψ ⁻¹' Fᶜ := by show ψ y₂ ∉ F; rwa [hyeq]
      have hy12 : y₁ = y₂ := hψ.2.2.1 h1F h2F (hy1eq.trans hyeq.symm)
      exact Set.disjoint_left.mp hclDisj hy₁ (hy12 ▸ hy₂)
    · exact .inr ⟨hp, hp1⟩
  have hN : NearDiag N := fun p => by
    by_cases hpF : p ∈ F
    · exact Filter.mem_of_superset ((hW₀o.prod hW₀o).mem_nhds ⟨hFU₀ hpF, hFU₀ hpF⟩)
        (fun _ h => .inl (.inl (.inl (.inl h))))
    · by_cases hpcl : p ∈ closure U₀
      · rcases hnot_both p hpF with hA | hA
        · exact Filter.mem_of_superset ((hW₁o.prod hW₁o).mem_nhds ⟨⟨hclU₀ hpcl, hA⟩, ⟨hclU₀ hpcl, hA⟩⟩)
            (fun _ h => .inl (.inl (.inl (.inr h))))
        · exact Filter.mem_of_superset ((hW₂o.prod hW₂o).mem_nhds ⟨⟨hclU₀ hpcl, hA⟩, ⟨hclU₀ hpcl, hA⟩⟩)
            (fun _ h => .inl (.inl (.inr h)))
      · rcases hnot_both p hpF with hA | hA
        · exact Filter.mem_of_superset ((hW₃₁o.prod hW₃₁o).mem_nhds ⟨⟨hpcl, hA⟩, ⟨hpcl, hA⟩⟩)
            (fun _ h => .inl (.inr h))
        · exact Filter.mem_of_superset ((hW₃₂o.prod hW₃₂o).mem_nhds ⟨⟨hpcl, hA⟩, ⟨hpcl, hA⟩⟩)
            (fun _ h => .inr h)
  have hzero_off_W0 : ∀ a b : S, (a, b) ∈ N → a ∉ W₀ → cutCocycle ψ V_X V_X' X a b = 0 := by
    intro a b hab ha
    rcases hab with (((h | h) | h) | h) | h
    · exact absurd h.1 ha
    · exact cutCocycle_eq_zero_on_A1 hψ hun h.1.2 h.2.2
    · exact cutCocycle_eq_zero_on_A2 h.1.2.2 h.2.2.2
    · exact cutCocycle_eq_zero_on_A1 hψ hun h.1.2 h.2.2
    · exact cutCocycle_eq_zero_on_A2 h.1.2.2 h.2.2.2
  have hnotU_notW0 : ∀ a b : S, (a, b) ∈ N → a ∉ cutNbhd ψ V_X V_X' → a ∉ W₀ ∧ b ∉ W₀ := by
    intro a b hab haU
    rcases hab with (((h | h) | h) | h) | h
    · exact absurd (hclU₀ (subset_closure h.1)) haU
    · exact absurd h.1.1 haU
    · exact absurd h.1.1 haU
    · exact ⟨fun h0 => h.1.1 (subset_closure h0), fun h0 => h.2.1 (subset_closure h0)⟩
    · exact ⟨fun h0 => h.1.1 (subset_closure h0), fun h0 => h.2.1 (subset_closure h0)⟩
  have hnotU_notW0' : ∀ a b : S, (a, b) ∈ N → b ∉ cutNbhd ψ V_X V_X' → a ∉ W₀ ∧ b ∉ W₀ := by
    intro a b hab hbU
    rcases hab with (((h | h) | h) | h) | h
    · exact absurd (hclU₀ (subset_closure h.2)) hbU
    · exact absurd h.2.1 hbU
    · exact absurd h.2.1 hbU
    · exact ⟨fun h0 => h.1.1 (subset_closure h0), fun h0 => h.2.1 (subset_closure h0)⟩
    · exact ⟨fun h0 => h.1.1 (subset_closure h0), fun h0 => h.2.1 (subset_closure h0)⟩
  refine ⟨N, hN, fun x y z hxy hyz hxz => ?_⟩
  by_cases hU : x ∈ cutNbhd ψ V_X V_X' ∧ y ∈ cutNbhd ψ V_X V_X' ∧ z ∈ cutNbhd ψ V_X V_X'
  · unfold cutCocycle
    rw [ite_eq_left ⟨hU.1, hU.2.1⟩, ite_eq_left ⟨hU.2.1, hU.2.2⟩, ite_eq_left ⟨hU.1, hU.2.2⟩]
    ring
  · have hnotW0 : x ∉ W₀ ∧ y ∉ W₀ ∧ z ∉ W₀ := by
      by_cases hxU : x ∈ cutNbhd ψ V_X V_X'
      · by_cases hyU : y ∈ cutNbhd ψ V_X V_X'
        · have hzU : z ∉ cutNbhd ψ V_X V_X' := fun hz => hU ⟨hxU, hyU, hz⟩
          exact ⟨(hnotU_notW0' x z hxz hzU).1, (hnotU_notW0' y z hyz hzU).1, (hnotU_notW0' y z hyz hzU).2⟩
        · exact ⟨(hnotU_notW0' x y hxy hyU).1, (hnotU_notW0' x y hxy hyU).2, (hnotU_notW0 y z hyz hyU).2⟩
      · exact ⟨(hnotU_notW0 x y hxy hxU).1, (hnotU_notW0 x y hxy hxU).2, (hnotU_notW0 x z hxz hxU).2⟩
    rw [hzero_off_W0 x y hxy hnotW0.1, hzero_off_W0 y z hyz hnotW0.2.1, hzero_off_W0 x z hxz hnotW0.1, add_zero]

/-- Pulling back `cutCocycle` along `ψ` yields the exact coboundary of the indicator `1_X` on `Y`. -/
theorem pbk_cutCocycle_coboundary [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) {X X' V_X V_X' : Set Y}
    (hX : IsClosed X) (hX' : IsClosed X')
    (hun : X ∪ X' = ψ ⁻¹' F) (hVX : IsOpen V_X) (hVX' : IsOpen V_X')
    (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X')
    (hclDisj : Disjoint (closure V_X) (closure V_X')) :
    ∃ N : Set (Y × Y), NearDiag N ∧
      ∀ y₁ y₂ : Y, (y₁, y₂) ∈ N →
        cutCocycle ψ V_X V_X' X (ψ y₁) (ψ y₂) =
          (open Classical in if y₂ ∈ X then (1 : ZMod 2) else 0) -
          (open Classical in if y₁ ∈ X then (1 : ZMod 2) else 0) := by
  classical
  have hUo : IsOpen (cutNbhd ψ V_X V_X') := isOpen_cutNbhd hψ hVX hVX'
  have hFsub : F ⊆ cutNbhd ψ V_X V_X' := subset_cutNbhd hun hXV hX'V'
  have hdisj : Disjoint V_X V_X' := hclDisj.mono subset_closure subset_closure
  have hoff := cutCocycle_zero_off hψ hF hun hclDisj
  have hloc : ∀ y : Y, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧
      ∀ y₁ ∈ W, ∀ y₂ ∈ W,
        cutCocycle ψ V_X V_X' X (ψ y₁) (ψ y₂) =
          (if y₂ ∈ X then (1 : ZMod 2) else 0) - (if y₁ ∈ X then (1 : ZMod 2) else 0) := by
    intro y
    by_cases hyX : y ∈ X
    · refine ⟨V_X ∩ ψ ⁻¹' cutNbhd ψ V_X V_X', hVX.inter (hUo.preimage hψ.1),
        ⟨hXV hyX, hFsub (mem_F_of_left hun hyX)⟩, fun y₁ hy₁ y₂ hy₂ => ?_⟩
      unfold cutCocycle
      rw [ite_eq_left ⟨hy₁.2, hy₂.2⟩]
      have hside : ∀ w ∈ V_X, cutSide ψ V_X X (ψ w) = 1 + (if w ∈ X then (1 : ZMod 2) else 0) := by
        intro w hw
        by_cases hwX : w ∈ X
        · rw [ite_eq_left hwX, cutSide_of_mem_F hun (hdisj.mono_right hX'V') (mem_F_of_left hun hwX)]
          rfl
        · rw [ite_eq_right hwX, cutSide_of_mem_VX ⟨hw, hwX⟩, add_zero]
      rw [hside y₁ hy₁.1, hside y₂ hy₂.1]
      ring
    · by_cases hyX' : y ∈ X'
      · refine ⟨V_X' ∩ ψ ⁻¹' cutNbhd ψ V_X V_X', hVX'.inter (hUo.preimage hψ.1),
          ⟨hX'V' hyX', hFsub (mem_F_of_right hun hyX')⟩, fun y₁ hy₁ y₂ hy₂ => ?_⟩
        unfold cutCocycle
        rw [ite_eq_left ⟨hy₁.2, hy₂.2⟩]
        have hnotX : ∀ w ∈ V_X', w ∉ X := fun w hw hwX => Set.disjoint_left.mp hdisj (hXV hwX) hw
        rw [cutSide_of_mem_VX' hψ hun hdisj hX'V' hy₁.1, cutSide_of_mem_VX' hψ hun hdisj hX'V' hy₂.1,
          ite_eq_right (hnotX y₁ hy₁.1), ite_eq_right (hnotX y₂ hy₂.1)]
      · have hyF : ψ y ∉ F := fun h => by
          have : y ∈ X ∪ X' := hun.symm ▸ h
          exact this.elim hyX hyX'
        obtain ⟨W, hWo, hyW, -, hW⟩ := hoff (ψ y) hyF
        refine ⟨ψ ⁻¹' W ∩ (X ∪ X')ᶜ, (hWo.preimage hψ.1).inter (hX.union hX').isOpen_compl,
          ⟨hyW, fun h => h.elim hyX hyX'⟩, fun y₁ hy₁ y₂ hy₂ => ?_⟩
        rw [hW (ψ y₁) hy₁.1 (ψ y₂) hy₂.1,
          ite_eq_right (fun h => hy₁.2 (.inl h)), ite_eq_right (fun h => hy₂.2 (.inl h))]
        simp
  choose W hWo hyW hW using hloc
  refine ⟨⋃ y : Y, W y ×ˢ W y, fun y =>
    Filter.mem_of_superset ((hWo y).prod (hWo y) |>.mem_nhds ⟨hyW y, hyW y⟩)
      (subset_iUnion (fun w => W w ×ˢ W w) y), fun y₁ y₂ hpair => ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := mem_iUnion.mp hpair
  exact hW y y₁ hy₁ y₂ hy₂

/-- Pulling back `cutCocycle` along `ψ` is cohomologous to `0` on `Y`. -/
theorem cohRel_pbk_cutCocycle_zero [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}
    (hψ : IsCutting ψ F) (hF : IsClosed F) {X X' V_X V_X' : Set Y}
    (hX : IsClosed X) (hX' : IsClosed X')
    (hun : X ∪ X' = ψ ⁻¹' F) (hVX : IsOpen V_X) (hVX' : IsOpen V_X')
    (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X')
    (hclDisj : Disjoint (closure V_X) (closure V_X')) :
    CohRel (pbk ψ (cutCocycle ψ V_X V_X' X)) (fun _ _ => 0) := by
  obtain ⟨N, hN, hdiff⟩ := pbk_cutCocycle_coboundary hψ hF hX hX' hun hVX hVX' hXV hX'V' hclDisj
  refine ⟨fun y => open Classical in if y ∈ X then 1 else 0, N, hN, fun y₁ y₂ h => ?_⟩
  simpa [pbk] using hdiff y₁ y₂ h

/-- Comparing `cutCocycle` from ANY two cuttings `(Y₁, ψ₁, X₁, X₁')` and `(Y₂, ψ₂, X₂, X₂')` of the
same proper `I`-arc `F`: their difference is locally `δ h` with `h = 0` on `bd S \ {s, t}`. -/
theorem cutCocycle_bdCohRel_of_same_arc {Y₁ Y₂ : Type u} [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    [T2Space S] {ψ₁ : Y₁ → S} {ψ₂ : Y₂ → S} {F : Set S} {s t : S}
    (hY₁ : IsSurface Y₁) (hY₂ : IsSurface Y₂) (hψ₁ : IsCutting ψ₁ F) (hψ₂ : IsCutting ψ₂ F)
    (hF : IsClosed F) (hb : F ∩ bd S = {s, t})
    {X₁ X₁' V₁ V₁' : Set Y₁} {X₂ X₂' V₂ V₂' : Set Y₂}
    (hX₁c : IsPreconnected X₁) (hX₁'c : IsPreconnected X₁')
    (hX₁ne : X₁.Nonempty) (hX₁'ne : X₁'.Nonempty)
    (hX₂ne : X₂.Nonempty) (hX₂'ne : X₂'.Nonempty)
    (hun₁ : X₁ ∪ X₁' = ψ₁ ⁻¹' F) (hun₂ : X₂ ∪ X₂' = ψ₂ ⁻¹' F)
    (hV₁ : IsOpen V₁) (hV₁' : IsOpen V₁') (hV₂ : IsOpen V₂) (hV₂' : IsOpen V₂')
    (hX₁V₁ : X₁ ⊆ V₁) (hX₁'V₁' : X₁' ⊆ V₁') (hX₂V₂ : X₂ ⊆ V₂) (hX₂'V₂' : X₂' ⊆ V₂')
    (hcl₁ : Disjoint (closure V₁) (closure V₁')) (hcl₂ : Disjoint (closure V₂) (closure V₂')) :
    BdCohRel s t (cutCocycle ψ₁ V₁ V₁' X₁) (cutCocycle ψ₂ V₂ V₂' X₂) := by
  classical
  have : CompactSpace Y₁ := hY₁.1
  have : CompactSpace Y₂ := hY₂.1
  have hdisj₁ : Disjoint V₁ V₁' := hcl₁.mono subset_closure subset_closure
  have hdisj₂ : Disjoint V₂ V₂' := hcl₂.mono subset_closure subset_closure
  have hU₁o : IsOpen (cutNbhd ψ₁ V₁ V₁') := isOpen_cutNbhd hψ₁ hV₁ hV₁'
  have hU₂o : IsOpen (cutNbhd ψ₂ V₂ V₂') := isOpen_cutNbhd hψ₂ hV₂ hV₂'
  have hFU₁ : F ⊆ cutNbhd ψ₁ V₁ V₁' := subset_cutNbhd hun₁ hX₁V₁ hX₁'V₁'
  have hFU₂ : F ⊆ cutNbhd ψ₂ V₂ V₂' := subset_cutNbhd hun₂ hX₂V₂ hX₂'V₂'
  have him₂_open : ∀ W : Set Y₂, IsOpen W → W ⊆ (ψ₂ ⁻¹' F)ᶜ → IsOpen (ψ₂ '' W) := fun W hWo hWsub => by
    have hq : IsQuotientMap ψ₂ := hψ₂.1.isClosedMap.isQuotientMap hψ₂.1 hψ₂.2.1
    rw [← hq.isOpen_preimage]
    have heq : ψ₂ ⁻¹' (ψ₂ '' W) = W := subset_antisymm (fun y ⟨w, hw, hweq⟩ =>
      hψ₂.2.2.1 (by show ψ₂ y ∉ F; rw [← hweq]; exact hWsub hw) (hWsub hw) hweq.symm ▸ hw)
      (subset_preimage_image ψ₂ W)
    rwa [heq]
  have hS2_pos_o : IsOpen (ψ₂ '' (V₂ \ X₂)) := by
    have hsub : V₂ \ X₂ = V₂ ∩ (ψ₂ ⁻¹' F)ᶜ := by
      ext y; simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_preimage]
      constructor
      · rintro ⟨hyV, hyX⟩; refine ⟨hyV, fun hF => ?_⟩
        have : y ∈ X₂ ∪ X₂' := hun₂.symm ▸ hF
        exact Set.disjoint_left.mp hdisj₂ hyV (hX₂'V₂' (this.resolve_left hyX))
      · rintro ⟨hyV, hyF⟩; exact ⟨hyV, fun hyX => hyF (mem_F_of_left hun₂ hyX)⟩
    rw [hsub]
    exact him₂_open _ (hV₂.inter (hF.preimage hψ₂.1).isOpen_compl) inter_subset_right
  have hS2_neg_o : IsOpen (ψ₂ '' (V₂' \ X₂')) := by
    have hsub : V₂' \ X₂' = V₂' ∩ (ψ₂ ⁻¹' F)ᶜ := by
      ext y; simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_preimage]
      constructor
      · rintro ⟨hyV, hyX⟩; refine ⟨hyV, fun hF => ?_⟩
        have : y ∈ X₂ ∪ X₂' := hun₂.symm ▸ hF
        exact Set.disjoint_left.mp hdisj₂ (hX₂V₂ (this.resolve_right hyX)) hyV
      · rintro ⟨hyV, hyF⟩; exact ⟨hyV, fun hyX => hyF (mem_F_of_right hun₂ hyX)⟩
    rw [hsub]
    exact him₂_open _ (hV₂'.inter (hF.preimage hψ₂.1).isOpen_compl) inter_subset_right
  have hS2_disj : Disjoint (ψ₂ '' (V₂ \ X₂)) (ψ₂ '' (V₂' \ X₂')) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w₁, ⟨hw1V, hw1X⟩, rfl⟩ ⟨w₂, ⟨hw2V', hw2X'⟩, hweq⟩
    have hw1F : ψ₂ w₁ ∉ F := fun hF => by
      have : w₁ ∈ X₂ ∪ X₂' := hun₂.symm ▸ hF
      exact Set.disjoint_left.mp hdisj₂ hw1V (hX₂'V₂' (this.resolve_left hw1X))
    have h12 : w₁ = w₂ := hψ₂.2.2.1 hw1F (by show ψ₂ w₂ ∉ F; rwa [hweq]) hweq.symm
    exact Set.disjoint_left.mp hdisj₂ hw1V (h12 ▸ hw2V')
  have hS2_cover : cutNbhd ψ₂ V₂ V₂' \ F ⊆ ψ₂ '' (V₂ \ X₂) ∪ ψ₂ '' (V₂' \ X₂') := by
    rintro z ⟨hzU, hzF⟩
    obtain ⟨w, rfl⟩ := hψ₂.2.1 z
    rcases preimage_cutNbhd_subset hzU with hw | hw
    · exact .inl ⟨w, ⟨hw, fun h => hzF (mem_F_of_left hun₂ h)⟩, rfl⟩
    · exact .inr ⟨w, ⟨hw, fun h => hzF (mem_F_of_right hun₂ h)⟩, rfl⟩
  have hball_const : ∀ (Z V : Set Y₁), Z ⊆ X₁ ∪ X₁' → V ⊆ V₁ ∪ V₁' → IsOpen V → Z ⊆ V →
      IsPreconnected Z → Z.Nonempty →
      ∃ (W : Set Y₁) (c₀ : ZMod 2), IsOpen W ∧ Z ⊆ W ∧ W ⊆ V ∩ ψ₁ ⁻¹' (cutNbhd ψ₁ V₁ V₁' ∩ cutNbhd ψ₂ V₂ V₂') ∧
        ∀ y ∈ W, ψ₁ y ∉ F → cutSide ψ₂ V₂ X₂ (ψ₁ y) = c₀ := by
    intro Z V hZsub _ hVo hZV hZconn hZne
    have hloc : ∀ y ∈ Z, ∃ (B : Set Y₁) (c₀ : ZMod 2), IsOpen B ∧ y ∈ B ∧
        B ⊆ V ∩ ψ₁ ⁻¹' (cutNbhd ψ₁ V₁ V₁' ∩ cutNbhd ψ₂ V₂ V₂') ∧
        (B ∩ (bd Y₁)ᶜ).Nonempty ∧
        ∀ w ∈ B, ψ₁ w ∉ F → cutSide ψ₂ V₂ X₂ (ψ₁ w) = c₀ := by
      intro y hyZ
      obtain ⟨ch, hych⟩ := exists_surfChart (hY₁.2.2 y)
      have hO' : IsOpen (V ∩ ψ₁ ⁻¹' (cutNbhd ψ₁ V₁ V₁' ∩ cutNbhd ψ₂ V₂ V₂') ∩ ch.U) :=
        (hVo.inter ((hU₁o.inter hU₂o).preimage hψ₁.1)).inter ch.hU
      have hyF : ψ₁ y ∈ F := by
        have : y ∈ ψ₁ ⁻¹' F := hun₁ ▸ hZsub hyZ
        exact this
      have hyO' : y ∈ V ∩ ψ₁ ⁻¹' (cutNbhd ψ₁ V₁ V₁' ∩ cutNbhd ψ₂ V₂ V₂') ∩ ch.U :=
        ⟨⟨hZV hyZ, hFU₁ hyF, hFU₂ hyF⟩, hych⟩
      obtain ⟨r, hr, -, -, hBo, hyB, hBsub, ⟨y₀, hy₀B, hy₀I⟩, hBconn⟩ :=
        ch.exists_ball_nbhd hO' hyO' inter_subset_right
      set B := ch.U ∩ ch.j ⁻¹' ball (ch.j y) r
      have hBI_conn : IsPreconnected (B ∩ (bd Y₁)ᶜ) := by
        have hIm : ch.k '' (ch.j '' (B ∩ (bd Y₁)ᶜ)) = B ∩ (bd Y₁)ᶜ := by
          ext w; constructor
          · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩; rwa [ch.hl hz.1.1]
          · intro hw; exact ⟨ch.j w, ⟨w, hw, rfl⟩, ch.hl hw.1.1⟩
        rw [← hIm]
        exact hBconn.image ch.k (ch.hk.mono (by
          rintro _ ⟨z, hz, rfl⟩; exact ch.hm hz.1.1))
      have hBI_map : ψ₁ '' (B ∩ (bd Y₁)ᶜ) ⊆ ψ₂ '' (V₂ \ X₂) ∪ ψ₂ '' (V₂' \ X₂') := by
        rintro _ ⟨w, ⟨hwB, hwI⟩, rfl⟩
        exact hS2_cover ⟨(hBsub hwB).1.2.2, fun hFw => hwI (hψ₁.2.2.2.2 hFw)⟩
      have hImgConn : IsPreconnected (ψ₁ '' (B ∩ (bd Y₁)ᶜ)) :=
        hBI_conn.image ψ₁ hψ₁.1.continuousOn
      have hside_BI : (ψ₁ '' (B ∩ (bd Y₁)ᶜ) ⊆ ψ₂ '' (V₂ \ X₂)) ∨
          (ψ₁ '' (B ∩ (bd Y₁)ᶜ) ⊆ ψ₂ '' (V₂' \ X₂')) := by
        have h := hImgConn (ψ₂ '' (V₂ \ X₂)) (ψ₂ '' (V₂' \ X₂')) hS2_pos_o hS2_neg_o hBI_map
        by_cases h1 : (ψ₁ '' (B ∩ (bd Y₁)ᶜ) ∩ ψ₂ '' (V₂ \ X₂)).Nonempty
        · by_cases h2 : (ψ₁ '' (B ∩ (bd Y₁)ᶜ) ∩ ψ₂ '' (V₂' \ X₂')).Nonempty
          · obtain ⟨z, -, hz1, hz2⟩ := h h1 h2
            exact absurd hz2 (Set.disjoint_left.mp hS2_disj hz1)
          · left; intro z hz
            rcases hBI_map hz with hpos | hneg
            · exact hpos
            · exact absurd ⟨z, hz, hneg⟩ h2
        · right; intro z hz
          rcases hBI_map hz with hpos | hneg
          · exact absurd ⟨z, hz, hpos⟩ h1
          · exact hneg
      have hBI_dense : ∀ U' : Set Y₁, IsOpen U' → (B ∩ U').Nonempty → (B ∩ (bd Y₁)ᶜ ∩ U').Nonempty := by
        rintro U' hU'o ⟨w, hwB, hwU'⟩
        have hBU' : IsOpen (B ∩ U') := hBo.inter hU'o
        have hnhd : ch.k ⁻¹' (B ∩ U') ∈ 𝓝[ch.O ∩ halfPlane] (ch.j w) :=
          (ch.hk _ (ch.hm hwB.1)).preimage_mem_nhdsWithin (hBU'.mem_nhds (by rw [ch.hl hwB.1]; exact ⟨hwB, hwU'⟩))
        obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.mp hnhd
        obtain ⟨ρ', hρ', hρ'sub⟩ := Metric.isOpen_iff.mp ch.hO _ (ch.hm hwB.1).1
        set ε := min (ρ / 2) (ρ' / 2)
        have hε : 0 < ε := lt_min (half_pos hρ) (half_pos hρ')
        set z' : ℂ := ch.j w + (ε : ℂ)
        have hz'dist : dist z' (ch.j w) < min ρ ρ' := by
          rw [dist_eq_norm, show z' - ch.j w = (ε : ℂ) by simp [z'], Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
          exact lt_min (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ))
            (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hρ'))
        have hz're : 0 < z'.re := by
          have : 0 ≤ (ch.j w).re := (ch.hm hwB.1).2
          simp [z']; linarith
        have hz'mem : z' ∈ ch.O ∩ halfPlane :=
          ⟨hρ'sub (lt_of_lt_of_le hz'dist (min_le_right _ _)), hz're.le⟩
        have hkz' : ch.k z' ∈ B ∩ U' := hρsub ⟨lt_of_lt_of_le hz'dist (min_le_left _ _), hz'mem⟩
        have hkz'I : ch.k z' ∈ (bd Y₁)ᶜ := by
          rw [mem_compl_iff, ch.mem_bd_iff (ch.hk' hz'mem), ch.hr hz'mem]
          exact hz're.ne'
        exact ⟨ch.k z', ⟨hkz'.1, hkz'I⟩, hkz'.2⟩
      rcases hside_BI with hpos | hneg
      · refine ⟨B, 1, hBo, hyB, fun w hw => (hBsub hw).1, ⟨y₀, hy₀B, hy₀I⟩, fun w hwB hwF => ?_⟩
        rcases hS2_cover ⟨(hBsub hwB).1.2.2, hwF⟩ with h1 | h2
        · unfold cutSide; exact ite_eq_left h1
        · exfalso
          obtain ⟨w', ⟨hw'B, hw'I⟩, hw'2⟩ := hBI_dense (ψ₁ ⁻¹' (ψ₂ '' (V₂' \ X₂')))
            (hS2_neg_o.preimage hψ₁.1) ⟨w, hwB, h2⟩
          exact Set.disjoint_left.mp hS2_disj (hpos ⟨w', ⟨hw'B, hw'I⟩, rfl⟩) hw'2
      · refine ⟨B, 0, hBo, hyB, fun w hw => (hBsub hw).1, ⟨y₀, hy₀B, hy₀I⟩, fun w hwB hwF => ?_⟩
        rcases hS2_cover ⟨(hBsub hwB).1.2.2, hwF⟩ with h1 | h2
        · exfalso
          obtain ⟨w', ⟨hw'B, hw'I⟩, hw'1⟩ := hBI_dense (ψ₁ ⁻¹' (ψ₂ '' (V₂ \ X₂)))
            (hS2_pos_o.preimage hψ₁.1) ⟨w, hwB, h1⟩
          exact Set.disjoint_left.mp hS2_disj hw'1 (hneg ⟨w', ⟨hw'B, hw'I⟩, rfl⟩)
        · unfold cutSide
          exact ite_eq_right fun h1 => Set.disjoint_left.mp hS2_disj h1 h2
    choose B cVal hBo hyB hBsub hBne hBconst using fun (y : Z) => hloc y.1 y.2
    have hlc : ∀ z₁ z₂ : Z, cVal z₁ = cVal z₂ := by
      have : ConnectedSpace Z := isConnected_iff_connectedSpace.mp ⟨hZne, hZconn⟩
      have hlc' : IsLocallyConstant cVal := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro z₀
        have hnhd : (Subtype.val ⁻¹' B z₀ : Set Z) ∈ 𝓝 z₀ :=
          ((hBo z₀).preimage continuous_subtype_val).mem_nhds (hyB z₀)
        refine Filter.mem_of_superset hnhd fun z hz => ?_
        have hne : (B z ∩ B z₀ ∩ (bd Y₁)ᶜ).Nonempty := by
          obtain ⟨ch, hzch⟩ := exists_surfChart (hY₁.2.2 z.1)
          have hO'' : IsOpen (B z ∩ B z₀ ∩ ch.U) := ((hBo z).inter (hBo z₀)).inter ch.hU
          obtain ⟨r, -, -, -, -, -, hsub', ⟨w₀, hw₀, hw₀I⟩, -⟩ :=
            ch.exists_ball_nbhd hO'' ⟨⟨hyB z, hz⟩, hzch⟩ inter_subset_right
          exact ⟨w₀, (hsub' hw₀).1, hw₀I⟩
        obtain ⟨w, ⟨hw1, hw2⟩, hwI⟩ := hne
        have hwF : ψ₁ w ∉ F := fun h => hwI (hψ₁.2.2.2.2 h)
        change cVal z = cVal z₀
        rw [← hBconst z w hw1 hwF, hBconst z₀ w hw2 hwF]
      intro z₁ z₂; exact hlc'.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ z₁) (mem_univ z₂)
    obtain ⟨z₀, hz₀⟩ := hZne
    refine ⟨⋃ z : Z, B z, cVal ⟨z₀, hz₀⟩, isOpen_iUnion hBo,
      fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hyB ⟨y, hy⟩⟩,
      iUnion_subset fun z => hBsub z, fun y hy hyF => ?_⟩
    obtain ⟨z, hyBz⟩ := mem_iUnion.mp hy
    rw [hBconst z y hyBz hyF, hlc z ⟨z₀, hz₀⟩]
  obtain ⟨W₁, c₁, hW₁o, hX₁W₁, hW₁sub, hW₁c⟩ :=
    hball_const X₁ V₁ subset_union_left subset_union_left hV₁ hX₁V₁ hX₁c hX₁ne
  obtain ⟨W₁', c₁', hW₁'o, hX₁'W₁', hW₁'sub, hW₁'c⟩ :=
    hball_const X₁' V₁' subset_union_right subset_union_right hV₁' hX₁'V₁' hX₁'c hX₁'ne
  have hU_small_o : IsOpen (cutNbhd ψ₁ W₁ W₁') := isOpen_cutNbhd hψ₁ hW₁o hW₁'o
  have hFU_small : F ⊆ cutNbhd ψ₁ W₁ W₁' := subset_cutNbhd hun₁ hX₁W₁ hX₁'W₁'
  have hU_small_sub : cutNbhd ψ₁ W₁ W₁' ⊆ cutNbhd ψ₁ V₁ V₁' ∩ cutNbhd ψ₂ V₂ V₂' := by
    intro x hx
    obtain ⟨y, rfl⟩ := hψ₁.2.1 x
    rcases preimage_cutNbhd_subset hx with hy | hy
    · exact (hW₁sub hy).2
    · exact (hW₁'sub hy).2
  have hc_ne : c₁ ≠ c₁' := by
    intro hce
    have hall : ∀ z ∈ cutNbhd ψ₁ W₁ W₁', z ∉ F → cutSide ψ₂ V₂ X₂ z = c₁ := by
      intro z hz hzF
      obtain ⟨y, rfl⟩ := hψ₁.2.1 z
      rcases preimage_cutNbhd_subset hz with hy | hy
      · exact hW₁c y hy hzF
      · rw [hce]; exact hW₁'c y hy hzF
    rcases zmod2_eq_zero_or_one c₁ with h0 | h1
    · obtain ⟨y₂, hy₂⟩ := hX₂ne
      obtain ⟨ch, hy₂ch⟩ := exists_surfChart (hY₂.2.2 y₂)
      have hO₂ : IsOpen (V₂ ∩ ψ₂ ⁻¹' cutNbhd ψ₁ W₁ W₁' ∩ ch.U) :=
        (hV₂.inter (hU_small_o.preimage hψ₂.1)).inter ch.hU
      obtain ⟨r, -, -, -, -, -, hsub, ⟨w, hw, hwI⟩, -⟩ :=
        ch.exists_ball_nbhd hO₂ ⟨⟨hX₂V₂ hy₂, hFU_small (mem_F_of_left hun₂ hy₂)⟩, hy₂ch⟩ inter_subset_right
      have hwF : ψ₂ w ∉ F := fun h => hwI (hψ₂.2.2.2.2 h)
      have hwX₂ : w ∉ X₂ := fun h => hwF (mem_F_of_left hun₂ h)
      have h1' : cutSide ψ₂ V₂ X₂ (ψ₂ w) = 1 := cutSide_of_mem_VX ⟨(hsub hw).1.1, hwX₂⟩
      have h0' : cutSide ψ₂ V₂ X₂ (ψ₂ w) = 0 := h0 ▸ hall (ψ₂ w) (hsub hw).1.2 hwF
      rw [h1'] at h0'; exact one_ne_zero h0'
    · obtain ⟨y₂, hy₂⟩ := hX₂'ne
      obtain ⟨ch, hy₂ch⟩ := exists_surfChart (hY₂.2.2 y₂)
      have hO₂ : IsOpen (V₂' ∩ ψ₂ ⁻¹' cutNbhd ψ₁ W₁ W₁' ∩ ch.U) :=
        (hV₂'.inter (hU_small_o.preimage hψ₂.1)).inter ch.hU
      obtain ⟨r, -, -, -, -, -, hsub, ⟨w, hw, hwI⟩, -⟩ :=
        ch.exists_ball_nbhd hO₂ ⟨⟨hX₂'V₂' hy₂, hFU_small (mem_F_of_right hun₂ hy₂)⟩, hy₂ch⟩ inter_subset_right
      have hwF : ψ₂ w ∉ F := fun h => hwI (hψ₂.2.2.2.2 h)
      have h0' : cutSide ψ₂ V₂ X₂ (ψ₂ w) = 0 := cutSide_of_mem_VX' hψ₂ hun₂ hdisj₂ hX₂'V₂' (hsub hw).1.1
      have h1' : cutSide ψ₂ V₂ X₂ (ψ₂ w) = 1 := h1 ▸ hall (ψ₂ w) (hsub hw).1.2 hwF
      rw [h0'] at h1'; exact zero_ne_one h1'
  have hoff₁ := cutCocycle_zero_off hψ₁ hF hun₁ hcl₁
  have hoff₂ := cutCocycle_zero_off hψ₂ hF hun₂ hcl₂
  rcases zmod2_eq_zero_or_one c₁ with hc0 | hc1
  · have hc1' : c₁' = 1 := by
      rcases zmod2_eq_zero_or_one c₁' with h | h
      · exact absurd (hc0.trans h.symm) hc_ne
      · exact h
    let h : S → ZMod 2 := fun x => if x ∈ F then 1 else 0
    have hbd : ∀ x ∈ bd S \ {s, t}, h x = 0 := fun x ⟨hxbd, hxst⟩ => by
      refine ite_eq_right fun hxF => hxst ?_
      have : x ∈ F ∩ bd S := ⟨hxF, hxbd⟩
      rwa [hb] at this
    have hloc : ∀ p : S, ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
        ∀ x ∈ U, ∀ y ∈ U, cutCocycle ψ₁ V₁ V₁' X₁ x y - cutCocycle ψ₂ V₂ V₂' X₂ x y = h y - h x := by
      intro p
      by_cases hp : p ∈ F
      · refine ⟨cutNbhd ψ₁ W₁ W₁', hU_small_o, hFU_small hp, fun x hx y hy => ?_⟩
        have hx12 := hU_small_sub hx
        have hy12 := hU_small_sub hy
        unfold cutCocycle
        rw [ite_eq_left ⟨hx12.1, hy12.1⟩, ite_eq_left ⟨hx12.2, hy12.2⟩]
        have hdiff_s : ∀ z ∈ cutNbhd ψ₁ W₁ W₁', cutSide ψ₁ V₁ X₁ z - cutSide ψ₂ V₂ X₂ z = 1 + h z := by
          intro z hz
          by_cases hzF : z ∈ F
          · rw [cutSide_of_mem_F hun₁ (hdisj₁.mono_right hX₁'V₁') hzF,
              cutSide_of_mem_F hun₂ (hdisj₂.mono_right hX₂'V₂') hzF]
            simp [h, hzF]; rfl
          · obtain ⟨w, rfl⟩ := hψ₁.2.1 z
            rcases preimage_cutNbhd_subset hz with hw | hw
            · have hwX₁ : w ∉ X₁ := fun hwX => hzF (mem_F_of_left hun₁ hwX)
              rw [cutSide_of_mem_VX ⟨(hW₁sub hw).1, hwX₁⟩, hW₁c w hw hzF, hc0]
              simp [h, hzF]
            · rw [cutSide_of_mem_VX' hψ₁ hun₁ hdisj₁ hX₁'V₁' (hW₁'sub hw).1, hW₁'c w hw hzF, hc1']
              simp [h, hzF]
        have ex := hdiff_s x hx
        have ey := hdiff_s y hy
        rw [show cutSide ψ₁ V₁ X₁ y - cutSide ψ₁ V₁ X₁ x - (cutSide ψ₂ V₂ X₂ y - cutSide ψ₂ V₂ X₂ x) =
            (cutSide ψ₁ V₁ X₁ y - cutSide ψ₂ V₂ X₂ y) - (cutSide ψ₁ V₁ X₁ x - cutSide ψ₂ V₂ X₂ x) by ring,
          ey, ex]
        ring
      · obtain ⟨U₁, hU₁, hpU₁, hU₁F, hZ₁⟩ := hoff₁ p hp
        obtain ⟨U₂, hU₂, hpU₂, -, hZ₂⟩ := hoff₂ p hp
        refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hpU₁, hpU₂⟩, fun x hx y hy => ?_⟩
        rw [hZ₁ x hx.1 y hy.1, hZ₂ x hx.2 y hy.2]
        simp [h, show x ∉ F from hU₁F hx.1, show y ∉ F from hU₁F hy.1]
    choose U hUo hpU hU using hloc
    refine ⟨h, hbd, ⋃ p : S, U p ×ˢ U p, fun p =>
      Filter.mem_of_superset ((hUo p).prod (hUo p) |>.mem_nhds ⟨hpU p, hpU p⟩)
        (subset_iUnion (fun q => U q ×ˢ U q) p), fun x y hxy => ?_⟩
    obtain ⟨p, hx, hy⟩ := mem_iUnion.mp hxy
    exact hU p x hx y hy
  · have hc0' : c₁' = 0 := by
      rcases zmod2_eq_zero_or_one c₁' with h | h
      · exact h
      · exact absurd (hc1.trans h.symm) hc_ne
    have hloc : ∀ p : S, ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
        ∀ x ∈ U, ∀ y ∈ U, cutCocycle ψ₁ V₁ V₁' X₁ x y - cutCocycle ψ₂ V₂ V₂' X₂ x y = 0 := by
      intro p
      by_cases hp : p ∈ F
      · refine ⟨cutNbhd ψ₁ W₁ W₁', hU_small_o, hFU_small hp, fun x hx y hy => ?_⟩
        have hx12 := hU_small_sub hx
        have hy12 := hU_small_sub hy
        unfold cutCocycle
        rw [ite_eq_left ⟨hx12.1, hy12.1⟩, ite_eq_left ⟨hx12.2, hy12.2⟩]
        have heq_s : ∀ z ∈ cutNbhd ψ₁ W₁ W₁', cutSide ψ₁ V₁ X₁ z = cutSide ψ₂ V₂ X₂ z := by
          intro z hz
          by_cases hzF : z ∈ F
          · rw [cutSide_of_mem_F hun₁ (hdisj₁.mono_right hX₁'V₁') hzF,
              cutSide_of_mem_F hun₂ (hdisj₂.mono_right hX₂'V₂') hzF]
          · obtain ⟨w, rfl⟩ := hψ₁.2.1 z
            rcases preimage_cutNbhd_subset hz with hw | hw
            · have hwX₁ : w ∉ X₁ := fun hwX => hzF (mem_F_of_left hun₁ hwX)
              rw [cutSide_of_mem_VX ⟨(hW₁sub hw).1, hwX₁⟩, hW₁c w hw hzF, hc1]
            · rw [cutSide_of_mem_VX' hψ₁ hun₁ hdisj₁ hX₁'V₁' (hW₁'sub hw).1, hW₁'c w hw hzF, hc0']
        rw [heq_s x hx, heq_s y hy, sub_self]
      · obtain ⟨U₁, hU₁, hpU₁, -, hZ₁⟩ := hoff₁ p hp
        obtain ⟨U₂, hU₂, hpU₂, -, hZ₂⟩ := hoff₂ p hp
        refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hpU₁, hpU₂⟩, fun x hx y hy => ?_⟩
        rw [hZ₁ x hx.1 y hy.1, hZ₂ x hx.2 y hy.2, sub_self]
    choose U hUo hpU hU using hloc
    refine ⟨fun _ => 0, fun _ _ => rfl, ⋃ p : S, U p ×ˢ U p, fun p =>
      Filter.mem_of_superset ((hUo p).prod (hUo p) |>.mem_nhds ⟨hpU p, hpU p⟩)
        (subset_iUnion (fun q => U q ×ˢ U q) p), fun x y hxy => ?_⟩
    obtain ⟨p, hx, hy⟩ := mem_iUnion.mp hxy
    simpa using hU p x hx y hy

end CutCocycle

/-! ### Canonical `arcCocycle` of a proper `I`-arc -/

section ArcCocycle

variable {S : Type u} [TopologicalSpace S] [ConnectedSpace S]

/-- Choose a cutting and separated open neighborhoods of its two lifts for a proper `I`-arc `F`. -/
theorem exists_cut_cocycle_data (hS : IsSurface S) {F : Set S} {s t : S}
    (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : T2Space Y) (ψ : Y → S)
      (X X' V_X V_X' : Set Y),
      IsSurface Y ∧ IsCutting ψ F ∧ LiftPair ψ F s t X X' ∧
      IsOpen V_X ∧ IsOpen V_X' ∧ X ⊆ V_X ∧ X' ⊆ V_X' ∧
      Disjoint (closure V_X) (closure V_X') := by
  have : T2Space S := hS.2.1
  obtain ⟨Y, tY, t2Y, ψ, hY, hψ, X, X', hP⟩ := exists_cut_arc hS hne hb hl
  have : CompactSpace Y := hY.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, -⟩ := id hP
  obtain ⟨V_X, V_X', hVX, hVX', hXV, hX'V', hcl⟩ :=
    exists_disjoint_closure_nhds l1.isCompact.isClosed l2.isCompact.isClosed hd
  exact ⟨Y, tY, t2Y, ψ, X, X', V_X, V_X', hY, hψ, hP, hVX, hVX', hXV, hX'V', hcl⟩

/-- Canonical `ZMod 2` crossing local cocycle of a proper `I`-arc `F` in a connected surface `S`. -/
noncomputable def arcCocycle (hS : IsSurface S) {F : Set S} {s t : S}
    (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t) : S → S → ZMod 2 :=
  let d := exists_cut_cocycle_data hS hne hb hl
  let ψ := d.choose_spec.choose_spec.choose_spec.choose
  let X := d.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let V_X := d.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let V_X' := d.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  cutCocycle ψ V_X V_X' X

/-- `arcCocycle` is a local 1-cocycle. -/
theorem isCoc_arcCocycle (hS : IsSurface S) {F : Set S} {s t : S}
    (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t) :
    IsCoc (arcCocycle hS hne hb hl) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  unfold arcCocycle
  set d := exists_cut_cocycle_data hS hne hb hl
  let _ := d.choose_spec.choose
  let _ := d.choose_spec.choose_spec.choose
  obtain ⟨hY, hψ, hP, hVX, hVX', hXV, hX'V', hcl⟩ :=
    d.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have : CompactSpace d.choose := hY.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, -⟩ := id hP
  exact isCoc_cutCocycle hψ hl.isCompact.isClosed hun hVX hVX' hXV hX'V' hcl

/-- `arcCocycle` is boundary-cohomologous (`BdCohRel s t`) to `cutCocycle` from ANY cutting of `F`. -/
theorem arcCocycle_bdCohRel_cutCocycle (hS : IsSurface S) {F : Set S} {s t : S}
    (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t)
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S}
    (hY : IsSurface Y) (hψ : IsCutting ψ F) {X X' V_X V_X' : Set Y}
    (hP : LiftPair ψ F s t X X') (hVX : IsOpen V_X) (hVX' : IsOpen V_X')
    (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X') (hcl : Disjoint (closure V_X) (closure V_X')) :
    BdCohRel s t (arcCocycle hS hne hb hl) (cutCocycle ψ V_X V_X' X) := by
  have : T2Space S := hS.2.1
  unfold arcCocycle
  set d := exists_cut_cocycle_data hS hne hb hl
  let _ := d.choose_spec.choose
  let _ := d.choose_spec.choose_spec.choose
  obtain ⟨hY₁, hψ₁, hP₁, hV₁, hV₁', hX₁V₁, hX₁'V₁', hcl₁⟩ :=
    d.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨x0₁, x1₁, y0₁, y1₁, l1₁, l2₁, -, hun₁, -⟩ := id hP₁
  obtain ⟨x0, x1, y0, y1, l1, l2, -, hun, -⟩ := id hP
  have h1c : IsPreconnected d.choose_spec.choose_spec.choose_spec.choose_spec.choose := by
    obtain ⟨a, ha, e, -, -⟩ := l1₁.exists_arc; exact e ▸ isPreconnected_range ha.1
  have h2c : IsPreconnected d.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose := by
    obtain ⟨a, ha, e, -, -⟩ := l2₁.exists_arc; exact e ▸ isPreconnected_range ha.1
  exact cutCocycle_bdCohRel_of_same_arc hY₁ hY hψ₁ hψ hl.isCompact.isClosed hb
    h1c h2c ⟨x0₁, l1₁.left_mem⟩ ⟨y0₁, l2₁.left_mem⟩
    ⟨x0, l1.left_mem⟩ ⟨y0, l2.left_mem⟩
    hun₁ hun hV₁ hV₁' hVX hVX' hX₁V₁ hX₁'V₁' hXV hX'V' hcl₁ hcl

end ArcCocycle

/-! ### Separating arcs, non-separating arcs, and orientability after cutting -/

section CutTopology

variable {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]

/-- When a cutting `ψ : Y → S` along `F` disconnects `Y` into two clopen pieces `W₁, W₂` with
`X ⊆ W₁` and `X' ⊆ W₂`, `cutCocycle` is globally a coboundary `δ g_sep`, where `g_sep` takes BOTH
values `1` and `0` on `bd S \ {s, t}`! -/
theorem cutCocycle_sep_coboundary [T2Space Y] [T2Space S] (hY : IsSurface Y)
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    (hb : F ∩ bd S = {s, t}) {X X' V_X V_X' : Set Y}
    (hP : LiftPair ψ F s t X X') (hVX : IsOpen V_X) (hVX' : IsOpen V_X')
    (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X') (hclDisj : Disjoint (closure V_X) (closure V_X'))
    {W₁ W₂ : Set Y} (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂)
    (hXW₁ : X ⊆ W₁) (hX'W₂ : X' ⊆ W₂) (hWun : W₁ ∪ W₂ = univ) (hWdisj : Disjoint W₁ W₂) :
    ∃ g : S → ZMod 2,
      (∃ N : Set (S × S), NearDiag N ∧ ∀ x y, (x, y) ∈ N → cutCocycle ψ V_X V_X' X x y = g y - g x) ∧
      (∃ x₁ ∈ bd S \ {s, t}, g x₁ = 1) ∧ (∃ x₂ ∈ bd S \ {s, t}, g x₂ = 0) := by
  classical
  have : CompactSpace Y := hY.1
  obtain ⟨x0, x1, y0, y1, l1, l2, -, hun, -⟩ := id hP
  have hdisj : Disjoint V_X V_X' := hclDisj.mono subset_closure subset_closure
  let U₁ : Set Y := V_X ∩ W₁
  let U₂ : Set Y := V_X' ∩ W₂
  have hU₁o : IsOpen U₁ := hVX.inter hW₁.2
  have hU₂o : IsOpen U₂ := hVX'.inter hW₂.2
  have hU_small_o : IsOpen (cutNbhd ψ U₁ U₂) := isOpen_cutNbhd hψ hU₁o hU₂o
  have hFU_small : F ⊆ cutNbhd ψ U₁ U₂ :=
    subset_cutNbhd hun (subset_inter hXV hXW₁) (subset_inter hX'V' hX'W₂)
  have hU_small_sub : cutNbhd ψ U₁ U₂ ⊆ cutNbhd ψ V_X V_X' := fun x hx ⟨y, hyc, hyeq⟩ =>
    hx ⟨y, fun hy => hyc (hy.elim (fun h => .inl h.1) (fun h => .inr h.1)), hyeq⟩
  let g : S → ZMod 2 := fun x => if x ∈ ψ '' (W₁ \ X) then 1 else 0
  have hcl : IsClosedMap ψ := hψ.1.isClosedMap
  have hW₁_img_open : IsOpen (ψ '' (W₁ \ X)) := by
    have hq : IsQuotientMap ψ := hcl.isQuotientMap hψ.1 hψ.2.1
    rw [← hq.isOpen_preimage]
    have hsub : W₁ \ X = W₁ ∩ (ψ ⁻¹' F)ᶜ := by
      ext y; simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_preimage]
      constructor
      · rintro ⟨hy1, hyX⟩; refine ⟨hy1, fun hF => ?_⟩
        have : y ∈ X ∪ X' := hun.symm ▸ hF
        exact Set.disjoint_left.mp hWdisj hy1 (hX'W₂ (this.resolve_left hyX))
      · rintro ⟨hy1, hyF⟩; exact ⟨hy1, fun hyX => hyF (mem_F_of_left hun hyX)⟩
    have heq : ψ ⁻¹' (ψ '' (W₁ \ X)) = W₁ \ X := subset_antisymm (fun y ⟨w, hw, hweq⟩ => by
      have hwF : ψ w ∉ F := (hsub ▸ hw).2
      exact hψ.2.2.1 (by show ψ y ∉ F; rw [← hweq]; exact hwF) hwF hweq.symm ▸ hw)
      (subset_preimage_image ψ _)
    rw [heq, hsub]
    exact hW₁.2.inter (hF.preimage hψ.1).isOpen_compl
  have hW₂_img_open : IsOpen (ψ '' (W₂ \ X')) := by
    have hq : IsQuotientMap ψ := hcl.isQuotientMap hψ.1 hψ.2.1
    rw [← hq.isOpen_preimage]
    have hsub : W₂ \ X' = W₂ ∩ (ψ ⁻¹' F)ᶜ := by
      ext y; simp only [mem_sdiff, mem_inter_iff, mem_compl_iff, mem_preimage]
      constructor
      · rintro ⟨hy2, hyX'⟩; refine ⟨hy2, fun hF => ?_⟩
        have : y ∈ X ∪ X' := hun.symm ▸ hF
        exact Set.disjoint_left.mp hWdisj (hXW₁ (this.resolve_right hyX')) hy2
      · rintro ⟨hy2, hyF⟩; exact ⟨hy2, fun hyX' => hyF (mem_F_of_right hun hyX')⟩
    have heq : ψ ⁻¹' (ψ '' (W₂ \ X')) = W₂ \ X' := subset_antisymm (fun y ⟨w, hw, hweq⟩ => by
      have hwF : ψ w ∉ F := (hsub ▸ hw).2
      exact hψ.2.2.1 (by show ψ y ∉ F; rw [← hweq]; exact hwF) hwF hweq.symm ▸ hw)
      (subset_preimage_image ψ _)
    rw [heq, hsub]
    exact hW₂.2.inter (hF.preimage hψ.1).isOpen_compl
  have hW12_disj : Disjoint (ψ '' (W₁ \ X)) (ψ '' (W₂ \ X')) := by
    rw [Set.disjoint_left]
    rintro _ ⟨w₁, ⟨hw1, hw1X⟩, rfl⟩ ⟨w₂, ⟨hw2, hw2X'⟩, hweq⟩
    have hw1F : ψ w₁ ∉ F := fun hF => by
      have : w₁ ∈ X ∪ X' := hun.symm ▸ hF
      exact Set.disjoint_left.mp hWdisj hw1 (hX'W₂ (this.resolve_left hw1X))
    have h12 : w₁ = w₂ := hψ.2.2.1 hw1F (by show ψ w₂ ∉ F; rwa [hweq]) hweq.symm
    exact Set.disjoint_left.mp hWdisj hw1 (h12 ▸ hw2)
  have hoff := cutCocycle_zero_off hψ hF hun hclDisj
  have hloc : ∀ p : S, ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
      ∀ x ∈ U, ∀ y ∈ U, cutCocycle ψ V_X V_X' X x y = g y - g x := by
    intro p
    by_cases hp : p ∈ F
    · refine ⟨cutNbhd ψ U₁ U₂, hU_small_o, hFU_small hp, fun x hx y hy => ?_⟩
      unfold cutCocycle
      rw [ite_eq_left ⟨hU_small_sub hx, hU_small_sub hy⟩]
      have hsg : ∀ z ∈ cutNbhd ψ U₁ U₂, cutSide ψ V_X X z = g z := by
        intro z hz
        by_cases hzF : z ∈ F
        · rw [cutSide_of_mem_F hun (hdisj.mono_right hX'V') hzF]
          refine (ite_eq_right ?_).symm
          rintro ⟨w, ⟨hw1, hwX⟩, rfl⟩
          have : w ∈ X ∪ X' := hun.symm ▸ hzF
          exact Set.disjoint_left.mp hWdisj hw1 (hX'W₂ (this.resolve_left hwX))
        · obtain ⟨w, rfl⟩ := hψ.2.1 z
          rcases preimage_cutNbhd_subset hz with ⟨hwV, hw1⟩ | ⟨hwV', hw2⟩
          · have hwX : w ∉ X := fun h => hzF (mem_F_of_left hun h)
            rw [cutSide_of_mem_VX ⟨hwV, hwX⟩]
            exact (ite_eq_left ⟨w, ⟨hw1, hwX⟩, rfl⟩).symm
          · have hwX' : w ∉ X' := fun h => hzF (mem_F_of_right hun h)
            rw [cutSide_of_mem_VX' hψ hun hdisj hX'V' hwV']
            exact (ite_eq_right fun h => Set.disjoint_left.mp hW12_disj h ⟨w, ⟨hw2, hwX'⟩, rfl⟩).symm
      rw [hsg x hx, hsg y hy]
    · obtain ⟨U, hUo, hpU, -, hU⟩ := hoff p hp
      obtain ⟨w, rfl⟩ := hψ.2.1 p
      rcases (hWun ▸ mem_univ w : w ∈ W₁ ∪ W₂) with hw1 | hw2
      · have hwX : w ∉ X := fun h => hp (mem_F_of_left hun h)
        refine ⟨U ∩ ψ '' (W₁ \ X), hUo.inter hW₁_img_open, ⟨hpU, ⟨w, ⟨hw1, hwX⟩, rfl⟩⟩,
          fun x hx y hy => ?_⟩
        rw [hU x hx.1 y hy.1]
        have hx1 : g x = 1 := ite_eq_left hx.2
        have hy1 : g y = 1 := ite_eq_left hy.2
        rw [hx1, hy1, sub_self]
      · have hwX' : w ∉ X' := fun h => hp (mem_F_of_right hun h)
        refine ⟨U ∩ ψ '' (W₂ \ X'), hUo.inter hW₂_img_open, ⟨hpU, ⟨w, ⟨hw2, hwX'⟩, rfl⟩⟩,
          fun x hx y hy => ?_⟩
        rw [hU x hx.1 y hy.1]
        have hx1 : g x = 0 := ite_eq_right fun h => Set.disjoint_left.mp hW12_disj h hx.2
        have hy1 : g y = 0 := ite_eq_right fun h => Set.disjoint_left.mp hW12_disj h hy.2
        rw [hx1, hy1, sub_self]
  choose U hUo hpU hU using hloc
  have hex_off : ∀ (Z W : Set Y), IsLine Z → Z ⊆ W → IsClopen W → Z ⊆ bd Y →
      ∃ y ∈ W \ Z, y ∈ bd Y := by
    intro Z W hZ hZW hWcl hZbd
    obtain ⟨fZ⟩ := id hZ
    have hZne : Z.Nonempty := ⟨(fZ 0).1, (fZ 0).2⟩
    obtain ⟨z₀, hz₀⟩ := hZne
    have hC : connectedComponentIn (bd Y) z₀ ∈ cuffs Y := ⟨z₀, hZbd hz₀, rfl⟩
    obtain ⟨φ⟩ := (cuff_statement.{u} Y hY).2.2 _ hC
    have hCsub : connectedComponentIn (bd Y) z₀ ⊆ W :=
      isPreconnected_connectedComponentIn.subset_isClopen hWcl ⟨z₀, mem_connectedComponentIn (hZbd hz₀), hZW hz₀⟩
    have hZimg : (Subtype.val ∘ fZ) '' univ = Z := by
      ext x; simp only [mem_image, mem_univ, true_and, comp_apply]
      exact ⟨fun ⟨u, hu⟩ => hu ▸ (fZ u).2, fun hx => ⟨fZ.symm ⟨x, hx⟩, by simp⟩⟩
    have hZconn : IsPreconnected Z :=
      hZimg ▸ isPreconnected_univ.image (Subtype.val ∘ fZ) (continuous_subtype_val.comp fZ.continuous).continuousOn
    have hZsub : Z ⊆ connectedComponentIn (bd Y) z₀ := hZconn.subset_connectedComponentIn hz₀ hZbd
    let η : ℝ → Y := fun u => (fZ (Set.projIcc 0 1 zero_le_one u)).1
    have hηc : ContinuousOn η (Icc 0 1) :=
      (continuous_subtype_val.comp (fZ.continuous.comp continuous_projIcc)).continuousOn
    have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ connectedComponentIn (bd Y) z₀ :=
      fun u _ => hZsub (fZ _).2
    have hηinj : InjOn η (Icc 0 1) := fun u hu v hv he => by
      have h1 := fZ.injective (Subtype.ext he)
      have h2 := congrArg Subtype.val h1
      simpa [projIcc_of_mem zero_le_one hu, projIcc_of_mem zero_le_one hv] using h2
    obtain ⟨m, hmc, hm⟩ := exists_lift φ hηc hηm
    have hmono := lift_mono hmc (inj_of_lift hm hηinj)
    have hgap_pt : ∃ r : ℝ, ∀ u ∈ Icc (0 : ℝ) 1, ee r ≠ ee (m u) := by
      rcases hmono with hsm | hsa
      · have hlt := lift_lt_add_one hmc hsm (inj_of_lift hm hηinj)
        refine ⟨(m 1 + (m 0 + 1)) / 2, fun u hu he => ?_⟩
        have h1 : m 0 ≤ m u := hsm.monotoneOn (by simp) hu hu.1
        have h2 : m u ≤ m 1 := hsm.monotoneOn hu (by simp) hu.2
        exact ee_ne (x := m u) (y := (m 1 + (m 0 + 1)) / 2) (by linarith) (by linarith) he.symm
      · have hsm' : StrictMonoOn (fun u => -m u) (Icc 0 1) :=
          fun x hx y hy hxy => neg_lt_neg (hsa hx hy hxy)
        have hlt : -m 1 < -m 0 + 1 := lift_lt_add_one hmc.neg hsm' (fun x hx y hy he =>
          inj_of_lift hm hηinj hx hy (by
            have h1 : ee (m x) = (ee (-m x))⁻¹ := by simp [ee, Circle.exp_neg]
            have h2 : ee (m y) = (ee (-m y))⁻¹ := by simp [ee, Circle.exp_neg]
            have he' : ee (-m x) = ee (-m y) := he
            show ee (m x) = ee (m y)
            rw [h1, h2, he']))
        refine ⟨-((-m 1 + (-m 0 + 1)) / 2), fun u hu he => ?_⟩
        have h1 : -m 0 ≤ -m u := hsm'.monotoneOn (by simp) hu hu.1
        have h2 : -m u ≤ -m 1 := hsm'.monotoneOn hu (by simp) hu.2
        have he' : ee (-m u) = ee ((-m 1 + (-m 0 + 1)) / 2) := by
          have := congrArg Inv.inv he
          simpa [ee, Circle.exp_neg] using this.symm
        exact ee_ne (x := -m u) (y := (-m 1 + (-m 0 + 1)) / 2) (by linarith) (by linarith) he'
    obtain ⟨r, hr⟩ := hgap_pt
    refine ⟨(φ (ee r)).1, ⟨hCsub (φ (ee r)).2, fun hZmem => ?_⟩, connectedComponentIn_subset _ _ (φ (ee r)).2⟩
    let u0 : unitInterval := fZ.symm ⟨(φ (ee r)).1, hZmem⟩
    have hηu : η u0.1 = (φ (ee r)).1 := by
      simp [η, u0, projIcc_of_mem zero_le_one u0.2]
    exact hr u0.1 u0.2 (φ.injective (Subtype.ext ((hm u0.1 u0.2).trans hηu).symm))
  have hZ1 : W₁ ∩ ψ ⁻¹' F = X := by
    ext y; rw [← hun]; simp only [mem_inter_iff, mem_union]
    exact ⟨fun ⟨h1, h2⟩ => h2.resolve_right fun hX' => Set.disjoint_left.mp hWdisj h1 (hX'W₂ hX'),
      fun h => ⟨hXW₁ h, .inl h⟩⟩
  have hZ2 : W₂ ∩ ψ ⁻¹' F = X' := by
    ext y; rw [← hun]; simp only [mem_inter_iff, mem_union]
    exact ⟨fun ⟨h1, h2⟩ => h2.resolve_left fun hX => Set.disjoint_left.mp hWdisj (hXW₁ hX) h1,
      fun h => ⟨hX'W₂ h, .inr h⟩⟩
  obtain ⟨f1, -⟩ := l1
  obtain ⟨f2, -⟩ := l2
  obtain ⟨y₁, ⟨hy₁W, hy₁X⟩, hy₁bd⟩ := hex_off X W₁ ⟨f1⟩ hXW₁ hW₁
    (fun z hz => hψ.2.2.2.2 (mem_F_of_left hun hz))
  obtain ⟨y₂, ⟨hy₂W, hy₂X'⟩, hy₂bd⟩ := hex_off X' W₂ ⟨f2⟩ hX'W₂ hW₂
    (fun z hz => hψ.2.2.2.2 (mem_F_of_right hun hz))
  have hy₁F : ψ y₁ ∉ F := fun h => hy₁X (hZ1 ▸ ⟨hy₁W, h⟩)
  have hy₂F : ψ y₂ ∉ F := fun h => hy₂X' (hZ2 ▸ ⟨hy₂W, h⟩)
  have hx₁bd : ψ y₁ ∈ bd S \ {s, t} :=
    ⟨bd_of_bd hψ hF hy₁bd hy₁F, fun h => hy₁F ((hb.symm ▸ h : ψ y₁ ∈ F ∩ bd S).1)⟩
  have hx₂bd : ψ y₂ ∈ bd S \ {s, t} :=
    ⟨bd_of_bd hψ hF hy₂bd hy₂F, fun h => hy₂F ((hb.symm ▸ h : ψ y₂ ∈ F ∩ bd S).1)⟩
  refine ⟨g, ⟨⋃ p : S, U p ×ˢ U p, fun p =>
    Filter.mem_of_superset ((hUo p).prod (hUo p) |>.mem_nhds ⟨hpU p, hpU p⟩)
      (subset_iUnion (fun q => U q ×ˢ U q) p), fun x y hxy => ?_⟩,
    ⟨ψ y₁, hx₁bd, ite_eq_left ⟨y₁, ⟨hy₁W, hy₁X⟩, rfl⟩⟩,
    ⟨ψ y₂, hx₂bd, ite_eq_right fun h => Set.disjoint_left.mp hW12_disj h ⟨y₂, ⟨hy₂W, hy₂X'⟩, rfl⟩⟩⟩
  obtain ⟨p, hx, hy⟩ := mem_iUnion.mp hxy
  exact hU p x hx y hy

/-- If a proper `I`-arc `F` is non-separating (its cut surface `Y` is connected) and `F'` is another
proper `I`-arc with the same ends `s, t` satisfying `BdCohRel s t (arcCocycle F') (arcCocycle F)`,
then `F'` is also non-separating (its cut surface `Y'` is connected)! -/
theorem connected_cut_of_bdCohRel [ConnectedSpace S] (hS : IsSurface S)
    {F F' : Set S} {s t : S} (hne : s ≠ t)
    (hb : F ∩ bd S = {s, t}) (hb' : F' ∩ bd S = {s, t})
    (hl : IsLineWithEnds F s t) (hl' : IsLineWithEnds F' s t)
    {Y Y' : Type u} [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Y'] [T2Space Y']
    {ψ : Y → S} {ψ' : Y' → S} (hY : IsSurface Y) (hY' : IsSurface Y')
    (hψ : IsCutting ψ F) (hψ' : IsCutting ψ' F')
    {X X' : Set Y} {X₂ X₂' : Set Y'}
    (hP : LiftPair ψ F s t X X') (hP' : LiftPair ψ' F' s t X₂ X₂')
    (hconn : ConnectedSpace Y)
    (hrel : BdCohRel s t (arcCocycle hS hne hb' hl') (arcCocycle hS hne hb hl)) :
    ConnectedSpace Y' := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace Y := hY.1
  have : CompactSpace Y' := hY'.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, -⟩ := id hP
  obtain ⟨x0', x1', y0', y1', l1', l2', hd', hun', -⟩ := id hP'
  have hl1'c : IsPreconnected X₂ := by obtain ⟨a, ha, e, -, -⟩ := l1'.exists_arc; exact e ▸ isPreconnected_range ha.1
  have hl2'c : IsPreconnected X₂' := by obtain ⟨a, ha, e, -, -⟩ := l2'.exists_arc; exact e ▸ isPreconnected_range ha.1
  rcases cut_comps hψ' hY' hl1'c hl2'c hun' l1'.left_mem l2'.left_mem with
    hYc' | ⟨W₁, W₂, -, -, hXW₁, hX'W₂, hW₁, hW₂, hWun, hWdisj, -, -⟩
  · exact hYc'
  · exfalso
    obtain ⟨V_X, V_X', hVX, hVX', hXV, hX'V', hcl⟩ :=
      exists_disjoint_closure_nhds l1.isCompact.isClosed l2.isCompact.isClosed hd
    obtain ⟨V₂, V₂', hV₂, hV₂', hXV₂, hX'V₂', hcl₂⟩ :=
      exists_disjoint_closure_nhds l1'.isCompact.isClosed l2'.isCompact.isClosed hd'
    have hrel_cut : BdCohRel s t (cutCocycle ψ' V₂ V₂' X₂) (cutCocycle ψ V_X V_X' X) :=
      bdCohRel_trans (bdCohRel_symm (arcCocycle_bdCohRel_cutCocycle hS hne hb' hl' hY' hψ' hP' hV₂ hV₂' hXV₂ hX'V₂' hcl₂))
        (bdCohRel_trans hrel (arcCocycle_bdCohRel_cutCocycle hS hne hb hl hY hψ hP hVX hVX' hXV hX'V' hcl))
    obtain ⟨h, hbd, N₁, hN₁, hdiff₁⟩ := hrel_cut
    obtain ⟨g, ⟨N₂, hN₂, hdiff₂⟩, ⟨x₁, hx₁bd, hx₁⟩, ⟨x₂, hx₂bd, hx₂⟩⟩ :=
      cutCocycle_sep_coboundary hY' hψ' hl'.isCompact.isClosed hb' hP' hV₂ hV₂' hXV₂ hX'V₂' hcl₂
        hW₁ hW₂ hXW₁ hX'W₂ hWun hWdisj
    obtain ⟨N₃, hN₃, hdiff₃⟩ :=
      pbk_cutCocycle_coboundary hψ hl.isCompact.isClosed l1.isCompact.isClosed l2.isCompact.isClosed
        hun hVX hVX' hXV hX'V' hcl
    let f : Y → ZMod 2 := fun y => g (ψ y) - h (ψ y) - (if y ∈ X then 1 else 0)
    have hN : NearDiag (((fun p : Y × Y => (ψ p.1, ψ p.2)) ⁻¹' (N₁ ∩ N₂)) ∩ N₃) := fun y =>
      Filter.inter_mem
        (((hψ.1.comp continuous_fst).prodMk (hψ.1.comp continuous_snd)).continuousAt.preimage_mem_nhds
          (Filter.inter_mem (hN₁ (ψ y)) (hN₂ (ψ y))))
        (hN₃ y)
    have hf_const := const_of_nearDiag_eq hN (g := f) (fun y₁ y₂ hy => by
      have e1 := hdiff₁ (ψ y₁) (ψ y₂) hy.1.1
      have e2 := hdiff₂ (ψ y₁) (ψ y₂) hy.1.2
      have e3 := hdiff₃ y₁ y₂ hy.2
      dsimp only [f]
      linear_combination -e1 + e2 - e3)
    obtain ⟨y₁, hy₁⟩ := hψ.2.1 x₁
    obtain ⟨y₂, hy₂⟩ := hψ.2.1 x₂
    have hy₁X : y₁ ∉ X := fun hX1 =>
      hx₁bd.2 (hb.symm ▸ ⟨hy₁ ▸ mem_F_of_left hun hX1, hx₁bd.1⟩)
    have hy₂X : y₂ ∉ X := fun hX2 =>
      hx₂bd.2 (hb.symm ▸ ⟨hy₂ ▸ mem_F_of_left hun hX2, hx₂bd.1⟩)
    have heq := hf_const y₁ y₂
    simp only [f, hy₁, hy₂, hbd x₁ hx₁bd, hbd x₂ hx₂bd, hx₁, hx₂, ite_eq_right hy₁X, ite_eq_right hy₂X,
      sub_zero] at heq
    exact one_ne_zero heq

/-- When cutting a connected surface `S` along a proper `I`-arc `F` produces a surface `Y` with
`w1 AY = δ h_Y`, either `S` is orientable (`w1 AS = δ g_S`, with `g_S (ψ y) = h_Y y + cutOrientDiff y`)
or `w1 AS - cutCocycle F = δ g_S` (with `g_S (ψ y) = h_Y y + cutOrientDiff y + 1_X y`)! -/
theorem exists_w1_cut_descent [ConnectedSpace S] (hS : IsSurface S) (hY : IsSurface Y) [T2Space Y]
    {ψ : Y → S} {F : Set S} {s t : S} (hψ : IsCutting ψ F) (hF : IsClosed F)
    {X X' V_X V_X' : Set Y} (hP : LiftPair ψ F s t X X')
    (hVX : IsOpen V_X) (hVX' : IsOpen V_X') (hXV : X ⊆ V_X) (hX'V' : X' ⊆ V_X')
    (hclDisj : Disjoint (closure V_X) (closure V_X'))
    (AY : SurfAtlas Y) (AS : SurfAtlas S)
    {h_Y : Y → ZMod 2} {N_Y : Set (Y × Y)} (hNY : NearDiag N_Y)
    (hhY : ∀ y₁ y₂, (y₁, y₂) ∈ N_Y → w1 AY y₁ y₂ = h_Y y₂ - h_Y y₁) :
    (∃ g_S : S → ZMod 2,
      (∀ y : Y, g_S (ψ y) = h_Y y + cutOrientDiff AY AS ψ y) ∧
      ∃ N : Set (S × S), NearDiag N ∧ ∀ x₁ x₂, (x₁, x₂) ∈ N → w1 AS x₁ x₂ = g_S x₂ - g_S x₁) ∨
    (∃ g_S : S → ZMod 2,
      (∀ y : Y, g_S (ψ y) = h_Y y + cutOrientDiff AY AS ψ y + (open Classical in if y ∈ X then 1 else 0)) ∧
      ∃ N : Set (S × S), NearDiag N ∧
        ∀ x₁ x₂, (x₁, x₂) ∈ N → w1 AS x₁ x₂ - cutCocycle ψ V_X V_X' X x₁ x₂ = g_S x₂ - g_S x₁) := by
  classical
  have : CompactSpace Y := hY.1
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, hbijX, hbijX', -⟩ := id hP
  have hdisj : Disjoint V_X V_X' := hclDisj.mono subset_closure subset_closure
  obtain ⟨N_cut, hNcut, hcut⟩ := cohRel_w1_cut_explicit hY hS hψ hF AY AS
  let g_Y : Y → ZMod 2 := fun y => h_Y y + cutOrientDiff AY AS ψ y
  have hgY : ∀ y₁ y₂, (y₁, y₂) ∈ N_Y ∩ N_cut → w1 AS (ψ y₁) (ψ y₂) = g_Y y₂ - g_Y y₁ := fun y₁ y₂ h => by
    have e1 := hhY y₁ y₂ h.1
    have e2 := hcut y₁ y₂ h.2
    dsimp only [g_Y]
    linear_combination e1 + e2
  have hN_Y' : NearDiag (N_Y ∩ N_cut) := fun y => Filter.inter_mem (hNY y) (hNcut y)
  obtain ⟨a, ξ, η, L, -, -, himξ, himη, -, -⟩ := exists_arcLift hP hψ
  have hΔ_const : ∀ u ∈ Icc (0 : ℝ) 1, g_Y (η u) - g_Y (ξ u) = g_Y (η 0) - g_Y (ξ 0) := by
    have hloc : ∀ u ∈ Icc (0 : ℝ) 1, ∃ δ > 0, ∀ v ∈ Icc (0 : ℝ) 1, |v - u| < δ →
        g_Y (η v) - g_Y (ξ v) = g_Y (η u) - g_Y (ξ u) := by
      intro u hu
      obtain ⟨U₁, hU₁, U₂, hU₂, hU₁₂⟩ := mem_nhds_prod_iff.mp (hN_Y' (ξ u))
      obtain ⟨V₁, hV₁, V₂, hV₂, hV₁₂⟩ := mem_nhds_prod_iff.mp (hN_Y' (η u))
      have hξ_nhd : ξ ⁻¹' (U₁ ∩ U₂) ∈ 𝓝[Icc (0 : ℝ) 1] u :=
        (L.cξ u hu).preimage_mem_nhdsWithin (Filter.inter_mem hU₁ hU₂)
      have hη_nhd : η ⁻¹' (V₁ ∩ V₂) ∈ 𝓝[Icc (0 : ℝ) 1] u :=
        (L.cη u hu).preimage_mem_nhdsWithin (Filter.inter_mem hV₁ hV₂)
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp (Filter.inter_mem hξ_nhd hη_nhd)
      refine ⟨δ, hδ, fun v hv hlt => ?_⟩
      have hvmem := hδsub ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hlt, hv⟩
      have e1 := hgY (ξ u) (ξ v) (hU₁₂ ⟨mem_of_mem_nhds hU₁, hvmem.1.2⟩)
      have e2 := hgY (η u) (η v) (hV₁₂ ⟨mem_of_mem_nhds hV₁, hvmem.2.2⟩)
      rw [L.hξ u hu, L.hξ v hv] at e1
      rw [L.hη u hu, L.hη v hv] at e2
      linear_combination e1 - e2
    let Δ : ℝ → ZMod 2 := fun u => g_Y (η u) - g_Y (ξ u)
    have hlc : IsLocallyConstant (fun u : Icc (0 : ℝ) 1 => Δ u.1) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      rintro ⟨u, hu⟩
      obtain ⟨δ, hδ, hδeq⟩ := hloc u hu
      have hball : (Subtype.val ⁻¹' ball u δ : Set (Icc (0 : ℝ) 1)) ∈ 𝓝 (⟨u, hu⟩ : Icc (0 : ℝ) 1) :=
        (isOpen_ball.preimage continuous_subtype_val).mem_nhds (mem_ball_self hδ)
      refine Filter.mem_of_superset hball fun ⟨v, hv⟩ hvb => ?_
      exact hδeq v hv (by simpa [mem_ball, Real.dist_eq] using hvb)
    have : ConnectedSpace (Icc (0 : ℝ) 1) := isConnected_iff_connectedSpace.mp (isConnected_Icc zero_le_one)
    intro u hu
    exact hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ ⟨u, hu⟩) (mem_univ ⟨0, by simp⟩)
  have hdesc_eq : ∀ (c₀ : ZMod 2) (g_S : S → ZMod 2),
      (∀ y : Y, g_S (ψ y) = g_Y y + c₀ * (if y ∈ X then 1 else 0)) →
      ∃ N : Set (S × S), NearDiag N ∧ ∀ x₁ x₂, (x₁, x₂) ∈ N →
        w1 AS x₁ x₂ - c₀ * cutCocycle ψ V_X V_X' X x₁ x₂ = g_S x₂ - g_S x₁ := by
    intro c₀ g_S hgS
    have hUo : IsOpen (cutNbhd ψ V_X V_X') := isOpen_cutNbhd hψ hVX hVX'
    have hFsub : F ⊆ cutNbhd ψ V_X V_X' := subset_cutNbhd hun hXV hX'V'
    have hoff := cutCocycle_zero_off hψ hF hun hclDisj
    have hloc : ∀ p : S, ∃ W : Set S, IsOpen W ∧ p ∈ W ∧
        ∀ x₁ ∈ W, ∀ x₂ ∈ W, w1 AS x₁ x₂ - c₀ * cutCocycle ψ V_X V_X' X x₁ x₂ = g_S x₂ - g_S x₁ := by
      intro p
      by_cases hp : p ∈ F
      · obtain ⟨u, hu, rfl⟩ := L.img.symm.subset hp
        have hξX : ξ u ∈ X := himξ ▸ ⟨u, hu, rfl⟩
        have hηX' : η u ∈ X' := himη ▸ ⟨u, hu, rfl⟩
        obtain ⟨cS, hpcS⟩ := exists_surfChart (hS.2.2 (a u))
        obtain ⟨W_S, hWSo, hpWS, -, hWS⟩ := w1_eq_chartSign_sub AS cS hpcS
        obtain ⟨NS, hNS, hcocS⟩ := isCoc_w1 hS AS
        obtain ⟨S1, hS1, S2, hS2, hS12⟩ := mem_nhds_prod_iff.mp (hNS (a u))
        let W₀ : Set S := W_S ∩ cutNbhd ψ V_X V_X' ∩ (interior S1 ∩ interior S2)
        have hW₀o : IsOpen W₀ := (hWSo.inter hUo).inter (isOpen_interior.inter isOpen_interior)
        have hpW₀ : a u ∈ W₀ := ⟨⟨hpWS, hFsub hp⟩, mem_interior_iff_mem_nhds.mpr hS1, mem_interior_iff_mem_nhds.mpr hS2⟩
        obtain ⟨A1, hA1, B1, hB1, hAB1⟩ := mem_nhds_prod_iff.mp (hN_Y' (ξ u))
        obtain ⟨A2, hA2, B2, hB2, hAB2⟩ := mem_nhds_prod_iff.mp (hN_Y' (η u))
        let O₁ : Set Y := V_X ∩ ψ ⁻¹' W₀ ∩ interior B1
        let O₂ : Set Y := V_X' ∩ ψ ⁻¹' W₀ ∩ interior B2
        have hO₁o : IsOpen O₁ := (hVX.inter (hW₀o.preimage hψ.1)).inter isOpen_interior
        have hO₂o : IsOpen O₂ := (hVX'.inter (hW₀o.preimage hψ.1)).inter isOpen_interior
        have hξO₁ : ξ u ∈ O₁ := ⟨⟨hXV hξX, by show ψ (ξ u) ∈ W₀; rw [L.hξ u hu]; exact hpW₀⟩, mem_interior_iff_mem_nhds.mpr hB1⟩
        have hηO₂ : η u ∈ O₂ := ⟨⟨hX'V' hηX', by show ψ (η u) ∈ W₀; rw [L.hη u hu]; exact hpW₀⟩, mem_interior_iff_mem_nhds.mpr hB2⟩
        have hcl : IsClosedMap ψ := hψ.1.isClosedMap
        let W : Set S := W₀ ∩ (ψ '' (O₁ ∪ O₂)ᶜ)ᶜ
        have hWo : IsOpen W := hW₀o.inter (hcl _ (hO₁o.union hO₂o).isClosed_compl).isOpen_compl
        have hpW : a u ∈ W := ⟨hpW₀, by
          rintro ⟨y, hyc, hyeq⟩
          have hy_cases : y = ξ u ∨ y = η u := by
            by_cases h1 : y = ξ u
            · exact .inl h1
            · obtain ⟨v, hv, hpair⟩ := L.fib y (ξ u) (hyeq.trans (L.hξ u hu).symm) h1
              rcases hpair with ⟨rfl, hξeq⟩ | ⟨-, rfl⟩
              · exact absurd hξeq (fun h => Set.disjoint_left.mp hdisj (hXV hξX) (hX'V' (himη ▸ ⟨v, hv, h.symm⟩)))
              · have hηv : η v ∈ X' := himη ▸ ⟨v, hv, rfl⟩
                have hψeq : ψ (η v) = ψ (η u) := hyeq.trans (L.hη u hu).symm
                exact .inr (hbijX'.injOn hηv hηX' hψeq)
          exact hyc (hy_cases.elim (fun h => .inl (h ▸ hξO₁)) (fun h => .inr (h ▸ hηO₂)))⟩
        refine ⟨W, hWo, hpW, fun x₁ hx₁ x₂ hx₂ => ?_⟩
        have hval : ∀ z ∈ W, g_S z - c₀ * cutSide ψ V_X X z - w1 AS (a u) z = g_S (a u) := by
          intro z hz
          obtain ⟨w, rfl⟩ := hψ.2.1 z
          have hwO : w ∈ O₁ ∪ O₂ := by_contra fun hc => hz.2 ⟨w, hc, rfl⟩
          rcases hwO with hw1 | hw2
          · have hpair : (ξ u, w) ∈ N_Y ∩ N_cut := hAB1 ⟨mem_of_mem_nhds hA1, interior_subset hw1.2⟩
            have e1 := hgY (ξ u) w hpair
            rw [L.hξ u hu] at e1
            have hside : cutSide ψ V_X X (ψ w) = 1 + (if w ∈ X then (1 : ZMod 2) else 0) := by
              by_cases hwX : w ∈ X
              · rw [ite_eq_left hwX, cutSide_of_mem_F hun (hdisj.mono_right hX'V') (mem_F_of_left hun hwX)]; rfl
              · rw [ite_eq_right hwX, cutSide_of_mem_VX ⟨hw1.1.1, hwX⟩, add_zero]
            have egw := hgS w
            have egξ := hgS (ξ u)
            rw [L.hξ u hu, ite_eq_left hξX, mul_one] at egξ
            rw [egw, egξ, e1, hside]
            simp only [mul_add, mul_one, zmod2_sub_eq_add]
            ring_nf
            simp [zmod2_two]
          · have hpair : (η u, w) ∈ N_Y ∩ N_cut := hAB2 ⟨mem_of_mem_nhds hA2, interior_subset hw2.2⟩
            have e1 := hgY (η u) w hpair
            rw [L.hη u hu] at e1
            have hwX : w ∉ X := fun h => Set.disjoint_left.mp hdisj (hXV h) hw2.1.1
            have hηX : η u ∉ X := fun h => Set.disjoint_left.mp hdisj (hXV h) (hX'V' hηX')
            have hside : cutSide ψ V_X X (ψ w) = 0 := cutSide_of_mem_VX' hψ hun hdisj hX'V' hw2.1.1
            have egw := hgS w
            have egη := hgS (η u)
            rw [L.hη u hu, ite_eq_right hηX, mul_zero, add_zero] at egη
            rw [ite_eq_right hwX, mul_zero, add_zero] at egw
            rw [egw, egη, e1, hside]
            simp only [mul_zero, sub_zero, zmod2_sub_eq_add]
            ring_nf
            simp [zmod2_two]
        have h12 : w1 AS x₁ x₂ = w1 AS (a u) x₂ - w1 AS (a u) x₁ := by
          have ha1 : (a u, x₁) ∈ NS := hS12 ⟨interior_subset hpW₀.2.1, interior_subset hx₁.1.2.2⟩
          have ha2 : (x₁, x₂) ∈ NS := hS12 ⟨interior_subset hx₁.1.2.1, interior_subset hx₂.1.2.2⟩
          have ha3 : (a u, x₂) ∈ NS := hS12 ⟨interior_subset hpW₀.2.1, interior_subset hx₂.1.2.2⟩
          exact eq_sub_of_add_eq' (hcocS (a u) x₁ x₂ ha1 ha2 ha3)
        have hcut12 : cutCocycle ψ V_X V_X' X x₁ x₂ = cutSide ψ V_X X x₂ - cutSide ψ V_X X x₁ := by
          unfold cutCocycle; exact ite_eq_left ⟨hx₁.1.1.2, hx₂.1.1.2⟩
        have e1 := hval x₁ hx₁
        have e2 := hval x₂ hx₂
        have h21 : g_S x₂ - c₀ * cutSide ψ V_X X x₂ - w1 AS (a u) x₂ =
            g_S x₁ - c₀ * cutSide ψ V_X X x₁ - w1 AS (a u) x₁ := e2.trans e1.symm
        rw [h12, hcut12, ← sub_eq_zero]
        have hrew : (w1 AS (a u) x₂ - w1 AS (a u) x₁ - c₀ * (cutSide ψ V_X X x₂ - cutSide ψ V_X X x₁)) -
            (g_S x₂ - g_S x₁) =
            (g_S x₁ - c₀ * cutSide ψ V_X X x₁ - w1 AS (a u) x₁) -
            (g_S x₂ - c₀ * cutSide ψ V_X X x₂ - w1 AS (a u) x₂) := by
          simp only [zmod2_sub_eq_add, mul_add]
          ring_nf
        rw [hrew, h21, sub_self]
      · obtain ⟨W₁, hW₁o, hpW₁, hW₁F, hW₁zero⟩ := hoff p hp
        obtain ⟨y₀, rfl⟩ := hψ.2.1 p
        obtain ⟨A1, hA1, B1, hB1, hAB1⟩ := mem_nhds_prod_iff.mp (hN_Y' y₀)
        let O : Set Y := ψ ⁻¹' W₁ ∩ interior A1 ∩ interior B1
        have hOo : IsOpen O := ((hW₁o.preimage hψ.1).inter isOpen_interior).inter isOpen_interior
        have hy₀O : y₀ ∈ O := ⟨⟨hpW₁, mem_interior_iff_mem_nhds.mpr hA1⟩, mem_interior_iff_mem_nhds.mpr hB1⟩
        have hOsub : O ⊆ (ψ ⁻¹' F)ᶜ := fun y hy => hW₁F hy.1.1
        have hq : IsQuotientMap ψ := hψ.1.isClosedMap.isQuotientMap hψ.1 hψ.2.1
        have hpre : ψ ⁻¹' (ψ '' O) = O := subset_antisymm (fun y ⟨w, hw, hweq⟩ =>
          hψ.2.2.1 (by show ψ y ∉ F; rw [← hweq]; exact hOsub hw) (hOsub hw) hweq.symm ▸ hw)
          (subset_preimage_image ψ O)
        have hψOo : IsOpen (ψ '' O) := by rw [← hq.isOpen_preimage, hpre]; exact hOo
        refine ⟨ψ '' O, hψOo, ⟨y₀, hy₀O, rfl⟩, ?_⟩
        rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
        rw [hW₁zero (ψ y₁) hy₁.1.1 (ψ y₂) hy₂.1.1, mul_zero, sub_zero]
        have hpair : (y₁, y₂) ∈ N_Y ∩ N_cut := hAB1 ⟨interior_subset hy₁.1.2, interior_subset hy₂.2⟩
        have hy₁X : y₁ ∉ X := fun h => hOsub hy₁ (mem_F_of_left hun h)
        have hy₂X : y₂ ∉ X := fun h => hOsub hy₂ (mem_F_of_left hun h)
        have e1 := hgS y₁; have e2 := hgS y₂
        rw [ite_eq_right hy₁X, mul_zero, add_zero] at e1
        rw [ite_eq_right hy₂X, mul_zero, add_zero] at e2
        rw [e1, e2]
        exact hgY y₁ y₂ hpair
    choose W hWo hpW hW using hloc
    refine ⟨⋃ p : S, W p ×ˢ W p, fun p =>
      Filter.mem_of_superset ((hWo p).prod (hWo p) |>.mem_nhds ⟨hpW p, hpW p⟩)
        (subset_iUnion (fun q => W q ×ˢ W q) p), fun x₁ x₂ hpair => ?_⟩
    obtain ⟨p, h1, h2⟩ := mem_iUnion.mp hpair
    exact hW p x₁ h1 x₂ h2
  rcases zmod2_eq_zero_or_one (g_Y (η 0) - g_Y (ξ 0)) with hc0 | hc1
  · left
    let g_S : S → ZMod 2 := fun x => g_Y (surjInv hψ.2.1 x)
    have hgS : ∀ y : Y, g_S (ψ y) = g_Y y := fun y => by
      dsimp only [g_S]
      set y' := surjInv hψ.2.1 (ψ y)
      have hψeq : ψ y' = ψ y := surjInv_eq hψ.2.1 (ψ y)
      by_cases he : y' = y
      · rw [he]
      · obtain ⟨u, hu, hpair⟩ := L.fib y' y hψeq he
        have hΔ : g_Y (η u) - g_Y (ξ u) = 0 := (hΔ_const u hu).trans hc0
        rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact (sub_eq_zero.mp hΔ).symm
        · rw [h1, h2]; exact sub_eq_zero.mp hΔ
    obtain ⟨N, hN, hdiff⟩ := hdesc_eq 0 g_S (fun y => by simp [hgS y])
    exact ⟨g_S, hgS, N, hN, fun x₁ x₂ h => by simpa using hdiff x₁ x₂ h⟩
  · right
    let g_Y' : Y → ZMod 2 := fun y => g_Y y + (if y ∈ X then 1 else 0)
    let g_S : S → ZMod 2 := fun x => g_Y' (surjInv hψ.2.1 x)
    have hgS : ∀ y : Y, g_S (ψ y) = g_Y' y := fun y => by
      dsimp only [g_S]
      set y' := surjInv hψ.2.1 (ψ y)
      have hψeq : ψ y' = ψ y := surjInv_eq hψ.2.1 (ψ y)
      by_cases he : y' = y
      · rw [he]
      · obtain ⟨u, hu, hpair⟩ := L.fib y' y hψeq he
        have hΔ : g_Y (η u) - g_Y (ξ u) = 1 := (hΔ_const u hu).trans hc1
        have hξX : ξ u ∈ X := himξ ▸ ⟨u, hu, rfl⟩
        have hηX : η u ∉ X := fun h => Set.disjoint_left.mp hdisj (hXV h) (hX'V' (himη ▸ ⟨u, hu, rfl⟩))
        have heq_u : g_Y' (ξ u) = g_Y' (η u) := by
          dsimp only [g_Y']
          rw [ite_eq_left hξX, ite_eq_right hηX, add_zero]
          linear_combination -hΔ
        rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact heq_u
        · rw [h1, h2]; exact heq_u.symm
    obtain ⟨N, hN, hdiff⟩ := hdesc_eq 1 g_S (fun y => by simpa [g_Y'] using hgS y)
    exact ⟨g_S, hgS, N, hN, fun x₁ x₂ h => by simpa using hdiff x₁ x₂ h⟩

/-- For a proper `I`-arc `F` in a connected surface `S` with cutting `ψ : Y → S`,
`Y` is orientable (`CohRel (w1 AY) 0`) if and only if either `S` is orientable (`CohRel (w1 AS) 0`)
or `w1 AS` is cohomologous to `arcCocycle F` (`CohRel (w1 AS) (arcCocycle F)`). -/
theorem cut_orientable_iff_cohRel_w1 [ConnectedSpace S] (hS : IsSurface S)
    {F : Set S} {s t : S} (hne : s ≠ t) (hb : F ∩ bd S = {s, t}) (hl : IsLineWithEnds F s t)
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] {ψ : Y → S}
    (hY : IsSurface Y) (hψ : IsCutting ψ F) {X X' : Set Y} (hP : LiftPair ψ F s t X X')
    (AY : SurfAtlas Y) (AS : SurfAtlas S) :
    CohRel (w1 AY) (fun _ _ => 0) ↔
      CohRel (w1 AS) (fun _ _ => 0) ∨ CohRel (w1 AS) (arcCocycle hS hne hb hl) := by
  have : CompactSpace Y := hY.1
  have : T2Space S := hS.2.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, -⟩ := id hP
  obtain ⟨V_X, V_X', hVX, hVX', hXV, hX'V', hcl⟩ :=
    exists_disjoint_closure_nhds l1.isCompact.isClosed l2.isCompact.isClosed hd
  have hrel_arc : CohRel (arcCocycle hS hne hb hl) (cutCocycle ψ V_X V_X' X) :=
    (arcCocycle_bdCohRel_cutCocycle hS hne hb hl hY hψ hP hVX hVX' hXV hX'V' hcl).cohRel
  constructor
  · rintro ⟨h_Y, N_Y, hNY, hhY⟩
    rcases exists_w1_cut_descent hS hY hψ hl.isCompact.isClosed hP hVX hVX' hXV hX'V' hcl AY AS hNY
        (fun y₁ y₂ h => by simpa using hhY y₁ y₂ h) with
      ⟨g_S, -, N, hN, hdiff⟩ | ⟨g_S, -, N, hN, hdiff⟩
    · exact .inl ⟨g_S, N, hN, fun x₁ x₂ h => by simpa using hdiff x₁ x₂ h⟩
    · exact .inr (CohRel.trans ⟨g_S, N, hN, hdiff⟩ hrel_arc.symm)
  · rintro (h0 | hF)
    · exact CohRel.trans (cohRel_w1_cut hY hS hψ hl.isCompact.isClosed AY AS).symm
        (cohRel_pbk_cont hψ.1 h0)
    · have h1 : CohRel (w1 AS) (cutCocycle ψ V_X V_X' X) := CohRel.trans hF hrel_arc
      have h2 : CohRel (pbk ψ (w1 AS)) (pbk ψ (cutCocycle ψ V_X V_X' X)) := cohRel_pbk_cont hψ.1 h1
      have h3 : CohRel (pbk ψ (cutCocycle ψ V_X V_X' X)) (fun _ _ => 0) :=
        cohRel_pbk_cutCocycle_zero hψ hl.isCompact.isClosed l1.isCompact.isClosed l2.isCompact.isClosed
          hun hVX hVX' hXV hX'V' hcl
      exact CohRel.trans (cohRel_w1_cut hY hS hψ hl.isCompact.isClosed AY AS).symm
        (CohRel.trans h2 h3)

end CutTopology

end GraphMinor.GHR18
