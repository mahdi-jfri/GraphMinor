module

public import GraphMinor.GM08.Section7Defs
public import GraphMinor.GM08.Section7Grid
public import GraphMinor.GM07.CylinderGrid
public import GraphMinor.GM07.CylinderPaths
public import GraphMinor.GM07.CylinderTrim

@[expose] public section

/-!
# Graph Minors VIII, Section 8 Helpers: Subdrawing Transport and `ρ(C)` Paths

Infrastructure for Section 8 (and Section 9) of Graph Minors VIII:
1. Walk mapping `GraphWalk.mapLink` and bidirectional transport of subdrawings, paths, circuits,
   forests, centred O-arcs, sleeves, `circuitRho`, `IsBoss`, and `IsCRing` across `SphereDiscChart`.
2. Menger's theorem for `circuitRho` (`exists_disjoint_paths_of_circuitRho`), producing `r`
   pairwise vertex-disjoint path subdrawings between a circuit `C` and `discBd Δ` whenever
   `r ≤ circuitRho C`, together with path trimming onto an enclosing normal O-arc `F`.
-/

namespace GraphMinor
namespace GM08

open Set Topology Function Surface GraphMinor.GM11

universe u

/-!
## 1. Mapping Graph Walks Along Vertex/Edge Maps
-/

section WalkMap

variable {α α' β β' : Type*} {G : Graph α β} {H : Graph α' β'}

/-- Map a `GraphWalk G a b` to `GraphWalk H (fv a) (fv b)` along vertex and edge maps preserving
`V(G)` and `IsLink`. -/
def mapGraphWalk (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ Graph.vertexSet G, fv x ∈ Graph.vertexSet H)
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v)) :
    ∀ {a b : α}, GraphWalk G a b → GraphWalk H (fv a) (fv b)
  | _, _, .nil ha => .nil (hV _ ha)
  | _, _, .cons hl rest => .cons (hL hl) (mapGraphWalk fv fe hV hL rest)

@[simp]
theorem mapGraphWalk_support (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ Graph.vertexSet G, fv x ∈ Graph.vertexSet H)
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v))
    {a b : α} (W : GraphWalk G a b) :
    (mapGraphWalk fv fe hV hL W).support = W.support.map fv := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mapGraphWalk, GraphWalk.support_cons, ih]

@[simp]
theorem mapGraphWalk_edges (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ Graph.vertexSet G, fv x ∈ Graph.vertexSet H)
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v))
    {a b : α} (W : GraphWalk G a b) :
    (mapGraphWalk fv fe hV hL W).edges = W.edges.map fe := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mapGraphWalk, ih]

@[simp]
theorem mapGraphWalk_length (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ Graph.vertexSet G, fv x ∈ Graph.vertexSet H)
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v))
    {a b : α} (W : GraphWalk G a b) :
    (mapGraphWalk fv fe hV hL W).length = W.length := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih => simp [mapGraphWalk, ih]

theorem mapGraphWalk_isSimple (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ Graph.vertexSet G, fv x ∈ Graph.vertexSet H)
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v))
    {a b : α} {W : GraphWalk G a b}
    (hinj : InjOn fv {x | x ∈ W.support}) (hW : W.IsSimple) :
    (mapGraphWalk fv fe hV hL W).IsSimple := by
  unfold GraphWalk.IsSimple at *
  rw [mapGraphWalk_support]
  exact List.Nodup.map_on (fun x hx y hy h => hinj hx hy h) hW

theorem mapGraphWalk_isSimpleClosed (fv : α → α') (fe : β → β')
    (hV : ∀ x ∈ Graph.vertexSet G, fv x ∈ Graph.vertexSet H)
    (hL : ∀ {e : β} {u v : α}, G.IsLink e u v → H.IsLink (fe e) (fv u) (fv v))
    {u : α} {W : GraphWalk G u u}
    (hinjV : InjOn fv {x | x ∈ W.support}) (hinjE : InjOn fe {e | e ∈ W.edges})
    (hW : W.IsSimpleClosed) :
    (mapGraphWalk fv fe hV hL W).IsSimpleClosed := by
  obtain ⟨hsup, hedg⟩ := hW
  refine ⟨?_, ?_⟩
  · rw [mapGraphWalk_support, ← List.map_tail]
    exact List.Nodup.map_on
      (fun x hx y hy h => hinjV (List.mem_of_mem_tail hx) (List.mem_of_mem_tail hy) h) hsup
  · rw [mapGraphWalk_edges]
    exact List.Nodup.map_on (fun e₁ h₁ e₂ h₂ h => hinjE h₁ h₂ h) hedg

end WalkMap

/-!
## 2. Subdrawing and Structure Transport Across `SphereDiscChart`
-/

namespace SphereDiscChart

variable {S : Type u} [TopologicalSpace S]
variable {Δ : Set S} {f : S → OnePoint EuclideanPlane} {f' : OnePoint EuclideanPlane → S}

private theorem arcComponentsIn_image_local {S₁ S₂ : Type*}
    [TopologicalSpace S₁] [TopologicalSpace S₂] {F : Set S₁} {φ : S₁ → S₂} {ψ : S₂ → S₁}
    (hφ : ContinuousOn φ F) (hψ : ContinuousOn ψ (φ '' F)) (hψφ : ∀ x ∈ F, ψ (φ x) = x) :
    arcComponentsIn (φ '' F) = image φ '' arcComponentsIn F := by
  have hφψ : ∀ y ∈ φ '' F, φ (ψ y) = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hψφ x hx]
  have hconn : ∀ {A : Set S₁}, A ⊆ F → IsPathConnected A → IsPathConnected (φ '' A) :=
    fun hA h => h.image' (hφ.mono hA)
  have hconn' : ∀ {B : Set S₂}, B ⊆ φ '' F → IsPathConnected B → IsPathConnected (ψ '' B) :=
    fun hB h => h.image' (hψ.mono hB)
  have hψsub : ∀ {B : Set S₂}, B ⊆ φ '' F → ψ '' B ⊆ F := by
    rintro B hB _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hB hy
    rwa [hψφ x hx]
  have hφψim : ∀ {B : Set S₂}, B ⊆ φ '' F → φ '' (ψ '' B) = B := fun {B} hB => by
    rw [image_image]
    exact (image_congr fun y hy => hφψ y (hB hy)).trans (image_id' B)
  have hψφim : ∀ {A : Set S₁}, A ⊆ F → ψ '' (φ '' A) = A := fun {A} hA => by
    rw [image_image]
    exact (image_congr fun x hx => hψφ x (hA hx)).trans (image_id' A)
  ext C'
  constructor
  · rintro ⟨hne, hsub, hpc, hmax⟩
    refine ⟨ψ '' C', ⟨hne.image ψ, hψsub hsub, hconn' hsub hpc, ?_⟩, hφψim hsub⟩
    intro A hA hAc hCA
    have h₁ : C' ⊆ φ '' A := by
      have := image_mono (f := φ) hCA
      rwa [hφψim hsub] at this
    have h₂ := hmax _ (image_mono hA) (hconn hA hAc) h₁
    rw [← h₂, hψφim hA]
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨hne.image φ, image_mono hsub, hconn hsub hpc, ?_⟩
    intro B hB hBc hCB
    have h₁ : C ⊆ ψ '' B := by
      have := image_mono (f := ψ) hCB
      rwa [hψφim hsub] at this
    have h₂ := hmax _ (hψsub hB) (hconn' hB hBc) h₁
    rw [← h₂, hφψim hB]

/-- For `B ⊆ f '' Δ`, `f' '' (X \ Y) = f' '' X \ f' '' Y`. -/
theorem f'_sdiff (sc : SphereDiscChart Δ f f') {X Y : Set (OnePoint EuclideanPlane)}
    (hX : X ⊆ f '' Δ) (hY : Y ⊆ f '' Δ) :
    f' '' (X \ Y) = f' '' X \ f' '' Y := by
  ext x
  constructor
  · rintro ⟨p, ⟨hpX, hpY⟩, rfl⟩
    refine ⟨⟨p, hpX, rfl⟩, ?_⟩
    rintro ⟨q, hqY, heq⟩
    obtain rfl := sc.injOn_f' (hY hqY) (hX hpX) heq
    exact hpY hqY
  · rintro ⟨⟨p, hpX, rfl⟩, hn⟩
    exact ⟨p, ⟨hpX, fun hpY => hn ⟨p, hpY, rfl⟩⟩, rfl⟩

/-- Pull back a closed subset `Z ⊆ f '' D.U` to a closed subset `f' '' Z` of `S` (using only
`D.isClosed_U : IsClosed D.U`, without assuming `T2Space S`). -/
theorem isClosed_f'_of_subset_U (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ) {Z : Set (OnePoint EuclideanPlane)}
    (hZU : Z ⊆ f '' D.U) (hZcl : IsClosed Z) :
    IsClosed (f' '' Z) := by
  have hsub_K : f' '' Z ⊆ D.U := by
    have := image_mono (f := f') hZU
    rwa [sc.f'_f hDU] at this
  let g : ↥D.U → OnePoint EuclideanPlane := fun x => f x.1
  have hgc : Continuous g := (sc.fc.mono hDU).comp_continuous continuous_subtype_val fun x => x.2
  have hcl_sub : IsClosed (g ⁻¹' Z) := hZcl.preimage hgc
  rw [isClosed_induced_iff] at hcl_sub
  obtain ⟨W, hWcl, hWeq⟩ := hcl_sub
  have heq : f' '' Z = D.U ∩ W := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ D.U := hsub_K hx
      obtain ⟨p, hpZ, rfl⟩ := hx
      have hpΔ : p ∈ f '' Δ := hZU hpZ |>.elim fun y ⟨hyU, hy⟩ => hy ▸ mem_image_of_mem f (hDU hyU)
      have hfp : g ⟨f' p, hxU⟩ ∈ Z := by
        change f (f' p) ∈ Z
        rwa [sc.ff' hpΔ]
      have hxW : (⟨f' p, hxU⟩ : ↥D.U) ∈ Subtype.val ⁻¹' W := hWeq ▸ hfp
      exact ⟨hxU, hxW⟩
    · rintro ⟨hxU, hxW⟩
      have hfx : f x ∈ Z := by
        have : (⟨x, hxU⟩ : ↥D.U) ∈ g ⁻¹' Z := hWeq.symm ▸ hxW
        exact this
      have := mem_image_of_mem f' hfx
      rwa [sc.f'f (hDU hxU)] at this
  rw [heq]
  exact D.isClosed_U.inter hWcl

/-- For `A ⊆ Z` where `Z ⊆ f '' D.U` is closed and `D.U ⊆ Δ`, `closure (f' '' A) = f' '' closure A`. -/
theorem closure_f'_eq_of_subset_U (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ) {Z A : Set (OnePoint EuclideanPlane)}
    (hZU : Z ⊆ f '' D.U) (hZcl : IsClosed Z) (hAZ : A ⊆ Z) :
    closure (f' '' A) = f' '' closure A := by
  have hcl_Z : closure A ⊆ Z := closure_minimal hAZ hZcl
  have hcl_im : IsClosed (f' '' closure A) :=
    sc.isClosed_f'_of_subset_U hDU (hcl_Z.trans hZU) isClosed_closure
  apply Subset.antisymm
  · exact closure_minimal (image_mono subset_closure) hcl_im
  · rintro _ ⟨p, hpcl, rfl⟩
    have hpΔ : p ∈ f '' Δ := image_mono hDU (hZU (hcl_Z hpcl))
    rw [mem_closure_iff]
    intro W hWopen hfpW
    have hcont : ContinuousOn f' (f '' Δ) := sc.f'c
    rw [continuousOn_iff] at hcont
    obtain ⟨V, hVopen, hpV, hVsub⟩ := hcont p hpΔ W hWopen hfpW
    obtain ⟨q, hqV, hqA⟩ := mem_closure_iff.mp hpcl V hVopen hpV
    have hqΔ : q ∈ f '' Δ := image_mono hDU (hZU (hAZ hqA))
    exact ⟨f' q, hVsub ⟨hqV, hqΔ⟩, mem_image_of_mem f' hqA⟩

/-- Pull back a subdrawing `H'` of `D'` (where `D'` is the transported drawing of `D` in `f '' Δ`)
to a subdrawing `H` of `D` in `S`. -/
theorem exists_pullback_subdrawing (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ)
    {D' H' : Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V) (hD'E : D'.E = image f '' D.E)
    (hsub' : H'.IsSubdrawing D') :
    ∃ H : Drawing S,
      H.IsSubdrawing D ∧
      H.U = f' '' H'.U ∧ H.V = f' '' H'.V ∧ H.E = image f' '' H'.E ∧
      (∀ e' ∈ H'.E, closure (f' '' e') = f' '' closure e') ∧
      (∀ {e' : Set (OnePoint EuclideanPlane)} {u' v' : OnePoint EuclideanPlane},
        H'.toGraph.IsLink e' u' v' → H.toGraph.IsLink (f' '' e') (f' u') (f' v')) ∧
      (∀ {e : Set S} {u v : S},
        H.toGraph.IsLink e u v → H'.toGraph.IsLink (f '' e) (f u) (f v)) := by
  have hH'U_sub : H'.U ⊆ f '' D.U := hD'U ▸ hsub'.U_subset
  have hH'U_Δ : H'.U ⊆ f '' Δ := hH'U_sub.trans (image_mono hDU)
  have hH'V_Δ : H'.V ⊆ f '' Δ := H'.V_subset_U.trans hH'U_Δ
  have hdiff_Δ : H'.U \ H'.V ⊆ f '' Δ := sdiff_subset.trans hH'U_Δ
  have hclU : IsClosed (f' '' H'.U) :=
    sc.isClosed_f'_of_subset_U hDU hH'U_sub H'.isClosed_U
  have hdiff : f' '' H'.U \ f' '' H'.V = f' '' (H'.U \ H'.V) :=
    (sc.f'_sdiff hH'U_Δ hH'V_Δ).symm
  have harc : arcComponentsIn (f' '' (H'.U \ H'.V)) = image f' '' arcComponentsIn (H'.U \ H'.V) :=
    arcComponentsIn_image_local (sc.f'c.mono hdiff_Δ)
      (sc.fc.mono (sc.f'_subset hdiff_Δ)) (fun p hp => sc.ff' (hdiff_Δ hp))
  have hcl_edge : ∀ e' ∈ H'.E, closure (f' '' e') = f' '' closure e' := fun e' he' =>
    sc.closure_f'_eq_of_subset_U hDU hH'U_sub H'.isClosed_U (fun p hp => (he'.2.1 hp).1)
  have hcap : ∀ e' ∈ H'.E, closure (f' '' e') ∩ f' '' H'.V = f' '' (closure e' ∩ H'.V) := by
    intro e' he'
    rw [hcl_edge e' he']
    have hcle' : closure e' ⊆ f '' Δ :=
      (closure_minimal (fun p hp => (he'.2.1 hp).1) H'.isClosed_U).trans hH'U_Δ
    exact (InjOn.image_inter sc.injOn_f' hcle' hH'V_Δ).symm
  let H : Drawing S :=
    { U := f' '' H'.U
      V := f' '' H'.V
      V_subset_U := image_mono H'.V_subset_U
      isClosed_U := hclU
      finite_V := H'.finite_V.image f'
      finite_edges := by
        rw [hdiff, harc]
        exact H'.finite_edges.image _
      edge_cond := by
        rw [hdiff, harc]
        rintro _ ⟨e', he', rfl⟩
        have hcle' : closure e' ⊆ f '' Δ :=
          (closure_minimal (fun p hp => (he'.2.1 hp).1) H'.isClosed_U).trans hH'U_Δ
        have hinje' : InjOn f' (closure e') := sc.injOn_f'.mono hcle'
        rw [hcap e' he']
        rcases H'.edge_cond e' he' with ⟨u', v', huv', hc', hL'⟩ | ⟨u', hc', hF'⟩
        · left
          have hu' : u' ∈ closure e' := (hc' ▸ (by simp : u' ∈ ({u', v'} : Set _))).1
          have hv' : v' ∈ closure e' := (hc' ▸ (by simp : v' ∈ ({u', v'} : Set _))).1
          refine ⟨f' u', f' v', fun h => huv' (hinje' hu' hv' h), by rw [hc', image_pair], ?_⟩
          obtain ⟨φ₁, h0, h1⟩ := hL'
          have him_cl : f '' closure (f' '' e') ⊆ closure e' := by
            rw [hcl_edge e' he']
            rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
            rwa [sc.ff' (hcle' hp)]
          let hclHomeo : closure e' ≃ₜ closure (f' '' e') :=
            { toFun := fun p => ⟨f' p.1, hcl_edge e' he' ▸ mem_image_of_mem f' p.2⟩
              invFun := fun q => ⟨f q.1, him_cl (mem_image_of_mem f q.2)⟩
              left_inv := fun p => Subtype.ext (sc.ff' (hcle' p.2))
              right_inv := fun q => Subtype.ext (sc.f'f (by
                let qx : S := q.1
                have hqmem : qx ∈ closure (f' '' e') := q.2
                rw [hcl_edge e' he'] at hqmem
                obtain ⟨p, hp, hpeq⟩ := hqmem
                change qx ∈ Δ
                rw [← hpeq]
                exact sc.f'_subset hcle' (mem_image_of_mem f' hp)))
              continuous_toFun :=
                ((sc.f'c.mono hcle').comp_continuous continuous_subtype_val fun p => p.2).subtype_mk _
              continuous_invFun :=
                ((sc.fc.mono (by
                  rw [hcl_edge e' he']
                  exact sc.f'_subset hcle')).comp_continuous continuous_subtype_val fun q => q.2).subtype_mk _ }
          let ψ := φ₁.trans hclHomeo
          exact ⟨ψ, by change f' (φ₁ 0).1 = f' u'; rw [h0], by change f' (φ₁ 1).1 = f' v'; rw [h1]⟩
        · right
          refine ⟨f' u', by rw [hc', image_singleton], ?_⟩
          exact hcl_edge e' he' ▸ sc.oArc_f' hcle' hF' }
  have hHE : H.E = image f' '' H'.E := by
    change arcComponentsIn (f' '' H'.U \ f' '' H'.V) = image f' '' H'.E
    rw [hdiff, harc]
    rfl
  have hsub : H.IsSubdrawing D := by
    refine ⟨?_, ?_⟩
    · have : f' '' H'.V ⊆ f' '' (f '' D.V) := image_mono (hD'V ▸ hsub'.1)
      rwa [sc.f'_f (D.V_subset_U.trans hDU)] at this
    · rw [hHE]
      rintro _ ⟨e', he', rfl⟩
      obtain ⟨e, heD, rfl⟩ := hD'E ▸ hsub'.2 he'
      have heΔ : e ⊆ Δ := fun x hx => hDU (heD.2.1 hx).1
      rwa [sc.f'_f heΔ]
  refine ⟨H, hsub, rfl, rfl, hHE, hcl_edge, ?_, ?_⟩
  · intro e' u' v' ⟨he', hu', hv', hcl'⟩
    refine ⟨hHE ▸ mem_image_of_mem _ he', mem_image_of_mem f' hu', mem_image_of_mem f' hv', ?_⟩
    change closure (f' '' e') ∩ f' '' H'.V = {f' u', f' v'}
    rw [hcap e' he', hcl', image_pair]
  · intro e u v ⟨he, hu, hv, hcl⟩
    obtain ⟨e', he', rfl⟩ := hHE ▸ he
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    have he'Δ : e' ⊆ f '' Δ := fun p hp => hH'U_Δ (he'.2.1 hp).1
    rw [sc.f_f' he'Δ, sc.ff' (hH'V_Δ hu'), sc.ff' (hH'V_Δ hv')]
    refine ⟨he', hu', hv', ?_⟩
    change closure (f' '' e') ∩ f' '' H'.V = {f' u', f' v'} at hcl
    rw [hcap e' he', ← image_pair] at hcl
    have h₁ : closure e' ∩ H'.V ⊆ f '' Δ := inter_subset_right.trans hH'V_Δ
    have h₂ : ({u', v'} : Set _) ⊆ f '' Δ := by
      rintro z (rfl | rfl) <;> [exact hH'V_Δ hu'; exact hH'V_Δ hv']
    rw [← sc.f_f' h₁, ← sc.f_f' h₂, hcl]

/-- Push a subdrawing `H` of `D` forward to a subdrawing `H'` of `D'` in `f '' Δ`. -/
theorem exists_push_subdrawing (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D H : Drawing S} (hDU : D.U ⊆ Δ)
    {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'V : D'.V = f '' D.V) (hD'E : D'.E = image f '' D.E)
    (hsub : H.IsSubdrawing D) :
    ∃ H' : Drawing (OnePoint EuclideanPlane),
      H'.IsSubdrawing D' ∧
      H'.U = f '' H.U ∧ H'.V = f '' H.V ∧ H'.E = image f '' H.E ∧
      (∀ e ∈ H.E, closure (f '' e) = f '' closure e) ∧
      (∀ {e : Set S} {u v : S},
        H.toGraph.IsLink e u v → H'.toGraph.IsLink (f '' e) (f u) (f v)) ∧
      (∀ {e' : Set (OnePoint EuclideanPlane)} {u' v' : OnePoint EuclideanPlane},
        H'.toGraph.IsLink e' u' v' → H.toGraph.IsLink (f' '' e') (f' u') (f' v')) := by
  have hHU : H.U ⊆ Δ := hsub.U_subset.trans hDU
  obtain ⟨H', iso, hH'U, hH'V, hH'E, hcl_e, hv_iso, he_iso⟩ :=
    sc.exists_transport_drawing hΔ H hHU
  have hsub' : H'.IsSubdrawing D' := by
    refine ⟨?_, ?_⟩
    · rw [hH'V, hD'V]
      exact image_mono hsub.1
    · rw [hH'E, hD'E]
      exact image_mono hsub.2
  refine ⟨H', hsub', hH'U, hH'V, hH'E, hcl_e, ?_, ?_⟩
  · intro e u v hl
    have hl' := (iso.isLink_iff ⟨e, hl.1⟩ ⟨u, hl.2.1⟩ ⟨v, hl.2.2.1⟩).mp hl
    simpa [hv_iso, he_iso] using hl'
  · intro e' u' v' hl'
    obtain ⟨e, heH, rfl⟩ := hH'E ▸ hl'.1
    obtain ⟨u, huH, rfl⟩ := hH'V ▸ hl'.2.1
    obtain ⟨v, hvH, rfl⟩ := hH'V ▸ hl'.2.2.1
    have heΔ : e ⊆ Δ := fun x hx => hHU (heH.2.1 hx).1
    rw [sc.f'_f heΔ, sc.f'f (hHU (H.V_subset_U huH)), sc.f'f (hHU (H.V_subset_U hvH))]
    have hl'' : H'.toGraph.IsLink (iso.edgeEquiv ⟨e, heH⟩).1
        (iso.vertexEquiv ⟨u, huH⟩).1 (iso.vertexEquiv ⟨v, hvH⟩).1 := by
      simpa [hv_iso, he_iso] using hl'
    exact (iso.isLink_iff ⟨e, heH⟩ ⟨u, huH⟩ ⟨v, hvH⟩).mpr hl''

/-- Transport `IsPathBetween` from `H'` to `H` under pullback. -/
theorem isPathBetween_of_pullback (sc : SphereDiscChart Δ f f')
    {H : Drawing S} {H' : Drawing (OnePoint EuclideanPlane)}
    (hH'U : H'.U ⊆ f '' Δ)
    (hHV : H.V = f' '' H'.V) (hHE : H.E = image f' '' H'.E)
    (hL : ∀ {e' u' v'}, H'.toGraph.IsLink e' u' v' → H.toGraph.IsLink (f' '' e') (f' u') (f' v'))
    {a' b' : OnePoint EuclideanPlane} (hp : H'.IsPathBetween a' b') :
    H.IsPathBetween (f' a') (f' b') := by
  obtain ⟨W', hW', hV', hE'⟩ := hp
  have hV_map : ∀ x ∈ Graph.vertexSet H'.toGraph, f' x ∈ Graph.vertexSet H.toGraph := by
    intro x hx
    change f' x ∈ H.V
    rw [hHV]
    exact mem_image_of_mem f' hx
  let W := mapGraphWalk f' (image f') hV_map hL W'
  have hinj : InjOn f' {x | x ∈ W'.support} :=
    sc.injOn_f'.mono fun x hx => hH'U (H'.V_subset_U (hV' ▸ hx))
  refine ⟨W, mapGraphWalk_isSimple f' (image f') hV_map hL hinj hW', ?_, ?_⟩
  · rw [hHV, hV', mapGraphWalk_support]
    ext x
    simp [Set.mem_image]
  · rw [hHE, hE', mapGraphWalk_edges]
    ext e
    simp [Set.mem_image]

/-- Transport `IsPathBetween` forward from `H` to `H'`. -/
theorem isPathBetween_of_push (sc : SphereDiscChart Δ f f')
    {H : Drawing S} {H' : Drawing (OnePoint EuclideanPlane)}
    (hHU : H.U ⊆ Δ)
    (hH'V : H'.V = f '' H.V) (hH'E : H'.E = image f '' H.E)
    (hL : ∀ {e u v}, H.toGraph.IsLink e u v → H'.toGraph.IsLink (f '' e) (f u) (f v))
    {a b : S} (hp : H.IsPathBetween a b) :
    H'.IsPathBetween (f a) (f b) := by
  obtain ⟨W, hW, hV, hE⟩ := hp
  have hV_map : ∀ x ∈ Graph.vertexSet H.toGraph, f x ∈ Graph.vertexSet H'.toGraph := by
    intro x hx
    change f x ∈ H'.V
    rw [hH'V]
    exact mem_image_of_mem f hx
  let W' := mapGraphWalk f (image f) hV_map hL W
  have hinj : InjOn f {x | x ∈ W.support} :=
    sc.injOn_f.mono fun x hx => hHU (H.V_subset_U (hV ▸ hx))
  refine ⟨W', mapGraphWalk_isSimple f (image f) hV_map hL hinj hW, ?_, ?_⟩
  · rw [hH'V, hV, mapGraphWalk_support]
    ext x
    simp [Set.mem_image]
  · rw [hH'E, hE, mapGraphWalk_edges]
    ext e
    simp [Set.mem_image]

/-- Transport `IsCircuit` from `H'` to `H` under pullback. -/
theorem isCircuit_of_pullback (sc : SphereDiscChart Δ f f')
    {H : Drawing S} {H' : Drawing (OnePoint EuclideanPlane)}
    (hH'U : H'.U ⊆ f '' Δ)
    (hHV : H.V = f' '' H'.V) (hHE : H.E = image f' '' H'.E)
    (hL : ∀ {e' u' v'}, H'.toGraph.IsLink e' u' v' → H.toGraph.IsLink (f' '' e') (f' u') (f' v'))
    (hc : H'.IsCircuit) :
    H.IsCircuit := by
  obtain ⟨u', W', hW', hlen', hV', hE'⟩ := hc
  have hV_map : ∀ x ∈ Graph.vertexSet H'.toGraph, f' x ∈ Graph.vertexSet H.toGraph := by
    intro x hx
    change f' x ∈ H.V
    rw [hHV]
    exact mem_image_of_mem f' hx
  let W := mapGraphWalk f' (image f') hV_map hL W'
  have hinjV : InjOn f' {x | x ∈ W'.support} :=
    sc.injOn_f'.mono fun x hx => hH'U (H'.V_subset_U (hV' ▸ hx))
  have hinjE : InjOn (image f') {e' | e' ∈ W'.edges} := by
    intro e₁ he₁ e₂ he₂ heq
    have h₁ : e₁ ⊆ f '' Δ := fun p hp => hH'U (((hE' ▸ he₁ : e₁ ∈ H'.E).2.1 hp).1)
    have h₂ : e₂ ⊆ f '' Δ := fun p hp => hH'U (((hE' ▸ he₂ : e₂ ∈ H'.E).2.1 hp).1)
    rw [← sc.f_f' h₁, ← sc.f_f' h₂, heq]
  refine ⟨f' u', W, mapGraphWalk_isSimpleClosed f' (image f') hV_map hL hinjV hinjE hW', ?_, ?_, ?_⟩
  · rwa [mapGraphWalk_length]
  · rw [hHV, hV', mapGraphWalk_support]
    ext x
    simp [Set.mem_image]
  · rw [hHE, hE', mapGraphWalk_edges]
    ext e
    simp [Set.mem_image]

/-- Transport `IsInsideDisc` forward across `SphereDiscChart`. -/
theorem isInsideDisc_f (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {F D_F : Set S} (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hD_F : IsInsideDisc Δ F D_F) :
    IsInsideDisc (f '' Δ) (f '' F) (f '' D_F) := by
  have hΔ' : IsClosedDisc (f '' Δ) := (sc.disc_f Subset.rfl hΔ).1
  obtain ⟨E', hE', hE'_uniq⟩ := disc_oArc (f '' Δ) (f '' F) hΔ' (image_mono hFΔ) (sc.oArc_f hFΔ hFo)
  have heq : f '' D_F = E' := hE'_uniq (f '' D_F) (image_mono hD_F.1)
    (sc.disc_f hD_F.1 hD_F.2.1).1 (by rw [(sc.disc_f hD_F.1 hD_F.2.1).2, hD_F.2.2.1])
  exact heq ▸ hE'

/-- Transport `InsideOArc` forward and backward across `SphereDiscChart`. -/
theorem insideOArc_f_iff (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {F : Set S} (hFΔ : F ⊆ Δ) (hFo : IsOArc F) {x : S} (hxΔ : x ∈ Δ) :
    InsideOArc (f '' Δ) (f '' F) (f x) ↔ InsideOArc Δ F x := by
  obtain ⟨D_F, hD_F, _⟩ := disc_oArc Δ F hΔ hFΔ hFo
  have hΔ' : IsClosedDisc (f '' Δ) := (sc.disc_f Subset.rfl hΔ).1
  have hD_F' : IsInsideDisc (f '' Δ) (f '' F) (f '' D_F) := sc.isInsideDisc_f hΔ hFΔ hFo hD_F
  rw [insideOArc_iff_mem_discInt hΔ' hD_F', insideOArc_iff_mem_discInt hΔ hD_F,
    sc.discInt_f hD_F.1 hD_F.2.1]
  constructor
  · rintro ⟨y, hy, heq⟩
    obtain rfl := sc.injOn_f (hD_F.1 hy.1) hxΔ heq
    exact hy
  · intro hx
    exact mem_image_of_mem f hx

/-- Transport `SetInsideOArc` across `SphereDiscChart`. -/
theorem setInsideOArc_f_iff (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {F X : Set S} (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hXΔ : X ⊆ Δ) :
    SetInsideOArc (f '' Δ) (f '' F) (f '' X) ↔ SetInsideOArc Δ F X := by
  constructor
  · intro h x hx
    exact (sc.insideOArc_f_iff hΔ hFΔ hFo (hXΔ hx)).mp (h (f x) (mem_image_of_mem f hx))
  · rintro h _ ⟨x, hx, rfl⟩
    exact (sc.insideOArc_f_iff hΔ hFΔ hFo (hXΔ hx)).mpr (h x hx)

/-- Transport `OArcEncloses` across `SphereDiscChart`. -/
theorem oArcEncloses_f_iff (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {F X : Set S} (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hXΔ : X ⊆ Δ) :
    OArcEncloses (f '' Δ) (f '' F) (f '' X) ↔ OArcEncloses Δ F X := by
  rw [OArcEncloses, OArcEncloses, ← sc.f_sdiff hXΔ hFΔ]
  exact sc.setInsideOArc_f_iff hΔ hFΔ hFo (sdiff_subset.trans hXΔ)

/-- Transport `D.IsNormal F` across `SphereDiscChart`. -/
theorem isNormal_f_iff (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ) {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V)
    {F : Set S} (hFΔ : F ⊆ Δ) :
    D'.IsNormal (f '' F) ↔ D.IsNormal F := by
  unfold Drawing.IsNormal
  rw [hD'U, hD'V, ← InjOn.image_inter sc.injOn_f hFΔ hDU]
  constructor
  · intro h x hx
    obtain ⟨y, hyV, heq⟩ := h (mem_image_of_mem f hx)
    obtain rfl := sc.injOn_f (hDU (D.V_subset_U hyV)) (hFΔ hx.1) heq
    exact hyV
  · intro h
    exact image_mono h

/-- Cardinality `(D'.V ∩ f '' F).ncard = (D.V ∩ F).ncard` across `SphereDiscChart`. -/
theorem ncard_V_inter_f (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ) {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'V : D'.V = f '' D.V) {F : Set S} (hFΔ : F ⊆ Δ) :
    (D'.V ∩ f '' F).ncard = (D.V ∩ F).ncard := by
  rw [hD'V, ← InjOn.image_inter sc.injOn_f (D.V_subset_U.trans hDU) hFΔ]
  exact (sc.injOn_f.mono (inter_subset_left.trans (D.V_subset_U.trans hDU))).ncard_image

/-- Push a `DiscCircuit D Δ` forward to `DiscCircuit D' (f '' Δ)`. -/
def pushDiscCircuit (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D : Drawing S} {D' : Drawing (OnePoint EuclideanPlane)} (hD'U : D'.U = f '' D.U)
    (C : DiscCircuit D Δ) : DiscCircuit D' (f '' Δ) where
  U := f '' C.U
  ins := f '' C.ins
  U_sub_drawing := hD'U ▸ image_mono C.U_sub_drawing
  U_sub_disc := image_mono C.U_sub_disc
  isOArc_U := sc.oArc_f C.U_sub_disc C.isOArc_U
  isInside := sc.isInsideDisc_f hΔ C.U_sub_disc C.isOArc_U C.isInside

/-- Push a `DrawingNest D Δ r s` forward to `DrawingNest D' (f '' Δ) r s`. -/
noncomputable def pushNest (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ)
    {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V)
    {r s : ℕ} (N : DrawingNest D Δ r s) :
    DrawingNest D' (f '' Δ) r s where
  circuit j := sc.pushDiscCircuit hΔ hD'U (N.circuit j)
  inside_of_lt {i j} hij :=
    (sc.setInsideOArc_f_iff hΔ (N.circuit j).U_sub_disc (N.circuit j).isOArc_U
      (N.circuit i).U_sub_disc).mpr (N.inside_of_lt hij)
  radialPath p := f '' N.radialPath p
  isPreconnected_radialPath p :=
    (N.isPreconnected_radialPath p).image f (sc.fc.mono (N.radialPath_sub_disc p))
  radialPath_sub_U p := hD'U ▸ image_mono (N.radialPath_sub_U p)
  radialPath_sub_disc p := image_mono (N.radialPath_sub_disc p)
  pairwise_disjoint_paths p q hpq := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨x, hxP, rfl⟩, hfxV⟩ ⟨⟨y, hyQ, heq⟩, _⟩
    obtain rfl := sc.injOn_f (N.radialPath_sub_disc q hyQ) (N.radialPath_sub_disc p hxP) heq
    obtain ⟨z, hzV, hfz⟩ := hD'V ▸ hfxV
    obtain rfl := sc.injOn_f (hDU (D.V_subset_U hzV)) (N.radialPath_sub_disc p hxP) hfz
    exact Set.disjoint_left.mp (N.pairwise_disjoint_paths hpq) ⟨hxP, hzV⟩ ⟨hyQ, hzV⟩
  meets_inner p hs := by
    obtain ⟨z, hzP, hzC⟩ := N.meets_inner p hs
    exact ⟨f z, mem_image_of_mem f hzP, mem_image_of_mem f hzC⟩
  meets_outer p hs := by
    obtain ⟨z, hzP, hzC⟩ := N.meets_outer p hs
    exact ⟨f z, mem_image_of_mem f hzP, mem_image_of_mem f hzC⟩

/-- `circuitRho` is preserved under `pushDiscCircuit`. -/
theorem circuitRho_pushDiscCircuit (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ)
    {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V)
    (C : DiscCircuit D Δ) :
    circuitRho (sc.pushDiscCircuit hΔ hD'U C) = circuitRho C := by
  unfold circuitRho
  congr 1
  ext k
  constructor
  · rintro ⟨F', hF'Δ, hF'o, hF'norm, henc', hcard'⟩
    let F := f' '' F'
    have hFΔ : F ⊆ Δ := sc.f'_subset hF'Δ
    have hFo : IsOArc F := sc.oArc_f' hF'Δ hF'o
    have hfF : f '' F = F' := sc.f_f' hF'Δ
    refine ⟨F, hFΔ, hFo, ?_, ?_, ?_⟩
    · exact (sc.isNormal_f_iff hDU hD'U hD'V hFΔ).mp (hfF ▸ hF'norm)
    · exact (sc.oArcEncloses_f_iff hΔ hFΔ hFo C.U_sub_disc).mp (hfF ▸ henc')
    · rw [← sc.ncard_V_inter_f hDU hD'V hFΔ, hfF]
      exact hcard'
  · rintro ⟨F, hFΔ, hFo, hFnorm, henc, hcard⟩
    refine ⟨f '' F, image_mono hFΔ, sc.oArc_f hFΔ hFo,
      (sc.isNormal_f_iff hDU hD'U hD'V hFΔ).mpr hFnorm,
      (sc.oArcEncloses_f_iff hΔ hFΔ hFo C.U_sub_disc).mpr henc, ?_⟩
    rw [sc.ncard_V_inter_f hDU hD'V hFΔ]
    exact hcard

/-- Reindex a `DrawingNest` along equalities of `r` and `s` without transport opacity. -/
def reindexNest {S₀ : Type*} [TopologicalSpace S₀] {D₀ : Drawing S₀} {Δ₀ : Set S₀}
    {r₁ r₂ s₁ s₂ : ℕ} (hr : r₁ = r₂) (hs : s₁ = s₂)
    (N : DrawingNest D₀ Δ₀ r₁ s₁) : DrawingNest D₀ Δ₀ r₂ s₂ where
  circuit j := N.circuit (Fin.cast hs.symm j)
  inside_of_lt {i j} hij := N.inside_of_lt (by simpa using hij)
  radialPath p := N.radialPath (Fin.cast hr.symm p)
  isPreconnected_radialPath p := N.isPreconnected_radialPath (Fin.cast hr.symm p)
  radialPath_sub_U p := N.radialPath_sub_U (Fin.cast hr.symm p)
  radialPath_sub_disc p := N.radialPath_sub_disc (Fin.cast hr.symm p)
  pairwise_disjoint_paths p q hpq := N.pairwise_disjoint_paths
    (fun h => hpq (Fin.ext (by simpa using congrArg Fin.val h)))
  meets_inner p hs₂ := by
    have hs₁ : 0 < s₁ := hs.symm ▸ hs₂
    have hcast : Fin.cast hs.symm (⟨0, hs₂⟩ : Fin s₂) = ⟨0, hs₁⟩ := Fin.ext rfl
    simpa [hcast] using N.meets_inner (Fin.cast hr.symm p) hs₁
  meets_outer p hs₂ := by
    have hs₁ : 0 < s₁ := hs.symm ▸ hs₂
    have hcast : Fin.cast hs.symm ⟨s₂ - 1, Nat.sub_lt hs₂ Nat.one_pos⟩ =
        ⟨s₁ - 1, Nat.sub_lt hs₁ Nat.one_pos⟩ := by
      ext
      subst hs
      rfl
    simpa [hcast] using N.meets_outer (Fin.cast hr.symm p) hs₁

/-- Push `IsCentredOArc D Δ F` forward along `SphereDiscChart`. -/
theorem push_isCentredOArc (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ)
    {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V) (hD'E : D'.E = image f '' D.E)
    {F : Set S} (hc : IsCentredOArc D Δ F) :
    IsCentredOArc D' (f '' Δ) (f '' F) := by
  obtain ⟨hFΔ, hFo, hFnorm, N, hN_in, P, hP, hPdis⟩ := hc
  have hcard : (D'.V ∩ f '' F).ncard = (D.V ∩ F).ncard := sc.ncard_V_inter_f hDU hD'V hFΔ
  have hs_eq : ((D.V ∩ F).ncard + 1) / 2 = ((D'.V ∩ f '' F).ncard + 1) / 2 := by rw [hcard]
  refine ⟨image_mono hFΔ, sc.oArc_f hFΔ hFo,
    (sc.isNormal_f_iff hDU hD'U hD'V hFΔ).mpr hFnorm, ?_⟩
  let N' : DrawingNest D' (f '' Δ) (D'.V ∩ f '' F).ncard (((D'.V ∩ f '' F).ncard + 1) / 2) :=
    reindexNest hcard.symm hs_eq (sc.pushNest hΔ hDU hD'U hD'V N)
  have hN'_circ : ∀ (j : Fin (((D'.V ∩ f '' F).ncard + 1) / 2)),
      (N'.circuit j).U = f '' (N.circuit (Fin.cast hs_eq.symm j)).U := fun _ => rfl
  refine ⟨N', ?_, ?_⟩
  · intro j
    rw [hN'_circ j]
    exact (sc.setInsideOArc_f_iff hΔ hFΔ hFo (N.circuit _).U_sub_disc).mpr (hN_in _)
  · have hexP' : ∀ i : Fin (D'.V ∩ f '' F).ncard,
        ∃ P' : Drawing (OnePoint EuclideanPlane),
          ∃ (hs' : 0 < ((D'.V ∩ f '' F).ncard + 1) / 2) (u' v' : OnePoint EuclideanPlane),
            P'.IsSubdrawing D' ∧ u' ∈ (N'.circuit ⟨0, hs'⟩).U ∧ v' ∈ f '' F ∧
            P'.IsPathBetween u' v' ∧
            P'.V = f '' (P (Fin.cast hcard i)).V := by
      intro i
      let i₀ := Fin.cast hcard i
      obtain ⟨hs, u, v, hPsub, hu, hv, hPpath⟩ := hP i₀
      obtain ⟨P', hP'sub, _, hP'V, hP'E, _, hL, _⟩ :=
        sc.exists_push_subdrawing hΔ hDU hD'V hD'E hPsub
      have hs' : 0 < ((D'.V ∩ f '' F).ncard + 1) / 2 := hs_eq ▸ hs
      refine ⟨P', hs', f u, f v, hP'sub, ?_, mem_image_of_mem f hv,
        sc.isPathBetween_of_push (hPsub.U_subset.trans hDU) hP'V hP'E hL hPpath, hP'V⟩
      rw [hN'_circ ⟨0, hs'⟩]
      have hcast : Fin.cast hs_eq.symm (⟨0, hs'⟩ : Fin _) = ⟨0, hs⟩ := Fin.ext rfl
      rw [hcast]
      exact mem_image_of_mem f hu
    choose P' hs' u' v' hP'sub hu' hv' hP'path hP'V using hexP'
    refine ⟨P', fun i => ⟨hs' i, u' i, v' i, hP'sub i, hu' i, hv' i, hP'path i⟩, ?_⟩
    intro i j hij
    rw [hP'V i, hP'V j]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxΔ : x ∈ Δ := hDU ((hP _).choose_spec.choose_spec.choose_spec.1.1 hx |> D.V_subset_U)
    have hyΔ : y ∈ Δ := hDU ((hP _).choose_spec.choose_spec.choose_spec.1.1 hy |> D.V_subset_U)
    obtain rfl := sc.injOn_f hyΔ hxΔ heq
    have hne : Fin.cast hcard i ≠ Fin.cast hcard j :=
      fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
    exact Set.disjoint_left.mp (hPdis hne) hx hy

/-- Pull `SleeveData D' (f '' Δ) (f '' F)` back to `SleeveData D Δ F` along `SphereDiscChart`. -/
noncomputable def pullBackSleeveData (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D : Drawing S} (hDU : D.U ⊆ Δ)
    {D' : Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V) (hD'E : D'.E = image f '' D.E)
    {F : Set S} (hFΔ : F ⊆ Δ) (hFo : IsOArc F)
    (sd' : SleeveData D' (f '' Δ) (f '' F)) :
    SleeveData D Δ F := by
  classical
  have hcard : (D'.V ∩ f '' F).ncard = (D.V ∩ F).ncard := sc.ncard_V_inter_f hDU hD'V hFΔ
  let r := (D.V ∩ F).ncard
  let s := (r + 1) / 2
  have hr_eq : (D'.V ∩ f '' F).ncard = r := hcard
  have hs_eq : ((D'.V ∩ f '' F).ncard + 1) / 2 = s := by rw [hr_eq]
  let N'_cast : DrawingNest D' (f '' Δ) r s := reindexNest hr_eq hs_eq sd'.nest
  have hN'_circ : ∀ j : Fin s,
      (N'_cast.circuit j).U = (sd'.nest.circuit (Fin.cast hs_eq.symm j)).U := fun _ => rfl
  let N : DrawingNest D Δ r s := sc.pullBackNest hΔ hDU hD'U hD'V N'_cast
  have hN_circ : ∀ j : Fin s,
      (N.circuit j).U = f' '' (sd'.nest.circuit (Fin.cast hs_eq.symm j)).U := by
    intro j
    change f' '' (N'_cast.circuit j).U = _
    rw [hN'_circ j]
  have hex_cd : ∀ j : Fin s, ∃ C_j : Drawing S,
      C_j.IsSubdrawing D ∧ C_j.IsCircuit ∧ C_j.U = (N.circuit j).U ∧
      C_j.V = f' '' (sd'.circuitDraw (Fin.cast hs_eq.symm j)).V ∧
      C_j.E = image f' '' (sd'.circuitDraw (Fin.cast hs_eq.symm j)).E := by
    intro j
    let j' := Fin.cast hs_eq.symm j
    obtain ⟨hC'sub, hC'circ, hC'U⟩ := sd'.isCircuit_draw j'
    obtain ⟨C_j, hCsub, hCU, hCV, hCE, _, hL, _⟩ :=
      sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E hC'sub
    have hC'U_Δ : (sd'.circuitDraw j').U ⊆ f '' Δ :=
      hC'sub.U_subset.trans (hD'U ▸ image_mono hDU)
    refine ⟨C_j, hCsub, sc.isCircuit_of_pullback hC'U_Δ hCV hCE hL hC'circ, ?_, hCV, hCE⟩
    rw [hCU, hC'U, hN_circ j]
  choose cd hcd_sub hcd_circ hcd_U hcd_V hcd_E using hex_cd
  have hex_sp : ∀ i : Fin r, ∃ P_i : Drawing S,
      (∃ (hs : 0 < s) (u v : S),
        P_i.IsSubdrawing D ∧ u ∈ (N.circuit ⟨0, hs⟩).U ∧ v ∈ F ∧
        P_i.IsPathBetween u v ∧ OArcEncloses Δ F P_i.U ∧ P_i.V ∩ F = {v}) ∧
      P_i.V = f' '' (sd'.spoke (Fin.cast hr_eq.symm i)).V ∧
      P_i.E = image f' '' (sd'.spoke (Fin.cast hr_eq.symm i)).E := by
    intro i
    let i' := Fin.cast hr_eq.symm i
    obtain ⟨hs', u', v', hP'sub, hu', hv', hP'path, henc', hcap'⟩ := sd'.isPath_spoke i'
    obtain ⟨P_i, hPsub, hPU, hPV, hPE, _, hL, _⟩ :=
      sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E hP'sub
    have hP'U_Δ : (sd'.spoke i').U ⊆ f '' Δ :=
      hP'sub.U_subset.trans (hD'U ▸ image_mono hDU)
    have hs : 0 < s := hs_eq ▸ hs'
    obtain ⟨v, hvF, rfl⟩ := hv'
    have hfv : f' (f v) = v := sc.f'f (hFΔ hvF)
    refine ⟨P_i, ⟨hs, f' u', v, hPsub, ?_, hvF, ?_, ?_, ?_⟩, hPV, hPE⟩
    · rw [hN_circ ⟨0, hs⟩]
      have hcast : Fin.cast hs_eq.symm (⟨0, hs⟩ : Fin s) = ⟨0, hs'⟩ := Fin.ext rfl
      rw [hcast]
      exact mem_image_of_mem f' hu'
    · rw [← hfv]
      exact sc.isPathBetween_of_pullback hP'U_Δ hPV hPE hL hP'path
    · have hfPU : f '' P_i.U = (sd'.spoke i').U := by
        rw [hPU, sc.f_f' hP'U_Δ]
      exact (sc.oArcEncloses_f_iff hΔ hFΔ hFo (hPsub.U_subset.trans hDU)).mp (hfPU ▸ henc')
    · ext x
      constructor
      · rintro ⟨hxPV, hxF⟩
        rw [hPV] at hxPV
        obtain ⟨p, hpV, rfl⟩ := hxPV
        have hpΔ : p ∈ f '' Δ := hP'U_Δ ((sd'.spoke i').V_subset_U hpV)
        have hfp : p ∈ f '' F := by
          rw [← sc.ff' hpΔ]
          exact mem_image_of_mem f hxF
        have hp_eq : p = f v := by
          have : p ∈ (sd'.spoke i').V ∩ f '' F := ⟨hpV, hfp⟩
          rwa [hcap', mem_singleton_iff] at this
        rw [hp_eq, hfv, mem_singleton_iff]
      · intro hx
        rw [mem_singleton_iff] at hx
        rw [hx]
        have hfvV : f v ∈ (sd'.spoke i').V := by
          have : f v ∈ (sd'.spoke i').V ∩ f '' F := by rw [hcap']; exact rfl
          exact this.1
        refine ⟨?_, hvF⟩
        rw [hPV, ← hfv]
        exact mem_image_of_mem f' hfvV
  choose sp hsp_spec hsp_V hsp_E using hex_sp
  refine
    { nest := N
      circuitDraw := cd
      isCircuit_draw := fun j => ⟨hcd_sub j, hcd_circ j, hcd_U j⟩
      circuit_inside := fun j => by
        let j' := Fin.cast hs_eq.symm j
        have hfU : f '' (N.circuit j).U = (sd'.nest.circuit j').U := by
          rw [hN_circ j, sc.f_f' (sd'.nest.circuit j').U_sub_disc]
        exact (sc.setInsideOArc_f_iff hΔ hFΔ hFo (N.circuit j).U_sub_disc).mp
          (hfU ▸ sd'.circuit_inside j')
      spoke := sp
      isPath_spoke := hsp_spec
      pairwise_disjoint_spokes := fun i j hij => by
        dsimp only
        rw [hsp_V i, hsp_V j]
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
        have hD'U_Δ : D'.U ⊆ f '' Δ := hD'U ▸ image_mono hDU
        have hpΔ : p ∈ f '' Δ :=
          hD'U_Δ (D'.V_subset_U ((sd'.isPath_spoke _).choose_spec.choose_spec.choose_spec.1.1 hp))
        have hqΔ : q ∈ f '' Δ :=
          hD'U_Δ (D'.V_subset_U ((sd'.isPath_spoke _).choose_spec.choose_spec.choose_spec.1.1 hq))
        obtain rfl := sc.injOn_f' hqΔ hpΔ heq
        have hne : Fin.cast hr_eq.symm i ≠ Fin.cast hr_eq.symm j :=
          fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
        exact Set.disjoint_left.mp (sd'.pairwise_disjoint_spokes hne) hp hq
      inter_isPath := fun i j => by
        let i' := Fin.cast hr_eq.symm i
        let j' := Fin.cast hs_eq.symm j
        obtain ⟨Q', a', b', hQ'sub, hQ'V, hQ'E, hQ'path⟩ := sd'.inter_isPath i' j'
        obtain ⟨Q, hQsub, _, hQV, hQE, _, hL, _⟩ :=
          sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E hQ'sub
        have hQ'U_Δ : Q'.U ⊆ f '' Δ := hQ'sub.U_subset.trans (hD'U ▸ image_mono hDU)
        have hspV_Δ : (sd'.spoke i').V ⊆ f '' Δ :=
          (sd'.isPath_spoke i').choose_spec.choose_spec.choose_spec.1.1.trans
            (hD'V ▸ image_mono (D.V_subset_U.trans hDU))
        have hcdV_Δ : (sd'.circuitDraw j').V ⊆ f '' Δ :=
          (sd'.isCircuit_draw j').1.1.trans (hD'V ▸ image_mono (D.V_subset_U.trans hDU))
        refine ⟨Q, f' a', f' b', hQsub, ?_, ?_,
          sc.isPathBetween_of_pullback hQ'U_Δ hQV hQE hL hQ'path⟩
        · rw [hQV, hQ'V, hsp_V i, hcd_V j]
          exact InjOn.image_inter sc.injOn_f' hspV_Δ hcdV_Δ
        · rw [hQE, hQ'E, hsp_E i, hcd_E j]
          have hinjE : InjOn (image f') D'.E := by
            intro e₁ he₁ e₂ he₂ heq
            have h₁ : e₁ ⊆ f '' Δ := fun p hp => (hD'U ▸ image_mono hDU) (he₁.2.1 hp).1
            have h₂ : e₂ ⊆ f '' Δ := fun p hp => (hD'U ▸ image_mono hDU) (he₂.2.1 hp).1
            rw [← sc.f_f' h₁, ← sc.f_f' h₂, heq]
          exact InjOn.image_inter (hinjE.mono
            (union_subset (sd'.isPath_spoke i').choose_spec.choose_spec.choose_spec.1.2
              (sd'.isCircuit_draw j').1.2)) subset_union_left subset_union_right }

end SphereDiscChart

/-!
## 3. Menger's Theorem for `circuitRho` and Path Trimming onto an Enclosing O-Arc
-/

section CircuitRhoPaths

/-- Every edge `e ∈ D.E` of a drawing `D` in `SphereSurf` is disjoint from `discInt C.ins` if and
only if it is not contained in `discInt C.ins`. -/
private theorem edge_disjoint_discInt_or_subset {D : Drawing SphereSurf} {Δ : Set SphereSurf}
    (C : DiscCircuit D Δ) {e : Set SphereSurf} (he : e ∈ D.E) :
    e ⊆ discInt C.ins ∨ Disjoint e (discInt C.ins) := by
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  have hdis_bd : Disjoint e (discBd C.ins) ∨ e ⊆ discBd C.ins := by
    by_cases h : Disjoint e (discBd C.ins)
    · exact Or.inl h
    · right
      obtain ⟨z, hze, hzbd⟩ := Set.not_disjoint_iff.mp h
      rw [C.isInside.2.2.1] at hzbd ⊢
      have hz_not_V : z ∉ D.V := (he.2.1 hze).2
      -- `C.U` is an O-arc in `D.U`; any edge `e` meeting `C.U` lies in `C.U`.
      obtain ⟨C', _, hC'sub, hC'U⟩ := GM11.exists_circuit_of_oArc C.isOArc_U C.U_sub_drawing
      have hz_not_C'V : z ∉ C'.V := fun h => hz_not_V (hC'sub.1 h)
      obtain ⟨e', he', hze'⟩ := C'.exists_edge_of_mem (hC'U ▸ hzbd) hz_not_C'V
      have heq : e = e' := D.edge_eq_of_mem he (hC'sub.2 he') hze hze'
      rw [heq, ← hC'U]
      exact fun p hp => (he'.2.1 hp).1
  rcases hdis_bd with hbd | hsub_bd
  · rcases C.isInside.2.1.side hman he.2.2.1.isConnected.isPreconnected hbd with hin | hout
    · exact Or.inl hin
    · exact Or.inr (hout.mono_right (discInt_subset _))
  · exact Or.inr (Set.disjoint_left.mpr fun p hp hpint => hpint.2 (hsub_bd hp))

/-- Menger's theorem for `circuitRho` on `OnePoint EuclideanPlane`: if `r ≤ circuitRho C` and
`D.IsNormal (discBd Δ)`, there are `r` pairwise vertex-disjoint path subdrawings of `D` between
`C.U` and `discBd Δ`. -/
theorem exists_disjoint_paths_of_circuitRho_sphere
    {D : Drawing SphereSurf} {Δ : Set SphereSurf}
    (hΔ : IsClosedDisc Δ)
    (hDU : D.U ⊆ Δ) (hprop : D.IsNormal (discBd Δ))
    (C : DiscCircuit D Δ) {r : ℕ} (hr : r ≤ circuitRho C) :
    ∃ (P : Fin r → Drawing SphereSurf) (u v : Fin r → SphereSurf),
      (∀ i, (P i).IsSubdrawing D ∧ u i ∈ C.U ∧ v i ∈ discBd Δ ∧ (P i).IsPathBetween (u i) (v i)) ∧
      Pairwise (fun i j => Disjoint (P i).V (P j).V) := by
  classical
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hsph : Surface.IsSphere SphereSurf := ⟨Homeomorph.refl _⟩
  have : ConnectedSpace SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).2
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  -- Restrict `D` outside `discInt C.ins` so `C.U` is kept intact and `discInt C.ins` is empty.
  let V_out : Set SphereSurf := {x ∈ D.V | x ∉ discInt C.ins}
  let E_out : Set (Set SphereSurf) := {e ∈ D.E | Disjoint e (discInt C.ins)}
  let Γ₀ : Drawing SphereSurf := D.span V_out E_out
  have hΓ₀_sub : Γ₀.IsSubdrawing D := D.span_isSubdrawing V_out E_out
  have hΓ₀_V : Γ₀.V = V_out := by
    apply Subset.antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨heE, _⟩, hxe, hxDV⟩ := mem_iUnion₂.mp hx
        refine ⟨hxDV, fun hxint => ?_⟩
        obtain ⟨y, hyint, hye⟩ := mem_closure_iff.mp hxe _ (C.isInside.2.1.isOpen_discInt hman) hxint
        exact Set.disjoint_left.mp heE.2 hye hyint
    · intro x hx
      exact Or.inl ⟨hx, hx.1⟩
  have hΓ₀_E : Γ₀.E = E_out := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr fun e he => he.1
  have hΓ₀_dis_int : Disjoint Γ₀.U (discInt C.ins) := by
    rw [Drawing.U_eq, hΓ₀_V, hΓ₀_E]
    refine Disjoint.union_left (Set.disjoint_left.mpr fun x hx => hx.2) ?_
    refine disjoint_iUnion₂_left.mpr fun e he => ?_
    refine Set.disjoint_left.mpr fun x hxcl hxint => ?_
    obtain ⟨y, hyint, hye⟩ := mem_closure_iff.mp hxcl _ (C.isInside.2.1.isOpen_discInt hman) hxint
    exact Set.disjoint_left.mp he.2 hye hyint
  -- Every vertex and edge of `C` lies in `Γ₀`, so `C.U ⊆ Γ₀.U`.
  obtain ⟨C_draw, hC_circ, hC_sub_D, hC_U⟩ := GM11.exists_circuit_of_oArc C.isOArc_U C.U_sub_drawing
  have hC_sub_Γ₀ : C_draw.IsSubdrawing Γ₀ := by
    refine ⟨?_, ?_⟩
    · rw [hΓ₀_V]
      intro x hx
      exact ⟨hC_sub_D.1 hx, fun hxint => hxint.2 (C.isInside.2.2.1 ▸ hC_U ▸ C_draw.V_subset_U hx)⟩
    · rw [hΓ₀_E]
      intro e he
      refine ⟨hC_sub_D.2 he, Set.disjoint_left.mpr fun p hp hpint => ?_⟩
      exact hpint.2 (C.isInside.2.2.1 ▸ hC_U ▸ (he.2.1 hp).1)
  have hCU_sub_Γ₀ : C.U ⊆ Γ₀.U := hC_U ▸ hC_sub_Γ₀.U_subset
  let Z₁ : Set SphereSurf := Γ₀.V ∩ C.U
  let Z₂ : Set SphereSurf := Γ₀.V ∩ discBd Δ
  have hZ₁_eq : Z₁ = D.V ∩ C.U := by
    ext x
    change x ∈ Γ₀.V ∧ x ∈ C.U ↔ x ∈ D.V ∧ x ∈ C.U
    rw [hΓ₀_V]
    exact ⟨fun ⟨⟨hxV, _⟩, hxC⟩ => ⟨hxV, hxC⟩,
      fun ⟨hxV, hxC⟩ => ⟨⟨hxV, fun hint => hint.2 (C.isInside.2.2.1 ▸ hxC)⟩, hxC⟩⟩
  have hZ₂_eq : Z₂ = D.V ∩ discBd Δ := by
    ext x
    change x ∈ Γ₀.V ∧ x ∈ discBd Δ ↔ x ∈ D.V ∧ x ∈ discBd Δ
    rw [hΓ₀_V]
    refine ⟨fun ⟨⟨hxV, _⟩, hxB⟩ => ⟨hxV, hxB⟩, fun ⟨hxV, hxB⟩ => ⟨⟨hxV, fun hint => ?_⟩, hxB⟩⟩
    have hint_Δ : discInt C.ins ⊆ discInt Δ := by
      intro p hp
      refine ⟨C.isInside.1 hp.1, fun hpbd => ?_⟩
      -- `discInt C.ins` is open and contained in `Δ`, while every open set meeting `discBd Δ`
      -- meets `univ \ Δ`.
      obtain ⟨_, hE₀_tmp⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hΔ
      have hpcl : p ∈ closure (univ \ Δ) :=
        Surface.discBd_subset (closure (univ \ Δ)) (hE₀_tmp.symm ▸ hpbd)
      obtain ⟨q, hq_in, hq_out⟩ :=
        mem_closure_iff.mp hpcl _ (C.isInside.2.1.isOpen_discInt hman) hp
      exact hq_out.2 (C.isInside.1 hq_in.1)
    exact (hint_Δ hint).2 hxB
  by_cases hp : HasDisjointPaths Γ₀.toHypergraph.skeleton Z₁ Z₂ r
  · obtain ⟨Q, hQ⟩ := hp
    have hex : ∀ i, ∃ P : Drawing SphereSurf,
        P.IsPathBetween (Q i).first (Q i).last ∧ P.IsSubdrawing Γ₀ ∧
        P.V = {x | x ∈ (Q i).walk.support} := fun i =>
      GM16.drawing_path_of_skeleton_path (Q i).first_mem.1 (Q i).walk (Q i).isPath
    choose P hP hPs hPV using hex
    refine ⟨P, fun i => (Q i).first, fun i => (Q i).last,
      fun i => ⟨(hPs i).trans hΓ₀_sub, (Q i).first_mem.2, (Q i).last_mem.2, hP i⟩,
      fun i j hne => ?_⟩
    dsimp only
    rw [hPV i, hPV j]
    exact hQ hne
  · exfalso
    -- Delete all edges meeting `C.ins` (`Γ_cyl`), then glue back `C.U` subdivided at `Z₁ ∪ M`
    -- where `M` picks one interior point `m_e ∈ e` on each edge `e ∈ C_draw.E`.
    let V_cyl : Set SphereSurf := {x ∈ D.V | x ∉ discInt C.ins}
    let E_cyl : Set (Set SphereSurf) := {e ∈ D.E | Disjoint e C.ins}
    let Γ_cyl : Drawing SphereSurf := D.span V_cyl E_cyl
    have hΓ_cyl_sub_Γ₀ : Γ_cyl.IsSubdrawing Γ₀ := by
      refine ⟨?_, ?_⟩
      · rw [hΓ₀_V]
        rintro x (⟨hx, _⟩ | hx)
        · exact hx
        · obtain ⟨e, ⟨heE, _⟩, hxe, hxDV⟩ := mem_iUnion₂.mp hx
          exact ⟨hxDV, fun hint => by
            obtain ⟨y, hyint, hye⟩ :=
              mem_closure_iff.mp hxe _ (C.isInside.2.1.isOpen_discInt hman) hint
            exact Set.disjoint_left.mp heE.2 hye hyint.1⟩
      · rw [Drawing.span_E, hΓ₀_E]
        rintro e ⟨he, _⟩
        exact ⟨he.1, he.2.mono_right (discInt_subset _)⟩
    have hΓ_cyl_V : Γ_cyl.V = Γ₀.V := by
      apply Subset.antisymm hΓ_cyl_sub_Γ₀.1
      rw [hΓ₀_V]
      intro x hx
      exact Or.inl ⟨hx, hx.1⟩
    have hΓ_cyl_E : Γ_cyl.E = E_cyl := by
      rw [Drawing.span_E]
      exact inter_eq_left.mpr fun e he => he.1
    have hΓ_cyl_cap_C : Γ_cyl.U ∩ C.ins = Z₁ := by
      ext x
      constructor
      · rintro ⟨hxU, hxins⟩
        rw [Drawing.U_eq, hΓ_cyl_V, hΓ_cyl_E] at hxU
        rcases hxU with hxV | hxE
        · have hxbd : x ∈ discBd C.ins := by
            by_contra hnb
            exact (hΓ₀_V ▸ hxV).2 ⟨hxins, hnb⟩
          exact ⟨hxV, C.isInside.2.2.1 ▸ hxbd⟩
        · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
          have hxbd : x ∈ discBd C.ins := by
            by_contra hnb
            obtain ⟨y, hyint, hye⟩ :=
              mem_closure_iff.mp hxe _ (C.isInside.2.1.isOpen_discInt hman) ⟨hxins, hnb⟩
            exact Set.disjoint_left.mp he.2 hye hyint.1
          have hxCU : x ∈ C.U := C.isInside.2.2.1 ▸ hxbd
          have hxDV : x ∈ D.V := by
            by_contra hx_not_V
            obtain ⟨e', he', hxe'⟩ :=
              C_draw.exists_edge_of_mem (hC_U ▸ hxCU) (fun h => hx_not_V (hC_sub_D.1 h))
            have hcl_sub : closure e ⊆ D.U :=
              closure_minimal (fun p hp => (he.1.2.1 hp).1) D.isClosed_U
            obtain ⟨e'', he'', hxe''⟩ := D.exists_edge_of_mem (hcl_sub hxe) hx_not_V
            -- If `x ∉ D.V`, `x ∈ closure e \ D.V` implies `x ∈ e`, contradicting `Disjoint e C.ins`.
            have hx_in_e : x ∈ e := by
              obtain ⟨c, h1, h2, h3, h4, h5⟩ := GM11.exists_edge_param D he.1
              have hc_p : GM07.EdgeParam D e c := ⟨h1, h2, h3, h4, h5⟩
              rw [hc_p.closure_eq] at hxe
              obtain ⟨t, rfl⟩ := hxe
              obtain ⟨h6, h7⟩ := hc_p.pos_of_ne he.1 hx_not_V
              exact hc_p.mem_edge h6 h7
            exact Set.disjoint_left.mp he.2 hx_in_e hxins
          exact ⟨hΓ₀_V.symm ▸ ⟨hxDV, fun h => h.2 hxbd⟩, hxCU⟩
      · rintro ⟨hxV, hxCU⟩
        exact ⟨Γ_cyl.V_subset_U (hΓ_cyl_V.symm ▸ hxV),
          Surface.discBd_subset C.ins (C.isInside.2.2.1 ▸ hxCU)⟩
    -- Note `HasDisjointPaths` on `Γ_cyl` implies `HasDisjointPaths` on `Γ₀`.
    have hnot_hp_cyl : ¬ HasDisjointPaths Γ_cyl.toHypergraph.skeleton Z₁ Z₂ r := by
      intro hp_cyl
      refine hp ?_
      obtain ⟨Q, hQ⟩ := hp_cyl
      have hskel_le : Γ_cyl.toHypergraph.skeleton ≤ Γ₀.toHypergraph.skeleton := by
        intro a b ⟨hab, e, h1, h2⟩
        exact ⟨hab, e, ⟨hΓ_cyl_sub_Γ₀.2 h1.1, hΓ_cyl_sub_Γ₀.1 h1.2.1, h1.2.2⟩,
          ⟨hΓ_cyl_sub_Γ₀.2 h2.1, hΓ_cyl_sub_Γ₀.1 h2.2.1, h2.2.2⟩⟩
      refine ⟨fun i =>
        { first := (Q i).first
          last := (Q i).last
          first_mem := (Q i).first_mem
          last_mem := (Q i).last_mem
          walk := (Q i).walk.mapLe hskel_le
          isPath := (Q i).isPath.mapLe hskel_le }, fun i j hne => ?_⟩
      simpa [SimpleGraph.Walk.mapLe] using hQ hne
    have hZ₁_sub_cyl : Z₁ ⊆ Γ_cyl.toHypergraph.vertexSet := by
      change Z₁ ⊆ Γ_cyl.V
      rw [hΓ_cyl_V]
      exact inter_subset_left
    have hZ₂_sub_cyl : Z₂ ⊆ Γ_cyl.toHypergraph.vertexSet := by
      change Z₂ ⊆ Γ_cyl.V
      rw [hΓ_cyl_V]
      exact inter_subset_left
    obtain ⟨X, hsep, hlt⟩ :=
      Thomas.exists_separates_lt_of_not_hasDisjointPaths Γ_cyl.toHypergraph
        hZ₁_sub_cyl hZ₂_sub_cyl hnot_hp_cyl
    -- Pick one interior point `m_e ∈ e` on each edge `e ∈ C_draw.E`.
    have hex_mid : ∀ e : C_draw.E, ∃ m ∈ e.1, m ∈ C.U ∧ m ∉ D.V := by
      intro ⟨e, he⟩
      obtain ⟨m, hm⟩ := he.1
      exact ⟨m, hm, hC_U ▸ (he.2.1 hm).1, (hC_sub_D.2 he |>.2.1 hm).2⟩
    choose mid hmid_e hmid_CU hmid_notDV using hex_mid
    let M : Set SphereSurf := range mid
    have hCE_fin : C_draw.E.Finite := C_draw.finite_edges
    have : Finite C_draw.E := hCE_fin.to_subtype
    have hM_fin : M.Finite := Set.finite_range mid
    have hM_sub_CU : M ⊆ C.U := by rintro _ ⟨e, rfl⟩; exact hmid_CU e
    have hM_dis_DV : Disjoint M D.V := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨e, rfl⟩ hV
      exact hmid_notDV e hV
    have hZ₁_Eq_CV : Z₁ = C_draw.V := by
      rw [hZ₁_eq]
      apply Subset.antisymm
      · rintro x ⟨hxDV, hxCU⟩
        by_contra hx_not_CV
        obtain ⟨e, he, hxe⟩ := C_draw.exists_edge_of_mem (hC_U ▸ hxCU) hx_not_CV
        exact ((hC_sub_D.2 he).2.1 hxe).2 hxDV
      · intro x hx
        exact ⟨hC_sub_D.1 hx, hC_U ▸ C_draw.V_subset_U hx⟩
    let A_cuff : Set SphereSurf := Z₁ ∪ M
    have hA_fin : A_cuff.Finite := (Γ₀.finite_V.subset inter_subset_left).union hM_fin
    have hA_ne : A_cuff.Nonempty := by
      obtain ⟨u, W, _, _, hCV, _⟩ := hC_circ
      exact ⟨u, Or.inl (hZ₁_Eq_CV.symm ▸ hCV ▸ W.start_mem_support)⟩
    have hA_sub_CU : A_cuff ⊆ C.U := union_subset inter_subset_right hM_sub_CU
    obtain ⟨D_C, hDC_U, hDC_V⟩ :=
      GM11.exists_drawing_on_oArc C.isOArc_U hA_fin hA_ne hA_sub_CU
    -- Glue `D_C` (`D_C.U = C.U`, `D_C.V = Z₁ ∪ M`) onto `Γ_cyl`.
    have hglue_DC : Γ_cyl.U ∩ D_C.U ⊆ Γ_cyl.V ∩ D_C.V := by
      rintro x ⟨hx_cyl, hx_DC⟩
      have hxZ₁ : x ∈ Z₁ :=
        hΓ_cyl_cap_C ▸ ⟨hx_cyl, Surface.discBd_subset C.ins (C.isInside.2.2.1 ▸ hDC_U ▸ hx_DC)⟩
      exact ⟨hΓ_cyl_V.symm ▸ hxZ₁.1, hDC_V ▸ Or.inl hxZ₁⟩
    let G₀ := Γ_cyl.glue D_C hglue_DC
    have hG₀_U : G₀.U = Γ_cyl.U ∪ C.U := by change Γ_cyl.U ∪ D_C.U = _; rw [hDC_U]
    have hG₀_V : G₀.V = Γ₀.V ∪ M := by
      change Γ_cyl.V ∪ D_C.V = _
      rw [hΓ_cyl_V, hDC_V]
      ext x
      simp only [A_cuff, mem_union]
      exact ⟨fun h => h.elim Or.inl (fun h' => h'.elim (fun hz => Or.inl hz.1) Or.inr),
        fun h => h.elim Or.inl (fun hm => Or.inr (Or.inr hm))⟩
    have hG₀_E : G₀.E = Γ_cyl.E ∪ D_C.E := Drawing.glue_E hglue_DC
    have hG₀_dis_int : Disjoint G₀.U (discInt C.ins) := by
      rw [hG₀_U]
      refine Disjoint.union_left ?_ ?_
      · exact hΓ₀_dis_int.mono_left hΓ_cyl_sub_Γ₀.U_subset
      · exact Set.disjoint_left.mpr fun x hxCU hxint => hxint.2 (C.isInside.2.2.1 ▸ hxCU)
    -- Every point of `D.U \ discInt C.ins` lies in `G₀.U`.
    have hDU_sub_G₀ : D.U \ discInt C.ins ⊆ G₀.U := by
      rintro x ⟨hxDU, hx_not_int⟩
      rw [hG₀_U]
      by_cases hxCU : x ∈ C.U
      · exact Or.inr hxCU
      · left
        by_cases hxDV : x ∈ D.V
        · exact Γ_cyl.V_subset_U (hΓ_cyl_V.symm ▸ hΓ₀_V.symm ▸ ⟨hxDV, hx_not_int⟩)
        · obtain ⟨e, heD, hxe⟩ := D.exists_edge_of_mem hxDU hxDV
          have he_dis_int : Disjoint e (discInt C.ins) := by
            rcases edge_disjoint_discInt_or_subset C heD with hsub | hdis
            · exact absurd (hsub hxe) hx_not_int
            · exact hdis
          have he_dis_C : Disjoint e C.ins := by
            refine Set.disjoint_left.mpr fun p hpe hpins => ?_
            by_cases hpbd : p ∈ discBd C.ins
            · have hpCU : p ∈ C.U := C.isInside.2.2.1 ▸ hpbd
              obtain ⟨e', he', hpe'⟩ :=
                C_draw.exists_edge_of_mem (hC_U ▸ hpCU) (fun h => (heD.2.1 hpe).2 (hC_sub_D.1 h))
              have heq : e = e' := D.edge_eq_of_mem heD (hC_sub_D.2 he') hpe hpe'
              exact hxCU (hC_U ▸ (heq ▸ he' |>.2.1 hxe).1)
            · exact Set.disjoint_left.mp he_dis_int hpe ⟨hpins, hpbd⟩
          have he_cyl : e ∈ Γ_cyl.E := hΓ_cyl_E.symm ▸ ⟨heD, he_dis_C⟩
          exact Drawing.U_eq Γ_cyl ▸ Or.inr (mem_iUnion₂.mpr ⟨e, he_cyl, subset_closure hxe⟩)
    -- Every edge `e' ∈ D_C.E` has at least one endpoint in `M`.
    have hDC_edge_meets_M : ∀ e' ∈ D_C.E, (closure e' ∩ M).Nonempty := by
      intro e' he'
      by_contra hnot_M
      rw [Set.not_nonempty_iff_eq_empty] at hnot_M
      obtain ⟨p₀, hp₀⟩ := he'.1
      have hp₀_CU : p₀ ∈ C.U := hDC_U ▸ (he'.2.1 hp₀).1
      have hp₀_not_A : p₀ ∉ A_cuff := hDC_V ▸ (he'.2.1 hp₀).2
      have hp₀_not_CV : p₀ ∉ C_draw.V := fun h => hp₀_not_A (Or.inl (hZ₁_Eq_CV.symm ▸ h))
      obtain ⟨e, heC, hp₀e⟩ := C_draw.exists_edge_of_mem (hC_U ▸ hp₀_CU) hp₀_not_CV
      -- `e' ⊆ C.U \ A_cuff ⊆ C_draw.U \ C_draw.V`, and `e'` is path-connected meeting `e`, so `e' ⊆ e`.
      have he'_sub_CD : e' ⊆ C_draw.U \ C_draw.V := by
        intro q hq
        exact ⟨hC_U ▸ hDC_U ▸ (he'.2.1 hq).1,
          fun hqV => (hDC_V ▸ (he'.2.1 hq).2) (Or.inl (hZ₁_Eq_CV.symm ▸ hqV))⟩
      have he'_sub_e : e' ⊆ e := by
        intro q hq
        obtain ⟨e₂, he₂, hqe₂⟩ := C_draw.exists_edge_of_mem (he'_sub_CD hq).1 (he'_sub_CD hq).2
        have hpc_u : IsPathConnected (e₂ ∪ e') := by
          obtain ⟨γ⟩ := he'.2.2.1.joinedIn p₀ hp₀ q hq
          exact he₂.2.2.1.union he'.2.2.1 ⟨q, hqe₂, hq⟩
        have he₂_eq : e₂ ∪ e' = e₂ :=
          he₂.2.2.2 (e₂ ∪ e') (union_subset he₂.2.1 he'_sub_CD) hpc_u subset_union_left
        have hp₀_e₂ : p₀ ∈ e₂ := he₂_eq ▸ Or.inr hp₀
        have he_eq : e = e₂ := C_draw.edge_eq_of_mem heC he₂ hp₀e hp₀_e₂
        exact he_eq ▸ hqe₂
      -- `mid ⟨e, heC⟩ ∈ e ∩ M`, so `mid ⟨e, heC⟩ ∉ closure e'`; yet `closure e' ∩ e = e'` and
      -- `e \ e'` is closed in `e`, contradicting connectedness of `e`.
      let m₀ := mid ⟨e, heC⟩
      have hm₀_e : m₀ ∈ e := hmid_e ⟨e, heC⟩
      have hm₀_M : m₀ ∈ M := ⟨⟨e, heC⟩, rfl⟩
      have hm₀_not_e' : m₀ ∉ e' := fun h =>
        (Set.eq_empty_iff_forall_notMem.mp hnot_M m₀) ⟨subset_closure h, hm₀_M⟩
      have hcl_e'_inter_e : e ∩ closure e' = e' := by
        apply Subset.antisymm
        · rintro q ⟨hqe, hqcl⟩
          by_contra hq_not_e'
          obtain ⟨c, h1, h2, h3, h4, h5⟩ := GM11.exists_edge_param D_C he'
          have hc_p : GM07.EdgeParam D_C e' c := ⟨h1, h2, h3, h4, h5⟩
          have hq_DCV : q ∈ D_C.V := by
            by_contra hq_not_V
            rw [hc_p.closure_eq] at hqcl
            obtain ⟨t, rfl⟩ := hqcl
            obtain ⟨h6, h7⟩ := hc_p.pos_of_ne he' hq_not_V
            exact hq_not_e' (hc_p.mem_edge h6 h7)
          have hq_A : q ∈ Z₁ ∪ M := by rwa [hDC_V] at hq_DCV
          rcases hq_A with hqZ₁ | hqM
          · exact (heC.2.1 hqe).2 (hZ₁_Eq_CV ▸ hqZ₁)
          · exact (Set.eq_empty_iff_forall_notMem.mp hnot_M q) ⟨hqcl, hqM⟩
        · exact fun q hq => ⟨he'_sub_e hq, subset_closure hq⟩
      let R_other : Set SphereSurf := M ∪ ⋃ f ∈ D_C.E \ {e'}, closure f
      have hR_closed : IsClosed R_other :=
        hM_fin.isClosed.union ((D_C.finite_edges.subset sdiff_subset).isClosed_biUnion
          fun _ _ => isClosed_closure)
      have he_cov : e ⊆ closure e' ∪ R_other := by
        intro q hqe
        have hq_CU : q ∈ D_C.U := hDC_U.symm ▸ hC_U ▸ (heC.2.1 hqe).1
        by_cases hqM : q ∈ M
        · exact Or.inr (Or.inl hqM)
        · have hq_not_DCV : q ∉ D_C.V := by
            rw [hDC_V]
            rintro (hqZ₁ | hqM')
            · exact (heC.2.1 hqe).2 (hZ₁_Eq_CV ▸ hqZ₁)
            · exact hqM hqM'
          obtain ⟨f, hf, hqf⟩ := D_C.exists_edge_of_mem hq_CU hq_not_DCV
          by_cases hfe' : f = e'
          · exact Or.inl (subset_closure (hfe' ▸ hqf))
          · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨f, ⟨hf, hfe'⟩, subset_closure hqf⟩))
      obtain ⟨z, hze, hzcl, hzR⟩ :=
        isPreconnected_closed_iff.mp heC.2.2.1.isConnected.isPreconnected (closure e') R_other
          isClosed_closure hR_closed he_cov ⟨p₀, hp₀e, subset_closure hp₀⟩ ⟨m₀, hm₀_e, Or.inl hm₀_M⟩
      have hze' : z ∈ e' := hcl_e'_inter_e ▸ ⟨hze, hzcl⟩
      rcases hzR with hzM | hzf
      · exact (Set.eq_empty_iff_forall_notMem.mp hnot_M z) ⟨hzcl, hzM⟩
      · obtain ⟨f, ⟨hfE, hfe'⟩, hzf_cl⟩ := mem_iUnion₂.mp hzf
        have hz_not_DCV : z ∉ D_C.V := (he'.2.1 hze').2
        obtain ⟨c, h1, h2, h3, h4, h5⟩ := GM11.exists_edge_param D_C hfE
        have hc_p : GM07.EdgeParam D_C f c := ⟨h1, h2, h3, h4, h5⟩
        rw [hc_p.closure_eq] at hzf_cl
        obtain ⟨t, rfl⟩ := hzf_cl
        obtain ⟨h6, h7⟩ := hc_p.pos_of_ne hfE hz_not_DCV
        have hzf_in : c t ∈ f := hc_p.mem_edge h6 h7
        exact hfe' (D_C.edge_eq_of_mem hfE he' hzf_in hze')
    -- Attach inner wheel `(E₁, q₁, ℓ₁)` inside `C.ins` at `A_cuff = Z₁ ∪ M ⊆ discBd C.ins`.
    have hA_bd : A_cuff ⊆ discBd C.ins := C.isInside.2.2.1 ▸ hA_sub_CU
    obtain ⟨E₁, q₁, ℓ₁, hE₁, hE₁_int, hw₁, hd₁⟩ := GM07.exists_wheel C.isInside.2.1 hA_bd
    let Q_set : Set SphereSurf := q₁ '' A_cuff
    have hQ_fin : Q_set.Finite := hA_fin.image q₁
    have hQ_dis_G₀ : Disjoint Q_set G₀.U := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨x, hx, rfl⟩ hxU
      exact Set.disjoint_left.mp hG₀_dis_int hxU
        (hE₁_int (Surface.discBd_subset E₁ (hw₁ x hx).1))
    have hQ_arc_empty : arcComponentsIn (Q_set \ Q_set) = ∅ := by
      ext e
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨⟨z, hz⟩, hsub, _⟩
      exact (hsub hz).2 (hsub hz).1
    let Γ_pts : Drawing SphereSurf :=
      { U := Q_set
        V := Q_set
        V_subset_U := Subset.rfl
        isClosed_U := hQ_fin.isClosed
        finite_V := hQ_fin
        finite_edges := by rw [hQ_arc_empty]; exact finite_empty
        edge_cond := fun e he => False.elim (by rw [hQ_arc_empty] at he; exact he) }
    have hglue_pts : G₀.U ∩ Γ_pts.U ⊆ G₀.V ∩ Γ_pts.V := by
      intro x hx
      exact absurd hx.1 (Set.disjoint_left.mp hQ_dis_G₀ hx.2)
    let G₁ := G₀.glue Γ_pts hglue_pts
    have hG₁_U : G₁.U = G₀.U ∪ Q_set := rfl
    have hG₁_V : G₁.V = G₀.V ∪ Q_set := rfl
    have hG₁_E : G₁.E = G₀.E := by
      have hpts_E : Γ_pts.E = ∅ := hQ_arc_empty
      rw [Drawing.glue_E, hpts_E, union_empty]
    have hA_sub_G₁V : A_cuff ⊆ G₁.V := by
      rintro x (hxZ₁ | hxM)
      · exact Or.inl (hG₀_V ▸ Or.inl hxZ₁.1)
      · exact Or.inl (hG₀_V ▸ Or.inr hxM)
    have hl_spec : ∀ x ∈ hA_fin.toFinset,
        IsLineWithEnds (ℓ₁ x) x (q₁ x) ∧ x ≠ q₁ x ∧ x ∈ G₁.V ∧ q₁ x ∈ G₁.V ∧
        ℓ₁ x ∩ G₁.U ⊆ {x, q₁ x} := by
      intro x hx
      have hxA : x ∈ A_cuff := hA_fin.mem_toFinset.mp hx
      obtain ⟨_, hline, hne, hℓ_sub, hℓ_bd, hℓ_E₁⟩ := hw₁ x hxA
      refine ⟨hline, hne, hA_sub_G₁V hxA, Or.inr ⟨x, hxA, rfl⟩, ?_⟩
      rintro z ⟨hzℓ, hzG₁⟩
      rw [hG₁_U] at hzG₁
      rcases hzG₁ with hzG₀ | ⟨y, hyA, rfl⟩
      · have hz_bd : z ∈ discBd C.ins := by
          by_contra hnot_bd
          exact Set.disjoint_left.mp hG₀_dis_int hzG₀ ⟨hℓ_sub hzℓ, hnot_bd⟩
        have : z ∈ ℓ₁ x ∩ discBd C.ins := ⟨hzℓ, hz_bd⟩
        rw [hℓ_bd] at this
        exact Or.inl this
      · have : q₁ y ∈ ℓ₁ x ∩ E₁ := ⟨hzℓ, Surface.discBd_subset E₁ (hw₁ y hyA).1⟩
        rw [hℓ_E₁] at this
        exact Or.inr this
    obtain ⟨Γ', hΓ'U, hΓ'V, hΓ'E⟩ := GM07.exists_add_lines G₁ hA_fin.toFinset ℓ₁ id q₁ hl_spec
      (fun x hx y hy hne => hd₁ x (hA_fin.mem_toFinset.mp hx) y (hA_fin.mem_toFinset.mp hy) hne)
    -- Outer disc `E₀ := closure (univ \ Δ)`.
    let E₀ : Set SphereSurf := closure (univ \ Δ)
    obtain ⟨hE₀, hE₀_bd⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hΔ
    have hint_C_Δ : discInt C.ins ⊆ discInt Δ := by
      intro p hp
      refine ⟨C.isInside.1 hp.1, fun hpbd => ?_⟩
      have hpcl : p ∈ E₀ := Surface.discBd_subset E₀ (hE₀_bd.symm ▸ hpbd)
      obtain ⟨q, hq_in, hq_out⟩ :=
        mem_closure_iff.mp hpcl _ (C.isInside.2.1.isOpen_discInt hman) hp
      exact hq_out.2 (C.isInside.1 hq_in.1)
    have hdis_intC_E₀ : Disjoint (discInt C.ins) E₀ := by
      refine Set.disjoint_left.mpr fun p hp hpcl => ?_
      obtain ⟨q, hq_in, hq_out⟩ :=
        mem_closure_iff.mp hpcl _ (C.isInside.2.1.isOpen_discInt hman) hp
      exact hq_out.2 (C.isInside.1 hq_in.1)
    have hd_E₁_E₀ : Disjoint E₁ E₀ := hdis_intC_E₀.mono_left hE₁_int
    have hE₀_sub_compl : discInt E₀ ⊆ univ \ Δ := by
      intro p ⟨hpcl, hp_not_bd⟩
      refine ⟨mem_univ p, fun hpΔ => ?_⟩
      by_cases hp_bdΔ : p ∈ discBd Δ
      · exact hp_not_bd (hE₀_bd.symm ▸ hp_bdΔ)
      · obtain ⟨q, hq_in, hq_out⟩ :=
          mem_closure_iff.mp hpcl _ (hΔ.isOpen_discInt hman) ⟨hpΔ, hp_bdΔ⟩
        exact hq_out.2 hq_in.1
    have hG₀_sub_Δ : G₀.U ⊆ Δ := by
      rw [hG₀_U]
      exact union_subset (hΓ_cyl_sub_Γ₀.U_subset.trans (hΓ₀_sub.U_subset.trans hDU)) C.U_sub_disc
    have hΓ'_sub_Δ : Γ'.U ⊆ Δ := by
      rw [hΓ'U, hG₁_U]
      refine union_subset (union_subset hG₀_sub_Δ ?_) ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact C.isInside.1 (hE₁_int (Surface.discBd_subset E₁ (hw₁ x hx).1)).1
      · refine iUnion₂_subset fun x hx => ?_
        exact (hw₁ x (hA_fin.mem_toFinset.mp hx)).2.2.2.1.trans C.isInside.1
    have hE₀_inter_Δ : Δ ∩ E₀ ⊆ discBd Δ := by
      rintro p ⟨hpΔ, hpE₀⟩
      by_contra hnot_bd
      obtain ⟨q, hq_in, hq_out⟩ :=
        mem_closure_iff.mp hpE₀ _ (hΔ.isOpen_discInt hman) ⟨hpΔ, hnot_bd⟩
      exact hq_out.2 hq_in.1
    -- Define `K := Q_set ∪ M ∪ K_left` and rank `ρ` (`0` on `Q_set`, `1` on `M`, `dist + 2` on `K_left`).
    let K_cyl := Γ_cyl.toHypergraph.skeleton
    let K_left := Thomas.sepCompLeft K_cyl Γ_cyl.V X Z₁
    have hXV_cyl : X ⊆ Γ_cyl.V := hsep.1
    have hXV_Γ₀ : X ⊆ Γ₀.V := hΓ_cyl_V ▸ hXV_cyl
    have hK_left_sub : K_left ⊆ Γ_cyl.V \ X := Thomas.sepCompLeft_subset_sdiff _ _ _ _
    let K : Set SphereSurf := Q_set ∪ M ∪ K_left
    let P_rk : SphereSurf → ℕ → Prop := fun u n =>
      ∃ z ∈ Z₁ \ X, ∃ p : K_cyl.Walk z u, (∀ w ∈ p.support, w ∈ Γ_cyl.V \ X) ∧ p.length = n
    have hne_rk : ∀ u ∈ K_left, ∃ n, P_rk u n :=
      fun u ⟨_, z, hz, p, hp_w⟩ => ⟨_, z, hz, p, hp_w, rfl⟩
    let ρ : SphereSurf → ℕ := fun u =>
      if u ∈ Q_set then 0 else if u ∈ M then 1 else sInf {n | P_rk u n} + 2
    have hM_sub_G₀U : M ⊆ G₀.U := by
      rw [hG₀_U]
      exact hM_sub_CU.trans subset_union_right
    have hM_dis_Q : Disjoint M Q_set := hQ_dis_G₀.symm.mono_left hM_sub_G₀U
    have hρ_left : ∀ u ∈ K_left, ρ u = sInf {n | P_rk u n} + 2 := by
      intro u hu
      have hu_DV : u ∈ D.V := (hΓ₀_V ▸ hΓ_cyl_V ▸ (hK_left_sub hu).1).1
      have hnotQ : u ∉ Q_set := fun hQ =>
        Set.disjoint_left.mp hQ_dis_G₀ hQ (G₀.V_subset_U (hG₀_V ▸ Or.inl (hΓ_cyl_V ▸ (hK_left_sub hu).1)))
      have hnotM : u ∉ M := fun hM => Set.disjoint_left.mp hM_dis_DV hM hu_DV
      simp [ρ, hnotQ, hnotM]
    have hbd_E₁ : Γ'.U ∩ discBd E₁ ⊆ Γ'.V := by
      rintro p ⟨hpU, hpbd⟩
      rw [hΓ'V, hG₁_V]
      rw [hΓ'U, hG₁_U] at hpU
      rcases hpU with (hpG₀ | hpQ) | hpℓ
      · exact absurd (hE₁_int (Surface.discBd_subset E₁ hpbd))
          (Set.disjoint_left.mp hG₀_dis_int hpG₀)
      · exact Or.inr hpQ
      · obtain ⟨x, hx, hpℓx⟩ := mem_iUnion₂.mp hpℓ
        have hxA : x ∈ A_cuff := hA_fin.mem_toFinset.mp hx
        have : p ∈ ℓ₁ x ∩ E₁ := ⟨hpℓx, Surface.discBd_subset E₁ hpbd⟩
        rw [(hw₁ x hxA).2.2.2.2.2] at this
        exact Or.inr ⟨x, hxA, this.symm⟩
    have hint_E₁ : Disjoint Γ'.U (discInt E₁) := by
      rw [hΓ'U, hG₁_U]
      refine Disjoint.union_left (Disjoint.union_left
        (hG₀_dis_int.mono_right ((discInt_subset E₁).trans hE₁_int)) ?_) ?_
      · refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ hpint
        exact hpint.2 (hw₁ x hx).1
      · refine disjoint_iUnion₂_left.mpr fun x hx => ?_
        have hxA : x ∈ A_cuff := hA_fin.mem_toFinset.mp hx
        refine Set.disjoint_left.mpr fun p hpℓ hpint => ?_
        have : p ∈ ℓ₁ x ∩ E₁ := ⟨hpℓ, hpint.1⟩
        rw [(hw₁ x hxA).2.2.2.2.2, mem_singleton_iff] at this
        exact hpint.2 (this ▸ (hw₁ x hxA).1)
    have hEU : Γ'.U ∩ E₀ ⊆ Γ'.V := by
      rintro p ⟨hpU, hpE₀⟩
      have hp_bdΔ : p ∈ discBd Δ := hE₀_inter_Δ ⟨hΓ'_sub_Δ hpU, hpE₀⟩
      rw [hΓ'V, hG₁_V, hG₀_V]
      rw [hΓ'U, hG₁_U, hG₀_U] at hpU
      rcases hpU with ((hp_cyl | hpCU) | ⟨x, hx, rfl⟩) | hpℓ
      · have hpDV : p ∈ D.V := hprop ⟨hp_bdΔ, hΓ₀_sub.U_subset (hΓ_cyl_sub_Γ₀.U_subset hp_cyl)⟩
        have hp_not_int : p ∉ discInt C.ins := fun hint => (hint_C_Δ hint).2 hp_bdΔ
        exact Or.inl (Or.inl (hΓ₀_V.symm ▸ ⟨hpDV, hp_not_int⟩))
      · have hpDV : p ∈ D.V := hprop ⟨hp_bdΔ, C.U_sub_drawing hpCU⟩
        have hp_not_int : p ∉ discInt C.ins := fun hint => (hint_C_Δ hint).2 hp_bdΔ
        exact Or.inl (Or.inl (hΓ₀_V.symm ▸ ⟨hpDV, hp_not_int⟩))
      · exact absurd hpE₀ (Set.disjoint_left.mp hd_E₁_E₀ (Surface.discBd_subset E₁ (hw₁ x hx).1))
      · obtain ⟨x, hx, hpℓx⟩ := mem_iUnion₂.mp hpℓ
        have hxA : x ∈ A_cuff := hA_fin.mem_toFinset.mp hx
        by_cases hpx : p = x
        · subst hpx
          rcases hxA with hxZ₁ | hxM
          · exact Or.inl (Or.inl hxZ₁.1)
          · exact Or.inl (Or.inr hxM)
        · have hp_intC : p ∈ discInt C.ins :=
            ⟨(hw₁ x hxA).2.2.2.1 hpℓx, fun hbdC =>
              hpx (mem_singleton_iff.mp ((hw₁ x hxA).2.2.2.2.1 ▸ ⟨hpℓx, hbdC⟩))⟩
          exact absurd hp_bdΔ (hint_C_Δ hp_intC).2
    have hEint : Disjoint Γ'.U (discInt E₀) :=
      Set.disjoint_left.mpr fun p hpU hpE₀ => (hE₀_sub_compl hpE₀).2 (hΓ'_sub_Δ hpU)
    have hKV : K ⊆ Γ'.V := by
      rw [hΓ'V, hG₁_V, hG₀_V]
      rintro u ((huQ | huM) | huL)
      · exact Or.inr huQ
      · exact Or.inl (Or.inr huM)
      · exact Or.inl (Or.inl (hΓ_cyl_V ▸ (hK_left_sub huL).1))
    have hXV' : X ⊆ Γ'.V := by
      rw [hΓ'V, hG₁_V, hG₀_V]
      exact hXV_Γ₀.trans (subset_union_left.trans subset_union_left)
    have hXK : Disjoint X K := by
      refine Disjoint.union_right (Disjoint.union_right ?_ ?_)
        (Thomas.disjoint_sepCompLeft_sep _ _ _ _).symm
      · exact Set.disjoint_left.mpr fun x hxX hxQ =>
          Set.disjoint_left.mp hQ_dis_G₀ hxQ
            (G₀.V_subset_U (hG₀_V ▸ Or.inl (hXV_Γ₀ hxX)))
      · exact Set.disjoint_left.mpr fun x hxX hxM =>
          Set.disjoint_left.mp hM_dis_DV hxM (hΓ₀_sub.1 (hXV_Γ₀ hxX))
    have hcuff : Γ'.V ∩ discBd E₁ ⊆ K ∪ X := by
      rintro p ⟨hpV, hpbd⟩
      rw [hΓ'V, hG₁_V] at hpV
      rcases hpV with hpG₀ | hpQ
      · exact absurd (hE₁_int (Surface.discBd_subset E₁ hpbd))
          (Set.disjoint_left.mp hG₀_dis_int (G₀.V_subset_U hpG₀))
      · exact Or.inl (Or.inl (Or.inl hpQ))
    have hKE : Disjoint K E₀ := by
      refine Disjoint.union_left (Disjoint.union_left ?_ ?_) ?_
      · refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ hpE₀
        exact Set.disjoint_left.mp hd_E₁_E₀ (Surface.discBd_subset E₁ (hw₁ x hx).1) hpE₀
      · refine Set.disjoint_left.mpr fun m hmM hmE₀ => ?_
        have hm_bdΔ : m ∈ discBd Δ := hE₀_inter_Δ ⟨C.U_sub_disc (hM_sub_CU hmM), hmE₀⟩
        exact Set.disjoint_left.mp hM_dis_DV hmM (hprop ⟨hm_bdΔ, C.U_sub_drawing (hM_sub_CU hmM)⟩)
      · refine Set.disjoint_left.mpr fun u huL huE₀ => ?_
        have hu_Γ₀ : u ∈ Γ₀.V := hΓ_cyl_V ▸ (hK_left_sub huL).1
        have hu_bdΔ : u ∈ discBd Δ :=
          hE₀_inter_Δ ⟨hDU (D.V_subset_U (hΓ₀_sub.1 hu_Γ₀)), huE₀⟩
        have huZ₂ : u ∈ Z₂ := ⟨hu_Γ₀, hu_bdΔ⟩
        obtain ⟨_, z, hz, p_w, hp_w⟩ := huL
        obtain ⟨w, hw_sup, hwX⟩ := hsep.2 hz.1 huZ₂ p_w fun w hw => (hp_w w hw).1
        exact (hp_w w hw_sup).2 hwX
    have hZ₁_sub_KX : Z₁ ⊆ K ∪ X := by
      intro x hxZ₁
      by_cases hxX : x ∈ X
      · exact Or.inr hxX
      · have hx_cyl : x ∈ Γ_cyl.V := hΓ_cyl_V.symm ▸ hxZ₁.1
        refine Or.inl (Or.inr ⟨⟨hx_cyl, hxX⟩, x, ⟨hxZ₁, hxX⟩, .nil, fun y hy => ?_⟩)
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
        exact hy ▸ ⟨hx_cyl, hxX⟩
    have hedge : ∀ e ∈ Γ'.E, ∀ u ∈ K, u ∈ closure e → ∀ w ∈ Γ'.V, w ∈ closure e → w ∈ K ∪ X := by
      intro e he u hu huc w hw hwc
      by_cases huw : u = w
      · exact Or.inl (huw ▸ hu)
      rw [hΓ'E, hG₁_E, hG₀_E] at he
      rcases he with (he_cyl | he_DC) | ⟨x, hx, rfl⟩
      · -- `e ∈ Γ_cyl.E`: `closure e ⊆ Γ_cyl.U`, disjoint from `Q_set` and from `M`.
        have hcle_cyl : closure e ⊆ Γ_cyl.U :=
          closure_minimal (fun p hp => (he_cyl.2.1 hp).1) Γ_cyl.isClosed_U
        have hcle_notQ : ∀ z ∈ closure e, z ∉ Q_set := fun z hz hQ =>
          Set.disjoint_left.mp hQ_dis_G₀ hQ (hG₀_U ▸ Or.inl (hcle_cyl hz))
        have hcle_notM : ∀ z ∈ closure e, z ∉ M := fun z hz hM => by
          have hzZ₁ : z ∈ Z₁ :=
            hΓ_cyl_cap_C ▸ ⟨hcle_cyl hz,
              Surface.discBd_subset C.ins (C.isInside.2.2.1 ▸ hM_sub_CU hM)⟩
          exact Set.disjoint_left.mp hM_dis_DV hM (hΓ₀_sub.1 hzZ₁.1)
        have huL : u ∈ K_left := by
          rcases hu with (huQ | huM) | huL
          · exact absurd huc (fun h => hcle_notQ u h huQ)
          · exact absurd huc (fun h => hcle_notM u h huM)
          · exact huL
        have hw_cyl : w ∈ Γ_cyl.V := by
          rw [hΓ'V, hG₁_V, hG₀_V, ← hΓ_cyl_V] at hw
          rcases hw with (hw_cyl | hwM) | hwQ
          · exact hw_cyl
          · exact absurd hwc (fun h => hcle_notM w h hwM)
          · exact absurd hwc (fun h => hcle_notQ w h hwQ)
        by_contra hn
        have hw_right : w ∈ Thomas.sepCompRight K_cyl Γ_cyl.V X Z₁ :=
          ⟨⟨hw_cyl, fun h => hn (Or.inr h)⟩, fun h => hn (Or.inl (Or.inr h))⟩
        exact Thomas.not_adj_sepCompLeft_sepCompRight huL hw_right
          ⟨huw, e, ⟨he_cyl, (hK_left_sub huL).1, huc⟩, ⟨he_cyl, hw_cyl, hwc⟩⟩
      · -- `e ∈ D_C.E`: `closure e ⊆ C.U`, so `w ∈ C.U ∩ Γ'.V = Z₁ ∪ M ⊆ K ∪ X`.
        have hcle_CU : closure e ⊆ C.U :=
          hDC_U ▸ closure_minimal (fun p hp => (he_DC.2.1 hp).1) D_C.isClosed_U
        have hw_CU : w ∈ C.U := hcle_CU hwc
        rw [hΓ'V, hG₁_V, hG₀_V] at hw
        rcases hw with (hwΓ₀ | hwM) | hwQ
        · exact hZ₁_sub_KX ⟨hwΓ₀, hw_CU⟩
        · exact Or.inl (Or.inl (Or.inr hwM))
        · exact absurd (hG₀_U ▸ Or.inr hw_CU) (Set.disjoint_left.mp hQ_dis_G₀ hwQ)
      · -- Spoke `e = ℓ₁ x \ {x, q₁ x}` with `x ∈ Z₁ ∪ M`.
        have hxA : x ∈ A_cuff := hA_fin.mem_toFinset.mp hx
        have hcl_ℓ : closure (ℓ₁ x \ {x, q₁ x}) = ℓ₁ x :=
          GM11.closure_sdiff_pair (hw₁ x hxA).2.1
        dsimp only [id] at hwc
        rw [hcl_ℓ] at hwc
        have hwc_end : w = x ∨ w = q₁ x := by
          rw [hΓ'V] at hw
          exact (hl_spec x hx).2.2.2.2 ⟨hwc, G₁.V_subset_U hw⟩
        rcases hwc_end with rfl | rfl
        · rcases hxA with hxZ₁ | hxM
          · exact hZ₁_sub_KX hxZ₁
          · exact Or.inl (Or.inl (Or.inr hxM))
        · exact Or.inl (Or.inl (Or.inl ⟨x, hxA, rfl⟩))
    have hreach : ∀ u ∈ K, u ∉ discBd E₁ →
        ∃ e ∈ Γ'.E, ∃ w ∈ K, w ≠ u ∧ u ∈ closure e ∧ w ∈ closure e ∧
          (w ∉ discBd E₁ → ρ w < ρ u) := by
      intro u hu hub
      rcases hu with (⟨x, hxA, rfl⟩ | huM) | huL
      · exact absurd (hw₁ x hxA).1 hub
      · -- `u ∈ M ⊆ A_cuff`: step along spoke `ℓ₁ u` to `q₁ u ∈ discBd E₁`.
        have huA : u ∈ A_cuff := Or.inr huM
        have hu_fin : u ∈ hA_fin.toFinset := hA_fin.mem_toFinset.mpr huA
        have he_mem : ℓ₁ u \ {u, q₁ u} ∈ Γ'.E := hΓ'E ▸ Or.inr ⟨u, hu_fin, rfl⟩
        have hcl_ℓ : closure (ℓ₁ u \ {u, q₁ u}) = ℓ₁ u :=
          GM11.closure_sdiff_pair (hw₁ u huA).2.1
        refine ⟨ℓ₁ u \ {u, q₁ u}, he_mem, q₁ u, Or.inl (Or.inl ⟨u, huA, rfl⟩),
          (hw₁ u huA).2.2.1.symm, by rw [hcl_ℓ]; exact (hw₁ u huA).2.1.left_mem,
          by rw [hcl_ℓ]; exact (hw₁ u huA).2.1.right_mem,
          fun hnot => absurd (hw₁ u huA).1 hnot⟩
      · have hρu := Nat.sInf_mem (hne_rk u huL)
        obtain ⟨z, hz, p_w, hp_w, hlen⟩ := hρu
        by_cases huz : u = z
        · subst huz
          have huA : u ∈ A_cuff := Or.inl hz.1
          have hu_fin : u ∈ hA_fin.toFinset := hA_fin.mem_toFinset.mpr huA
          have he_mem : ℓ₁ u \ {u, q₁ u} ∈ Γ'.E := hΓ'E ▸ Or.inr ⟨u, hu_fin, rfl⟩
          have hcl_ℓ : closure (ℓ₁ u \ {u, q₁ u}) = ℓ₁ u :=
            GM11.closure_sdiff_pair (hw₁ u huA).2.1
          refine ⟨ℓ₁ u \ {u, q₁ u}, he_mem, q₁ u, Or.inl (Or.inl ⟨u, huA, rfl⟩),
            (hw₁ u huA).2.2.1.symm, by rw [hcl_ℓ]; exact (hw₁ u huA).2.1.left_mem,
            by rw [hcl_ℓ]; exact (hw₁ u huA).2.1.right_mem,
            fun hnot => absurd (hw₁ u huA).1 hnot⟩
        · obtain ⟨w, hadj, q_w, hq_w⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huz p_w.reverse
          obtain ⟨huw, e, h1, h2⟩ := hadj
          have hsup : ∀ y ∈ q_w.support, y ∈ Γ_cyl.V \ X := fun y hy => hp_w y (by
            have : y ∈ p_w.reverse.support := by
              rw [hq_w]
              exact List.mem_cons_of_mem _ hy
            rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at this)
          have hsup' : ∀ y ∈ q_w.reverse.support, y ∈ Γ_cyl.V \ X :=
            fun y hy => hsup y (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hy)
          have hwL : w ∈ K_left := ⟨hsup w q_w.start_mem_support, z, hz, q_w.reverse, hsup'⟩
          have he_mem : e ∈ Γ'.E := by
            rw [hΓ'E, hG₁_E, hG₀_E]
            exact Or.inl (Or.inl h1.1)
          refine ⟨e, he_mem, w, Or.inr hwL, huw.symm, h1.2.2, h2.2.2, fun _ => ?_⟩
          rw [hρ_left w hwL, hρ_left u huL]
          have hle : sInf {n | P_rk w n} ≤ q_w.length := by
            simpa [SimpleGraph.Walk.length_reverse] using
              (Nat.sInf_le ⟨z, hz, q_w.reverse, hsup', rfl⟩ :
                sInf {n | P_rk w n} ≤ q_w.reverse.length)
          have hlen_eq : p_w.length = q_w.length + 1 := by
            have h3 : p_w.reverse.length = q_w.length + 1 := by rw [hq_w]; rfl
            rwa [SimpleGraph.Walk.length_reverse] at h3
          have hlen_u : p_w.length = sInf {n | P_rk u n} := hlen
          omega
    obtain ⟨B, hB, hE₁_sub_B, hdis_E₀_B, hbdB_X⟩ :=
      GM07.exists_disc_of_side hS hsph Γ' hE₁ hE₀ hd_E₁_E₀ hbd_E₁ hint_E₁ hEU hEint
        hKV hXV' hXK hcuff hKE hedge hreach
    have hB_sub_Δ : B ⊆ Δ := by
      intro p hpB
      by_contra hp_not_Δ
      have hp_intE₀ : p ∈ discInt E₀ :=
        ⟨subset_closure ⟨mem_univ p, hp_not_Δ⟩,
          fun hpbd => hp_not_Δ (Surface.discBd_subset Δ (hE₀_bd ▸ hpbd))⟩
      exact Set.disjoint_left.mp hdis_E₀_B hp_intE₀ hpB
    -- Every `x ∈ A_cuff = Z₁ ∪ M` lies in `B` via its spoke `ℓ₁ x`.
    have hA_sub_B : A_cuff ⊆ B := by
      intro x hxA
      by_contra hx_not_B
      obtain ⟨_, hline, _, _, _, _⟩ := hw₁ x hxA
      have hℓ_sub_U : ℓ₁ x ⊆ Γ'.U := by
        rw [hΓ'U]
        exact subset_union_of_subset_right
          (subset_biUnion_of_mem (hA_fin.mem_toFinset.mpr hxA)) _
      have hconn_ℓ : IsPreconnected (ℓ₁ x) := (GM07.isConnected_line hline).isPreconnected
      have hnot_dis : ¬ Disjoint (ℓ₁ x) (discBd B) := by
        intro hdis
        rcases hB.side hman hconn_ℓ hdis with hin | hout
        · exact hx_not_B (hin.trans (discInt_subset B) hline.left_mem)
        · exact Set.disjoint_left.mp hout hline.right_mem
            (hE₁_sub_B (Surface.discBd_subset E₁ (hw₁ x hxA).1))
      obtain ⟨z, hzℓ, hzbdB⟩ := Set.not_disjoint_iff.mp hnot_dis
      have hzX : z ∈ X := hbdB_X ⟨hzbdB, hℓ_sub_U hzℓ⟩
      have hz_cap : z ∈ {x, q₁ x} :=
        (hl_spec x (hA_fin.mem_toFinset.mpr hxA)).2.2.2.2
          ⟨hzℓ, Or.inl (G₀.V_subset_U (hG₀_V ▸ Or.inl (hXV_Γ₀ hzX)))⟩
      rcases hz_cap with rfl | rfl
      · exact hx_not_B (Surface.discBd_subset B hzbdB)
      · exact Set.disjoint_left.mp hQ_dis_G₀ ⟨x, hxA, rfl⟩
          (G₀.V_subset_U (hG₀_V ▸ Or.inl (hXV_Γ₀ hzX)))
    -- Every `m ∈ M` lies in `discInt B` (since `m ∈ B ∩ Γ'.U` and `m ∉ X`).
    have hM_sub_intB : M ⊆ discInt B := by
      intro m hmM
      refine ⟨hA_sub_B (Or.inr hmM), fun hmbd => ?_⟩
      have hm_Γ'U : m ∈ Γ'.U :=
        hΓ'U ▸ subset_union_left (Or.inl (hG₀_U ▸ Or.inr (hM_sub_CU hmM)))
      have hmX : m ∈ X := hbdB_X ⟨hmbd, hm_Γ'U⟩
      exact Set.disjoint_left.mp hM_dis_DV hmM (hΓ₀_sub.1 (hXV_Γ₀ hmX))
    -- Every edge `e' ∈ D_C.E` has an endpoint in `M ⊆ discInt B`, hence `e' ⊆ discInt B`.
    have hCU_sub_B : C.U ⊆ B := by
      rw [← hDC_U, Drawing.U_eq, hDC_V]
      refine union_subset hA_sub_B (iUnion₂_subset fun e' he' => ?_)
      obtain ⟨m, hmcl, hmM⟩ := hDC_edge_meets_M e' he'
      have hm_intB : m ∈ discInt B := hM_sub_intB hmM
      have he'_dis_bdB : Disjoint e' (discBd B) := by
        refine Set.disjoint_left.mpr fun p hpe' hpbdB => ?_
        have hp_Γ'U : p ∈ Γ'.U :=
          hΓ'U ▸ subset_union_left (Or.inl (hG₀_U ▸ Or.inr (hDC_U ▸ (he'.2.1 hpe').1)))
        have hpX : p ∈ X := hbdB_X ⟨hpbdB, hp_Γ'U⟩
        have hp_Z₁ : p ∈ Z₁ := ⟨hXV_Γ₀ hpX, hDC_U ▸ (he'.2.1 hpe').1⟩
        exact (he'.2.1 hpe').2 (hDC_V ▸ Or.inl hp_Z₁)
      rcases hB.side hman he'.2.2.1.isConnected.isPreconnected he'_dis_bdB with hin | hout
      · exact closure_minimal (hin.trans (discInt_subset B)) hB.isClosed
      · exfalso
        obtain ⟨q, hq_intB, hqe'⟩ :=
          mem_closure_iff.mp hmcl _ (hB.isOpen_discInt hman) hm_intB
        exact Set.disjoint_left.mp hout hqe' hq_intB.1
    -- Now `C.ins ⊆ B` and `discInt C.ins ⊆ discInt B`!
    obtain ⟨B_ins, hB_ins₀, hB_uniq⟩ := disc_oArc Δ (discBd B) hΔ
      ((Surface.discBd_subset B).trans hB_sub_Δ) hB.isOArc_discBd
    have hB_ins : IsInsideDisc Δ (discBd B) B := (hB_uniq B hB_sub_Δ hB rfl).symm ▸ hB_ins₀
    have henc_B_C : OArcEncloses Δ (discBd B) C.U :=
      (oArcEncloses_iff_subset hΔ hB_ins).mpr hCU_sub_B
    have hC_sub_B : C.ins ⊆ B ∧ discInt C.ins ⊆ discInt B :=
      insideDisc_subset_of_oArcEncloses hΔ hB_ins C.isInside henc_B_C
    -- `discBd B` is `D`-normal and `D.V ∩ discBd B ⊆ X`!
    have hbdB_cap_DU : discBd B ∩ D.U ⊆ X := by
      rintro p ⟨hpbdB, hpDU⟩
      have hp_not_intC : p ∉ discInt C.ins := fun hint => (hC_sub_B.2 hint).2 hpbdB
      have hp_G₀U : p ∈ G₀.U := hDU_sub_G₀ ⟨hpDU, hp_not_intC⟩
      exact hbdB_X ⟨hpbdB, hΓ'U ▸ subset_union_left (Or.inl hp_G₀U)⟩
    have hbdB_norm : D.IsNormal (discBd B) :=
      fun p hp => hΓ₀_sub.1 (hXV_Γ₀ (hbdB_cap_DU hp))
    have hDV_bdB_sub_X : D.V ∩ discBd B ⊆ X :=
      fun p ⟨hpDV, hpbdB⟩ => hbdB_cap_DU ⟨hpbdB, D.V_subset_U hpDV⟩
    have hrho_le : circuitRho C ≤ (D.V ∩ discBd B).ncard :=
      Nat.sInf_le ⟨discBd B, (Surface.discBd_subset B).trans hB_sub_Δ, hB.isOArc_discBd,
        hbdB_norm, henc_B_C, rfl⟩
    have hncard_le : (D.V ∩ discBd B).ncard ≤ X.ncard :=
      Set.ncard_le_ncard hDV_bdB_sub_X (Γ_cyl.finite_V.subset hXV_cyl)
    omega

/-- Menger's theorem for `circuitRho` in any closed disc `Δ ⊆ S`: if `r ≤ circuitRho C` and
`D.IsNormal (discBd Δ)`, there are `r` pairwise vertex-disjoint path subdrawings of `D` between
`C.U` and `discBd Δ`. -/
theorem exists_disjoint_paths_of_circuitRho {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hprop : D.IsNormal (discBd Δ))
    (C : DiscCircuit D Δ) {r : ℕ} (hr : r ≤ circuitRho C) :
    ∃ (P : Fin r → Drawing S) (u v : Fin r → S),
      (∀ i, (P i).IsSubdrawing D ∧ u i ∈ C.U ∧ v i ∈ discBd Δ ∧ (P i).IsPathBetween (u i) (v i)) ∧
      Pairwise (fun i j => Disjoint (P i).V (P j).V) := by
  classical
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, _, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  obtain ⟨hΔ', hbdΔ'⟩ := sc.disc_f Subset.rfl hΔ
  have hD'U_sub : D'.U ⊆ f '' Δ := hD'U ▸ image_mono hDU
  have hprop' : D'.IsNormal (discBd (f '' Δ)) := by
    rw [hbdΔ']
    exact (sc.isNormal_f_iff hDU hD'U hD'V (Surface.discBd_subset Δ)).mpr hprop
  let C' := sc.pushDiscCircuit hΔ hD'U C
  have hr' : r ≤ circuitRho C' := by
    rwa [sc.circuitRho_pushDiscCircuit hΔ hDU hD'U hD'V C]
  obtain ⟨P', u', v', hP', hP'dis⟩ :=
    exists_disjoint_paths_of_circuitRho_sphere hΔ' hD'U_sub hprop' C' hr'
  have hex : ∀ i : Fin r, ∃ P_i : Drawing S, ∃ u_i v_i : S,
      P_i.IsSubdrawing D ∧ u_i ∈ C.U ∧ v_i ∈ discBd Δ ∧ P_i.IsPathBetween u_i v_i ∧
      P_i.V = f' '' (P' i).V := by
    intro i
    obtain ⟨hP'sub, hu', hv', hP'path⟩ := hP' i
    obtain ⟨P_i, hPsub, _, hPV, hPE, _, hL, _⟩ :=
      sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E hP'sub
    have hP'U_Δ : (P' i).U ⊆ f '' Δ := hP'sub.U_subset.trans hD'U_sub
    obtain ⟨u_i, huC, hfu_eq⟩ := hu'
    obtain ⟨v_i, hvBd, hfv_eq⟩ := hbdΔ' ▸ hv'
    have hfu : f' (u' i) = u_i := by rw [← hfu_eq]; exact sc.f'f (C.U_sub_disc huC)
    have hfv : f' (v' i) = v_i := by rw [← hfv_eq]; exact sc.f'f (Surface.discBd_subset Δ hvBd)
    refine ⟨P_i, u_i, v_i, hPsub, huC, hvBd, ?_, hPV⟩
    rw [← hfu, ← hfv]
    exact sc.isPathBetween_of_pullback hP'U_Δ hPV hPE hL hP'path
  choose P u v hPsub hu hv hPpath hPV using hex
  refine ⟨P, u, v, fun i => ⟨hPsub i, hu i, hv i, hPpath i⟩, fun i j hne => ?_⟩
  dsimp only
  rw [hPV i, hPV j]
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
  have hpΔ : p ∈ f '' Δ := hD'U_sub (D'.V_subset_U ((hP' i).1.1 hp))
  have hqΔ : q ∈ f '' Δ := hD'U_sub (D'.V_subset_U ((hP' j).1.1 hq))
  obtain rfl := sc.injOn_f' hqΔ hpΔ heq
  exact Set.disjoint_left.mp (hP'dis hne) hp hq

/-- Trim a path subdrawing `P` of `D` between `u ∈ C` (where `C` is inside `F`) and `v ∈ discBd Δ`
at its first vertex in a `D`-normal O-arc `F ⊆ Δ`, producing a subdrawing `P'` of `P` that is a
path between `u` and some `v' ∈ F`. -/
theorem exists_trimmed_spoke_to_enclosing {S : Type u} [TopologicalSpace S]
    {D P : Drawing S} {Δ F : Set S} {u v : S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hFΔ : F ⊆ Δ) (hFo : IsOArc F) (hFnorm : D.IsNormal F)
    (hPsub : P.IsSubdrawing D) (hu_in : InsideOArc Δ F u) (hv_bd : v ∈ discBd Δ)
    (hPpath : P.IsPathBetween u v) :
    ∃ (P' : Drawing S) (v' : S),
      P'.IsSubdrawing P ∧ P'.IsSubdrawing D ∧ v' ∈ F ∧ P'.IsPathBetween u v' := by
  classical
  -- Transport to `SphereSurf` to find a vertex of `P` in `F`, then cut in `S`? Wait: cutting a walk
  -- needs `[T1Space S]` if using `walkDrawing P W₁` directly in `S`; instead cut on `SphereSurf` and
  -- pull back `P'` via `sc.exists_pullback_subdrawing`!
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, _, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  obtain ⟨P'₀, hP'₀sub, hP'₀U, hP'₀V, hP'₀E, _, hLP, _⟩ :=
    sc.exists_push_subdrawing hΔ hDU hD'V hD'E hPsub
  obtain ⟨hΔ', hbdΔ'⟩ := sc.disc_f Subset.rfl hΔ
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hsph : Surface.IsSphere SphereSurf := ⟨Homeomorph.refl _⟩
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  have huΔ : u ∈ Δ := by
    obtain ⟨W, _, hV, _⟩ := hPpath
    exact hDU (D.V_subset_U (hPsub.1 (hV ▸ W.start_mem_support)))
  have hF'Δ : f '' F ⊆ f '' Δ := image_mono hFΔ
  have hF'o : IsOArc (f '' F) := sc.oArc_f hFΔ hFo
  have hF'norm : D'.IsNormal (f '' F) := (sc.isNormal_f_iff hDU hD'U hD'V hFΔ).mpr hFnorm
  obtain ⟨D_F', hD_F', _⟩ := disc_oArc (f '' Δ) (f '' F) hΔ' hF'Δ hF'o
  have hfu_in : f u ∈ discInt D_F' :=
    (insideOArc_iff_mem_discInt hΔ' hD_F').mp ((sc.insideOArc_f_iff hΔ hFΔ hFo huΔ).mpr hu_in)
  have hfv_bd : f v ∈ discBd (f '' Δ) := hbdΔ' ▸ mem_image_of_mem f hv_bd
  have hfv_not_int : f v ∉ discInt D_F' := by
    intro hint
    have hint_Δ : discInt D_F' ⊆ discInt (f '' Δ) :=
      discInt_mono hman hD_F'.2.1 hD_F'.1
    exact (hint_Δ hint).2 hfv_bd
  have hP'₀path : P'₀.IsPathBetween (f u) (f v) :=
    sc.isPathBetween_of_push (hPsub.U_subset.trans hDU) hP'₀V hP'₀E hLP hPpath
  obtain ⟨W', hW', hV', _⟩ := hP'₀path
  -- Walk `W'` from `f u ∈ discInt D_F'` to `f v ∉ discInt D_F'` must hit `f '' F = discBd D_F'`.
  have hex_hit : ∃ w' ∈ W'.support, w' ∈ f '' F := by
    by_contra! hall
    have hstay : ∀ {a b : SphereSurf} (W₀ : GraphWalk P'₀.toGraph a b),
        a ∈ discInt D_F' → (∀ w' ∈ W₀.support, w' ∉ f '' F) → b ∈ discInt D_F' := by
      intro a b W₀ ha hno
      induction W₀ with
      | nil _ => exact ha
      | @cons a c b e hl rest ih =>
        have heD' : e ∈ D'.E := hP'₀sub.2 hl.1
        have he_dis_F' : Disjoint e (discBd D_F') := by
          rw [hD_F'.2.2.1]
          refine Set.disjoint_left.mpr fun p hpe hpF' => ?_
          exact (heD'.2.1 hpe).2 (hF'norm ⟨hpF', (heD'.2.1 hpe).1⟩)
        have ha_cl : a ∈ closure e := (hl.2.2.2 ▸ (by simp : a ∈ ({a, c} : Set _))).1
        have hc_cl : c ∈ closure e := (hl.2.2.2 ▸ (by simp : c ∈ ({a, c} : Set _))).1
        have he_sub : e ⊆ discInt D_F' := by
          rcases hD_F'.2.1.side hman heD'.2.2.1.isConnected.isPreconnected he_dis_F' with hin | hout
          · exact hin
          · exfalso
            obtain ⟨q, hq_in, hqe⟩ :=
              mem_closure_iff.mp ha_cl _ (hD_F'.2.1.isOpen_discInt hman) ha
            exact Set.disjoint_left.mp hout hqe hq_in.1
        have hc_DF' : c ∈ D_F' :=
          closure_minimal (he_sub.trans (discInt_subset D_F')) hD_F'.2.1.isClosed hc_cl
        have hc_not_F' : c ∉ f '' F :=
          hno c (by simp [GraphWalk.support_cons, rest.start_mem_support])
        have hc_int : c ∈ discInt D_F' := ⟨hc_DF', hD_F'.2.2.1 ▸ hc_not_F'⟩
        exact ih hc_int fun w' hw' => hno w' (by simp [GraphWalk.support_cons, hw'])
    exact hfv_not_int (hstay W' hfu_in hall)
  obtain ⟨v'₀, hv'₀F, W₁, W₂, hWeq, _⟩ := GM09.PlanarNests.exists_first_hit_split W' hex_hit
  subst hWeq
  obtain ⟨hW₁s, _⟩ := GM09.isSimple_of_append hW'
  let Q' := GM11.walkDrawing P'₀ W₁
  have hQ'_sub_P'₀ : Q'.IsSubdrawing P'₀ := GM11.walkDrawing_isSubdrawing P'₀ W₁
  have hQ'_sub_D' : Q'.IsSubdrawing D' := hQ'_sub_P'₀.trans hP'₀sub
  have hQ'_path : Q'.IsPathBetween (f u) v'₀ := GM11.walkDrawing_isPathBetween P'₀ hW₁s
  obtain ⟨P₁, hP₁_sub_D, _, hP₁V, hP₁E, _, hL₁, _⟩ :=
    sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E hQ'_sub_D'
  have hQ'U_Δ : Q'.U ⊆ f '' Δ := hQ'_sub_D'.U_subset.trans (hD'U ▸ image_mono hDU)
  obtain ⟨v', hv'F, rfl⟩ := hv'₀F
  have hfu : f' (f u) = u := sc.f'f huΔ
  have hfv' : f' (f v') = v' := sc.f'f (hFΔ hv'F)
  have hP₁_sub_P : P₁.IsSubdrawing P := by
    refine ⟨?_, ?_⟩
    · rw [hP₁V]
      have : f' '' Q'.V ⊆ f' '' P'₀.V := image_mono hQ'_sub_P'₀.1
      rwa [hP'₀V, sc.f'_f (P.V_subset_U.trans (hPsub.U_subset.trans hDU))] at this
    · rw [hP₁E]
      rintro _ ⟨e', he', rfl⟩
      obtain ⟨e, heP, rfl⟩ := hP'₀E ▸ hQ'_sub_P'₀.2 he'
      have heΔ : e ⊆ Δ := fun x hx => hDU (hPsub.U_subset (heP.2.1 hx).1)
      rwa [sc.f'_f heΔ]
  refine ⟨P₁, v', hP₁_sub_P, hP₁_sub_D, hv'F, ?_⟩
  rw [← hfu, ← hfv']
  exact sc.isPathBetween_of_pullback hQ'U_Δ hP₁V hP₁E hL₁ hQ'_path

end CircuitRhoPaths

end GM08
end GraphMinor
