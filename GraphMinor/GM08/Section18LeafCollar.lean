module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Taper
import GraphMinor.GM07.Section11f
import GraphMinor.GM07.CutBounds
import GraphMinor.GM11.Fan
import GraphMinor.Surface.Cuffs
import GraphMinor.Surface.Classification

/-!
# A collar of the whole boundary, with spokes

To correct the proof of VIII (18.1) we draw every root of a graft as a leaf.
For this we need a collar of the boundary. Each boundary point `x` gets a
spoke, a short line in the collar from `x` up to a point `e x`. The map `e`
pushes the whole surface into the part above the spokes. The map `g`
collapses each spoke onto its top point `e x` and fixes everything above. It is
homotopic to the identity by a homotopy `Φ`.

We build this one cuff at a time. For one cuff we take a collar `b` from
`exists_collar`, inside an open set that misses the other cuffs and the part
already built, and use `exists_collar_glue` for the two maps of heights:
`t ↦ (1 + t) / 2` for `e` and `t ↦ max t (p / 2)` for the homotopy.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

local notation "𝕀" => unitInterval

variable {S : Type u} [TopologicalSpace S]

/-- A collar of the boundary part `B`, with a spoke at each point of `B`.
The set `N` holds everything that moves. -/
structure BoundaryCollar (S : Type u) [TopologicalSpace S] (B : Set S) where
  /-- The push into the part above the spokes. -/
  e : S → S
  /-- The collapse of each spoke onto its top point. -/
  g : S → S
  /-- A homotopy from the identity to `g`. -/
  Φ : 𝕀 × S → S
  /-- The spoke at a boundary point. -/
  sp : S → Set S
  /-- A closed set holding everything that moves. -/
  N : Set S
  isClosed_N : IsClosed N
  cont_e : Continuous e
  inj_e : Injective e
  cont_Φ : Continuous Φ
  Φ_zero : ∀ x, Φ (0, x) = x
  Φ_one : ∀ x, Φ (1, x) = g x
  fix : ∀ y, y ∉ N → e y = y ∧ ∀ t, Φ (t, y) = y
  mapsTo : ∀ y ∈ N, e y ∈ N ∧ ∀ t, Φ (t, y) ∈ N
  B_subset : B ⊆ N
  N_bd : N ∩ bd S ⊆ B
  g_e : ∀ y, g (e y) = e y
  cover : ∀ y, y ∈ range e ∨ ∃ x ∈ B, y ∈ sp x ∧ g y = e x
  e_bd : ∀ y, e y ∈ bd S → y ∉ N
  line : ∀ x ∈ B, IsLineWithEnds (sp x) (e x) x
  ne : ∀ x ∈ B, e x ≠ x
  sp_range : ∀ x ∈ B, sp x ∩ range e = {e x}
  sp_bd : ∀ x ∈ B, sp x ∩ bd S = {x}
  sp_N : ∀ x ∈ B, sp x ⊆ N
  disjoint : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → Disjoint (sp x) (sp y)

/-- The empty collar. -/
def BoundaryCollar.empty (S : Type u) [TopologicalSpace S] : BoundaryCollar S ∅ where
  e := id
  g := id
  Φ := Prod.snd
  sp := fun _ => ∅
  N := ∅
  isClosed_N := isClosed_empty
  cont_e := continuous_id
  inj_e := injective_id
  cont_Φ := continuous_snd
  Φ_zero := fun _ => rfl
  Φ_one := fun _ => rfl
  fix := fun _ _ => ⟨rfl, fun _ => rfl⟩
  mapsTo := fun _ h => h.elim
  B_subset := Subset.rfl
  N_bd := fun _ h => h.1
  g_e := fun _ => rfl
  cover := fun y => .inl ⟨y, rfl⟩
  e_bd := fun _ _ h => h
  line := fun _ h => h.elim
  ne := fun _ h => h.elim
  sp_range := fun _ h => h.elim
  sp_bd := fun _ h => h.elim
  sp_N := fun _ h => h.elim
  disjoint := fun _ h => h.elim

/-- Half of `1 + t`, as a height. -/
noncomputable def upHalf (t : 𝕀) : 𝕀 := ⟨(1 + t.1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- Half of `1 - t`, as a height. -/
noncomputable def downHalf (t : 𝕀) : 𝕀 := ⟨(1 - t.1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

/-- The height `max t (p / 2)`. -/
noncomputable def liftTo (p t : 𝕀) : 𝕀 := ⟨max t.1 (p.1 / 2), by
  constructor
  · exact le_max_of_le_left t.2.1
  · exact max_le t.2.2 (by linarith [p.2.2])⟩

theorem continuous_upHalf : Continuous upHalf :=
  (by fun_prop : Continuous fun t : 𝕀 => (1 + t.1) / 2).subtype_mk _

theorem continuous_downHalf : Continuous downHalf :=
  (by fun_prop : Continuous fun t : 𝕀 => (1 - t.1) / 2).subtype_mk _

theorem continuous_liftTo : Continuous fun q : 𝕀 × 𝕀 => liftTo q.1 q.2 :=
  (by fun_prop : Continuous fun q : 𝕀 × 𝕀 => max q.2.1 (q.1.1 / 2)).subtype_mk _

/-- **Adding one cuff to a boundary collar.** -/
theorem BoundaryCollar.exists_add [T2Space S] [CompactSpace S] (hS : IsSurface S)
    {B C : Set S} (K : BoundaryCollar S B) (hC : C ∈ cuffs S) (hCB : Disjoint C B) :
    Nonempty (BoundaryCollar S (B ∪ C)) := by
  classical
  have hCbd : C ⊆ bd S := GM07.connectedComponentIn_subset_of_cuff hC
  have hCN : Disjoint C K.N := by
    refine disjoint_left.mpr fun x hxC hxN => disjoint_left.mp hCB hxC (K.N_bd ⟨hxN, hCbd hxC⟩)
  let U : Set S := K.Nᶜ ∩ (bd S \ C)ᶜ
  have hU : IsOpen U := K.isClosed_N.isOpen_compl.inter (GM07.isClosed_bd_diff_cuff hS hC).isOpen_compl
  have hCU : C ⊆ U := fun x hx => ⟨disjoint_left.mp hCN hx, fun h => h.2 hx⟩
  obtain ⟨φ⟩ := (cuff_statement S hS).2.2 C hC
  obtain ⟨b, hbc, hbi, hbU, hb0, hopen⟩ := exists_collar hS hC φ hU hCU
  obtain ⟨ce, hcec, hce, hceo⟩ := GM07.exists_collar_glue hbc hbi hopen
    (M := fun q => upHalf q.2.2) (continuous_upHalf.comp (continuous_snd.comp continuous_snd))
    (fun _ _ => Subtype.ext (by simp [upHalf]))
  obtain ⟨cg, hcgc, hcg, hcgo⟩ := GM07.exists_collar_glue hbc hbi hopen
    (M := fun q => liftTo q.1 q.2.2)
    (continuous_liftTo.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    (fun p _ => Subtype.ext (by simp [liftTo]; linarith [p.2.2]))
  -- basic facts about the collar
  have hbN : ∀ z, b z ∉ K.N := fun z h => (hbU (mem_range_self z)).1 h
  have hht : ∀ w t, b (w, t) ∈ bd S → t = 0 := by
    intro w t h
    have hC' : b (w, t) ∈ C := by
      by_contra hn
      exact (hbU (mem_range_self _)).2 ⟨h, hn⟩
    obtain ⟨w', hw'⟩ := φ.surjective ⟨_, hC'⟩
    have h2 : b (w', 0) = b (w, t) := by rw [hb0, hw']
    exact (Prod.ext_iff.mp (hbi h2)).2.symm
  have hCb : ∀ x (hx : x ∈ C), b (φ.symm ⟨x, hx⟩, 0) = x := by
    intro x hx; rw [hb0]; simp
  let E₁ : S → S := fun y => ce (1, y)
  let G₁ : S → S := fun y => cg (1, y)
  have hE₁b : ∀ w t, E₁ (b (w, t)) = b (w, upHalf t) := fun w t => hce 1 w t
  have hE₁o : ∀ y, y ∉ range b → E₁ y = y := fun y hy => hceo 1 y hy
  have hcgb : ∀ p w t, cg (p, b (w, t)) = b (w, liftTo p t) := hcg
  -- the new data
  let e' : S → S := E₁ ∘ K.e
  let g' : S → S := G₁ ∘ K.g
  let Φ' : 𝕀 × S → S := fun q => cg (q.1, K.Φ q)
  let N' : Set S := K.N ∪ range b
  let sp' : S → Set S := fun x =>
    if hx : x ∈ C then range (fun t => b (φ.symm ⟨x, hx⟩, downHalf t)) else K.sp x
  have hN_e : ∀ y ∈ K.N, e' y = K.e y := fun y hy =>
    hE₁o _ (fun ⟨z, hz⟩ => hbN z (hz ▸ (K.mapsTo y hy).1))
  have hNN_e : ∀ y, y ∉ K.N → e' y = E₁ y := fun y hy => by
    change E₁ (K.e y) = E₁ y; rw [(K.fix y hy).1]
  have he'b : ∀ w t, e' (b (w, t)) = b (w, upHalf t) := fun w t => by
    rw [hNN_e _ (hbN _), hE₁b]
  have hG₁N : ∀ y ∈ K.N, G₁ y = y := fun y hy =>
    hcgo 1 y (fun ⟨z, hz⟩ => hbN z (hz ▸ hy))
  have hrangeN : ∀ z ∈ K.N, z ∈ range e' ↔ z ∈ range K.e := by
    intro z hz
    constructor
    · rintro ⟨y, rfl⟩
      by_cases hy : y ∈ K.N
      · rw [hN_e y hy]; exact mem_range_self y
      · rw [hNN_e y hy] at hz
        by_cases hyb : y ∈ range b
        · obtain ⟨⟨w, t⟩, rfl⟩ := hyb
          rw [hE₁b] at hz; exact absurd hz (hbN _)
        · rw [hE₁o y hyb] at hz; exact absurd hz hy
    · rintro ⟨y, rfl⟩
      have hy : y ∈ K.N := by
        by_contra hy
        rw [(K.fix y hy).1] at hz
        exact hy hz
      exact ⟨y, hN_e y hy⟩
  have hrange_b : ∀ w t, b (w, t) ∈ range e' ↔ 1 / 2 ≤ t.1 := by
    intro w t
    constructor
    · rintro ⟨y, hy⟩
      by_cases hyN : y ∈ K.N
      · rw [hN_e y hyN] at hy
        exact absurd (hy ▸ (K.mapsTo y hyN).1) (hbN _)
      · rw [hNN_e y hyN] at hy
        by_cases hyb : y ∈ range b
        · obtain ⟨⟨w', s⟩, rfl⟩ := hyb
          rw [hE₁b] at hy
          have := congrArg Subtype.val (Prod.ext_iff.mp (hbi hy)).2
          simp only [upHalf] at this
          rw [← this]; linarith [s.2.1]
        · rw [hE₁o y hyb] at hy
          exact absurd ⟨_, hy.symm⟩ hyb
    · intro ht
      let s : 𝕀 := ⟨2 * t.1 - 1, by constructor <;> linarith [t.2.2]⟩
      refine ⟨b (w, s), ?_⟩
      rw [he'b]
      congr 2
      exact Subtype.ext (by simp [upHalf, s])
  have hsp'C : ∀ x (hx : x ∈ C), sp' x = range (fun t => b (φ.symm ⟨x, hx⟩, downHalf t)) :=
    fun x hx => by simp only [sp', hx, ↓reduceDIte]
  have hsp'B : ∀ x ∈ B, sp' x = K.sp x := fun x hx => by simp only [sp', disjoint_right.mp hCB hx, ↓reduceDIte]
  have hmem_sp : ∀ x (hx : x ∈ C) z, z ∈ sp' x ↔
      ∃ t : 𝕀, t.1 ≤ 1 / 2 ∧ z = b (φ.symm ⟨x, hx⟩, t) := by
    intro x hx z
    rw [hsp'C x hx]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨downHalf t, show (1 - t.1) / 2 ≤ 1 / 2 by linarith [t.2.1], rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨1 - 2 * t.1, by constructor <;> linarith [t.2.1]⟩, ?_⟩
      have h : downHalf ⟨1 - 2 * t.1, by constructor <;> linarith [t.2.1]⟩ = t :=
        Subtype.ext (by simp only [downHalf]; ring)
      simp only [h]
  have hex : ∀ x (hx : x ∈ C), e' x = b (φ.symm ⟨x, hx⟩, upHalf 0) := by
    intro x hx
    conv_lhs => rw [← hCb x hx]
    exact he'b _ _
  refine ⟨{
    e := e'
    g := g'
    Φ := Φ'
    sp := sp'
    N := N'
    isClosed_N := K.isClosed_N.union (isCompact_range hbc).isClosed
    cont_e := (hcec.comp (continuous_const.prodMk continuous_id)).comp K.cont_e
    inj_e := ?inj
    cont_Φ := hcgc.comp (continuous_fst.prodMk K.cont_Φ)
    Φ_zero := ?zero
    Φ_one := fun x => by change cg (1, K.Φ (1, x)) = cg (1, K.g x); rw [K.Φ_one]
    fix := ?fix
    mapsTo := ?mapsTo
    B_subset := ?Bsub
    N_bd := ?Nbd
    g_e := ?ge
    cover := ?cover
    e_bd := ?ebd
    line := ?line
    ne := ?ne
    sp_range := ?sprange
    sp_bd := ?spbd
    sp_N := ?spN
    disjoint := ?disj }⟩
  case inj =>
    have hE₁i : Injective E₁ := by
      intro y y' h
      by_cases hy : y ∈ range b <;> by_cases hy' : y' ∈ range b
      · obtain ⟨⟨w, t⟩, rfl⟩ := hy
        obtain ⟨⟨w', t'⟩, rfl⟩ := hy'
        rw [hE₁b, hE₁b] at h
        have h2 := Prod.ext_iff.mp (hbi h)
        have hw : w = w' := h2.1
        have ht : t = t' := Subtype.ext (by
          have := congrArg Subtype.val h2.2; simp only [upHalf] at this; linarith)
        rw [hw, ht]
      · obtain ⟨⟨w, t⟩, rfl⟩ := hy
        rw [hE₁b, hE₁o y' hy'] at h
        exact absurd ⟨_, h⟩ hy'
      · obtain ⟨⟨w', t'⟩, rfl⟩ := hy'
        rw [hE₁b, hE₁o y hy] at h
        exact absurd ⟨_, h.symm⟩ hy
      · rwa [hE₁o y hy, hE₁o y' hy'] at h
    exact hE₁i.comp K.inj_e
  case zero =>
    intro x
    change cg (0, K.Φ (0, x)) = x
    rw [K.Φ_zero]
    by_cases hx : x ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hx
      rw [hcgb]
      congr 2
      exact Subtype.ext (by simp [liftTo]; exact t.2.1)
    · exact hcgo 0 x hx
  case fix =>
    intro y hy
    have hyN : y ∉ K.N := fun h => hy (.inl h)
    have hyb : y ∉ range b := fun h => hy (.inr h)
    refine ⟨by rw [hNN_e y hyN, hE₁o y hyb], fun t => ?_⟩
    change cg (t, K.Φ (t, y)) = y
    rw [(K.fix y hyN).2 t, hcgo t y hyb]
  case mapsTo =>
    rintro y (hy | ⟨⟨w, s⟩, rfl⟩)
    · refine ⟨.inl (hN_e y hy ▸ (K.mapsTo y hy).1), fun t => .inl ?_⟩
      change cg (t, K.Φ (t, y)) ∈ K.N
      have h := (K.mapsTo y hy).2 t
      rw [hcgo t _ (fun ⟨z, hz⟩ => hbN z (hz ▸ h))]
      exact h
    · refine ⟨.inr (he'b w s ▸ mem_range_self _), fun t => .inr ?_⟩
      change cg (t, K.Φ (t, b (w, s))) ∈ range b
      rw [(K.fix _ (hbN _)).2 t, hcgb]
      exact mem_range_self _
  case Bsub =>
    rintro x (hx | hx)
    · exact .inl (K.B_subset hx)
    · exact .inr ⟨_, hCb x hx⟩
  case Nbd =>
    rintro x ⟨hx | ⟨⟨w, t⟩, rfl⟩, hxb⟩
    · exact .inl (K.N_bd ⟨hx, hxb⟩)
    · by_contra hn
      exact (hbU (mem_range_self _)).2 ⟨hxb, fun h => hn (.inr h)⟩
  case ge =>
    intro y
    change G₁ (K.g (e' y)) = e' y
    by_cases hy : y ∈ K.N
    · rw [hN_e y hy, K.g_e]
      exact hG₁N _ (K.mapsTo y hy).1
    · rw [hNN_e y hy]
      by_cases hyb : y ∈ range b
      · obtain ⟨⟨w, t⟩, rfl⟩ := hyb
        rw [hE₁b]
        have hg : K.g (b (w, upHalf t)) = b (w, upHalf t) := by
          rw [← K.Φ_one]; exact (K.fix _ (hbN _)).2 1
        change cg (1, K.g (b (w, upHalf t))) = _
        rw [hg, hcgb]
        congr 2
        exact Subtype.ext (by
          simp only [liftTo, upHalf, Set.Icc.coe_one]
          exact max_eq_left (by linarith [t.2.1]))
      · rw [hE₁o y hyb]
        have hg : K.g y = y := by rw [← K.Φ_one]; exact (K.fix y hy).2 1
        change cg (1, K.g y) = y
        rw [hg, hcgo 1 y hyb]
  case cover =>
    intro y
    by_cases hyb : y ∈ range b
    · obtain ⟨⟨w, t⟩, rfl⟩ := hyb
      by_cases ht : 1 / 2 ≤ t.1
      · exact .inl ((hrange_b w t).mpr ht)
      · right
        have hx : (φ w).1 ∈ C := (φ w).2
        refine ⟨(φ w).1, .inr hx, ?_, ?_⟩
        · rw [hmem_sp _ hx]
          refine ⟨t, by linarith, ?_⟩
          simp
        · rw [hex _ hx]
          change cg (1, K.g (b (w, t))) = _
          have hg : K.g (b (w, t)) = b (w, t) := by
            rw [← K.Φ_one]; exact (K.fix _ (hbN _)).2 1
          rw [hg, hcgb]
          simp only [Subtype.coe_eta, Homeomorph.symm_apply_apply]
          congr 2
          exact Subtype.ext (by
            simp only [liftTo, upHalf, Set.Icc.coe_one, Set.Icc.coe_zero]
            rw [max_eq_right (by linarith)]; norm_num)
    · rcases K.cover y with ⟨z, rfl⟩ | ⟨x, hx, hysp, hgy⟩
      · left
        have hz : z ∈ K.N ∨ z ∉ K.N := em _
        rcases hz with hz | hz
        · exact ⟨z, hN_e z hz⟩
        · refine ⟨z, ?_⟩
          have hzz : K.e z = z := (K.fix z hz).1
          rw [hNN_e z hz, hzz]
          rw [hzz] at hyb
          exact hE₁o z hyb
      · right
        refine ⟨x, .inl hx, (hsp'B x hx).symm ▸ hysp, ?_⟩
        change G₁ (K.g y) = e' x
        rw [hgy, hN_e x (K.B_subset hx)]
        exact hG₁N _ (K.mapsTo x (K.B_subset hx)).1
  case ebd =>
    intro y hy hyN
    rcases hyN with hyN | ⟨⟨w, t⟩, rfl⟩
    · rw [hN_e y hyN] at hy
      exact K.e_bd y hy hyN
    · rw [he'b] at hy
      have := hht w _ hy
      have h2 := congrArg Subtype.val this
      simp [upHalf] at h2
      linarith [t.2.1]
  case line =>
    rintro x (hx | hx)
    · rw [hsp'B x hx, hN_e x (K.B_subset hx)]
      exact K.line x hx
    · rw [hsp'C x hx, hex x hx]
      let f : C(𝕀, S) := ⟨fun t => b (φ.symm ⟨x, hx⟩, downHalf t),
        hbc.comp (continuous_const.prodMk continuous_downHalf)⟩
      have hf : Injective f := by
        intro t t' h
        have h2 := congrArg Subtype.val (Prod.ext_iff.mp (hbi h)).2
        simp [downHalf] at h2
        exact Subtype.ext (by linarith)
      have h := isLineWithEnds_range f hf
      have h0 : f 0 = b (φ.symm ⟨x, hx⟩, upHalf 0) := by
        change b _ = b _; congr 2; exact Subtype.ext (by simp [downHalf, upHalf])
      have h1 : f 1 = x := by
        change b _ = x
        conv_rhs => rw [← hCb x hx]
        congr 2; exact Subtype.ext (by simp [downHalf])
      rw [h0, h1] at h
      exact h
  case ne =>
    rintro x (hx | hx)
    · rw [hN_e x (K.B_subset hx)]; exact K.ne x hx
    · rw [hex x hx]
      conv_rhs => rw [← hCb x hx]
      intro h
      have h2 := congrArg Subtype.val (Prod.ext_iff.mp (hbi h)).2
      simp [upHalf] at h2
  case sprange =>
    rintro x (hx | hx)
    · rw [hsp'B x hx, hN_e x (K.B_subset hx), ← K.sp_range x hx]
      ext z
      constructor
      · rintro ⟨hz, hzr⟩
        exact ⟨hz, (hrangeN z (K.sp_N x hx hz)).mp hzr⟩
      · rintro ⟨hz, hzr⟩
        exact ⟨hz, (hrangeN z (K.sp_N x hx hz)).mpr hzr⟩
    · rw [hex x hx]
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      rw [hmem_sp x hx]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hr⟩
        have h := (hrange_b _ t).mp hr
        congr 2
        exact Subtype.ext (by simp [upHalf]; linarith)
      · rintro rfl
        refine ⟨⟨upHalf 0, by simp [upHalf], rfl⟩, (hrange_b _ _).mpr (by simp [upHalf])⟩
  case spbd =>
    rintro x (hx | hx)
    · rw [hsp'B x hx]; exact K.sp_bd x hx
    · ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      rw [hmem_sp x hx]
      constructor
      · rintro ⟨⟨t, -, rfl⟩, hb⟩
        rw [hht _ _ hb]
        exact hCb x hx
      · rintro rfl
        exact ⟨⟨0, by simp, (hCb _ hx).symm⟩, hCbd hx⟩
  case spN =>
    rintro x (hx | hx)
    · rw [hsp'B x hx]; exact (K.sp_N x hx).trans subset_union_left
    · rw [hsp'C x hx]; exact (range_subset_iff.mpr fun t => mem_range_self _).trans
        subset_union_right
  case disj =>
    have hspb : ∀ x (hx : x ∈ C), sp' x ⊆ range b := fun x hx => by
      rw [hsp'C x hx]; exact range_subset_iff.mpr fun t => mem_range_self _
    rintro x (hx | hx) y (hy | hy) hxy
    · rw [hsp'B x hx, hsp'B y hy]; exact K.disjoint x hx y hy hxy
    · rw [hsp'B x hx]
      exact disjoint_left.mpr fun z hz hz' => by
        obtain ⟨q, rfl⟩ := hspb y hy hz'
        exact hbN q (K.sp_N x hx hz)
    · rw [hsp'B y hy]
      exact disjoint_left.mpr fun z hz hz' => by
        obtain ⟨q, rfl⟩ := hspb x hx hz
        exact hbN q (K.sp_N y hy hz')
    · refine disjoint_left.mpr fun z hz hz' => hxy ?_
      obtain ⟨t, -, rfl⟩ := (hmem_sp x hx _).mp hz
      obtain ⟨t', -, h⟩ := (hmem_sp y hy _).mp hz'
      have h1 := (Prod.ext_iff.mp (hbi h)).1
      have h2 := congrArg (fun w => (φ w).1) h1
      simpa using h2

/-- **A collar of the whole boundary.** -/
theorem exists_boundaryCollar [T2Space S] [CompactSpace S] (hS : IsSurface S) :
    Nonempty (BoundaryCollar S (bd S)) := by
  have key : ∀ 𝒞 : Set (Set S), 𝒞.Finite → 𝒞 ⊆ cuffs S →
      Nonempty (BoundaryCollar S (⋃₀ 𝒞)) := by
    intro 𝒞 hfin
    induction 𝒞, hfin using Set.Finite.induction_on with
    | empty => intro _; rw [sUnion_empty]; exact ⟨BoundaryCollar.empty S⟩
    | @insert C 𝒞 hCnot hfin ih =>
      intro hsub
      obtain ⟨K⟩ := ih ((subset_insert C 𝒞).trans hsub)
      have hC : C ∈ cuffs S := hsub (mem_insert C 𝒞)
      have hdis : Disjoint C (⋃₀ 𝒞) := by
        refine disjoint_sUnion_right.mpr fun D hD => ?_
        have hD' : D ∈ cuffs S := hsub (mem_insert_of_mem C hD)
        exact cuffs_disjoint hC hD' (fun h => hCnot (h ▸ hD))
      obtain ⟨K'⟩ := K.exists_add hS hC hdis
      rw [sUnion_insert, union_comm]
      exact ⟨K'⟩
  have h := key (cuffs S) (cuff_statement S hS).2.1 Subset.rfl
  rwa [sUnion_cuffs] at h

end GraphMinor.GM08
