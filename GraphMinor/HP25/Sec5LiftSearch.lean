module

public import GraphMinor.HP25.Sec5Search
public import GraphMinor.HP25.Sec5Extract
public import GraphMinor.HP25.Lemma41

/-!
# Completeness of Figure 11 candidate-chain search (`liftSubCrossingBySearches_isSome`)

In `GraphMinor/HP25/Lemma41.lean`, `Setting.cross_of_side` lifts a crossing `(Q, R)` of a
subinstance frame `C_H = a :: A ++ b :: m.reverse` to a crossing of `C` via the five cases of
Figure 11 (`case4`, `case5`, and the direct index cases). Every case constructs two disjoint chains
`X` and `Y` in `H` whose endpoints alternate on `C`, where `X` is one of the `28` candidate chains
in `figure11CandidateChains P_supp Q.support R.support`.

By `runCandidateSearches_isSome_of_chain`, running `runCandidateSearches` over those `28` candidate
chains is therefore guaranteed to return `some` valid crossing of `C` in `H`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set PlaneEmbedding

variable {V : Type*} {G : SimpleGraph V}

/-- `runCandidateSearches` version of `isCrossed_of_lists`: if `X ∈ chains` and `Y` satisfy the
hypotheses of `isCrossed_of_lists`, then `runCandidateSearches` over `chains` returns `some` valid
crossing. -/
theorem runCandidateSearches_isSome_of_lists [DecidableEq V] [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts : List V} (hverts : ∀ v : V, v ∈ verts) {T : List V} (hTnd : T.Nodup)
    {chains : List (List V)} {a b c d : V} {k : ℕ} {L₁ L₂ X Y : List V}
    (hrot : T.rotate k = a :: L₁ ++ b :: L₂) (hc : c ∈ L₁) (hd : d ∈ L₂)
    (hX_mem : X ∈ chains)
    (hX : X.IsChain G.Adj) (_hXnd : X.Nodup) (hXh : X.head? = some a) (hXl : X.getLast? = some b)
    (hXin : ∀ w ∈ X, w ∈ T → w = a ∨ w = b)
    (hY : Y.IsChain G.Adj) (_hYnd : Y.Nodup) (hYh : Y.head? = some c) (hYl : Y.getLast? = some d)
    (_hYin : ∀ w ∈ Y, w ∈ T → w = c ∨ w = d) (hdisj : X.Disjoint Y) :
    (runCandidateSearches G verts T (chains.filterMap (walkOfChainOption G))).1.isSome = true := by
  have hmem : ∀ w, w ∈ a :: L₁ ++ b :: L₂ → w ∈ T := fun w hw => by
    rw [← hrot] at hw
    exact List.mem_rotate.mp hw
  obtain ⟨W, hW⟩ := exists_walk_of_chain Y hY hYh hYl
  have halt₀ : Alternate T a b c d := ⟨k, L₁, L₂, hrot, hc, hd⟩
  refine runCandidateSearches_isSome_of_chain hverts hTnd hX_mem hX hXh hXl
    (hmem a (by simp)) (hmem b (by simp)) hXin halt₀.comm.swap W.reverse fun w hw hwX => ?_
  rw [Walk.support_reverse, List.mem_reverse] at hw
  exact hdisj hwX (hW ▸ hw)

/-- `runCandidateSearches` version of `isCrossed_of_lists_idx`: if `X ∈ chains` and `Y` satisfy the
hypotheses of `isCrossed_of_lists_idx`, then `runCandidateSearches` over `chains` returns `some`
valid crossing. -/
theorem runCandidateSearches_isSome_of_lists_idx [DecidableEq V] [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    {verts : List V} (hverts : ∀ v : V, v ∈ verts) {T T' : List V} (hTnd : T.Nodup)
    {chains : List (List V)} {k : ℕ} (hrot : T.rotate k = T') {i r j s : ℕ}
    (hir : i < r) (hrj : r < j) (hjs : j < s) (hs : s < T'.length) {X Y : List V}
    (hX_mem : X ∈ chains)
    (hX : X.IsChain G.Adj) (_hXnd : X.Nodup) (hXh : X.head? = T'[i]?) (hXl : X.getLast? = T'[j]?)
    (hXin : ∀ w ∈ X, w ∈ T → X.head? = some w ∨ X.getLast? = some w)
    (hY : Y.IsChain G.Adj) (_hYnd : Y.Nodup) (hYh : Y.head? = T'[r]?) (hYl : Y.getLast? = T'[s]?)
    (_hYin : ∀ w ∈ Y, w ∈ T → Y.head? = some w ∨ Y.getLast? = some w) (hdisj : X.Disjoint Y) :
    (runCandidateSearches G verts T (chains.filterMap (walkOfChainOption G))).1.isSome = true := by
  have hmem : ∀ w, w ∈ T' → w ∈ T := fun w hw => by
    rw [← hrot] at hw
    exact List.mem_rotate.mp hw
  rw [List.getElem?_eq_getElem (by omega)] at hXh hXl hYh
  rw [List.getElem?_eq_getElem hs] at hYl
  have hin : ∀ {Z : List V} {u v : V}, Z.head? = some u → Z.getLast? = some v →
      (∀ w ∈ Z, w ∈ T → Z.head? = some w ∨ Z.getLast? = some w) →
      ∀ w ∈ Z, w ∈ T → w = u ∨ w = v := fun {Z u v} hh hl h w hw hwT => by
    rcases h w hw hwT with h' | h'
    · exact Or.inl (Option.some_injective _ (h'.symm.trans hh))
    · exact Or.inr (Option.some_injective _ (h'.symm.trans hl))
  obtain ⟨W, hW⟩ := exists_walk_of_chain Y hY hYh hYl
  have halt₀ : Alternate T T'[i] T'[j] T'[r] T'[s] := by
    refine ⟨k + i, (T'.drop (i + 1)).take (j - i - 1), T'.drop (j + 1) ++ T'.take i, ?_, ?_, ?_⟩
    · rw [← List.rotate_rotate, hrot, List.rotate_eq_drop_append_take (by omega)]
      have e1 : T'.drop i = T'[i] :: T'.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
      have e2 : T'.drop (i + 1) = (T'.drop (i + 1)).take (j - i - 1) ++ T'[j] :: T'.drop (j + 1) := by
        conv_lhs => rw [← List.take_append_drop (j - i - 1) (T'.drop (i + 1))]
        congr 1
        rw [List.drop_drop, List.drop_eq_getElem_cons (by omega)]
        congr 2 <;> omega
      rw [e1]
      nth_rw 1 [e2]
      simp only [List.cons_append, List.append_assoc]
    · rw [List.mem_iff_getElem]
      exact ⟨r - i - 1, by simp; omega, by simp; congr 1; omega⟩
    · refine List.mem_append_left _ (List.mem_iff_getElem.mpr ⟨s - j - 1, by simp; omega, ?_⟩)
      simp
      congr 1
      omega
  refine runCandidateSearches_isSome_of_chain hverts hTnd hX_mem hX hXh hXl
    (hmem _ (List.getElem_mem _)) (hmem _ (List.getElem_mem _)) (hin hXh hXl hXin)
    halt₀.comm.swap W.reverse fun w hw hwX => ?_
  rw [Walk.support_reverse, List.mem_reverse] at hw
  exact hdisj hwX (hW ▸ hw)

/-! ### Membership in `figure11CandidateChains` -/

/-- A list `X₀` is one of the four oriented support lists of `(Q, R)`. -/
def IsBaseChain (Q_supp R_supp X₀ : List V) : Prop :=
  X₀ ∈ [Q_supp, Q_supp.reverse, R_supp, R_supp.reverse]

theorem IsBaseChain.reverse {Q_supp R_supp X₀ : List V} (h : IsBaseChain Q_supp R_supp X₀) :
    IsBaseChain Q_supp R_supp X₀.reverse := by
  unfold IsBaseChain at h ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem mem_figure11CandidateChains_self [DecidableEq V] {P_supp Q_supp R_supp X₀ : List V}
    (hX₀ : IsBaseChain Q_supp R_supp X₀) :
    X₀ ∈ figure11CandidateChains P_supp Q_supp R_supp := by
  unfold figure11CandidateChains
  rw [List.mem_flatMap]
  refine ⟨X₀, hX₀, ?_⟩
  simp [figure11ChainsForOne]

theorem mem_figure11CandidateChains_ext [DecidableEq V] {P_supp Q_supp R_supp X₀ lp : List V}
    (hX₀ : IsBaseChain Q_supp R_supp X₀) (hlp : lp ∈ [P_supp, P_supp.reverse])
    (hlp_nd : lp.Nodup) {p : ℕ} {z : V} (hXl : X₀.getLast? = some z) (hz : lp[p]? = some z) :
    X₀ ++ (lp.take p).reverse ∈ figure11CandidateChains P_supp Q_supp R_supp := by
  obtain ⟨hp, rfl⟩ := List.getElem?_eq_some_iff.mp hz
  have hidx : lp.idxOf lp[p] = p := List.Nodup.idxOf_getElem hlp_nd p hp
  unfold figure11CandidateChains
  rw [List.mem_flatMap]
  refine ⟨X₀, hX₀, ?_⟩
  unfold figure11ChainsForOne
  rw [List.mem_cons]
  right
  rw [List.mem_append]
  left
  rw [List.mem_map]
  refine ⟨lp, hlp, ?_⟩
  rw [hXl]
  dsimp only
  rw [hidx]

theorem mem_figure11CandidateChains_spl [DecidableEq V] {P_supp Q_supp R_supp Y₀ lp : List V}
    (hY₀ : IsBaseChain Q_supp R_supp Y₀) (hlp : lp ∈ [P_supp, P_supp.reverse])
    (hlp_nd : lp.Nodup) {p₂ p₄ : ℕ} {z₂ z₄ : V}
    (hYh : Y₀.head? = some z₂) (hYl : Y₀.getLast? = some z₄)
    (hz₂ : lp[p₂]? = some z₂) (hz₄ : lp[p₄]? = some z₄) :
    lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1) ∈ figure11CandidateChains P_supp Q_supp R_supp ∧
    (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)).reverse ∈
      figure11CandidateChains P_supp Q_supp R_supp := by
  obtain ⟨hp₂, rfl⟩ := List.getElem?_eq_some_iff.mp hz₂
  obtain ⟨hp₄, rfl⟩ := List.getElem?_eq_some_iff.mp hz₄
  have hidx₂ : lp.idxOf lp[p₂] = p₂ := List.Nodup.idxOf_getElem hlp_nd p₂ hp₂
  have hidx₄ : lp.idxOf lp[p₄] = p₄ := List.Nodup.idxOf_getElem hlp_nd p₄ hp₄
  constructor <;>
  · unfold figure11CandidateChains
    rw [List.mem_flatMap]
    refine ⟨Y₀, hY₀, ?_⟩
    unfold figure11ChainsForOne
    rw [List.mem_cons]
    right
    rw [List.mem_append]
    right
    rw [List.mem_flatMap]
    refine ⟨lp, hlp, ?_⟩
    rw [hYh, hYl]
    dsimp only
    rw [hidx₂, hidx₄]
    simp

namespace Setting

variable {S₁ S₂ : Set V} {a b : V} {m A B C : List V} {k : ℕ}

theorem nodupC (hS : Setting G S₁ S₂ a b m A B C k) : C.Nodup := by
  rw [← List.nodup_rotate (n := k), hS.rot,
    show a :: A ++ b :: B = (a :: A ++ [b]) ++ B by simp, List.nodup_append]
  have h1 : (a :: A ++ [b]).Nodup := by
    have := hS.nodupH
    rw [show a :: A ++ b :: m.reverse = (a :: A ++ [b]) ++ m.reverse by simp] at this
    exact this.sublist (List.sublist_append_left _ _)
  have h2 : B.Nodup :=
    (hS.nodupK.sublist (List.sublist_append_left _ _)).sublist (List.sublist_cons_self _ _)
  refine ⟨h1, h2, fun u hu v hv huv => ?_⟩
  subst huv
  refine hS.B_not_S₁ hv (hS.mem_S₁ ?_)
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hu ⊢
  tauto

/-- Rerouting through `H` in `G` (without an added edge). -/
theorem reroute_G (hS : Setting G S₁ S₂ a b m A B C k) {P Y₀ α β : List V}
    {h₀ z u c : V} (hPc : P.IsChain G.Adj) (hPnd : P.Nodup)
    (hPh : P.head? = some h₀) (hPl : P.getLast? = some z) (hPS : ∀ w ∈ P, w ∈ S₁)
    (hPD : ∀ w ∈ P, w ∈ a :: A ++ b :: m.reverse → w = h₀ ∨ w = z)
    (hh₀ : h₀ ∈ a :: m ++ [b]) (hz : z ∈ a :: m ++ [b]) (hzC : z ∉ C)
    (hu : u ∈ P) (huD : u ∉ a :: A ++ b :: m.reverse) (huY : u ∉ Y₀) (hPY : P.Disjoint Y₀)
    (hPhc : (α ++ u :: β).IsChain G.Adj) (hPhnd : (α ++ u :: β).Nodup)
    (hPhl : (α ++ u :: β).getLast? = some c) (hPhS : ∀ w ∈ α ++ u :: β, w ∈ S₁)
    (hPhD : ∀ w ∈ α ++ u :: β, w ∈ a :: A ++ b :: m.reverse → w = c) (hc : c ∈ A)
    (hβ : ∀ w ∈ β, w ∉ P ∧ w ∉ Y₀) :
    ∃ Xh : List V, Xh.IsChain G.Adj ∧ Xh.Nodup ∧ Xh.head? = some c ∧
      Xh.getLast? = some z ∧ (∀ w ∈ Xh, w ∈ S₁) ∧ (∀ w ∈ Xh, w ∈ a :: m ++ [b] → w = z) ∧
      (∀ w ∈ Xh, w ∈ C → w = c) ∧ Xh.Disjoint Y₀ := by
  have hbot : SimpleGraph.edge a a = (⊥ : SimpleGraph V) := by ext x y; simp
  have hPc' : P.IsChain (G ⊔ edge a a).Adj := by rwa [hbot, sup_bot_eq]
  obtain ⟨Xh, hXc, rest⟩ := hS.reroute hPc' hPnd hPh hPl hPS hPD hh₀ hz hzC hu huD huY hPY
    hPhc hPhnd hPhl hPhS hPhD hc hβ
  rw [hbot, sup_bot_eq] at hXc
  exact ⟨Xh, hXc, rest⟩

/-- Walk facts in `restrict G S₁` (without an added edge). -/
theorem walk_facts_G (hS : Setting G S₁ S₂ a b m A B C k) {u v : V}
    (W : (restrict G S₁).Walk u v) (hW : IsTPath (restrict G S₁) (a :: A ++ b :: m.reverse) W) :
    W.support.IsChain G.Adj ∧ W.support.Nodup ∧ W.support.head? = some u ∧
      W.support.getLast? = some v ∧ (∀ w ∈ W.support, w ∈ S₁) ∧
      ∀ w ∈ W.support, w ∈ a :: A ++ b :: m.reverse → w = u ∨ w = v := by
  refine ⟨?_, (Walk.isPath_def W).mp hW.1, by rw [← Walk.cons_tail_support]; rfl,
    by rw [List.getLast?_eq_some_getLast (by simp), Walk.getLast_support],
    mem_of_support_restrict W (hS.mem_S₁ hW.2.1), fun w hw hwD => ?_⟩
  · have := (W.mapLe (restrict_le G S₁)).isChain_adj_support
    rwa [support_mapLe] at this
  · by_contra hne
    push Not at hne
    exact (hW.2.2.2 w hw hne.1 hne.2).1 hwD

/-- Search-completeness version of `Setting.case4`: one of the spliced chains in
`figure11CandidateChains` succeeds under `runCandidateSearches`. -/
theorem case4_search [DecidableEq V] [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V] (hS : Setting G S₁ S₂ a b m A B C k)
    {verts P_supp Q_supp R_supp : List V} (hverts : ∀ v : V, v ∈ verts)
    {lp : List V} {e₀ e₁ : V} (hlp : hS.IsAlong lp e₀ e₁)
    (hlp_mem : lp ∈ [P_supp, P_supp.reverse])
    {p₂ p₃ p₄ : ℕ} (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < lp.length) {c z₂ z₃ z₄ : V} (hz₂ : lp[p₂]? = some z₂) (hz₃ : lp[p₃]? = some z₃)
    (hz₄ : lp[p₄]? = some z₄) (hc : c ∈ A) {Xh Y₀ : List V}
    (hY₀_base : IsBaseChain Q_supp R_supp Y₀)
    (hXc : Xh.IsChain G.Adj) (hXnd : Xh.Nodup) (hXh : Xh.head? = some c)
    (hXl : Xh.getLast? = some z₃) (hXS : ∀ w ∈ Xh, w ∈ S₁)
    (hXl' : ∀ w ∈ Xh, w ∈ a :: m ++ [b] → w = z₃) (hXC : ∀ w ∈ Xh, w ∈ C → w = c)
    (hYc : Y₀.IsChain G.Adj) (hYnd : Y₀.Nodup) (hYh : Y₀.head? = some z₂)
    (hYl : Y₀.getLast? = some z₄) (hYS : ∀ w ∈ Y₀, w ∈ S₁)
    (hYl' : ∀ w ∈ Y₀, w ∈ a :: m ++ [b] → w = z₂ ∨ w = z₄)
    (hYC : ∀ w ∈ Y₀, w ∈ C → w ∈ a :: m ++ [b]) (hdisj : Xh.Disjoint Y₀) :
    (runCandidateSearches G verts C
      ((figure11CandidateChains P_supp Q_supp R_supp).filterMap
        (walkOfChainOption G))).1.isSome = true := by
  have hz₃l : z₃ ∈ a :: m ++ [b] := (hlp.mem z₃).mp (List.mem_of_getElem? hz₃)
  obtain ⟨d, hd, T, hTc, hTnd, hTl, hTS, hTC⟩ := hS.kext hz₃l
  obtain ⟨hYc', hYnd', hYh', hYl'', hYm⟩ := splice hlp.chain hlp.nodup
    (by omega) h4 hz₂ hz₄ hYc hYnd hYh hYl (fun w hw hwl => hYl' w hw ((hlp.mem w).mp hwl))
  have hT : T ≠ [] := by
    rintro rfl
    have hzd : z₃ = d := by simpa using hTl
    exact hS.B_not_l hd (hzd ▸ hz₃l)
  have hXc' : (Xh ++ T).IsChain G.Adj :=
    isChain_append_of_last hXc hXl hTc
  have hXnd' : (Xh ++ T).Nodup := List.nodup_append.mpr ⟨hXnd, (List.nodup_cons.mp hTnd).2,
    fun u hu v hv huv => hTS v hv (huv ▸ hXS u hu)⟩
  have hXh' : (Xh ++ T).head? = some c := by rw [List.head?_append, hXh]; rfl
  have hXl'' : (Xh ++ T).getLast? = some d := by
    obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
    rw [List.getLast?_cons_cons] at hTl
    rw [List.getLast?_append, hTl]
    rfl
  have hXin : ∀ w ∈ Xh ++ T, w ∈ C → w = c ∨ w = d := fun w hw hwC => by
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inl (hXC w hw hwC)
    · exact Or.inr (hTC w hw hwC)
  have hYS' : ∀ w ∈ lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1), w ∈ S₁ := fun w hw => by
    rcases hYm w hw with h | ⟨q, hq, he, -⟩
    · exact hYS w h
    · exact hS.l_S₁ ((hlp.mem w).mp (he ▸ List.getElem_mem hq))
  have hdisj' : (Xh ++ T).Disjoint (lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1)) := by
    intro w hwX hwY
    rcases List.mem_append.mp hwX with hw | hw
    · rcases hYm w hwY with hw' | ⟨q, hq, he, hq'⟩
      · exact hdisj hw hw'
      · have hwz := hXl' w hw ((hlp.mem w).mp (he ▸ List.getElem_mem hq))
        obtain ⟨h3, hz₃'⟩ := List.getElem?_eq_some_iff.mp hz₃
        have : q = p₃ := (hlp.nodup.getElem_inj_iff).mp (he.trans (hwz.trans hz₃'.symm))
        omega
    · exact hTS w hw (hYS' w hwY)
  have hYin : ∀ w ∈ lp.take p₂ ++ Y₀ ++ lp.drop (p₄ + 1), w ∈ C → w = a ∨ w = b :=
    fun w hw hwC => hS.C_l hwC (by
      rcases hYm w hw with h | ⟨q, hq, he, -⟩
      · exact hYC w h hwC
      · exact (hlp.mem w).mp (he ▸ List.getElem_mem hq))
  have hspl_mem := mem_figure11CandidateChains_spl hY₀_base hlp_mem hlp.nodup hYh hYl hz₂ hz₄
  rw [hlp.head] at hYh'
  rw [hlp.last] at hYl''
  rcases hlp.ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact runCandidateSearches_isSome_of_lists hverts hS.nodupC hS.rot hc hd hspl_mem.1
      hYc' hYnd' hYh' hYl'' hYin hXc' hXnd' hXh' hXl'' hXin hdisj'.symm
  · refine runCandidateSearches_isSome_of_lists hverts hS.nodupC hS.rot hc hd hspl_mem.2
      (List.isChain_reverse.mpr (hYc'.imp fun _ _ h => h.symm)) (List.nodup_reverse.mpr hYnd')
      (by rw [List.head?_reverse]; exact hYl'') (by rw [List.getLast?_reverse]; exact hYh')
      (fun w hw hwC => hYin w (List.mem_reverse.mp hw) hwC) hXc' hXnd' hXh' hXl'' hXin
      (fun w hw hw' => hdisj' hw' (List.mem_reverse.mp hw))

/-- Search-completeness version of `Setting.case5`. -/
theorem case5_search [DecidableEq V] [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V] (hS : Setting G S₁ S₂ a b m A B C k)
    {verts P_supp Q_supp R_supp : List V} (hverts : ∀ v : V, v ∈ verts)
    {lp : List V} {e₀ e₁ : V} (hlp : hS.IsAlong lp e₀ e₁)
    (hlp_mem : lp ∈ [P_supp, P_supp.reverse])
    {p₁ p₂ p₃ p₄ : ℕ} (h12 : p₁ < p₂) (h23 : p₂ < p₃) (h34 : p₃ < p₄)
    (h4 : p₄ < lp.length) {z₁ z₂ z₃ z₄ : V} (hz₁ : lp[p₁]? = some z₁) (hz₂ : lp[p₂]? = some z₂)
    (hz₃ : lp[p₃]? = some z₃) (hz₄ : lp[p₄]? = some z₄) {P₁ P₂ : List V}
    (h1_base : IsBaseChain Q_supp R_supp P₁) (h2_base : IsBaseChain Q_supp R_supp P₂)
    (h1c : P₁.IsChain G.Adj) (h1nd : P₁.Nodup) (h1h : P₁.head? = some z₁)
    (h1l : P₁.getLast? = some z₃) (h1S : ∀ w ∈ P₁, w ∈ S₁)
    (h1D : ∀ w ∈ P₁, w ∈ a :: A ++ b :: m.reverse → w = z₁ ∨ w = z₃)
    (h2c : P₂.IsChain G.Adj) (h2nd : P₂.Nodup) (h2h : P₂.head? = some z₂)
    (h2l : P₂.getLast? = some z₄) (h2S : ∀ w ∈ P₂, w ∈ S₁)
    (h2D : ∀ w ∈ P₂, w ∈ a :: A ++ b :: m.reverse → w = z₂ ∨ w = z₄)
    (hdisj : P₁.Disjoint P₂) :
    (runCandidateSearches G verts C
      ((figure11CandidateChains P_supp Q_supp R_supp).filterMap
        (walkOfChainOption G))).1.isSome = true := by
  have hl : ∀ {q : ℕ} {w : V}, lp[q]? = some w → w ∈ a :: m ++ [b] := fun hw =>
    (hlp.mem _).mp (List.mem_of_getElem? hw)
  obtain ⟨hp₁, rfl⟩ := List.getElem?_eq_some_iff.mp hz₁
  obtain ⟨hp₂, rfl⟩ := List.getElem?_eq_some_iff.mp hz₂
  obtain ⟨hp₃, rfl⟩ := List.getElem?_eq_some_iff.mp hz₃
  obtain ⟨hp₄, rfl⟩ := List.getElem?_eq_some_iff.mp hz₄
  have hinj : ∀ {q q' : ℕ} (hq : q < lp.length) (hq' : q' < lp.length), lp[q] = lp[q'] → q = q' :=
    fun hq hq' h => (hlp.nodup.getElem_inj_iff).mp h
  obtain ⟨t, ht, htD⟩ : ∃ t, (t ∈ P₁ ∨ t ∈ P₂) ∧ t ∉ a :: A ++ b :: m.reverse := by
    by_contra hno
    push Not at hno
    have e13 : G.Adj lp[p₁] lp[p₃] := adj_of_ends h1c h1nd h1h h1l
      (fun h => by have := hinj _ _ h; omega) (fun w hw => h1D w hw (hno w (Or.inl hw)))
    have hidx := (hlp.ind _ (List.getElem_mem _) _ (List.getElem_mem _) e13).idxOf hlp.nodup
    rw [List.Nodup.idxOf_getElem hlp.nodup p₁ hp₁,
      List.Nodup.idxOf_getElem hlp.nodup p₃ hp₃] at hidx
    omega
  have htS : t ∈ S₁ := ht.elim (h1S t) (h2S t)
  obtain ⟨c, hc, Ph, hPhh, hPhl, hPhc, hPhnd, hPhS, hPhD⟩ := hS.hpath' htS (fun h => htD (l_D h))
  obtain ⟨α, u, β, rfl, hu, hβ⟩ := exists_last_mem (Z := {w | w ∈ P₁ ∨ w ∈ P₂}) _
    ⟨t, List.mem_of_mem_head? hPhh, ht⟩
  have huD : u ∉ a :: A ++ b :: m.reverse := by
    intro huD
    have huc := hPhD u (by simp) huD
    subst huc
    have hul : u ∈ a :: m ++ [b] := by
      rcases hu with hu | hu
      · rcases h1D u hu huD with h | h <;> rw [h] <;> exact hl (List.getElem?_eq_getElem _)
      · rcases h2D u hu huD with h | h <;> rw [h] <;> exact hl (List.getElem?_eq_getElem _)
    exact hS.A_not_l hc hul
  have hβ' : ∀ w ∈ β, w ∉ P₁ ∧ w ∉ P₂ := fun w hw => by
    have := hβ w hw
    simp only [mem_ofPred_eq, not_or] at this
    exact this
  have hP2l : ∀ w ∈ P₂, w ∈ a :: m ++ [b] → w = lp[p₂] ∨ w = lp[p₄] :=
    fun w hw hwl => h2D w hw (l_D hwl)
  have hP2C : ∀ w ∈ P₂, w ∈ C → w ∈ a :: m ++ [b] := fun w hw hwC => by
    rcases h2D w hw (hS.C_S₁ hwC (h2S w hw)) with rfl | rfl <;>
      exact hl (List.getElem?_eq_getElem _)
  have hP1l : ∀ w ∈ P₁, w ∈ a :: m ++ [b] → w = lp[p₃] ∨ w = lp[p₁] :=
    fun w hw hwl => (h1D w hw (l_D hwl)).symm
  have hP1C : ∀ w ∈ P₁, w ∈ C → w ∈ a :: m ++ [b] := fun w hw hwC => by
    rcases h1D w hw (hS.C_S₁ hwC (h1S w hw)) with rfl | rfl <;>
      exact hl (List.getElem?_eq_getElem _)
  rcases hu with hu | hu
  · obtain ⟨Xh, hXc, hXnd, hXh, hXl, hXS, hXl', hXC, hXY⟩ := hS.reroute_G h1c h1nd h1h h1l h1S h1D
      (hl (List.getElem?_eq_getElem _)) (hl (List.getElem?_eq_getElem _))
      (hlp.not_C (List.getElem?_eq_getElem _) (by omega) (by omega)) hu huD
      (fun h => hdisj hu h) hdisj hPhc hPhnd hPhl hPhS hPhD hc
      (fun w hw => ⟨(hβ' w hw).1, (hβ' w hw).2⟩)
    exact hS.case4_search hverts hlp hlp_mem h23 h34 h4 (List.getElem?_eq_getElem _)
      (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem _) hc h2_base
      hXc hXnd hXh hXl hXS hXl' hXC h2c h2nd h2h h2l h2S hP2l hP2C hXY
  · have hrev : ∀ {q : ℕ} (hq : q < lp.length), lp.reverse[lp.length - 1 - q]? = some lp[q] :=
      fun {q} hq => by
        rw [List.getElem?_reverse (by omega), show lp.length - 1 - (lp.length - 1 - q) = q by omega]
        exact List.getElem?_eq_getElem _
    have hlp_rev_mem : lp.reverse ∈ [P_supp, P_supp.reverse] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlp_mem ⊢
      rcases hlp_mem with rfl | rfl <;> simp
    obtain ⟨Xh, hXc, hXnd, hXh, hXl, hXS, hXl', hXC, hXY⟩ := hS.reroute_G (P := P₂.reverse)
      (Y₀ := P₁) (List.isChain_reverse.mpr (h2c.imp fun _ _ h => h.symm))
      (List.nodup_reverse.mpr h2nd) (by rw [List.head?_reverse]; exact h2l)
      (by rw [List.getLast?_reverse]; exact h2h) (fun w hw => h2S w (List.mem_reverse.mp hw))
      (fun w hw hwD => (h2D w (List.mem_reverse.mp hw) hwD).symm)
      (hl (List.getElem?_eq_getElem _)) (hl (List.getElem?_eq_getElem _))
      (hlp.not_C (List.getElem?_eq_getElem _) (by omega) (by omega)) (List.mem_reverse.mpr hu)
      huD (fun h => hdisj h hu) (fun w hw hw' => hdisj hw' (List.mem_reverse.mp hw)) hPhc hPhnd
      hPhl hPhS hPhD hc (fun w hw => ⟨fun h => (hβ' w hw).2 (List.mem_reverse.mp h),
        (hβ' w hw).1⟩)
    exact hS.case4_search hverts hlp.reverse hlp_rev_mem (p₂ := lp.length - 1 - p₃)
      (p₃ := lp.length - 1 - p₂) (p₄ := lp.length - 1 - p₁)
      (by omega) (by omega) (by simp; omega) (hrev hp₃) (hrev hp₂) (hrev hp₁) hc h1_base.reverse
      hXc hXnd hXh hXl hXS hXl' hXC
      (List.isChain_reverse.mpr (h1c.imp fun _ _ h => h.symm)) (List.nodup_reverse.mpr h1nd)
      (by rw [List.head?_reverse]; exact h1l) (by rw [List.getLast?_reverse]; exact h1h)
      (fun w hw => h1S w (List.mem_reverse.mp hw))
      (fun w hw hwl => hP1l w (List.mem_reverse.mp hw) hwl)
      (fun w hw hwC => hP1C w (List.mem_reverse.mp hw) hwC)
      (fun w hw hw' => hXY hw (List.mem_reverse.mp hw'))

/-- **Search-completeness of Figure 11 (`Setting.cross_of_side_search`).** Given a crossing `(Q, R)`
of `a :: A ++ b :: m.reverse` in `restrict G S₁`, `runCandidateSearches` over the `28` candidate
chains of `figure11CandidateChains P_supp Q.support R.support` returns `some` valid crossing of `C`
in `G`. -/
theorem cross_of_side_search [DecidableEq V] [DecidableRel G.Adj]
    [WalkSearch V] [LawfulWalkSearch V]
    (hS : Setting G S₁ S₂ a b m A B C k) {verts P_supp Q_supp R_supp : List V}
    (hverts : ∀ v : V, v ∈ verts)
    (hlp_mem : (a :: m ++ [b]).reverse ∈ [P_supp, P_supp.reverse])
    {u₁ v₁ u₂ v₂ : V} {Q : (restrict G S₁).Walk u₁ v₁}
    {R : (restrict G S₁).Walk u₂ v₂}
    (hcr : IsCrossing (restrict G S₁) (a :: A ++ b :: m.reverse) Q R)
    (hQ_supp : Q.support = Q_supp) (hR_supp : R.support = R_supp) :
    (runCandidateSearches G verts C
      ((figure11CandidateChains P_supp Q_supp R_supp).filterMap
        (walkOfChainOption G))).1.isSome = true := by
  obtain ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩ := hcr
  obtain ⟨hQc, hQnd, hQh, hQl, hQS, hQD⟩ := hS.walk_facts_G Q hQ
  obtain ⟨hRc, hRnd, hRh, hRl, hRS, hRD⟩ := hS.walk_facts_G R hR
  have hQ_base : IsBaseChain Q_supp R_supp Q.support := by
    unfold IsBaseChain; simp [hQ_supp]
  have hR_base : IsBaseChain Q_supp R_supp R.support := by
    unfold IsBaseChain; simp [hR_supp]
  obtain ⟨n, hn⟩ : ∃ n, n = A.length := ⟨_, rfl⟩
  have hDlen : (a :: A ++ b :: m.reverse).length = n + 2 + m.length := by simp [hn]; omega
  have hsD : s < n + 2 + m.length := by
    rw [← hDlen]; exact (List.getElem?_eq_some_iff.mp hs).1
  have hlr := hS.along_l.reverse
  have hlrlen : (a :: m ++ [b]).reverse.length = m.length + 2 := by simp
  have hlr' : (a :: m ++ [b]).reverse = (b :: m.reverse) ++ [a] := by simp
  have hD1 : a :: A ++ b :: m.reverse = (a :: A) ++ (b :: m.reverse) := rfl
  have hD2 : a :: A ++ b :: m.reverse = (a :: A ++ [b]) ++ m.reverse := by simp
  have hT2 : a :: A ++ b :: B = (a :: A ++ [b]) ++ B := by simp
  have hlrD : ∀ {p : ℕ} {w : V}, n + 1 ≤ p → (a :: A ++ b :: m.reverse)[p]? = some w →
      (a :: m ++ [b]).reverse[p - (n + 1)]? = some w := fun {p w} hp hw => by
    have hpl : p < n + 2 + m.length := by rw [← hDlen]; exact (List.getElem?_eq_some_iff.mp hw).1
    have h1 : (a :: A).length ≤ p := by simp [hn] at hp ⊢; omega
    rw [hD1, List.getElem?_append_right h1] at hw
    have h2 : p - (n + 1) < (b :: m.reverse).length := by simp; omega
    rw [hlr', List.getElem?_append_left h2]
    have h3 : p - (a :: A).length = p - (n + 1) := by simp [hn]
    rwa [h3] at hw
  have hlra : (a :: m ++ [b]).reverse[m.length + 1]? = some a := by
    rw [hlr', List.getElem?_append_right (by simp)]
    simp
  have hlrb : (a :: m ++ [b]).reverse[0]? = some b := by simp
  have hDT : ∀ {p : ℕ}, p ≤ n + 1 →
      (a :: A ++ b :: m.reverse)[p]? = (a :: A ++ b :: B)[p]? := fun {p} hp => by
    have h1 : p < (a :: A ++ [b]).length := by simp [hn] at hp ⊢; omega
    rw [hD2, hT2, List.getElem?_append_left h1, List.getElem?_append_left h1]
  have hTB : ∀ q, (a :: A ++ b :: B)[n + 2 + q]? = B[q]? := fun q => by
    have h1 : (a :: A ++ [b]).length ≤ n + 2 + q := by simp [hn]
    rw [hT2, List.getElem?_append_right h1]
    congr 1
    simp [hn]
  have hTb : (a :: A ++ b :: B)[n + 1]? = some b := by
    have h1 : (a :: A).length ≤ n + 1 := by simp [hn]
    rw [show a :: A ++ b :: B = (a :: A) ++ (b :: B) from rfl, List.getElem?_append_right h1]
    simp [hn]
  have hTlen : (a :: A ++ b :: B).length = n + 2 + B.length := by simp [hn]; omega
  have hDA : ∀ {p : ℕ} {w : V}, 1 ≤ p → p ≤ n → (a :: A ++ b :: m.reverse)[p]? = some w →
      w ∈ A := fun {p w} h1 h2 hw => by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [List.cons_append, List.getElem?_cons_succ,
      List.getElem?_append_left (show p' < A.length by omega)] at hw
    exact List.mem_of_getElem? hw
  have hD0 : ∀ {w : V}, (a :: A ++ b :: m.reverse)[0]? = some w → w = a := fun hw => by
    simpa using hw.symm
  have hDb : ∀ {w : V}, (a :: A ++ b :: m.reverse)[n + 1]? = some w → w = b := fun {w} hw => by
    have h1 : (a :: A).length ≤ n + 1 := by simp [hn]
    rw [hD1, List.getElem?_append_right h1] at hw
    simpa [hn] using hw.symm
  have hlrl : ∀ {p : ℕ} {w : V}, n + 1 ≤ p → (a :: A ++ b :: m.reverse)[p]? = some w →
      w ∈ a :: m ++ [b] := fun hp hw =>
    (hlr.mem _).mp (List.mem_of_getElem? (hlrD hp hw))
  have hlrC : ∀ {p : ℕ} {w : V}, n + 2 ≤ p → (a :: A ++ b :: m.reverse)[p]? = some w → w ∉ C :=
    fun {p w} hp hw => by
      have hpl : p < n + 2 + m.length := by
        rw [← hDlen]; exact (List.getElem?_eq_some_iff.mp hw).1
      exact hlr.not_C (hlrD (by omega) hw) (by omega) (by rw [hlrlen]; omega)
  have hQc' := List.isChain_reverse.mpr (hQc.imp fun _ _ h => h.symm)
  have hQnd' := List.nodup_reverse.mpr hQnd
  have hQh' : Q.support.reverse.head? = some v₁ := by rw [List.head?_reverse]; exact hQl
  have hQl' : Q.support.reverse.getLast? = some u₁ := by rw [List.getLast?_reverse]; exact hQh
  have hQS' : ∀ w ∈ Q.support.reverse, w ∈ S₁ := fun w hw => hQS w (List.mem_reverse.mp hw)
  have hQD' : ∀ w ∈ Q.support.reverse, w ∈ a :: A ++ b :: m.reverse → w = v₁ ∨ w = u₁ :=
    fun w hw hwD => (hQD w (List.mem_reverse.mp hw) hwD).symm
  have hdisj' : R.support.Disjoint Q.support.reverse := fun w hw hw' =>
    hdisj (List.mem_reverse.mp hw') hw
  have hCQ : ∀ w ∈ Q.support, w ∈ C → w = u₁ ∨ w = v₁ := fun w hw hwC =>
    hQD w hw (hS.C_S₁ hwC (hQS w hw))
  have hCR : ∀ w ∈ R.support, w ∈ C → w = u₂ ∨ w = v₂ := fun w hw hwC =>
    hRD w hw (hS.C_S₁ hwC (hRS w hw))
  rcases (by omega : s ≤ n + 1 ∨ (j ≤ n + 1 ∧ n + 2 ≤ s) ∨ (r ≤ n + 1 ∧ n + 2 ≤ j) ∨
      (i ≤ n + 1 ∧ n + 2 ≤ r) ∨ n + 2 ≤ i) with h | ⟨hj', hs'⟩ | ⟨hr', hj'⟩ | ⟨hi', hr'⟩ | hi'
  · -- first case: no end in `m`
    refine runCandidateSearches_isSome_of_lists_idx hverts hS.nodupC hS.rot hir hrj hjs (by omega)
      (mem_figure11CandidateChains_self hQ_base)
      hQc hQnd (by rw [hQh, ← hi, hDT (by omega)])
      (by rw [hQl, ← hj, hDT (by omega)]) (fun w hw hwC => ?_) hRc hRnd
      (by rw [hRh, ← hr, hDT (by omega)]) (by rw [hRl, ← hs, hDT h]) (fun w hw hwC => ?_) hdisj
    · rcases hCQ w hw hwC with rfl | rfl
      · exact Or.inl hQh
      · exact Or.inr hQl
    · rcases hCR w hw hwC with rfl | rfl
      · exact Or.inl hRh
      · exact Or.inr hRl
  · -- second case: the end `v₂` of `R` is in `m`; extend `R` into `K`
    obtain ⟨d, hd, T, hTc, hTnd, hTl, hTS, hTC⟩ := hS.kext (hlrl (by omega) hs)
    obtain ⟨qd, hqd, rfl⟩ := List.getElem_of_mem hd
    have hT : T ≠ [] := by
      rintro rfl
      have hzd : v₂ = B[qd] := by simpa using hTl
      exact hS.B_not_l hd (hzd ▸ hlrl (by omega) hs)
    refine runCandidateSearches_isSome_of_lists_idx hverts hS.nodupC hS.rot (s := n + 2 + qd)
      hir hrj (by omega) (by omega) (mem_figure11CandidateChains_self hQ_base)
      hQc hQnd (by rw [hQh, ← hi, hDT (by omega)]) (by rw [hQl, ← hj, hDT (by omega)])
      (fun w hw hwC => ?_) (isChain_append_of_last hRc hRl hTc)
      (List.nodup_append.mpr ⟨hRnd, (List.nodup_cons.mp hTnd).2,
        fun u hu v hv huv => hTS v hv (huv ▸ hRS u hu)⟩)
      (by rw [List.head?_append, hRh, Option.some_or, ← hr, hDT (by omega)]) ?_ (fun w hw hwC => ?_) ?_
    · rcases hCQ w hw hwC with rfl | rfl
      · exact Or.inl hQh
      · exact Or.inr hQl
    · obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
      rw [List.getLast?_cons_cons] at hTl
      rw [List.getLast?_append, hTl, hTB, List.getElem?_eq_getElem hqd]
      rfl
    · have hl' : (R.support ++ T).getLast? = some B[qd] := by
        obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
        rw [List.getLast?_cons_cons] at hTl
        rw [List.getLast?_append, hTl]
        rfl
      rcases List.mem_append.mp hw with hw | hw
      · rcases hCR w hw hwC with rfl | rfl
        · left; rw [List.head?_append, hRh]; rfl
        · exact absurd hwC (hlrC (by omega) hs)
      · right; rw [hl', hTC w hw hwC]
    · intro w hw hw'
      rcases List.mem_append.mp hw' with hw' | hw'
      · exact hdisj hw hw'
      · exact hTS w hw' (hQS w hw)
  · -- third case: `v₁` and `v₂` are in `m`
    have hv₁ := hlrD (by omega) hj
    have hv₂ := hlrD (by omega) hs
    rcases (by omega : r ≤ n ∨ r = n + 1) with hr'' | hr''
    · have hu₂ : u₂ ∈ A := hDA (by omega) hr'' hr
      have hRl' : ∀ w ∈ R.support, w ∈ a :: m ++ [b] → w = v₂ := fun w hw hwl => by
        rcases hRD w hw (l_D hwl) with rfl | rfl
        · exact absurd hwl (hS.A_not_l hu₂)
        · rfl
      have hRC : ∀ w ∈ R.support, w ∈ C → w = u₂ := fun w hw hwC => by
        rcases hCR w hw hwC with rfl | rfl
        · rfl
        · exact absurd hwC (hlrC (by omega) hs)
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have hu₁ := hD0 hi
        subst hu₁
        exact hS.case4_search hverts hlr hlp_mem (p₂ := j - (n + 1)) (p₃ := s - (n + 1))
          (p₄ := m.length + 1) (by omega) (by omega) (by rw [hlrlen]; omega) hv₁ hv₂ hlra hu₂
          hQ_base.reverse hRc hRnd hRh hRl hRS hRl' hRC hQc' hQnd' hQh' hQl' hQS'
          (fun w hw hwl => hQD' w hw (l_D hwl))
          (fun w hw hwC => by
            rcases hQD' w hw (hS.C_S₁ hwC (hQS' w hw)) with rfl | rfl
            · exact hlrl (by omega) hj
            · simp)
          hdisj'
      · have hu₁ : u₁ ∈ A := hDA hi0 (by omega) hi
        obtain ⟨hEc, hEnd, hEh, hEl, hEm⟩ := extend_start (fun _ _ h => h.symm)
          hlr.chain hlr.nodup (p := j - (n + 1)) (by rw [hlrlen]; omega)
          hv₁ hQc hQnd hQl (fun w hw hwl => by
            rcases hQD w hw (l_D ((hlr.mem w).mp hwl)) with rfl | rfl
            · exact absurd ((hlr.mem _).mp hwl) (hS.A_not_l hu₁)
            · rfl)
        rw [hlr.head] at hEl
        obtain ⟨d, hd, T, hTc, hTnd, hTl, hTS, hTC⟩ := hS.kext (hlrl (by omega) hs)
        obtain ⟨qd, hqd, rfl⟩ := List.getElem_of_mem hd
        have hT : T ≠ [] := by
          rintro rfl
          have hzd : v₂ = B[qd] := by simpa using hTl
          exact hS.B_not_l hd (hzd ▸ hlrl (by omega) hs)
        have hYl : (R.support ++ T).getLast? = some B[qd] := by
          obtain ⟨t, T', rfl⟩ := List.exists_cons_of_ne_nil hT
          rw [List.getLast?_cons_cons] at hTl
          rw [List.getLast?_append, hTl]
          rfl
        have hlrS : ∀ {w : V} {q : ℕ} (hq : q < (a :: m ++ [b]).reverse.length),
            (a :: m ++ [b]).reverse[q] = w → w ∈ S₁ := fun hq he =>
          hS.l_S₁ ((hlr.mem _).mp (he ▸ List.getElem_mem hq))
        have hE_mem := mem_figure11CandidateChains_ext hQ_base hlp_mem hlr.nodup hQl hv₁
        refine runCandidateSearches_isSome_of_lists_idx hverts hS.nodupC hS.rot
          (i := i) (r := r) (j := n + 1) (s := n + 2 + qd)
          hir (by omega) (by omega) (by omega) hE_mem hEc hEnd
          (by rw [hEh, hQh, ← hi, hDT (by omega)]) (by rw [hEl, hTb])
          (fun w hw hwC => ?_) (isChain_append_of_last hRc hRl hTc)
          (List.nodup_append.mpr ⟨hRnd, (List.nodup_cons.mp hTnd).2,
            fun u hu v hv huv => hTS v hv (huv ▸ hRS u hu)⟩)
          (by rw [List.head?_append, hRh, Option.some_or, ← hr, hDT (by omega)])
          (by rw [hYl, hTB, List.getElem?_eq_getElem hqd]) (fun w hw hwC => ?_) ?_
        · rcases hEm w hw with hw | ⟨q, hq, rfl, hlt⟩
          · rcases hCQ w hw hwC with rfl | rfl
            · left; rw [hEh, hQh]
            · exact absurd hwC (hlrC (by omega) hj)
          · right
            rw [hEl]
            rcases hS.C_l hwC ((hlr.mem _).mp (List.getElem_mem hq)) with h | h
            · exfalso
              obtain ⟨ha0, ha'⟩ := List.getElem?_eq_some_iff.mp hlra
              have := (hlr.nodup.getElem_inj_iff).mp (h.trans ha'.symm)
              omega
            · rw [h]
        · rcases List.mem_append.mp hw with hw | hw
          · rcases hCR w hw hwC with rfl | rfl
            · left; rw [List.head?_append, hRh]; rfl
            · exact absurd hwC (hlrC (by omega) hs)
          · right; rw [hYl, hTC w hw hwC]
        · intro w hw hw'
          rcases List.mem_append.mp hw' with hw' | hw'
          · rcases hEm w hw with hw | ⟨q, hq, rfl, hlt⟩
            · exact hdisj hw hw'
            · have h1 := hRl' _ hw' ((hlr.mem _).mp (List.getElem_mem hq))
              obtain ⟨h20, h2⟩ := List.getElem?_eq_some_iff.mp hv₂
              have := (hlr.nodup.getElem_inj_iff).mp (h1.trans h2.symm)
              omega
          · rcases hEm w hw with hw | ⟨q, hq, rfl, hlt⟩
            · exact hTS _ hw' (hQS _ hw)
            · exact hTS _ hw' (hlrS hq rfl)
    · subst hr''
      have hu₂ := hDb hr
      subst hu₂
      rcases Nat.eq_zero_or_pos i with hi0 | hi0
      · subst hi0
        have hu₁ := hD0 hi
        subst hu₁
        exact hS.case5_search hverts hlr hlp_mem (p₁ := 0) (p₂ := j - (n + 1)) (p₃ := s - (n + 1))
          (p₄ := m.length + 1) (by omega) (by omega) (by omega) (by rw [hlrlen]; omega) hlrb hv₁
          hv₂ hlra hR_base hQ_base.reverse hRc hRnd hRh hRl hRS hRD hQc' hQnd' hQh' hQl' hQS' hQD'
          hdisj'
      · have hu₁ : u₁ ∈ A := hDA hi0 (by omega) hi
        exact hS.case4_search hverts hlr hlp_mem (p₂ := 0) (p₃ := j - (n + 1)) (p₄ := s - (n + 1))
          (by omega) (by omega) (by rw [hlrlen]; omega) hlrb hv₁ hv₂ hu₁ hR_base hQc hQnd hQh hQl
          hQS (fun w hw hwl => by
            rcases hQD w hw (l_D hwl) with rfl | rfl
            · exact absurd hwl (hS.A_not_l hu₁)
            · rfl)
          (fun w hw hwC => by
            rcases hCQ w hw hwC with rfl | rfl
            · rfl
            · exact absurd hwC (hlrC (by omega) hj))
          hRc hRnd hRh hRl hRS (fun w hw hwl => hRD w hw (l_D hwl))
          (fun w hw hwC => by
            rcases hCR w hw hwC with rfl | rfl
            · simp
            · exact hlrl (by omega) hs)
          hdisj
  · -- fourth case: `u₂`, `v₁`, `v₂` are in `m`
    have hu₂ := hlrD (by omega) hr
    have hv₁ := hlrD (by omega) hj
    have hv₂ := hlrD (by omega) hs
    rcases (by omega : i = 0 ∨ (1 ≤ i ∧ i ≤ n) ∨ i = n + 1) with hi0 | ⟨hi1, hi2⟩ | hi0
    · subst hi0
      have hu₁ := hD0 hi
      subst hu₁
      exact hS.case5_search hverts hlr hlp_mem (p₁ := r - (n + 1)) (p₂ := j - (n + 1))
        (p₃ := s - (n + 1)) (p₄ := m.length + 1) (by omega) (by omega) (by omega)
        (by rw [hlrlen]; omega) hu₂ hv₁ hv₂ hlra hR_base hQ_base.reverse
        hRc hRnd hRh hRl hRS hRD hQc' hQnd' hQh' hQl' hQS' hQD' hdisj'
    · have hu₁ : u₁ ∈ A := hDA hi1 hi2 hi
      exact hS.case4_search hverts hlr hlp_mem (p₂ := r - (n + 1)) (p₃ := j - (n + 1))
        (p₄ := s - (n + 1)) (by omega) (by omega) (by rw [hlrlen]; omega) hu₂ hv₁ hv₂ hu₁ hR_base
        hQc hQnd hQh hQl hQS (fun w hw hwl => by
          rcases hQD w hw (l_D hwl) with rfl | rfl
          · exact absurd hwl (hS.A_not_l hu₁)
          · rfl)
        (fun w hw hwC => by
          rcases hCQ w hw hwC with rfl | rfl
          · rfl
          · exact absurd hwC (hlrC (by omega) hj))
        hRc hRnd hRh hRl hRS (fun w hw hwl => hRD w hw (l_D hwl))
        (fun w hw hwC => by
          rcases hCR w hw hwC with rfl | rfl
          · exact hlrl (by omega) hr
          · exact hlrl (by omega) hs)
        hdisj
    · subst hi0
      have hu₁ := hDb hi
      subst hu₁
      exact hS.case5_search hverts hlr hlp_mem (p₁ := 0) (p₂ := r - (n + 1)) (p₃ := j - (n + 1))
        (p₄ := s - (n + 1)) (by omega) (by omega) (by omega) (by rw [hlrlen]; omega) hlrb hu₂ hv₁
        hv₂ hQ_base hR_base hQc hQnd hQh hQl hQS hQD hRc hRnd hRh hRl hRS hRD hdisj
  · -- fifth case: all four ends in `m`
    exact hS.case5_search hverts hlr hlp_mem (p₁ := i - (n + 1)) (p₂ := r - (n + 1))
      (p₃ := j - (n + 1)) (p₄ := s - (n + 1)) (by omega) (by omega) (by omega)
      (by rw [hlrlen]; omega) (hlrD (by omega) hi) (hlrD (by omega) hr) (hlrD (by omega) hj)
      (hlrD (by omega) hs) hQ_base hR_base hQc hQnd hQh hQl hQS hQD hRc hRnd hRh hRl hRS hRD hdisj

end Setting

end GraphMinor.HP25
