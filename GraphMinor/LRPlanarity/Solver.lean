module

public import GraphMinor.LRPlanarity.SolverFormula

/-!
# Correctness of the Boolean Left-Right Solver (`SolverStatement`, Part II)

This module proves `SolverStatement` from `GraphMinor/LRPlanarity/Statements.lean`:
the postorder Boolean solver `lrTest` accepts a valid adjacency list family if and
only if there exists a coloring of the back edges satisfying all fork constraints
and all weak alignments of the depth-first forest.
-/

@[expose] public section
namespace GraphMinor.LRPlanarity

open Classical

/-! ## Invariance of `solveOutgoing` and `solveLoop` under `postorder` Replacement -/

theorem solveOutgoing_with_postorder (s : Search) (p : List ℕ) (out : List ℕ)
    (results : Array (Option Summary)) (summary : Option Summary) :
    solveOutgoing { s with postorder := p } out results summary =
      solveOutgoing s out results summary := by
  induction out generalizing results summary with
  | nil => rfl
  | cons i rest ih =>
    simp only [solveOutgoing]
    rcases merge summary
      (if (s.edges[i]!).tree = true then (results[(s.edges[i]!).target]!, results.set! (s.edges[i]!).target none)
       else (some ⟨(s.depth[(s.edges[i]!).target]?.join).getD 0,
         [⟨i, (s.depth[(s.edges[i]!).target]?.join).getD 0⟩], []⟩, results)).1 with _ | summary'
    · rfl
    · exact ih _ summary'

theorem solveLoop_with_postorder (s : Search) (p : List ℕ) (outgoing : Array (List ℕ))
    (l : List ℕ) (results : Array (Option Summary)) :
    solveLoop { s with postorder := p } outgoing l results =
      solveLoop s outgoing l results := by
  induction l generalizing results with
  | nil => rfl
  | cons v rest ih =>
    simp only [solveLoop, solveOutgoing_with_postorder]
    rcases solveOutgoing s outgoing[v]! results none with _ | ⟨rs, summary⟩
    · rfl
    · exact ih _

theorem getElem!_set!_OptionSummary (a : Array (Option Summary)) (i j : ℕ) (x : Option Summary)
    (hi : i < a.size) :
    (a.set! i x)[j]! = if j = i then x else a[j]! := by
  by_cases hj : j = i
  · subst hj
    simp [Array.set!, Array.setIfInBounds, hi]
  · simp only [hj, ↓reduceIte]
    by_cases hlt : j < a.size
    · simp [Array.set!, Array.setIfInBounds, hi, hlt, Ne.symm hj]
    · simp [hlt]

/-! ## Base Case and Prefix Monotonicity for `PrefFormula` -/

theorem prefReturns_nil (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search) :
    PrefReturns N G s [] = ∅ := by
  ext b
  simp [PrefReturns]

theorem prefFormula_nil (N : ℕ) [NeZero N] (G : SimpleGraph (Fin N)) (s : Search)
    (c : ℕ → Color) :
    PrefFormula N G s [] c := by
  refine ⟨by simp, by simp, ?_⟩
  intro b hb
  simp [Forest.minDepthSet, PrefReturns] at hb

theorem prefFormula_prefix_of_append {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {s : Search} {L₁ L₂ : List ℕ}
    (hpair : (L₁ ++ L₂).Pairwise
      (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)))
    {c : ℕ → Color} (hform : PrefFormula N G s (L₁ ++ L₂) c) :
    PrefFormula N G s L₁ c := by
  let T := s.forest N
  have hcross := (List.pairwise_append.mp hpair).2.2
  have hmin_sub :
      T.minDepthSet (PrefReturns N G s L₁) ⊆ T.minDepthSet (PrefReturns N G s (L₁ ++ L₂)) := by
    rintro b₁ ⟨⟨k, hk, hbk⟩, hb₁_min⟩
    refine ⟨⟨k, List.mem_append_left _ hk, hbk⟩, ?_⟩
    rintro b₂ ⟨j, hj, hbj⟩
    rcases List.mem_append.mp hj with hj₁ | hj₂
    · exact hb₁_min b₂ ⟨j, hj₁, hbj⟩
    · obtain ⟨b₀, hb₀_ret, hb₀_eq⟩ :=
        T.exists_mem_returns_depth_eq_low G (arcOfIdx N s k) ⟨b₁, hbk⟩
      have h1 : T.depth b₁.2 ≤ T.low G (arcOfIdx N s k) :=
        hb₀_eq ▸ hb₁_min b₀ ⟨k, hk, hb₀_ret⟩
      have h2 : T.low G (arcOfIdx N s k) ≤ T.low G (arcOfIdx N s j) :=
        T.low_le_of_key_le G _ _ (hcross k hk j hj₂)
      have h3 : T.low G (arcOfIdx N s j) ≤ T.depth b₂.2 :=
        T.low_le_depth_of_mem_returns G (arcOfIdx N s j) b₂ hbj
      exact le_trans h1 (le_trans h2 h3)
  rcases hform with ⟨hbr, hfork, hmono⟩
  refine ⟨fun i hi => hbr i (List.mem_append_left _ hi),
    fun i hi j hj hne => hfork i (List.mem_append_left _ hi) j (List.mem_append_left _ hj) hne,
    hmono.subset hmin_sub⟩

/-! ## Specification of `solveOutgoing` -/

theorem solveOutgoing_loop_spec {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    (v : Fin N) (out : List ℕ)
    (hnodup : out.Nodup)
    (hout : ∀ i, i ∈ out ↔ i < s.edges.size ∧ (s.edges[i]!).source = v.val)
    (hkey_pair : out.Pairwise
      (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)))
    (results₀ : Array (Option Summary))
    (hchildren : ∀ w : Fin N, (s.forest N).TreeEdge (v, w) →
      SummaryRep N G s results₀[w.val]! ((s.forest N).returns G (v, w)) ∧
      ProjectsTo (fun c => (s.forest N).SubtreeFormula G w (toColoring N s c))
        (edgeSet N s ((s.forest N).returns G (v, w)))
        (SummaryFormula results₀[w.val]!))
    (rem pref : List ℕ) (hsplit : pref ++ rem = out)
    (rs : Array (Option Summary)) (summary : Option Summary)
    (hrs_sz : rs.size = N)
    (hrs_eq : ∀ u < N,
      (∀ k ∈ pref, (s.edges[k]!).tree = true → (s.edges[k]!).target ≠ u) →
      rs[u]! = results₀[u]!)
    (hrep : SummaryRep N G s summary (PrefReturns N G s pref))
    (hproj : ProjectsTo (PrefFormula N G s pref)
      (edgeSet N s (PrefReturns N G s pref)) (SummaryFormula summary)) :
    match solveOutgoing s rem rs summary with
    | none => ¬ ∃ c, PrefFormula N G s out c
    | some (rs_final, summary_final) =>
      rs_final.size = N ∧
      (∀ u < N, (∀ k ∈ out, (s.edges[k]!).tree = true → (s.edges[k]!).target ≠ u) →
        rs_final[u]! = results₀[u]!) ∧
      SummaryRep N G s summary_final (PrefReturns N G s out) ∧
      ProjectsTo (PrefFormula N G s out)
        (edgeSet N s (PrefReturns N G s out))
        (SummaryFormula summary_final) := by
  induction rem generalizing pref rs summary with
  | nil =>
    rw [List.append_nil] at hsplit
    subst hsplit
    simp only [solveOutgoing]
    exact ⟨hrs_sz, hrs_eq, hrep, hproj⟩
  | cons i rest ih =>
    have hsplit' : (pref ++ [i]) ++ rest = out := by
      simpa [List.append_assoc] using hsplit
    have hsub_pref_i : (pref ++ [i]).Sublist out :=
      hsplit' ▸ List.sublist_append_left (pref ++ [i]) rest
    have hnodup_pi : (pref ++ [i]).Nodup := hnodup.sublist hsub_pref_i
    have hout_pi : ∀ k ∈ pref ++ [i], k < s.edges.size ∧ (s.edges[k]!).source = v.val :=
      fun k hk => (hout k).mp (hsub_pref_i.subset hk)
    have hpair_pi : (pref ++ [i]).Pairwise
        (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)) :=
      hkey_pair.sublist hsub_pref_i
    have hi_in_pi : i ∈ pref ++ [i] := List.mem_append_right _ (List.mem_singleton_self i)
    obtain ⟨hi_lt, hi_src⟩ := hout_pi i hi_in_pi
    have hi_not_pref : i ∉ pref :=
      fun hi => (List.nodup_append.mp hnodup_pi).2.2 i hi i (List.mem_singleton_self i) rfl
    let e := s.edges[i]!
    let stepPair : Option Summary × Array (Option Summary) :=
      if e.tree then (rs[e.target]!, rs.set! e.target none)
      else (some ⟨(s.depth[e.target]?.join).getD 0,
        [⟨i, (s.depth[e.target]?.join).getD 0⟩], []⟩, rs)
    let child := stepPair.1
    let rs' := stepPair.2
    have hstep_child :
        rs'.size = N ∧
        (∀ u < N,
          (∀ k ∈ pref ++ [i], (s.edges[k]!).tree = true → (s.edges[k]!).target ≠ u) →
          rs'[u]! = results₀[u]!) ∧
        SummaryRep N G s child ((s.forest N).returns G (arcOfIdx N s i)) ∧
        ProjectsTo (BranchFormula N G s i)
          (edgeSet N s ((s.forest N).returns G (arcOfIdx N s i)))
          (SummaryFormula child) := by
      rcases arcOfIdx_tree_or_back hAdj hinv hall hi_lt with ⟨htr, hte⟩ | ⟨htr, _⟩
      · -- Tree edge case
        have hchild_eq : child = rs[e.target]! := by simp [child, stepPair, e, htr]
        have hrs'_eq_def : rs' = rs.set! e.target none := by simp [rs', stepPair, e, htr]
        let w : Fin N := (arcOfIdx N s i).2
        have hw_val : w.val = e.target := arcOfIdx_snd_val hinv hi_lt
        have hw_lt : e.target < N := hw_val ▸ w.isLt
        have harc_eq : arcOfIdx N s i = (v, w) := by
          ext
          · exact (arcOfIdx_fst_val hinv hi_lt).trans hi_src
          · rfl
        have hte_vw : (s.forest N).TreeEdge (v, w) := harc_eq ▸ hte
        have hrs_w : rs[e.target]! = results₀[w.val]! := by
          rw [← hw_val]
          apply hrs_eq w.val w.isLt
          intro k hk hktr hktgt
          have hk_in_pi : k ∈ pref ++ [i] := List.mem_append_left _ hk
          obtain ⟨hk_lt, hk_src⟩ := hout_pi k hk_in_pi
          have hki : k = i :=
            hinv.edges_inj k hk_lt i hi_lt (hk_src.trans hi_src.symm) (hktgt.trans hw_val)
          exact hi_not_pref (hki ▸ hk)
        obtain ⟨hrep_w, hproj_w⟩ := hchildren w hte_vw
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hrs'_eq_def, Array.size_set!]
          exact hrs_sz
        · intro u hu hno
          rw [hrs'_eq_def, getElem!_set!_OptionSummary rs e.target u none (hrs_sz ▸ hw_lt)]
          have hne_u : u ≠ e.target := Ne.symm (hno i hi_in_pi htr)
          simp only [hne_u, ↓reduceIte]
          exact hrs_eq u hu (fun k hk => hno k (List.mem_append_left _ hk))
        · rw [hchild_eq, hrs_w, harc_eq]
          exact hrep_w
        · rw [hchild_eq, hrs_w, harc_eq]
          refine ProjectsTo.congr_left hproj_w ?_
          intro c
          simp [BranchFormula, htr, w]
      · -- Back edge case
        have hchild_eq : child = some ⟨(s.depth[e.target]?.join).getD 0,
            [⟨i, (s.depth[e.target]?.join).getD 0⟩], []⟩ := by
          simp [child, stepPair, e, htr]
        have hrs'_eq_def : rs' = rs := by simp [rs', stepPair, e, htr]
        refine ⟨hrs'_eq_def ▸ hrs_sz, ?_, ?_, ?_⟩
        · intro u hu hno
          rw [hrs'_eq_def]
          exact hrs_eq u hu (fun k hk => hno k (List.mem_append_left _ hk))
        · rw [hchild_eq]
          exact SummaryRep.singleton_back hAdj hinv hall hi_lt htr
        · rw [hchild_eq]
          intro c
          have hbr_c : ∀ c', BranchFormula N G s i c' := by
            intro c'; simp [BranchFormula, htr]
          exact ⟨fun _ => ⟨c, hbr_c c, fun _ _ => rfl⟩,
            fun _ => summaryFormula_singleton _ i c⟩
    obtain ⟨hrs'_sz, hrs'_eq, hrep₂, hproj₂⟩ := hstep_child
    have hmerge := merge_step_spec hAdj hinv hall v pref i
      hnodup_pi hout_pi hpair_pi summary child hrep hproj hrep₂ hproj₂
    simp only [solveOutgoing]
    change match (do
        let summary ← merge summary child
        solveOutgoing s rest rs' summary) with
      | none => ¬ ∃ c, PrefFormula N G s out c
      | some (rs_final, summary_final) => _
    rcases hmerge_eq : merge summary child with _ | summary'
    · rw [hmerge_eq] at hmerge
      rintro ⟨c, hc⟩
      have hpair_split : ((pref ++ [i]) ++ rest).Pairwise
          (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)) :=
        hsplit'.symm ▸ hkey_pair
      exact hmerge ⟨c, prefFormula_prefix_of_append hpair_split (hsplit'.symm ▸ hc)⟩
    · rw [hmerge_eq] at hmerge
      exact ih (pref ++ [i]) hsplit' rs' summary' hrs'_sz hrs'_eq hmerge.1 hmerge.2

theorem solveOutgoing_spec {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    (v : Fin N) (out : List ℕ)
    (hnodup : out.Nodup)
    (hout : ∀ i, i ∈ out ↔ i < s.edges.size ∧ (s.edges[i]!).source = v.val)
    (hkey_pair : out.Pairwise
      (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)))
    (results₀ : Array (Option Summary)) (hsz₀ : results₀.size = N)
    (hchildren : ∀ w : Fin N, (s.forest N).TreeEdge (v, w) →
      SummaryRep N G s results₀[w.val]! ((s.forest N).returns G (v, w)) ∧
      ProjectsTo (fun c => (s.forest N).SubtreeFormula G w (toColoring N s c))
        (edgeSet N s ((s.forest N).returns G (v, w)))
        (SummaryFormula results₀[w.val]!)) :
    match solveOutgoing s out results₀ none with
    | none => ¬ ∃ color, (s.forest N).ForkConstraints G color ∧ (s.forest N).WeakAlignment G color
    | some (rs_final, summary_final) =>
      rs_final.size = N ∧
      (∀ y : Fin N, (s.forest N).parent y ≠ some v → rs_final[y.val]! = results₀[y.val]!) ∧
      SummaryRep N G s summary_final ((s.forest N).allReturnsAt G v) ∧
      ProjectsTo (fun c => (s.forest N).SubtreeFormula G v (toColoring N s c))
        (edgeSet N s ((s.forest N).allReturnsAt G v))
        (SummaryFormula summary_final) := by
  have hrep₀ : SummaryRep N G s none (PrefReturns N G s []) := by
    rw [prefReturns_nil]
    exact SummaryRep.none G s
  have hproj₀ : ProjectsTo (PrefFormula N G s [])
      (edgeSet N s (PrefReturns N G s [])) (SummaryFormula none) := by
    intro c
    exact ⟨fun _ => ⟨c, prefFormula_nil N G s c, fun _ _ => rfl⟩, fun _ => trivial⟩
  have hloop := solveOutgoing_loop_spec hAdj hinv hall v out hnodup hout hkey_pair
    results₀ hchildren out [] (List.nil_append out) results₀ none hsz₀
    (fun _ _ _ => rfl) hrep₀ hproj₀
  obtain ⟨hret_eq, hform_iff⟩ := prefFormula_outgoing_iff_subtreeFormula hAdj hinv hall v out hout
  rcases hres : solveOutgoing s out results₀ none with _ | ⟨rs_final, summary_final⟩
  · rw [hres] at hloop
    rintro ⟨color, hfork, halign⟩
    have hDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
    have hvc := ((s.forest N).fork_and_align_iff_forall_vertexConstraint hDFS color).mp ⟨hfork, halign⟩
    have hsub_v : (s.forest N).SubtreeFormula G v color := fun x _ => hvc x
    let c : ℕ → Color := fun i => color (arcOfIdx N s i)
    have hsub_c : (s.forest N).SubtreeFormula G v (toColoring N s c) := by
      refine (s.forest N).subtreeFormula_congr (fun b hb => ?_) hsub_v
      dsimp [toColoring, c]
      rw [(idxOfArc_spec hAdj hinv hall (Or.inr hb.1)).2]
    exact hloop ⟨c, (hform_iff c).mpr hsub_c⟩
  · rw [hres] at hloop
    obtain ⟨hrs_sz, hrs_eq, hrep_out, hproj_out⟩ := hloop
    rw [hret_eq] at hrep_out hproj_out
    refine ⟨hrs_sz, ?_, hrep_out, ProjectsTo.congr_left hproj_out hform_iff⟩
    intro y hy_par
    apply hrs_eq y.val y.isLt
    intro k hk hktr hktgt
    obtain ⟨hk_lt, hk_src⟩ := (hout k).mp hk
    have hpar_y : s.parent[y.val]?.join = some v.val :=
      (hinv.parent_iff_edge y.val y.isLt v.val).mpr ⟨k, hk_lt, hktr, hk_src, hktgt⟩
    exact hy_par ((hinv.forest_parent_some_iff v y).mpr hpar_y)

/-! ## Specification of `solveLoop` -/

theorem Forest.returns_treeEdge_eq_weakReturns_lt {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} (hDFS : T.IsDFS G) {u v : Fin N} (hte : T.TreeEdge (u, v)) :
    {b | b ∈ T.weakReturns G (u, v) ∧ T.depth b.2 < T.depth u} = T.returns G (u, v) := by
  rw [← T.allReturnsAt_eq_weakReturns_of_treeEdge hDFS hte,
    T.returns_treeEdge_eq_filter_allReturnsAt hDFS hte]

theorem solveLoop_spec {N : ℕ} [NeZero N] {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search}
    (hAdj : Compute.IsAdjListFamily G lists)
    (hinv : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v)
    (outgoing : Array (List ℕ))
    (hout_spec : ∀ v : Fin N,
      let out := outgoing[v.val]!
      out.Nodup ∧
      (∀ i, i ∈ out ↔ i < s.edges.size ∧ (s.edges[i]!).source = v.val) ∧
      out.Pairwise
        (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)))
    (rem_post done_post : List ℕ)
    (hsplit : done_post ++ rem_post = s.postorder.reverse)
    (results : Array (Option Summary))
    (hres_sz : results.size = N)
    (hroots : ∀ w : Fin N, w.val ∈ done_post → (s.forest N).parent w = none →
      ∃ color, (s.forest N).SubtreeFormula G w color)
    (hnonroots : ∀ u w : Fin N, w.val ∈ done_post → u.val ∈ rem_post →
      (s.forest N).TreeEdge (u, w) →
      SummaryRep N G s results[w.val]! ((s.forest N).returns G (u, w)) ∧
      ProjectsTo (fun c => (s.forest N).SubtreeFormula G w (toColoring N s c))
        (edgeSet N s ((s.forest N).returns G (u, w)))
        (SummaryFormula results[w.val]!)) :
    solveLoop s outgoing rem_post results = true ↔
      ∃ color, (s.forest N).ForkConstraints G color ∧ (s.forest N).WeakAlignment G color := by
  have hDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
  have hpost_nodup : s.postorder.reverse.Nodup := by
    have hnodup := hinv.nodup_verts
    simp only [List.map_nil, List.nil_append] at hnodup
    exact List.nodup_reverse.mpr hnodup
  have hpost_mem : ∀ x, x ∈ s.postorder.reverse ↔ x < N := by
    intro x
    rw [List.mem_reverse]
    constructor
    · exact fun hx => hinv.postorder_lt x hx
    · intro hx
      have hvis := (hinv.visited_iff x).mp (hall x hx)
      simpa using hvis
  have hpost_pair : s.postorder.reverse.Pairwise (fun x y => s.parent[y]?.join ≠ some x) :=
    List.pairwise_reverse.mpr hinv.postorder_order
  induction rem_post generalizing done_post results with
  | nil =>
    rw [List.append_nil] at hsplit
    simp only [solveLoop, true_iff]
    refine (s.forest N).exists_global_of_roots hDFS ?_
    intro r hr
    apply hroots r _ hr
    rw [hsplit, hpost_mem]
    exact r.isLt
  | cons v_val rest ih =>
    have hv_in_rev : v_val ∈ s.postorder.reverse := by
      rw [← hsplit]
      exact List.mem_append_right _ List.mem_cons_self
    have hv_lt : v_val < N := (hpost_mem v_val).mp hv_in_rev
    let v : Fin N := ⟨v_val, hv_lt⟩
    obtain ⟨hout_nodup, hout_mem, hout_pair⟩ := hout_spec v
    have hrem_pair : (v_val :: rest).Pairwise (fun x y => s.parent[y]?.join ≠ some x) :=
      (List.pairwise_append.mp (hsplit ▸ hpost_pair)).2.1
    have hv_not_parent_rest : ∀ y ∈ rest, s.parent[y]?.join ≠ some v_val :=
      (List.pairwise_cons.mp hrem_pair).1
    have hchildren_v : ∀ w : Fin N, (s.forest N).TreeEdge (v, w) →
        SummaryRep N G s results[w.val]! ((s.forest N).returns G (v, w)) ∧
        ProjectsTo (fun c => (s.forest N).SubtreeFormula G w (toColoring N s c))
          (edgeSet N s ((s.forest N).returns G (v, w)))
          (SummaryFormula results[w.val]!) := by
      intro w hte
      have hpar_w : s.parent[w.val]?.join = some v_val :=
        (hinv.forest_parent_some_iff v w).mp hte
      have hw_in_rev : w.val ∈ done_post ++ (v_val :: rest) := by
        rw [hsplit, hpost_mem]
        exact w.isLt
      have hw_in_done : w.val ∈ done_post := by
        rcases List.mem_append.mp hw_in_rev with hw_done | hw_rem
        · exact hw_done
        · rcases List.mem_cons.mp hw_rem with hw_eq | hw_rest
          · have hvw : w = v := Fin.ext hw_eq
            have hstep := hinv.depth_step v w hte
            rw [hvw] at hstep
            omega
          · exact absurd hpar_w (hv_not_parent_rest w.val hw_rest)
      exact hnonroots v w hw_in_done List.mem_cons_self hte
    have hout_res := solveOutgoing_spec hAdj hinv hall v outgoing[v_val]!
      hout_nodup hout_mem hout_pair results hres_sz hchildren_v
    simp only [solveLoop]
    rcases hout_eq : solveOutgoing s outgoing[v_val]! results none with _ | ⟨rs, summary⟩
    · rw [hout_eq] at hout_res
      simp only [Bool.false_eq_true, false_iff]
      exact hout_res
    · rw [hout_eq] at hout_res
      obtain ⟨hrs_sz, hrs_other, hrep_v, hproj_v⟩ := hout_res
      let summary' := match s.parent[v_val]?.join with
        | none => summary
        | some u => trim summary ((s.depth[u]?.join).getD 0)
      let results' := rs.set! v_val summary'
      have hsplit' : (done_post ++ [v_val]) ++ rest = s.postorder.reverse := by
        simpa [List.append_assoc] using hsplit
      have hnodup_split := List.nodup_append.mp (hsplit ▸ hpost_nodup)
      have hv_not_done : v_val ∉ done_post :=
        fun hv_d => hnodup_split.2.2 v_val hv_d v_val List.mem_cons_self rfl
      have hv_not_rest : v_val ∉ rest := (List.nodup_cons.mp hnodup_split.2.1).1
      apply ih (done_post ++ [v_val]) hsplit' results'
      · simp [results', hrs_sz]
      · intro w hw hroot_w
        rcases List.mem_append.mp hw with hw_done | hw_v
        · exact hroots w hw_done hroot_w
        · have hw_eq : w = v := Fin.ext (List.mem_singleton.mp hw_v)
          subst hw_eq
          have hemp : (s.forest N).allReturnsAt G v = ∅ :=
            (s.forest N).allReturnsAt_eq_empty_of_root hDFS hroot_w
          rw [hemp] at hrep_v hproj_v
          have hsum_none : summary = none := hrep_v.none_iff.mpr rfl
          rw [hsum_none] at hproj_v
          obtain ⟨c, hc, _⟩ := (hproj_v (fun _ => .left)).mp trivial
          exact ⟨toColoring N s c, hc⟩
      · intro u w hw hu_rest hte_uw
        have hu_ne_v : u ≠ v := by
          intro heq
          have : u.val = v_val := congrArg Fin.val heq
          exact hv_not_rest (this ▸ hu_rest)
        rcases List.mem_append.mp hw with hw_done | hw_v
        · have hw_ne_v : w.val ≠ v_val := fun heq => hv_not_done (heq ▸ hw_done)
          have hpar_ne_v : (s.forest N).parent w ≠ some v := by
            rw [hte_uw]
            exact fun h => hu_ne_v (Option.some.inj h)
          have hres'_w : results'[w.val]! = results[w.val]! := by
            change (rs.set! v_val summary')[w.val]! = results[w.val]!
            rw [getElem!_set!_OptionSummary rs v_val w.val summary' (hrs_sz ▸ hv_lt)]
            simp [hw_ne_v, hrs_other w hpar_ne_v]
          rw [hres'_w]
          exact hnonroots u w hw_done (List.mem_cons_of_mem v_val hu_rest) hte_uw
        · have hw_eq : w = v := Fin.ext (List.mem_singleton.mp hw_v)
          subst hw_eq
          have hpar_v : s.parent[v_val]?.join = some u.val :=
            (hinv.forest_parent_some_iff u v).mp hte_uw
          have hsum'_eq : summary' = trim summary ((s.forest N).depth u) := by
            simp [summary', hpar_v, Search.forest]
          have hres'_v : results'[v_val]! = summary' := by
            change (rs.set! v_val summary')[v_val]! = summary'
            rw [getElem!_set!_OptionSummary rs v_val v_val summary' (hrs_sz ▸ hv_lt)]
            simp
          rw [hres'_v, hsum'_eq]
          have hall_eq : (s.forest N).allReturnsAt G v = (s.forest N).weakReturns G (u, v) :=
            (s.forest N).allReturnsAt_eq_weakReturns_of_treeEdge hDFS hte_uw
          rw [hall_eq] at hrep_v hproj_v
          have hd_le : ∀ b ∈ (s.forest N).weakReturns G (u, v),
              (s.forest N).depth b.2 ≤ (s.forest N).depth u :=
            fun _ hb => hb.2.2
          obtain ⟨hrep_trim, hproj_trim⟩ := hrep_v.trim ((s.forest N).depth u) hd_le
          have hset_eq := (s.forest N).returns_treeEdge_eq_weakReturns_lt hDFS hte_uw
          rw [hset_eq] at hrep_trim hproj_trim
          have hsub_edge :
              edgeSet N s ((s.forest N).returns G (u, v)) ⊆
                edgeSet N s ((s.forest N).weakReturns G (u, v)) := by
            intro j hj
            rw [← hset_eq] at hj
            exact ⟨hj.1, hj.2.1, hj.2.2.1⟩
          exact ⟨hrep_trim, ProjectsTo.trans hproj_v hproj_trim hsub_edge⟩

/-! ## Proof of `SolverStatement` -/

/-- Part II, base and completion: the Boolean solver accepts exactly when a
coloring satisfies all fork constraints and all weak alignments. -/
theorem solverStatement : SolverStatement := by
  intro N G lists search hAdj hdfs
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · obtain ⟨s, hs, hinv, _⟩ := depthFirstSearch_spec hAdj
    rw [hs] at hdfs
    injection hdfs with hsearch_eq
    subst hsearch_eq
    have hpost_nil : s.postorder = [] := by
      rcases hp : s.postorder with _ | ⟨x, _⟩
      · rfl
      · have hx : x < 0 := hinv.postorder_lt x (hp ▸ List.mem_cons_self)
        omega
    unfold lrTest
    rw [hs]
    dsimp only
    rw [solve_eq_solveLoop]
    simp only [hpost_nil, List.reverse_nil, solveLoop, true_iff]
    refine ⟨fun _ => .left, ?_, ?_⟩
    · intro v; exact Fin.elim0 v
    · intro e; exact Fin.elim0 e.1
  · have : NeZero N := ⟨Nat.ne_of_gt hN_pos⟩
    obtain ⟨s, hs, hinv, hall⟩ := depthFirstSearch_spec hAdj
    have hlow_stmt := lowpointsStatement N G lists search hAdj hdfs
    rw [hs] at hdfs
    injection hdfs with hsearch_eq
    subst hsearch_eq
    have hDFS : (s.forest N).IsDFS G := hinv.isDFS_of_nil hall
    have hkey_eq : ∀ i < s.edges.size,
        (s.edges[i]!).key = (s.forest N).key G (arcOfIdx N s i) := by
      intro i hi
      obtain ⟨e, he1, he2, _, _, hkey⟩ := hlow_stmt i hi
      have he_eq : e = arcOfIdx N s i := by
        ext
        · exact he1.symm.trans (arcOfIdx_fst_val hinv hi).symm
        · exact he2.symm.trans (arcOfIdx_snd_val hinv hi).symm
      exact he_eq ▸ hkey
    have hbucket_in : ∀ i, i < s.edges.size →
        (s.edges[i]!).source < N ∧ (s.edges[i]!).key ≤ 2 * N := by
      intro i hi
      obtain ⟨hs_lt, _⟩ := hinv.edges_valid i hi
      refine ⟨hs_lt, ?_⟩
      rw [hkey_eq i hi]
      exact (s.forest N).key_le_two_mul_N hDFS (arcOfIdx N s i)
    have hbucket := bucketOrderStatement N s.edges hbucket_in
    have hout_spec : ∀ v : Fin N,
        let out := (bucketOrder N s.edges)[v.val]!
        out.Nodup ∧
        (∀ i, i ∈ out ↔ i < s.edges.size ∧ (s.edges[i]!).source = v.val) ∧
        out.Pairwise
          (fun k j => (s.forest N).key G (arcOfIdx N s k) ≤ (s.forest N).key G (arcOfIdx N s j)) := by
      intro v
      obtain ⟨hnodup, hmem, hpair⟩ := hbucket v.val v.isLt
      refine ⟨hnodup, hmem, ?_⟩
      rw [List.pairwise_iff_getElem] at hpair ⊢
      intro a b ha hb hab
      have ha_lt : ((bucketOrder N s.edges)[v.val]!)[a] < s.edges.size :=
        ((hmem _).mp (List.getElem_mem ha)).1
      have hb_lt : ((bucketOrder N s.edges)[v.val]!)[b] < s.edges.size :=
        ((hmem _).mp (List.getElem_mem hb)).1
      rw [← hkey_eq _ ha_lt, ← hkey_eq _ hb_lt]
      exact hpair a b ha hb hab
    unfold lrTest
    rw [hs]
    dsimp only
    rw [solve_eq_solveLoop, solveLoop_with_postorder]
    exact solveLoop_spec hAdj hinv hall (bucketOrder N s.edges) hout_spec
      s.postorder.reverse [] (List.nil_append _) (Array.replicate N none)
      (by simp) (by simp) (by simp)

end GraphMinor.LRPlanarity
