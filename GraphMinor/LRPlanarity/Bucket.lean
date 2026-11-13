module

public import GraphMinor.LRPlanarity.Statements

/-!
# Correctness of the global bucket pass (`BucketOrderStatement`)

This file proves `BucketOrderStatement` from `GraphMinor/LRPlanarity/Statements.lean`,
following Part I, Section 1 of `docs/planarity/planarity_test.tex`.
-/

@[expose] public section

namespace GraphMinor.LRPlanarity

open Classical

private theorem getElem!_set! {α : Type*} [Inhabited α] (a : Array α) (i : ℕ) (v : α)
    (hi : i < a.size) (j : ℕ) :
    (a.set! i v)[j]! = if j = i then v else a[j]! := by
  by_cases hji : j = i
  · subst hji
    rw [getElem!_pos _ j (by simpa using hi)]
    simp [Array.set!, Array.setIfInBounds, hi]
  · by_cases hj : j < a.size
    · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos _ j hj]
      simp [Array.set!, Array.setIfInBounds, hi, Array.getElem_set, Ne.symm hji, hji]
    · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg _ j hj]
      simp [hji]

private theorem getElem!_replicate {α : Type*} [Inhabited α] (n : ℕ) (v : α)
    {i : ℕ} (hi : i < n) :
    (Array.replicate n v)[i]! = v := by
  rw [getElem!_pos _ i (by simp [hi])]
  simp

private theorem getElem!_map {α β : Type*} [Inhabited α] [Inhabited β]
    (a : Array α) (f : α → β) {i : ℕ} (hi : i < a.size) :
    (a.map f)[i]! = f (a[i]!) := by
  rw [getElem!_pos _ i (by simp [hi]), getElem!_pos _ i hi, Array.getElem_map]

/-- Specification of the first `forIn` pass in `bucketOrder` over any index list `l`. -/
private theorem bucket_pass1_spec (n : ℕ) (edges : Array EdgeRecord)
    (hedges : ∀ i, i < edges.size → edges[i]!.source < n ∧ edges[i]!.key ≤ 2 * n) :
    ∀ (l : List ℕ) (_hl : ∀ i ∈ l, i < edges.size) (buckets : Array (List ℕ))
      (_hsz : buckets.size = 2 * n + 1),
      let res : Array (List ℕ) :=
        forIn (m := Id) l buckets (fun i buckets =>
          ForInStep.yield (buckets.set! edges[i]!.key (i :: buckets[edges[i]!.key]!)))
      res.size = 2 * n + 1 ∧
      ∀ k < 2 * n + 1,
        res[k]! = (l.filter (fun i => edges[i]!.key == k)).reverse ++ buckets[k]! := by
  intro l
  induction l with
  | nil =>
    intro _ buckets hsz
    simp only [List.forIn_nil, List.filter_nil, List.reverse_nil, List.nil_append]
    exact ⟨hsz, fun _ _ => rfl⟩
  | cons i rest ih =>
    intro hl buckets hsz
    simp only [List.forIn_cons]
    dsimp only [bind, pure, Id.run]
    have hi_lt : i < edges.size := hl i (by simp)
    have hkey_le : edges[i]!.key ≤ 2 * n := (hedges i hi_lt).2
    have hkey_sz : edges[i]!.key < buckets.size := by omega
    set buckets₁ := buckets.set! edges[i]!.key (i :: buckets[edges[i]!.key]!)
    have hsz₁ : buckets₁.size = 2 * n + 1 := by simp [buckets₁, hsz]
    obtain ⟨hsz_res, hget_res⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem i hj)) buckets₁ hsz₁
    refine ⟨hsz_res, fun k hk => ?_⟩
    rw [hget_res k hk]
    have hb₁ : buckets₁[k]! = if k = edges[i]!.key then i :: buckets[k]! else buckets[k]! := by
      rw [getElem!_set! buckets edges[i]!.key _ hkey_sz k]
      split_ifs with hkeq
      · subst hkeq; rfl
      · rfl
    rw [hb₁, List.filter_cons]
    by_cases hkeq : edges[i]!.key = k
    · subst hkeq
      simp [List.reverse_cons, List.append_assoc]
    · have hne : k ≠ edges[i]!.key := Ne.symm hkeq
      simp [hkeq, hne]

/-- Specification of the inner `forIn` loop of the second pass in `bucketOrder`. -/
private theorem bucket_pass2_inner_spec (n : ℕ) (edges : Array EdgeRecord)
    (hedges : ∀ i, i < edges.size → edges[i]!.source < n ∧ edges[i]!.key ≤ 2 * n) :
    ∀ (bucket : List ℕ) (_hb : ∀ i ∈ bucket, i < edges.size) (outgoing : Array (List ℕ))
      (_hsz : outgoing.size = n),
      let res : Array (List ℕ) :=
        forIn (m := Id) bucket outgoing (fun i outgoing =>
          ForInStep.yield (outgoing.set! edges[i]!.source (i :: outgoing[edges[i]!.source]!)))
      res.size = n ∧
      ∀ v < n,
        res[v]! = (bucket.filter (fun i => edges[i]!.source == v)).reverse ++ outgoing[v]! := by
  intro bucket
  induction bucket with
  | nil =>
    intro _ outgoing hsz
    simp only [List.forIn_nil, List.filter_nil, List.reverse_nil, List.nil_append]
    exact ⟨hsz, fun _ _ => rfl⟩
  | cons i rest ih =>
    intro hb outgoing hsz
    simp only [List.forIn_cons]
    dsimp only [bind, pure, Id.run]
    have hi_lt : i < edges.size := hb i (by simp)
    have hsrc_lt : edges[i]!.source < n := (hedges i hi_lt).1
    have hsrc_sz : edges[i]!.source < outgoing.size := by omega
    set outgoing₁ := outgoing.set! edges[i]!.source (i :: outgoing[edges[i]!.source]!)
    have hsz₁ : outgoing₁.size = n := by simp [outgoing₁, hsz]
    obtain ⟨hsz_res, hget_res⟩ := ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) outgoing₁ hsz₁
    refine ⟨hsz_res, fun v hv => ?_⟩
    rw [hget_res v hv]
    have ho₁ : outgoing₁[v]! = if v = edges[i]!.source then i :: outgoing[v]! else outgoing[v]! := by
      rw [getElem!_set! outgoing edges[i]!.source _ hsrc_sz v]
      split_ifs with hveq
      · subst hveq; rfl
      · rfl
    rw [ho₁, List.filter_cons]
    by_cases hveq : edges[i]!.source = v
    · subst hveq
      simp [List.reverse_cons, List.append_assoc]
    · have hne : v ≠ edges[i]!.source := Ne.symm hveq
      simp [hveq, hne]

/-- Specification of the outer `forIn` loop of the second pass in `bucketOrder`. -/
private theorem bucket_pass2_outer_spec (n : ℕ) (edges : Array EdgeRecord)
    (hedges : ∀ i, i < edges.size → edges[i]!.source < n ∧ edges[i]!.key ≤ 2 * n) :
    ∀ (bs : List (List ℕ)) (_hbs : ∀ b ∈ bs, ∀ i ∈ b, i < edges.size)
      (outgoing : Array (List ℕ)) (_hsz : outgoing.size = n),
      let res : Array (List ℕ) :=
        forIn (m := Id) bs outgoing (fun bucket outgoing =>
          ForInStep.yield
            (forIn (m := Id) bucket outgoing (fun i outgoing =>
              ForInStep.yield (outgoing.set! edges[i]!.source (i :: outgoing[edges[i]!.source]!)))))
      res.size = n ∧
      ∀ v < n,
        res[v]! = (bs.flatten.filter (fun i => edges[i]!.source == v)).reverse ++ outgoing[v]! := by
  intro bs
  induction bs with
  | nil =>
    intro _ outgoing hsz
    simp only [List.forIn_nil, List.flatten_nil, List.filter_nil, List.reverse_nil, List.nil_append]
    exact ⟨hsz, fun _ _ => rfl⟩
  | cons b rest ih =>
    intro hbs outgoing hsz
    simp only [List.forIn_cons]
    dsimp only [bind, pure, Id.run]
    obtain ⟨hsz₁, hget₁⟩ := bucket_pass2_inner_spec n edges hedges b
      (hbs b (by simp)) outgoing hsz
    obtain ⟨hsz₂, hget₂⟩ := ih (fun b' hb' => hbs b' (List.mem_cons_of_mem b hb')) _ hsz₁
    refine ⟨hsz₂, fun v hv => ?_⟩
    rw [hget₂ v hv, hget₁ v hv, List.flatten_cons, List.filter_append, List.reverse_append,
      List.append_assoc]

/-- Pairwise relation on `l.flatten` from pairwise relation within and across lists in `l`. -/
private theorem pairwise_flatten_of_getElem {α : Type*} {R : α → α → Prop} (l : List (List α))
    (hin : ∀ k (hk : k < l.length), (l[k]).Pairwise R)
    (hcross : ∀ k₁ k₂ (hk₁ : k₁ < l.length) (hk₂ : k₂ < l.length),
      k₁ < k₂ → ∀ x ∈ l[k₁], ∀ y ∈ l[k₂], R x y) :
    l.flatten.Pairwise R := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    rw [List.flatten_cons, List.pairwise_append]
    refine ⟨hin 0 (by simp), ?_, ?_⟩
    · apply ih
      · intro k hk
        exact hin (k + 1) (Nat.succ_lt_succ hk)
      · intro k₁ k₂ hk₁ hk₂ hlt
        exact hcross (k₁ + 1) (k₂ + 1) (Nat.succ_lt_succ hk₁) (Nat.succ_lt_succ hk₂)
          (Nat.succ_lt_succ hlt)
    · intro x hx y hy
      rw [List.mem_flatten] at hy
      obtain ⟨b', hb', hy'⟩ := hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb'
      exact hcross 0 (k + 1) (by simp) (Nat.succ_lt_succ hk) (Nat.succ_pos k) x hx y hy'

/-- Part I, Section 1: one global bucket pass gives all records of each source
exactly once and in nondecreasing key order. -/
theorem bucketOrderStatement : BucketOrderStatement := by
  intro n edges hedges v hv
  unfold bucketOrder
  dsimp only [Id.run, bind, pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', ← Array.forIn_toList]
  have hrange :
      List.range' [:edges.size].start [:edges.size].size [:edges.size].step =
      List.range edges.size := by
    simp [List.range_eq_range']
  rw [hrange]
  have hrange_lt : ∀ i ∈ List.range edges.size, i < edges.size := fun i hi => List.mem_range.mp hi
  have hinit_b_sz : (Array.replicate (2 * n + 1) ([] : List ℕ)).size = 2 * n + 1 := by simp
  obtain ⟨hb_sz, hb_get⟩ := bucket_pass1_spec n edges hedges (List.range edges.size)
    hrange_lt (Array.replicate (2 * n + 1) []) hinit_b_sz
  set buckets : Array (List ℕ) :=
    forIn (m := Id) (List.range edges.size) (Array.replicate (2 * n + 1) []) (fun i buckets =>
      ForInStep.yield (buckets.set! edges[i]!.key (i :: buckets[edges[i]!.key]!)))
  have hb_eq : ∀ k < 2 * n + 1,
      buckets[k]! = ((List.range edges.size).filter (fun i => edges[i]!.key == k)).reverse := by
    intro k hk
    rw [hb_get k hk, getElem!_replicate (2 * n + 1) [] hk, List.append_nil]
  have hb_mem_iff : ∀ k < 2 * n + 1, ∀ i,
      i ∈ buckets[k]! ↔ i < edges.size ∧ edges[i]!.key = k := by
    intro k hk i
    rw [hb_eq k hk, List.mem_reverse, List.mem_filter, List.mem_range, beq_iff_eq]
  have hbs_lt : ∀ b ∈ buckets.toList, ∀ i ∈ b, i < edges.size := by
    intro b hb i hi
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    have hk' : k < 2 * n + 1 := by simpa [hb_sz] using hk
    have hget : buckets.toList[k] = buckets[k]! := by
      rw [Array.getElem_toList, getElem!_pos buckets k hk]
    rw [hget] at hi
    exact ((hb_mem_iff k hk' i).mp hi).1
  have hinit_o_sz : (Array.replicate n ([] : List ℕ)).size = n := by simp
  obtain ⟨ho_sz, ho_get⟩ := bucket_pass2_outer_spec n edges hedges buckets.toList
    hbs_lt (Array.replicate n []) hinit_o_sz
  set outgoing_raw : Array (List ℕ) :=
    forIn (m := Id) buckets.toList (Array.replicate n []) (fun bucket outgoing =>
      ForInStep.yield
        (forIn (m := Id) bucket outgoing (fun i outgoing =>
          ForInStep.yield (outgoing.set! edges[i]!.source (i :: outgoing[edges[i]!.source]!)))))
  have hout_eq : (outgoing_raw.map List.reverse)[v]! =
      buckets.toList.flatten.filter (fun i => edges[i]!.source == v) := by
    have hv_sz : v < outgoing_raw.size := by omega
    rw [getElem!_map outgoing_raw List.reverse hv_sz, ho_get v hv,
      getElem!_replicate n [] hv, List.append_nil, List.reverse_reverse]
  change
    (outgoing_raw.map List.reverse)[v]!.Nodup ∧
    (∀ i, i ∈ (outgoing_raw.map List.reverse)[v]! ↔ i < edges.size ∧ edges[i]!.source = v) ∧
    ((outgoing_raw.map List.reverse)[v]!).Pairwise (fun i j => edges[i]!.key ≤ edges[j]!.key)
  rw [hout_eq]
  -- Properties of `buckets.toList.flatten`
  have hflat_mem : ∀ i, i ∈ buckets.toList.flatten ↔ i < edges.size := by
    intro i
    rw [List.mem_flatten]
    constructor
    · rintro ⟨b, hb, hi⟩
      exact hbs_lt b hb i hi
    · intro hi
      have hk : edges[i]!.key < 2 * n + 1 := by
        have := (hedges i hi).2
        omega
      have hk_len : edges[i]!.key < buckets.toList.length := by simpa [hb_sz] using hk
      refine ⟨buckets.toList[edges[i]!.key], List.getElem_mem hk_len, ?_⟩
      rw [Array.getElem_toList, ← getElem!_pos buckets _ hk_len]
      exact (hb_mem_iff edges[i]!.key hk i).mpr ⟨hi, rfl⟩
  have hflat_nodup : buckets.toList.flatten.Nodup := by
    apply pairwise_flatten_of_getElem buckets.toList
    · intro k hk
      have hk' : k < 2 * n + 1 := by simpa [hb_sz] using hk
      change buckets.toList[k].Nodup
      rw [Array.getElem_toList, ← getElem!_pos buckets k hk, hb_eq k hk', List.nodup_reverse]
      exact List.Nodup.filter _ List.nodup_range
    · intro k₁ k₂ hk₁ hk₂ hlt x hx y hy heq
      subst heq
      have hk₁' : k₁ < 2 * n + 1 := by simpa [hb_sz] using hk₁
      have hk₂' : k₂ < 2 * n + 1 := by simpa [hb_sz] using hk₂
      rw [Array.getElem_toList, ← getElem!_pos buckets k₁ hk₁, hb_mem_iff k₁ hk₁'] at hx
      rw [Array.getElem_toList, ← getElem!_pos buckets k₂ hk₂, hb_mem_iff k₂ hk₂'] at hy
      omega
  have hflat_sorted : buckets.toList.flatten.Pairwise (fun i j => edges[i]!.key ≤ edges[j]!.key) := by
    apply pairwise_flatten_of_getElem buckets.toList
    · intro k hk
      have hk' : k < 2 * n + 1 := by simpa [hb_sz] using hk
      rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      have hmem_a : buckets.toList[k][a] ∈ buckets[k]! := by
        rw [getElem!_pos buckets k hk, ← Array.getElem_toList]
        exact List.getElem_mem ha
      have hmem_b : buckets.toList[k][b] ∈ buckets[k]! := by
        rw [getElem!_pos buckets k hk, ← Array.getElem_toList]
        exact List.getElem_mem hb
      have hka := ((hb_mem_iff k hk' _).mp hmem_a).2
      have hkb := ((hb_mem_iff k hk' _).mp hmem_b).2
      omega
    · intro k₁ k₂ hk₁ hk₂ hlt x hx y hy
      have hk₁' : k₁ < 2 * n + 1 := by simpa [hb_sz] using hk₁
      have hk₂' : k₂ < 2 * n + 1 := by simpa [hb_sz] using hk₂
      rw [Array.getElem_toList, ← getElem!_pos buckets k₁ hk₁, hb_mem_iff k₁ hk₁'] at hx
      rw [Array.getElem_toList, ← getElem!_pos buckets k₂ hk₂, hb_mem_iff k₂ hk₂'] at hy
      omega
  refine ⟨List.Nodup.filter _ hflat_nodup, ?_, List.Pairwise.filter _ hflat_sorted⟩
  intro i
  rw [List.mem_filter, hflat_mem, beq_iff_eq]

end GraphMinor.LRPlanarity
