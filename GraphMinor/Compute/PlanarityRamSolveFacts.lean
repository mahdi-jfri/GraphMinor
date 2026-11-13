module

public import GraphMinor.LRPlanarity.Algorithm

/-!
# Facts about the Lean solver used by its RAM proof

The RAM proof of the solver follows the Lean function `solve` of
`LRPlanarity/Algorithm.lean` one vertex and one edge at a time. This file
gives the facts about the Lean side that it needs.

* `solve_eq` writes `solve` as a structural recursion `solveFrom` over the
  postorder, which is the form the outer RAM loop follows.
* `bucketOrder_facts` says that the outgoing lists of `bucketOrder` have the
  right number of entries, have total length at most the number of edges,
  and hold edge indices.
* `arraySum_set` is the change of a sum when one array entry is replaced. It
  pays for the summaries kept in the results array.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-! ### `solve` as a recursion over the postorder -/

/-- The trim at the end of a vertex in `solve`. -/
def solveTrim (search : Search) (v : ℕ) (summary : Option Summary) : Option Summary :=
  match search.parent[v]?.join with
  | none => summary
  | some u => trim summary ((search.depth[u]?.join).getD 0)

/-- The loop of `solve` over the remaining vertices of the postorder. -/
def solveFrom (search : Search) (outgoing : Array (List ℕ)) :
    List ℕ → Array (Option Summary) → Bool
  | [], _ => true
  | v :: vs, results =>
    match solveOutgoing search outgoing[v]! results none with
    | none => false
    | some (rs, summary) => solveFrom search outgoing vs (rs.set! v (solveTrim search v summary))

theorem solve_eq (n : ℕ) (search : Search) (outgoing : Array (List ℕ)) :
    solve n search outgoing =
      solveFrom search outgoing search.postorder (Array.replicate n none) := by
  unfold solve
  generalize Array.replicate n none = results
  generalize search.postorder = l
  induction l generalizing results with
  | nil => simp [solveFrom]
  | cons v vs ih =>
    simp only [List.forIn_cons, solveFrom]
    split
    · simp_all
    · rename_i rs summary h
      simp only [h, pure_bind]
      exact ih _

/-! ### Sums over lists -/

/-- Replacing entry `k` of a list changes the sum of `f` by the difference. -/
theorem sum_map_set {α : Type*} (l : List α) (f : α → ℕ) (k : ℕ) (x : α) (hk : k < l.length) :
    ((l.set k x).map f).sum + f l[k] = (l.map f).sum + f x := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    cases k with
    | zero => simp; omega
    | succ k =>
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have := ih k (by simpa using hk)
      omega

/-- The sum of `f` over the entries of an array. -/
def arraySum {α : Type*} (f : α → ℕ) (a : Array α) : ℕ := (a.toList.map f).sum

/-- `arraySum` after `set!` at a valid index. -/
theorem arraySum_set {α : Type*} [Inhabited α] (f : α → ℕ) (a : Array α) (k : ℕ) (x : α)
    (hk : k < a.size) : arraySum f (a.set! k x) + f a[k]! = arraySum f a + f x := by
  unfold arraySum
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, getElem!_pos a k hk,
    ← Array.getElem_toList]
  exact sum_map_set a.toList f k x (by simpa using hk)

private theorem sublist_sum_le {l₁ l₂ : List ℕ} (h : l₁.Sublist l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

/-- A sum over distinct indices below the size is at most the full sum. -/
theorem sum_le_arraySum {α : Type*} [Inhabited α] (f : α → ℕ) (a : Array α) (vs : List ℕ)
    (hnd : vs.Nodup) (hvs : ∀ v ∈ vs, v < a.size) :
    (vs.map fun v => f a[v]!).sum ≤ arraySum f a := by
  have hsub : vs ⊆ List.range a.size := fun v hv => List.mem_range.mpr (hvs v hv)
  obtain ⟨l, hp, hs⟩ := List.subperm_of_subset hnd hsub
  have hmap : (List.range a.size).map (fun v => f a[v]!) = a.toList.map f := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [getElem!_pos a i h1]
  rw [arraySum, ← hmap, ← (hp.map _).sum_eq]
  exact sublist_sum_le (hs.map _)

/-! ### The outgoing lists of `bucketOrder` -/

/-- The total length of the lists in an array. -/
abbrev totalLength (b : Array (List ℕ)) : ℕ := arraySum List.length b

private theorem push_size (b : Array (List ℕ)) (k a : ℕ) :
    (b.setIfInBounds k (a :: b[k]!)).size = b.size := by simp

private theorem push_total (b : Array (List ℕ)) (k a : ℕ) :
    totalLength (b.setIfInBounds k (a :: b[k]!)) ≤ totalLength b + 1 := by
  by_cases hk : k < b.size
  · have h := arraySum_set List.length b k (a :: b[k]!) hk
    rw [Array.set!_eq_setIfInBounds] at h
    simp only [List.length_cons] at h
    unfold totalLength
    omega
  · simp [Array.setIfInBounds, hk]

private theorem push_mem (b : Array (List ℕ)) (k a : ℕ) (P : ℕ → Prop)
    (hb : ∀ l ∈ b.toList, ∀ x ∈ l, P x) (ha : P a) :
    ∀ l ∈ (b.setIfInBounds k (a :: b[k]!)).toList, ∀ x ∈ l, P x := by
  intro l hl x hx
  rw [Array.toList_setIfInBounds] at hl
  rcases List.mem_or_eq_of_mem_set hl with hl | rfl
  · exact hb l hl x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · by_cases hk : k < b.size
      · rw [getElem!_pos b k hk] at hx
        exact hb _ (Array.getElem_mem_toList hk) x hx
      · rw [getElem!_neg b k hk] at hx
        simp [default] at hx

/-- One fold of pushes keeps the size, adds at most one entry per pushed
element, and adds only pushed elements. -/
private theorem fold_push (key : ℕ → ℕ) (P : ℕ → Prop) :
    ∀ (l : List ℕ) (b : Array (List ℕ)), (∀ x ∈ l, P x) → (∀ l ∈ b.toList, ∀ x ∈ l, P x) →
      let b' := l.foldl (fun b a => b.setIfInBounds (key a) (a :: b[key a]!)) b
      b'.size = b.size ∧ totalLength b' ≤ totalLength b + l.length ∧
        ∀ l ∈ b'.toList, ∀ x ∈ l, P x := by
  intro l
  induction l with
  | nil => intro b _ hb; exact ⟨rfl, by simp, hb⟩
  | cons a l ih =>
    intro b hl hb
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (b.setIfInBounds (key a) (a :: b[key a]!))
      (fun x hx => hl x (List.mem_cons_of_mem a hx))
      (push_mem b (key a) a P hb (hl a (List.mem_cons_self)))
    refine ⟨by rw [h1, push_size], ?_, h3⟩
    have := push_total b (key a) a
    simp only [List.length_cons]
    omega

/-- The second pass of `bucketOrder`: a fold over the buckets. -/
private theorem fold_buckets (key : ℕ → ℕ) (P : ℕ → Prop) :
    ∀ (B : List (List ℕ)) (b : Array (List ℕ)), (∀ l ∈ B, ∀ x ∈ l, P x) →
      (∀ l ∈ b.toList, ∀ x ∈ l, P x) →
      let b' := B.foldl (fun b l => l.foldl
        (fun b a => b.setIfInBounds (key a) (a :: b[key a]!)) b) b
      b'.size = b.size ∧ totalLength b' ≤ totalLength b + (B.map List.length).sum ∧
        ∀ l ∈ b'.toList, ∀ x ∈ l, P x := by
  intro B
  induction B with
  | nil => intro b _ hb; exact ⟨rfl, by simp, hb⟩
  | cons l B ih =>
    intro b hB hb
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := fold_push key P l b (hB l List.mem_cons_self) hb
    obtain ⟨h4, h5, h6⟩ := ih _ (fun l' hl' => hB l' (List.mem_cons_of_mem l hl')) h3
    refine ⟨by rw [h4, h1], ?_, h6⟩
    simp only [List.map_cons, List.sum_cons]
    omega

theorem bucketOrder_facts (n : ℕ) (edges : Array EdgeRecord) :
    (bucketOrder n edges).size = n ∧ totalLength (bucketOrder n edges) ≤ edges.size ∧
      ∀ l ∈ (bucketOrder n edges).toList, ∀ i ∈ l, i < edges.size := by
  simp only [bucketOrder]
  simp
  have hrep : ∀ k, totalLength (Array.replicate k ([] : List ℕ)) = 0 := by
    intro k; simp [totalLength, arraySum]
  have hrepm : ∀ k, ∀ l ∈ (Array.replicate k ([] : List ℕ)).toList, ∀ x ∈ l, x < edges.size := by
    intro k l hl x hx; simp at hl; rw [hl.2] at hx; simp at hx
  obtain ⟨hB1, hB2, hB3⟩ := fold_push (fun a => edges[a]!.key) (· < edges.size)
    (List.range' 0 edges.size) (Array.replicate (2 * n + 1) [])
    (fun x hx => by simp [List.mem_range'] at hx; omega) (hrepm _)
  set B := List.foldl (fun b a => b.setIfInBounds edges[a]!.key (a :: b[edges[a]!.key]!))
    (Array.replicate (2 * n + 1) []) (List.range' 0 edges.size) with hBdef
  simp only [← Array.foldl_toList]
  obtain ⟨hO1, hO2, hO3⟩ := fold_buckets (fun a => edges[a]!.source) (· < edges.size) B.toList
    (Array.replicate n []) hB3 (hrepm _)
  rw [hrep] at hB2 hO2
  refine ⟨hO1.trans (by simp), ?_, ?_⟩
  · have : totalLength (Array.map List.reverse (List.foldl (fun b l => List.foldl
        (fun b a => b.setIfInBounds edges[a]!.source (a :: b[edges[a]!.source]!)) b l)
        (Array.replicate n []) B.toList)) = totalLength (List.foldl (fun b l => List.foldl
        (fun b a => b.setIfInBounds edges[a]!.source (a :: b[edges[a]!.source]!)) b l)
        (Array.replicate n []) B.toList) := by
      simp [totalLength, arraySum, Function.comp_def]
    rw [this]
    have hBt : (B.toList.map List.length).sum = totalLength B := rfl
    simp only [List.length_range', zero_add] at hB2
    omega
  · intro l hl i hi
    exact hO3 l (by simpa using hl) i hi

end GraphMinor.Compute.PlanarityRam
