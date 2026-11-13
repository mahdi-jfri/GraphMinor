module

public import GraphMinor.Compute.GM02InjectedPattern
public import GraphMinor.Compute.GM02ConcatArrays

/-!
# Joining the constructed labelled pattern input

The host encoding is already present in the original input array.
Join the constructed vertex and edge suffixes, then append the result
to that host encoding. The resulting array is exactly the ordinary
input expected by (4.6), with no answer or certificate added.
-/

public section
namespace GraphMinor.Compute

/-- Join the two pattern suffixes, then append them to the original host input. -/
@[expose] def gm02JoinInjectedInputProg : Cmd :=
  .seq (gm02ConcatArraysProg 30 31 32) (gm02ConcatArraysProg inArr 32 33)

/-- The labelled encoding separates into host, vertex, and edge words. -/
theorem gm02InjectedPattern_enc (G H : GM02EdgeListInput) (f : Fin H.n ↪ Fin G.n) :
    (gm02InjectedPattern G H f).enc = G.enc ++
      (([H.n] ++ ((gm02InjectedPattern G H f).vertices.sort).map Fin.val) ++
        ([H.edges.length] ++ flatEdges (gm02InjectedPattern G H f).edges)) := by
  unfold GM02TopologicalInput.enc
  rw [gm02InjectedPattern_vertices_card, gm02InjectedPattern_edges_length]
  simp only [List.append_assoc]
  rfl

/-- The join computes exactly the labelled input, with a linear bound in that encoding's length. -/
theorem gm02JoinInjectedInputProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hG : s.arrs inArr = G.enc)
    (hV : s.arrs 30 = [H.n] ++ ((gm02InjectedPattern G H f).vertices.sort).map Fin.val)
    (hE : s.arrs 31 = [H.edges.length] ++ flatEdges (gm02InjectedPattern G H f).edges)
    (hw : 1 < 2 ^ W) (hlen : (gm02InjectedPattern G H f).enc.length < 2 ^ W)
    (hall : ∀ a ∈ (gm02InjectedPattern G H f).enc, a < 2 ^ W) :
    ∃ s' t, Exec W gm02JoinInjectedInputProg s s' t ∧
      t ≤ 40 + 32 * (gm02InjectedPattern G H f).enc.length ∧
      s'.arrs 33 = (gm02InjectedPattern G H f).enc ∧
      (∀ a, a ≠ 32 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r < 290, s'.regs r = s.regs r) := by
  let V := [H.n] ++ ((gm02InjectedPattern G H f).vertices.sort).map Fin.val
  let E := [H.edges.length] ++ flatEdges (gm02InjectedPattern G H f).edges
  have henc : (gm02InjectedPattern G H f).enc = G.enc ++ (V ++ E) := gm02InjectedPattern_enc G H f
  have hlength : (gm02InjectedPattern G H f).enc.length = G.enc.length + (V.length + E.length) := by
    rw [henc, List.length_append, List.length_append]
  have hVwords : ∀ a ∈ V, a < 2 ^ W := by
    intro a ha
    apply hall a
    rw [henc]
    exact List.mem_append_right _ (List.mem_append_left _ ha)
  have hEwords : ∀ a ∈ E, a < 2 ^ W := by
    intro a ha
    apply hall a
    rw [henc]
    exact List.mem_append_right _ (List.mem_append_right _ ha)
  obtain ⟨s₁, t₁, he₁, ht₁, hout₁, ha₁, hr₁⟩ := gm02ConcatArraysProg_exec 30 31 32
    (by decide) (by decide) V E s hV hE hw (by omega) hVwords hEwords
  have hGwords : ∀ a ∈ G.enc, a < 2 ^ W := by
    intro a ha
    apply hall a
    rw [henc]
    exact List.mem_append_left _ ha
  have hVEwords : ∀ a ∈ V ++ E, a < 2 ^ W := by
    intro a ha
    exact (List.mem_append.1 ha).elim (hVwords a) (hEwords a)
  obtain ⟨s₂, t₂, he₂, ht₂, hout₂, ha₂, hr₂⟩ := gm02ConcatArraysProg_exec inArr 32 33
    (by decide) (by decide) G.enc (V ++ E) s₁ ((ha₁ inArr (by decide)).trans hG) hout₁ hw
    (by simp only [List.length_append]; omega) hGwords hVEwords
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hout₂.trans henc.symm, ?_, ?_⟩
  · simp only [List.length_append] at ht₂
    omega
  · intro a ha32 ha33
    exact (ha₂ a ha33).trans (ha₁ a ha32)
  · intro r hr
    exact (hr₂ r hr).trans (hr₁ r hr)

end GraphMinor.Compute
