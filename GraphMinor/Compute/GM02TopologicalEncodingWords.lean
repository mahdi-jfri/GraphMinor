module

public import GraphMinor.Compute.GM02TopologicalInput
import GraphMinor.Compute.MultiDigraph

/-!
# Word bounds for the plain graph-pair encoding

Every endpoint word is smaller than the host vertex count. The remaining
words are the two edge counts and the supplied pattern vertex count.
The latter is at most the host count because the pattern vertices form
a subset of the host vertices.
-/

public section
namespace GraphMinor.Compute

/-- Every word of a plain edge-list graph fits whenever its two counts fit. -/
theorem GM02EdgeListInput.enc_all_lt {W : ℕ} (G : GM02EdgeListInput)
    (hn : G.n < 2 ^ W) (hm : G.edges.length < 2 ^ W) :
    ∀ a ∈ G.enc, a < 2 ^ W := by
  intro a ha
  simp only [GM02EdgeListInput.enc, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with (rfl | rfl) | ha
  · exact hn
  · exact hm
  · exact all_lt_flatEdges G.edges hn a ha

/-- Every word of the plain labelled-pattern encoding fits when the supplied counts fit. -/
theorem GM02TopologicalInput.enc_all_lt {W : ℕ} (x : GM02TopologicalInput)
    (hn : x.G.n < 2 ^ W) (hmG : x.G.edges.length < 2 ^ W) (hmH : x.edges.length < 2 ^ W) :
    ∀ a ∈ x.enc, a < 2 ^ W := by
  have hp : x.vertices.card ≤ x.G.n := by
    have h := Finset.card_le_card (Finset.subset_univ x.vertices)
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  intro a ha
  simp only [GM02TopologicalInput.enc, List.mem_append, List.mem_singleton] at ha
  rcases ha with (((hG | hP) | hV) | hM) | hE
  · exact x.G.enc_all_lt hn hmG a hG
  · exact hP ▸ hp.trans_lt hn
  · obtain ⟨v, _, rfl⟩ := List.mem_map.1 hV
    exact v.isLt.trans hn
  · exact hM ▸ hmH
  · exact all_lt_flatEdges x.edges hn a hE

end GraphMinor.Compute
