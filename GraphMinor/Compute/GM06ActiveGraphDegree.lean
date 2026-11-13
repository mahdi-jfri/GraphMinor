module

public import GraphMinor.Compute.GM06ActiveValencyRepresentation
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The active valency RAM query on the actual graph

The contraction and terminal tests in VI (5.7), page 133, need
the valency in the current drawing. The verified masked endpoint
counter computes that valency from original endpoint labels and
current activity bits. Its bound is linear in the original edge
count and it preserves every array, so it applies after deletions.
-/

public section
namespace GraphMinor.Compute
universe u v

/-- The masked endpoint program returns actual valency under the
primitive current-graph interpretation, with a linear time bound. -/
theorem gm06ActiveDegreeProg_exec_on_graph {w n : ℕ} {α : Type u} {β : Type v}
    (ends active : ℕ) (G : Graph α β) (vertex : Fin n → α) (hv : Function.Injective vertex)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hinj : Set.InjOn edge {j | tagged[j.val].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j.val].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j.val].1.1) (vertex tagged[j.val].1.2))
    (hcover : ∀ e ∈ G.edgeSet, ∃ j : Fin tagged.length, tagged[j.val].2 = 1 ∧ edge j = e)
    (a : Fin n) (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd) (h22 : s.regs 22 = a.val) :
    ∃ s' t, Exec w (gm06ActiveDegreeProg ends active) s s' t ∧
      t ≤ 7 + 42 * tagged.length ∧ TwoPaths.Keeps [20, 21] [] s s' ∧
      s'.regs 21 = GM06.vertexValency G (vertex a) := by
  have hx : ∀ x ∈ gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)), x < 2 ^ w := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact q.1.1.isLt.trans hn
    · exact q.1.2.isLt.trans hn
  obtain ⟨s', t, hex, ht, hframe, hcount⟩ := gm06ActiveDegreeProg_exec ends active
    (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (tagged.map Prod.snd) a.val s hw
      (by simp only [gm06EndpointWords_length, List.length_map])
      (by simpa only [gm06EndpointWords_length, List.length_map] using hm) hx
      (by intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; exact (hbits p hp).trans_lt (by omega))
      (a.isLt.trans hn) ha hb h22
  refine ⟨s', t, hex, ?_, hframe, ?_⟩
  · simpa only [gm06EndpointWords_length, List.length_map, ← Nat.mul_assoc] using ht
  · exact hcount.trans (gm06ActiveLabelledVertexValency G vertex hv tagged edge hinj hlinks hcover a).symm

end GraphMinor.Compute
