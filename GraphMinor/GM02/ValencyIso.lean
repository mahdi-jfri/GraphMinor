module

public import GraphMinor.GM02.Valency
public import GraphMinor.Minor.Basic

/-!
# Valency under graph isomorphism

The vertex and edge bijections of an isomorphism preserve incidence and
loops. Restrict the edge bijection first to incident edges and then to
loops. Their cardinalities are unchanged, and hence so is valency. This
lets branch-tree degree bounds be read on their realized original edges.
-/

public section
namespace GraphMinor.GM02
open Graph Set
universe u v u' v'

/-- The edge and vertex maps of an isomorphism preserve unary incidence. -/
theorem iso_inc_iff {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α β} {G : Graph α' β'} (φ : Iso H G) (e : E(H)) (x : V(H)) :
    H.Inc e.val x.val ↔ G.Inc (φ.edgeEquiv e).val (φ.vertexEquiv x).val := by
  constructor
  · rintro ⟨y, hxy⟩
    exact ⟨(φ.vertexEquiv ⟨y, hxy.right_mem⟩).val,
      (φ.isLink_iff e x ⟨y, hxy.right_mem⟩).1 hxy⟩
  · rintro ⟨y, hxy⟩
    let y' := φ.vertexEquiv.symm ⟨y, hxy.right_mem⟩
    have hmap : G.IsLink (φ.edgeEquiv e).val (φ.vertexEquiv x).val (φ.vertexEquiv y').val := by
      simpa only [y', Equiv.apply_symm_apply] using hxy
    exact ⟨y'.val, (φ.isLink_iff e x y').2 hmap⟩

private theorem ncard_edge_predicate_eq
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α β} {G : Graph α' β'} (φ : Iso H G) (p : β → Prop) (q : β' → Prop)
    (hp : ∀ e, p e → e ∈ E(H)) (hq : ∀ e, q e → e ∈ E(G))
    (hiff : ∀ e : E(H), p e.val ↔ q (φ.edgeEquiv e).val) :
    {e | p e}.ncard = {e | q e}.ncard := by
  let s : Set E(H) := {e | p e.val}
  let f : E(H) → β' := fun e => (φ.edgeEquiv e).val
  have hf : Function.Injective f := Subtype.val_injective.comp φ.edgeEquiv.injective
  have hs : s.ncard = {e | p e}.ncard := by
    calc
      s.ncard = ({e | p e} ∩ E(H)).ncard := Set.ncard_subtype (fun e => e ∈ E(H)) {e | p e}
      _ = {e | p e}.ncard := congrArg Set.ncard (Set.inter_eq_left.2 (fun e he => hp e he))
  have himage : f '' s = {e | q e} := by
    ext e
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hiff a).1 ha
    · intro he
      let a := φ.edgeEquiv.symm ⟨e, hq e he⟩
      have hfa : f a = e := congrArg Subtype.val (φ.edgeEquiv.apply_symm_apply ⟨e, hq e he⟩)
      refine ⟨a, (hiff a).2 ?_, hfa⟩
      change q (f a)
      rw [hfa]
      exact he
  exact hs.symm.trans ((Set.ncard_image_of_injective s hf).symm.trans (congrArg Set.ncard himage))

/-- A graph isomorphism preserves valency, counting loops twice. -/
theorem valency_eq_of_iso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α β} {G : Graph α' β'} (φ : Iso H G) (x : V(H)) :
    valency H x.val = valency G (φ.vertexEquiv x).val := by
  have hi := ncard_edge_predicate_eq φ (fun e => H.Inc e x.val)
    (fun e => G.Inc e (φ.vertexEquiv x).val)
    (fun _ h => h.edge_mem) (fun _ h => h.edge_mem) (fun e => iso_inc_iff φ e x)
  have hl := ncard_edge_predicate_eq φ (fun e => H.IsLoopAt e x.val)
    (fun e => G.IsLoopAt e (φ.vertexEquiv x).val)
    (fun _ h => h.edge_mem) (fun _ h => h.edge_mem) (fun e => by
      rw [← Graph.isLink_self_iff, ← Graph.isLink_self_iff]
      exact φ.isLink_iff e x x)
  exact congrArg₂ Nat.add hi hl

end GraphMinor.GM02
