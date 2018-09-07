/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Finite dimensional sub-vector spaces
-/
import linear_algebra.submodule
universes u v w
local attribute [instance] classical.dec
open lattice function set

structure fd_subspace (α : Type u) (β : Type v) [field α] [vector_space α β]
  extends submodule α β :=
(finite_generator : ∃b:finset β, carrier ⊆ span (↑b:set β))

namespace fd_subspace
variables {α : Type u} {β : Type v} {γ : Type w}
variables  [field α] [vector_space α β] [vector_space α γ]
include α

instance : has_coe (fd_subspace α β) (submodule α β) := ⟨fd_subspace.to_submodule⟩
instance (s : fd_subspace α β) : is_submodule (s : set β) := submodule.to_is_submodule _
instance : has_mem β (fd_subspace α β) := ⟨λ x y, x ∈ (y : set β)⟩

@[simp] theorem mem_coe {b : β} {s : fd_subspace α β} : b ∈ (s : set β) ↔ b ∈ s := iff.rfl

instance : has_subset (fd_subspace α β) := ⟨λ s t, (s : set β) ⊆ t⟩

@[extensionality] theorem ext : ∀{s t : fd_subspace α β}, ((s : set β) = t) → s = t
| ⟨s, _⟩ ⟨t, _⟩ eq := have s = t, from submodule.ext eq, by subst this

protected theorem ext_iff {s t : fd_subspace α β} : (s : set β) = t ↔ s = t :=
iff.intro ext (assume h, h ▸ rfl)

instance : partial_order (fd_subspace α β) :=
partial_order.lift (coe : fd_subspace α β → set β) $ λ a b h₁ h₂, ext (subset.antisymm h₁ h₂)

instance : has_bot (fd_subspace α β) := ⟨ ⟨0, ∅, subset.refl _⟩ ⟩

instance : has_sup (fd_subspace α β) :=
⟨λs t, ⟨s ⊔ t, let ⟨bs, hs⟩ := s.finite_generator, ⟨bt, ht⟩ := t.finite_generator in
  ⟨bs ∪ bt, span_minimal is_submodule_span $ subset.trans (union_subset_union hs ht) $
    union_subset (span_mono $ by simp) (span_mono $ by simp) ⟩⟩⟩

end fd_subspace
