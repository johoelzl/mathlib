/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Ordered (non-cancellative) monoids
-/
import data.set order.galois_connection algebra.ordered_monoid
open classical set lattice function
local attribute [instance] decidable_inhabited prop_decidable

section old_structure_cmd
set_option old_structure_cmd true

class completely_ordered_monoid (α : Type*)
  extends complete_lattice α, canonically_ordered_monoid α :=
(Sup_add : ∀(s:set α) (a:α), s ≠ ∅ → Sup s + a = ⨆b∈s, b + a)
(Inf_add : ∀(s:set α) (a:α), s ≠ ∅ → Inf s + a = ⨅b∈s, b + a)

end old_structure_cmd

section complete_lattice
variables {α : Type*} {ι : Sort*} [complete_lattice α]

lemma Inf_eq_Sup {s : set α} : Inf s = Sup {a | ∀b∈s, a ≤ b } :=
le_antisymm (le_Sup $ assume b hb, Inf_le hb) (le_Inf $ assume b hb, Sup_le $ assume c hc, hc _ hb)

@[simp] lemma infi_top : (⨅i:ι, ⊤ : α) = ⊤ :=
top_unique $ le_infi $ assume i, le_refl ⊤

@[simp] lemma supr_bot : (⨆i:ι, ⊥ : α) = ⊥ :=
bot_unique $ supr_le $ assume i, le_refl ⊥

end complete_lattice

section completely_ordered_monoid
variables {α : Type*} {β : Type*} {ι : Sort*} [completely_ordered_monoid α]
  {s : set α} {a : α} {f g : ι → α}

lemma Sup_add : s ≠ ∅ → Sup s + a = ⨆b∈s, b + a :=
completely_ordered_monoid.Sup_add _ _

lemma add_Sup (h : s ≠ ∅) : a + Sup s = ⨆b∈s, a + b :=
by rw [add_comm, Sup_add h]; simp

lemma add_supr (i : ι) : a + (⨆i, f i) = (⨆i, a + f i) :=
by rw [←Sup_range, add_Sup, supr_range]; exact ne_empty_of_mem (@mem_range _ _ _ i)

lemma supr_add (i : ι) : (⨆i, f i) + a = (⨆i, f i + a) :=
by rw [add_comm, add_supr i]; simp

@[simp] lemma add_top : a + ⊤ = ⊤ := top_unique $ le_add_of_nonneg_left' $ zero_le
@[simp] lemma top_add : ⊤ + a = ⊤ := top_unique $ le_add_of_nonneg_right' $ zero_le

lemma supr_add_supr (h : ∀i j, ∃k, f i + g j ≤ f k + g k) :
  (⨆i, f i) + (⨆i, g i) = (⨆i, f i + g i) :=
by_cases
  (assume : ∃i:ι, true,
    let ⟨i, _⟩ := this in
    le_antisymm
      (calc (⨆i, f i) + (⨆i, g i) = (⨆j, ⨆i, f i + g j) : by simp [supr_add i, add_supr i]
        ... ≤ _ : supr_le $ assume j, supr_le $ assume i, let ⟨k, hk⟩ := h i j in le_supr_of_le k hk)
      (supr_le $ assume i, add_le_add' (le_supr _ i) (le_supr _ i)))
  (assume : ¬ ∃i:ι, true,
    have ∀i:ι, false, from assume i, this ⟨i, trivial⟩,
    have ∀f : ι → α, (⨆i, f i) = 0,
      from assume f, le_antisymm (supr_le $ assume i, (this i).elim) zero_le,
    by simp [this])

lemma Inf_add : Inf s + a = ⨅b∈s, b + a :=
by_cases
  (assume : s = ∅, by simp [this])
  (assume : s ≠ ∅, completely_ordered_monoid.Inf_add s a this)

end completely_ordered_monoid
