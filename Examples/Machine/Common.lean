/-
Common infrastructure for the example machine executions.
-/

import Examples.WellTyped
import Rizzo.MainResults
import Examples.Machine.Reflect

open Term

@[simp] lemma Store.empty_now : (∅ : Store).now = ∅ := rfl
@[simp] lemma Store.empty_earlier : (∅ : Store).earlier = ∅ := rfl
@[simp] lemma Heap.empty_entries : (∅ : Heap).entries = [] := rfl
@[simp] lemma Store.mk_now {ηN ηE : Heap} {D} : (ηN ✓[D] ηE).now = ηN := rfl
@[simp] lemma Store.mk_earlier {ηN ηE : Heap} {D} : (ηN ✓[D] ηE).earlier = ηE := rfl

---------------------------------------------------
-- Side-condition tactics shared by the examples --
---------------------------------------------------

/-- Discharge a `l ∉ η` freshness side condition of a `cons`/`concat` for a
concrete-keyed heap. -/
macro "fresh_loc" : tactic =>
  `(tactic| simp [AList.mem_keys, AList.keys, AList.concat, List.keys])

---------------------------------------
-- Runtime numerals used as payloads --
---------------------------------------

/-- `0, 1, 2, 3 : Nat` as runtime values. -/
abbrev n0 : MVal := ⟨Term.zero, by is_value⟩
abbrev n1 : MVal := ⟨Term.succ Term.zero, by is_value⟩
abbrev n2 : MVal := ⟨Term.succ (Term.succ Term.zero), by is_value⟩
abbrev n3 : MVal := ⟨Term.succ (Term.succ (Term.succ Term.zero)), by is_value⟩

-----------------------------------
-- The shared `sig[wait κ]` tail --
-----------------------------------

open RizzoNotation in
valdef sigTail (D : Typ) (κ : Chan) : MVal :=
  delay ((λ f a . a ::{D} (f ⬝ wait (chan κ))) ⬝ mkSig {D}) ⧁ wait (chan κ)

----------------------------------------------------------------------
-- Proof-by-reflection drivers for the operational/update semantics --
----------------------------------------------------------------------

/-- Close a freshness/disjointness/`ticked` side goal of the update semantics
for a concrete heap. -/
macro "side" : tactic =>
  `(tactic|
    first
      | rfl
      | decide
      | (simp only [AList.Disjoint, AList.mem_keys, AList.keys, List.keys,
            AList.cons, AList.concat, Store.insert, Store.alloc, AList.alloc,
            Store.mk_now, Store.mk_earlier, Store.empty_now, Store.empty_earlier]; decide))

/-- Close a concrete evaluation goal `(t, ε) ⇓ (v, ε')` by reflection. -/
macro "eval_refl" : tactic =>
  `(tactic| exact Reflect.evalF_sound 100000 _ _ _ _ (by rfl))

/-- Close a concrete advance goal `(s, ε) [e]⇘ (v, ε')` by reflection. -/
macro "adv_refl" : tactic =>
  `(tactic| exact Reflect.advF_sound 100000 _ _ _ _ _ (by rfl))

/-- One update step that skips the processed signal (its tail has not ticked). -/
macro "update_skip" : tactic =>
  `(tactic| (apply Update.skip <;> side))

-- One update step that advances the processed signal (its tail has
-- ticked).
macro "update_adv_refl" : tactic =>
  `(tactic|
    (apply Update.adv
     all_goals (try (adv_refl; done))
     all_goals (try (first | exact Store.lookup_insert _ _ _ _ | rfl))
     all_goals side))

-- Drive an `[e]⇒*` (update sequence) by reflection
macro "update_tac_refl" : tactic =>
  `(tactic|
    repeat (first
      | apply Updates.nil
      | (apply Updates.cons; focus (first | update_adv_refl | update_skip))))
