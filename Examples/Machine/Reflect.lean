/-
Proof-by-reflection infrastructure for the operational semantics.
-/

import Rizzo.Semantics

open Term

namespace Reflect

-- IsMValue inversions (Prop → Prop, so fine to use proof terms)
theorem IsMValue.pair_fst {a b} : IsMValue (Term.pair a b) → IsMValue a := by intro h; cases h; assumption
theorem IsMValue.pair_snd {a b} : IsMValue (Term.pair a b) → IsMValue b := by intro h; cases h; assumption
theorem IsMValue.in1_inv {a} : IsMValue (Term.in1 a) → IsMValue a := by intro h; cases h; assumption
theorem IsMValue.in2_inv {a} : IsMValue (Term.in2 a) → IsMValue a := by intro h; cases h; assumption
theorem IsMValue.cons_inv {A a} : IsMValue (Term.cons A a) → IsMValue a := by intro h; cases h; assumption
theorem IsMValue.appE_snd {a b} : IsMValue (Term.appE a b) → IsMValue b := by intro h; cases h; assumption
theorem IsMValue.tail_inv {a} : IsMValue (Term.tail a) → IsMValue a := by intro h; cases h; exact IsMValue.loc
theorem IsMValue.tail_loc {a} : IsMValue (Term.tail a) → ∃ l, a = Term.loc l := by intro h; cases h; exact ⟨_, rfl⟩
theorem IsMValue.select_fst {a b} : IsMValue (Term.select a b) → IsMValue a := by intro h; cases h; assumption
theorem IsMValue.select_snd {a b} : IsMValue (Term.select a b) → IsMValue b := by intro h; cases h; assumption

-- Variants of the destructuring `Eval` rules whose extracted
-- sub-value is supplied through a `w.val = ctor ...`.
theorem Eval.pr1' {s ε w ε' a b} {ha : IsMValue a} :
    (s, ε) ⇓ (w, ε') → w.val = Term.pair a b → (pr1 s, ε) ⇓ (⟨a, ha⟩, ε') := by
  intro h1 hw
  obtain ⟨wt, wh⟩ := w; cases hw
  exact Eval.pr1 (u := ⟨a, ha⟩) (v := ⟨b, IsMValue.pair_snd wh⟩) h1

theorem Eval.pr2' {s ε w ε' a b} {hb : IsMValue b} :
    (s, ε) ⇓ (w, ε') → w.val = Term.pair a b → (pr2 s, ε) ⇓ (⟨b, hb⟩, ε') := by
  intro h1 hw
  obtain ⟨wt, wh⟩ := w; cases hw
  exact Eval.pr2 (u := ⟨a, IsMValue.pair_fst wh⟩) (v := ⟨b, hb⟩) h1

theorem Eval.case1' {t t1 t2} {ε w εt a v ε'} :
    (t, ε) ⇓ (w, εt) → w.val = Term.in1 a → (t1.sub a, εt) ⇓ (v, ε') →
    (Term.case t t1 t2, ε) ⇓ (v, ε') := by
  intro h1 hw h2
  obtain ⟨wt, wh⟩ := w; cases hw
  exact Eval.case1 (u := ⟨a, IsMValue.in1_inv wh⟩) h1 h2

theorem Eval.case2' {t t1 t2} {ε w εt a v ε'} :
    (t, ε) ⇓ (w, εt) → w.val = Term.in2 a → (t2.sub a, εt) ⇓ (v, ε') →
    (Term.case t t1 t2, ε) ⇓ (v, ε') := by
  intro h1 hw h2
  obtain ⟨wt, wh⟩ := w; cases hw
  exact Eval.case2 (u := ⟨a, IsMValue.in2_inv wh⟩) h1 h2

theorem Eval.recur' {B s t ε w εt A vt w2 ε'' u ε'''} :
    (t, ε) ⇓ (w, εt) → w.val = Term.cons A vt →
    (((Term.fmap₁ A (μ A ⨂ B)).app (Term.lam (pair (var 0) (recur B s (var 0))))).app vt, εt)
            ⇓ (w2, ε'') →
    (s.sub w2.val, ε'') ⇓ (u, ε''') → (Term.recur B s t, ε) ⇓ (u, ε''') := by
  intro h1 hw h2 h3
  obtain ⟨wt, wh⟩ := w; cases hw
  exact Eval.recur (v := ⟨vt, IsMValue.cons_inv wh⟩) h1 h2 h3

/-- A fuel-driven evaluator mirroring the `Eval` (`⇓`) relation.  Returns
`some (v, ε')` when `(t, ε) ⇓ (v, ε')` is derivable (with enough fuel). -/
def evalF : Nat → Term → Env → Option (MVal × Env)
  | 0, _, _ => none
  | fuel+1, t, ε =>
    match t with
    | .unit       => some (MVal.unit, ε)
    | .loc l      => some (MVal.loc l, ε)
    | .chan κ     => some (MVal.chan κ, ε)
    | .lam s      => some (MVal.lam s, ε)
    | .delay s    => some (MVal.delay s, ε)
    | .never      => some (MVal.never, ε)
    | .var _      => none
    | .pair s t   =>
        match evalF fuel s ε with
        | some (u, ε') =>
          match evalF fuel t ε' with
          | some (v, ε'') => some (MVal.pair u v, ε'')
          | none => none
        | none => none
    | .in1 s      => match evalF fuel s ε with
                     | some (v, ε') => some (MVal.in1 v, ε') | none => none
    | .in2 s      => match evalF fuel s ε with
                     | some (v, ε') => some (MVal.in2 v, ε') | none => none
    | .wait s     => match evalF fuel s ε with
                     | some (⟨.chan κ, _⟩, ε') => some (MVal.wait κ, ε') | _ => none
    | .watch s    => match evalF fuel s ε with
                     | some (⟨.loc l, _⟩, ε') => some (MVal.watch l, ε') | _ => none
    | .tail s     => match evalF fuel s ε with
                     | some (⟨.loc l, _⟩, ε') => some (MVal.tail l, ε') | _ => none
    | .cons A s   => match evalF fuel s ε with
                     | some (v, ε') => some (MVal.cons A v, ε') | none => none
    | .appE s t   =>
        match evalF fuel s ε with
        | some (u, ε') =>
          match evalF fuel t ε' with
          | some (v, ε'') => some (MVal.appE u v, ε'')
          | none => none
        | none => none
    | .select s t   =>
        match evalF fuel s ε with
        | some (u, ε') =>
          match evalF fuel t ε' with
          | some (v, ε'') => some (MVal.select u v, ε'')
          | none => none
        | none => none
    | .pr1 s      =>
        match evalF fuel s ε with
        | some (⟨.pair a _, h⟩, ε') => some (⟨a, IsMValue.pair_fst h⟩, ε')
        | _ => none
    | .pr2 s      =>
        match evalF fuel s ε with
        | some (⟨.pair _ b, h⟩, ε') => some (⟨b, IsMValue.pair_snd h⟩, ε')
        | _ => none
    | .case t t1 t2 =>
        match evalF fuel t ε with
        | some (⟨.in1 a, _⟩, ε') => evalF fuel (t1.sub a) ε'
        | some (⟨.in2 a, _⟩, ε') => evalF fuel (t2.sub a) ε'
        | _ => none
    | .app s t =>
        match evalF fuel s ε with
        | some (⟨.lam body, _⟩, ε') =>
          match evalF fuel t ε' with
          | some (u, ε'') => evalF fuel (body.sub u.val) ε''
          | none => none
        | _ => none
    | .appA s t =>
        match evalF fuel s ε with
        | some (⟨.delay s', _⟩, ε') =>
          match evalF fuel t ε' with
          | some (⟨.delay t', _⟩, ε'') => some (MVal.delay (app s' t'), ε'')
          | _ => none
        | _ => none
    | .head s =>
        match evalF fuel s ε with
        | some (⟨.loc l, _⟩, ε') =>
          match ε'.store.now.lookup l with
          | some sg => some (sg.head, ε')
          | none => none
        | _ => none
    | .sig A s t =>
        match evalF fuel s ε with
        | some (v, ε') =>
          match evalF fuel t ε' with
          | some (w, σ ⧸ Δ) =>
              some (MVal.loc σ.alloc, σ.insert σ.alloc (mksig A v false w) σ.alloc_fresh ⧸ Δ)
          | none => none
        | none => none
    | .newchan A =>
        match ε with
        | σ ⧸ Δ => some (MVal.chan Δ.alloc, σ ⧸ Δ.cons Δ.alloc A Δ.alloc_fresh)
    | .fix t => evalF fuel (t.sub (.delay (fix t))) ε
    | .recur B s t =>
        match evalF fuel t ε with
        | some (⟨.cons A vt, _⟩, ε') =>
          match evalF fuel
              (((Term.fmap₁ A (μ A ⨂ B)).app (Term.lam (pair (var 0) (recur B s (var 0))))).app vt) ε' with
          | some (w, ε'') => evalF fuel (s.sub w.val) ε''
          | none => none
        | _ => none

theorem evalF_sound : ∀ (n : Nat) (t : Term) (ε : Env) (v : MVal) (ε' : Env),
    evalF n t ε = some (v, ε') → (t, ε) ⇓ (v, ε') := by
  intro n
  induction n with
  | zero => intro t ε v ε' h; simp only [evalF, reduceCtorEq] at h
  | succ n IH =>
    intro t ε v ε' h
    cases t with
    | unit =>
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.value IsMValue.unit
    | loc l =>
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.value IsMValue.loc
    | chan κ =>
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.value IsMValue.chan
    | lam s =>
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.value IsMValue.lam
    | delay s =>
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.value IsMValue.delay
    | never =>
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.value IsMValue.never
    | var x => simp only [evalF, reduceCtorEq] at h
    | pair s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.pair (IH _ _ _ _ (by assumption)) (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | appE s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.appE (IH _ _ _ _ (by assumption)) (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | select s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.select (IH _ _ _ _ (by assumption)) (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | in1 s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.in1 (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | in2 s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.in2 (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | wait s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.wait (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | watch s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.watch (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | tail s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.tail (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | cons A s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.cons (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | pr1 s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.pr1' (IH _ _ _ _ (by assumption)) rfl)
        | simp only [reduceCtorEq] at h
    | pr2 s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.pr2' (IH _ _ _ _ (by assumption)) rfl)
        | simp only [reduceCtorEq] at h
    | «case» t t1 t2 =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | exact Eval.case1' (IH _ _ _ _ (by assumption)) rfl (IH _ _ _ _ h)
        | exact Eval.case2' (IH _ _ _ _ (by assumption)) rfl (IH _ _ _ _ h)
        | simp only [reduceCtorEq] at h
    | app s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | exact Eval.app (IH _ _ _ _ (by assumption)) (IH _ _ _ _ (by assumption)) (IH _ _ _ _ h)
        | simp only [reduceCtorEq] at h
    | appA s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.appA (IH _ _ _ _ (by assumption)) (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | head s =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.head (IH _ _ _ _ (by assumption)) (by assumption))
        | simp only [reduceCtorEq] at h
    | sig A s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
           exact Eval.sig (IH _ _ _ _ (by assumption)) (IH _ _ _ _ (by assumption)))
        | simp only [reduceCtorEq] at h
    | newchan A =>
      obtain ⟨σ, Δ⟩ := ε
      simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact Eval.newchan
    | fix t =>
      simp only [evalF] at h
      exact Eval.fix (IH _ _ _ _ h)
    | recur B s t =>
      simp only [evalF] at h; repeat' split at h
      all_goals first
        | exact Eval.recur' (IH _ _ _ _ (by assumption)) rfl (IH _ _ _ _ (by assumption)) (IH _ _ _ _ h)
        | simp only [reduceCtorEq] at h

/-- A fuel-driven evaluator mirroring the `Adv` (`⇘`) advance relation. -/
def advF : Nat → MVal → Event → Env → Option (MVal × Env)
  | 0, _, _, _ => none
  | fuel+1, ⟨vt, hv⟩, e, ε =>
    match vt, hv with
    | .appE (.delay t) v, hv =>
        match advF fuel ⟨v, IsMValue.appE_snd hv⟩ e ε with
        | some (v', ε') => evalF fuel (t.app v'.val) ε'
        | none => none
    | .wait (.chan κ), _ =>
        if e.chan = κ then evalF fuel e.val ε else none
    | .watch (.loc l), _ =>
        match ε.now.lookup l with
        | some s =>
            if s.ticked then
              match hh : s.head.val with
              | .in1 a => some (⟨a, IsMValue.in1_inv (hh ▸ s.head.property)⟩, ε)
              | _ => none
            else none
        | none => none
    | .tail v, hv => some (⟨v, IsMValue.tail_inv hv⟩, ε)
    | .select a b, hv =>
        -- the three `select`/`select` advance cases, dispatched on which side's clock
        -- has ticked (`a.ticked`/`b.ticked` against the current now-heap `ε.now`):
        if a.ticked ε.now e.chan then
          if b.ticked ε.now e.chan then
            -- both ticked  →  `in2 (w₁, w₂)`  (advance both, threading the env)
            match advF fuel ⟨a, IsMValue.select_fst hv⟩ e ε with
            | some (w1, ε') =>
                match advF fuel ⟨b, IsMValue.select_snd hv⟩ e ε' with
                | some (w2, ε'') => some (MVal.in2 (MVal.pair w1 w2), ε'')
                | none => none
            | none => none
          else
            -- only `a` ticked  →  `in1 (in1 w)`
            match advF fuel ⟨a, IsMValue.select_fst hv⟩ e ε with
            | some (w, ε') => some (MVal.in1 (MVal.in1 w), ε')
            | none => none
        else
          if b.ticked ε.now e.chan then
            -- only `b` ticked  →  `in1 (in2 w)`
            match advF fuel ⟨b, IsMValue.select_snd hv⟩ e ε with
            | some (w, ε') => some (MVal.in1 (MVal.in2 w), ε')
            | none => none
          else none
    | _, _ => none

-- Variants of the advance rules whose destructured *input* value is supplied
-- through an `it = ctor …` equation (closed by `rfl` at each call site).
theorem Adv.appE'' {tm} {x ε e v' ε' w ε''} {it} {ih : IsMValue it} :
    (x, ε) [e]⇘ (v', ε') → (tm.app v'.val, ε') ⇓ (w, ε'') →
    it = Term.appE (Term.delay tm) x.val → (⟨it, ih⟩, ε) [e]⇘ (w, ε'') := by
  intro h1 h2 hinp
  subst hinp; exact Adv.appE h1 h2

theorem Adv.wait' {κ ε ε'} {e} {v' it} {ih : IsMValue it} :
    (e.val, ε) ⇓ (v', ε') → e.chan = κ → it = Term.wait (Term.chan κ) →
    (⟨it, ih⟩, ε) [e]⇘ (v', ε') := by
  intro hev hκ hinp
  subst hinp; obtain ⟨ec, ev⟩ := e; cases hκ; exact Adv.wait hev

theorem Adv.tail'' {v} {ε e it} {ih : IsMValue it} :
    it = Term.tail v.val → (⟨it, ih⟩, ε) [e]⇘ (v, ε) := by
  intro hinp
  subst hinp
  obtain ⟨l, hl⟩ := IsMValue.tail_loc ih
  have hv : v = MVal.loc l := Subtype.ext hl
  subst hv; exact Adv.tail

theorem Adv.watch'' {l} {ε} {e s a} {ha : IsMValue a}
    {it} {ih : IsMValue it} :
    s ∈ ε.now.lookup l → s.ticked → s.head.val = Term.in1 a →
    it = Term.watch (Term.loc l) → (⟨it, ih⟩, ε) [e]⇘ (⟨a, ha⟩, ε) := by
  intro hl ht hh hinp
  subst hinp; exact Adv.watch hl ht (Subtype.ext hh)

theorem Adv.select1' {a b} {ε ε' e w it} {ih : IsMValue it}
    {ha : IsMValue a} :
    (⟨a, ha⟩, ε) [e]⇘ (w, ε') → a.ticked ε.now e.chan → ¬ b.ticked ε.now e.chan →
    it = Term.select a b → (⟨it, ih⟩, ε) [e]⇘ (MVal.in1 (MVal.in1 w), ε') := by
  intro h1 t1 t2 hinp
  subst hinp; exact Adv.select1 (v1 := ⟨a, ha⟩) (v2 := ⟨b, IsMValue.select_snd ih⟩) t1 t2 h1

theorem Adv.select2' {a b} {ε ε' e w it} {ih : IsMValue it}
    {hb : IsMValue b} :
    (⟨b, hb⟩, ε) [e]⇘ (w, ε') → b.ticked ε.now e.chan → ¬ a.ticked ε.now e.chan →
    it = Term.select a b → (⟨it, ih⟩, ε) [e]⇘ (MVal.in1 (MVal.in2 w), ε') := by
  intro h1 t2 t1 hinp
  subst hinp; exact Adv.select2 (v1 := ⟨a, IsMValue.select_fst ih⟩) (v2 := ⟨b, hb⟩) t2 t1 h1

theorem Adv.select3' {a b} {ε ε' ε'' e w1 w2 it} {ih : IsMValue it}
    {ha : IsMValue a} {hb : IsMValue b} :
    (⟨a, ha⟩, ε) [e]⇘ (w1, ε') → (⟨b, hb⟩, ε') [e]⇘ (w2, ε'') →
    a.ticked ε.now e.chan → b.ticked ε.now e.chan →
    it = Term.select a b → (⟨it, ih⟩, ε) [e]⇘ (MVal.in2 (MVal.pair w1 w2), ε'') := by
  intro h1 h2 t1 t2 hinp
  subst hinp; exact Adv.select3 (v1 := ⟨a, ha⟩) (v2 := ⟨b, hb⟩) t1 t2 h1 h2

theorem advF_sound (n : Nat) : ∀ (val : MVal) (e : Event) (ε : Env) (v' : MVal) (ε' : Env),
    advF n val e ε = some (v', ε') → (val, ε) [e]⇘ (v', ε') := by
  induction n with
  | zero => intro val e ε v' ε' h; simp only [advF, reduceCtorEq] at h
  | succ n IH =>
    intro val e ε v' ε' h
    obtain ⟨vt, hv⟩ := val
    simp only [advF] at h
    repeat' split at h
    all_goals first
      | exact Adv.appE'' (IH _ _ _ _ _ (by assumption)) (evalF_sound _ _ _ _ _ h) rfl
      | exact Adv.wait' (evalF_sound _ _ _ _ _ h) (by assumption) rfl
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
         exact Adv.watch'' (by assumption) (by assumption) (by assumption) rfl)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
         exact Adv.tail'' rfl)
      -- the three `select` cases: `apply` (not `refine`) so the intermediate env and
      -- value-proof implicits get synthesised from the advance sub-goals.
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
         apply Adv.select3' <;> first | rfl | exact IH _ _ _ _ _ (by assumption) | assumption)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
         apply Adv.select1' <;> first | rfl | exact IH _ _ _ _ _ (by assumption) | assumption)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h;
         apply Adv.select2' <;> first | rfl | exact IH _ _ _ _ _ (by assumption) | assumption)
      | simp only [reduceCtorEq] at h

end Reflect
