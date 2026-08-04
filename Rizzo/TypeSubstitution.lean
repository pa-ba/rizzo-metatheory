import Rizzo.Types

/-
Operations on types: shifting (`Typ.shift`), single substitution
(`Typ.subAt`/`Typ.sub`), and parallel substitution (`Typ.substAll`), and
their lemmas.
-/

open Typ

-- `shift c A` increments every free type variable of `A` with index
-- `≥ c` by one (used when pushing a substitution under the `μ`
-- binder).
@[simp]
def Typ.shift (c : Nat) (A : Typ) : Typ :=
  match A with
  | 𝟭 => 𝟭
  | A1 ⨂ A2 => A1.shift c ⨂ A2.shift c
  | A1 ⨁ A2 => A1.shift c ⨁ A2.shift c
  | A1 ⟶ A2 => A1.shift c ⟶ A2.shift c
  | var i => if i < c then var i else var (i+1)
  | □ A' => □ (A'.shift c)
  | ◯ A' => ◯ (A'.shift c)
  | μ A' => μ (A'.shift (c+1))
  | sig A' => sig (A'.shift c)
  | chan A' => chan (A'.shift c)

-- `subAt k B A` substitutes `B` for the type variable `var k` in `A`,
-- decrementing the free variables above `k` and shifting `B` when it
-- is pushed under the `μ` binder.
@[simp]
def Typ.subAt (A : Typ) (k : Nat) (B : Typ) : Typ :=
  match A with
  | 𝟭 => 𝟭
  | A1 ⨂ A2 => A1.subAt k B ⨂ A2.subAt k B
  | A1 ⨁ A2 => A1.subAt k B ⨁ A2.subAt k B
  | A1 ⟶ A2 => A1.subAt k B ⟶ A2.subAt k B
  | var i => if i = k then B else if k < i then var (i-1) else var i
  | □ A' => □ (A'.subAt k B)
  | ◯ A' => ◯ (A'.subAt k B)
  | μ A' => μ (A'.subAt (k+1) (B.shift 0))
  | sig A' => sig (A'.subAt k B)
  | chan A' => chan (A'.subAt k B)

-- Instantiation of the variable `var 0` (the one bound by the nearest
-- enclosing `μ`).
@[simp]
def Typ.sub (A B : Typ) : Typ := A.subAt 0 B

-- Parallel substitution of the type variables `var 0, var 1, …` by the
-- types in `Cs` (variables beyond `Cs.length` are left untouched).
def Typ.substAll (A : Typ) (Cs : List Typ) : Typ :=
  match A with
  | 𝟭 => 𝟭
  | A1 ⨂ A2 => A1.substAll Cs ⨂ A2.substAll Cs
  | A1 ⨁ A2 => A1.substAll Cs ⨁ A2.substAll Cs
  | A1 ⟶ A2 => A1.substAll Cs ⟶ A2.substAll Cs
  | var i => Cs.getD i (var i)
  | □ A' => □ (A'.substAll Cs)
  | ◯ A' => ◯ (A'.substAll Cs)
  | μ A' => μ (A'.substAll (α₀ :: Cs.map (Typ.shift 0)))
  | sig A' => sig (A'.substAll Cs)
  | chan A' => chan (A'.substAll Cs)

-- The iterated arrow `(S₀ ⟶ C₀) ⟶ … ⟶ (S_{m-1} ⟶ C_{m-1}) ⟶ T`.
def Typ.funcsTo : List Typ → List Typ → Typ → Typ
  | S :: Ss, C :: Cs, T => (S ⟶ C) ⟶ Typ.funcsTo Ss Cs T
  | _, _, T => T

-- `substAll` is the identity when the list reproduces the variables it
-- substitutes .
lemma Typ.substAll_id : ∀ {A : Typ} {k Cs},
    A.Wf k → (∀ i, i < k → Cs[i]? = some (Typ.var i)) → A.substAll Cs = A := by
  intro A
  induction A with
  | unit => intro k Cs _ _; rfl
  | prod A1 A2 ih1 ih2 => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [ih1 ‹_› H, ih2 ‹_› H]
  | sum A1 A2 ih1 ih2 => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [ih1 ‹_› H, ih2 ‹_› H]
  | arr A1 A2 ih1 ih2 =>
      intro k Cs W H; cases W; simp only [Typ.substAll]
      rw [ih1 ‹_› (fun i h => (Nat.not_lt_zero i h).elim), ih2 ‹_› H]
  | var i => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [List.getD_eq_getElem?_getD, H i ‹_›]; rfl
  | delayA A' ih => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› (fun i h => (Nat.not_lt_zero i h).elim)]
  | delayE A' ih => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› (fun i h => (Nat.not_lt_zero i h).elim)]
  | chan A' ih => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› (fun i h => (Nat.not_lt_zero i h).elim)]
  | sig A' ih => intro k Cs W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› H]
  | mu A' ih =>
      intro k Cs W H; cases W; simp only [Typ.substAll]
      rw [ih ‹_› ?_]
      intro i hi
      cases i with
      | zero => rfl
      | succ j =>
          simp only [List.getElem?_cons_succ, List.getElem?_map, H j (by omega), Option.map_some]
          simp [Typ.shift]

-- `substAll` depends on `Cs` only through its first `n` entries (where
-- `n` bounds the free variables of `A`).
lemma Typ.substAll_eq : ∀ {A : Typ} {n Cs Cs'},
    A.Wf n → (∀ i, i < n → Cs[i]? = Cs'[i]?) → A.substAll Cs = A.substAll Cs' := by
  intro A
  induction A with
  | unit => intro n Cs Cs' _ _; rfl
  | prod A1 A2 ih1 ih2 => intro n Cs Cs' W H; cases W; simp only [Typ.substAll]; rw [ih1 ‹_› H, ih2 ‹_› H]
  | sum A1 A2 ih1 ih2 => intro n Cs Cs' W H; cases W; simp only [Typ.substAll]; rw [ih1 ‹_› H, ih2 ‹_› H]
  | arr A1 A2 ih1 ih2 =>
      intro n Cs Cs' W H; cases W; simp only [Typ.substAll]
      rw [ih1 ‹_› (fun i h => (Nat.not_lt_zero i h).elim), ih2 ‹_› H]
  | var i =>
      intro n Cs Cs' W H; cases W; rename_i h
      simp only [Typ.substAll, List.getD_eq_getElem?_getD]; rw [H i h]
  | delayA A' ih => intro n Cs Cs' W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› (fun i h => (Nat.not_lt_zero i h).elim)]
  | delayE A' ih => intro n Cs Cs' W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› (fun i h => (Nat.not_lt_zero i h).elim)]
  | chan A' ih => intro n Cs Cs' W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› (fun i h => (Nat.not_lt_zero i h).elim)]
  | sig A' ih => intro n Cs Cs' W H; cases W; simp only [Typ.substAll]; rw [ih ‹_› H]
  | mu A' ih =>
      intro n Cs Cs' W H; cases W; simp only [Typ.substAll]
      rw [ih ‹_› ?_]
      intro i hi
      cases i with
      | zero => rfl
      | succ j => simp only [List.getElem?_cons_succ, List.getElem?_map, H j (by omega)]

-- Substituting a variable that is out of scope is the identity.
lemma Typ.Wf.subAt_ge : ∀ {A : Typ} {n k B}, A.Wf n → n ≤ k → A.subAt k B = A := by
  intro A n k B W Le
  induction W generalizing k B with
  | var h => simp only [Typ.subAt]; rw [if_neg (by omega), if_neg (by omega)]
  | _ => simp_all [Typ.subAt]

-- Likewise shifting above the scope is the identity.
lemma Typ.Wf.shift_ge : ∀ {A : Typ} {n c}, A.Wf n → n ≤ c → A.shift c = A := by
  intro A n c W Le
  induction W generalizing c <;> simp_all [Typ.shift]
  omega

lemma Typ.sub_closed {A : Typ} : A.Closed → A.sub B = A := fun W => W.subAt_ge (Nat.zero_le _)

lemma Typ.substAll_closed {A : Typ} (W : A.Closed) (Cs : List Typ) : A.substAll Cs = A :=
  Typ.substAll_id W (fun i h => (Nat.not_lt_zero i h).elim)

lemma Typ.shift_closed {A : Typ} : A.Closed → A.shift c = A := fun W => W.shift_ge (Nat.zero_le _)

-- Shifting preserves well-formedness (introducing one extra variable).
lemma Typ.Wf.shift : ∀ {A : Typ} {n c}, A.Wf n → c ≤ n → (A.shift c).Wf (n+1) := by
  intro A
  induction A with
  | unit => intro n c _ _; exact .unit
  | prod A1 A2 ih1 ih2 => intro n c W Le; cases W; simp only [Typ.shift]; exact .prod (ih1 ‹_› Le) (ih2 ‹_› Le)
  | sum A1 A2 ih1 ih2 => intro n c W Le; cases W; simp only [Typ.shift]; exact .sum (ih1 ‹_› Le) (ih2 ‹_› Le)
  | arr A1 A2 ih1 ih2 =>
      intro n c W Le; cases W
      simp only [Typ.shift]; rw [‹A1.Wf 0›.shift_ge (Nat.zero_le _)]
      exact .arr ‹_› (ih2 ‹_› Le)
  | var i => intro n c W Le; cases W; simp only [Typ.shift]; split <;> exact .var (by omega)
  | delayA A' _ => intro n c W Le; cases W; simp only [Typ.shift]; rw [‹A'.Wf 0›.shift_ge (Nat.zero_le _)]; exact .delayA ‹_›
  | delayE A' _ => intro n c W Le; cases W; simp only [Typ.shift]; rw [‹A'.Wf 0›.shift_ge (Nat.zero_le _)]; exact .delayE ‹_›
  | mu A' ih => intro n c W Le; cases W; simp only [Typ.shift]; exact .mu (ih ‹_› (by omega))
  | sig A' ih => intro n c W Le; cases W; simp only [Typ.shift]; exact .sig (ih ‹_› Le)
  | chan A' ih =>
      intro n c W Le; cases W; simp only [Typ.shift]; rw [‹A'.Wf 0›.shift_ge (Nat.zero_le _)]; exact .chan ‹_›

-- Substitution lemma

lemma Typ.Wf.subAt : ∀ {A : Typ} {n k} {B : Typ}, A.Wf (n+1) → k ≤ n → B.Wf n → (A.subAt k B).Wf n := by
  intro A
  induction A with
  | unit => intro n k B _ _ _; exact .unit
  | prod A1 A2 ih1 ih2 => intro n k B W Le WB; cases W; simp only [Typ.subAt]; exact .prod (ih1 ‹_› Le WB) (ih2 ‹_› Le WB)
  | sum A1 A2 ih1 ih2 => intro n k B W Le WB; cases W; simp only [Typ.subAt]; exact .sum (ih1 ‹_› Le WB) (ih2 ‹_› Le WB)
  | arr A1 A2 ih1 ih2 =>
      intro n k B W Le WB; cases W
      simp only [Typ.subAt]; rw [‹A1.Wf 0›.subAt_ge (Nat.zero_le _)]
      exact .arr ‹_› (ih2 ‹_› Le WB)
  | var i =>
      intro n k B W Le WB; cases W; rename_i h; simp only [Typ.subAt]
      by_cases hik : i = k
      · rw [if_pos hik]; exact WB
      · rw [if_neg hik]; by_cases hki : k < i <;> simp only [hki, if_true, if_false] <;> exact .var (by omega)
  | delayA A' _ => intro n k B W Le WB; cases W; simp only [Typ.subAt]; rw [‹A'.Wf 0›.subAt_ge (Nat.zero_le _)]; exact .delayA ‹_›
  | delayE A' _ => intro n k B W Le WB; cases W; simp only [Typ.subAt]; rw [‹A'.Wf 0›.subAt_ge (Nat.zero_le _)]; exact .delayE ‹_›
  | mu A' ih => intro n k B W Le WB; cases W; simp only [Typ.subAt]; exact .mu (ih ‹_› (by omega) (WB.shift (Nat.zero_le _)))
  | sig A' ih => intro n k B W Le WB; cases W; simp only [Typ.subAt]; exact .sig (ih ‹_› Le WB)
  | chan A' ih =>
      intro n k B W Le WB; cases W; simp only [Typ.subAt]; rw [‹A'.Wf 0›.subAt_ge (Nat.zero_le _)]; exact .chan ‹_›


lemma Typ.Wf.sub {A B : Typ} : A.Wf (n+1) → B.Wf n → (A.sub B).Wf n :=
  fun WA WB => WA.subAt (Nat.zero_le _) WB

lemma Typ.substAll_Wf : ∀ {A : Typ} {k n Cs},
    A.Wf k → (∀ i, i < k → ∃ C, Cs[i]? = some C ∧ C.Wf n) → (A.substAll Cs).Wf n := by
  intro A
  induction A with
  | unit => intro k n Cs _ _; exact .unit
  | prod A1 A2 ih1 ih2 => intro k n Cs W H; cases W; exact .prod (ih1 ‹_› H) (ih2 ‹_› H)
  | sum A1 A2 ih1 ih2 => intro k n Cs W H; cases W; exact .sum (ih1 ‹_› H) (ih2 ‹_› H)
  | arr A1 A2 ih1 ih2 =>
      intro k n Cs W H; cases W
      simp only [Typ.substAll]
      rw [Typ.substAll_id ‹A1.Wf 0› (fun i h => (Nat.not_lt_zero i h).elim)]
      exact .arr ‹_› (ih2 ‹_› H)
  | var i =>
      intro k n Cs W H; cases W
      obtain ⟨C, hC, hWf⟩ := H i ‹_›
      simp only [Typ.substAll]; rw [List.getD_eq_getElem?_getD, hC]; exact hWf
  | delayA A' _ =>
      intro k n Cs W H; cases W
      simp only [Typ.substAll]; rw [Typ.substAll_id ‹A'.Wf 0› (fun i h => (Nat.not_lt_zero i h).elim)]
      exact .delayA ‹_›
  | delayE A' _ =>
      intro k n Cs W H; cases W
      simp only [Typ.substAll]; rw [Typ.substAll_id ‹A'.Wf 0› (fun i h => (Nat.not_lt_zero i h).elim)]
      exact .delayE ‹_›
  | chan A' ih =>
      intro k n Cs W H; cases W
      simp only [Typ.substAll]; rw [Typ.substAll_id ‹A'.Wf 0› (fun i h => (Nat.not_lt_zero i h).elim)]
      exact .chan ‹_›
  | sig A' ih => intro k n Cs W H; cases W; exact .sig (ih ‹_› H)
  | mu A' ih =>
      intro k n Cs W H; cases W
      refine .mu (ih ‹_› ?_)
      intro i hi
      cases i with
      | zero => exact ⟨α₀, rfl, .var (by omega)⟩
      | succ j =>
          obtain ⟨C, hC, hWf⟩ := H j (by omega)
          refine ⟨C.shift 0, ?_, hWf.shift (Nat.zero_le _)⟩
          simp only [List.getElem?_cons_succ, List.getElem?_map, hC, Option.map_some]

-- Substituting closed types for all variables of a type yields a
-- closed type.
lemma Typ.substAll_Wf_closed {A : Typ} {Cs : List Typ} :
    A.Wf Cs.length → (∀ C ∈ Cs, C.Closed) → (A.substAll Cs).Closed :=
  fun W h => Typ.substAll_Wf W (fun i hi =>
    ⟨Cs[i], by rw [List.getElem?_eq_getElem hi], h _ (List.getElem_mem hi)⟩)

-- Commutation of single substitution with parallel substitution.
lemma Typ.substAll_subAt_comm : ∀ {A : Typ} {k} {pre L : List Typ} {X},
    A.Wf (k + L.length + 1) → pre.length = k →
    (∀ i, i < k → pre[i]? = some (Typ.var i)) → (∀ C ∈ L, C.Closed) →
    (A.substAll (pre ++ Typ.var k :: L)).subAt k X = A.substAll (pre ++ X :: L) := by
  intro A
  induction A with
  | unit => intro k pre L X _ _ _ _; rfl
  | prod A1 A2 ih1 ih2 =>
      intro k pre L X W hp hpre hL; cases W
      simp only [Typ.substAll, Typ.subAt]; rw [ih1 ‹_› hp hpre hL, ih2 ‹_› hp hpre hL]
  | sum A1 A2 ih1 ih2 =>
      intro k pre L X W hp hpre hL; cases W
      simp only [Typ.substAll, Typ.subAt]; rw [ih1 ‹_› hp hpre hL, ih2 ‹_› hp hpre hL]
  | arr A1 A2 ih1 ih2 =>
      intro k pre L X W hp hpre hL; cases W; rename_i W1 W2
      simp only [Typ.substAll, Typ.subAt,
        Typ.substAll_id W1 (fun i h => (Nat.not_lt_zero i h).elim),
        W1.subAt_ge (Nat.zero_le k), ih2 W2 hp hpre hL]
  | delayA A' _ =>
      intro k pre L X W hp hpre hL; cases W; rename_i W'
      simp only [Typ.substAll, Typ.subAt,
        Typ.substAll_id W' (fun i h => (Nat.not_lt_zero i h).elim), W'.subAt_ge (Nat.zero_le k)]
  | delayE A' _ =>
      intro k pre L X W hp hpre hL; cases W; rename_i W'
      simp only [Typ.substAll, Typ.subAt,
        Typ.substAll_id W' (fun i h => (Nat.not_lt_zero i h).elim), W'.subAt_ge (Nat.zero_le k)]
  | chan A' ih =>
      intro k pre L X W hp hpre hL; cases W; rename_i W'
      simp only [Typ.substAll, Typ.subAt,
        Typ.substAll_id W' (fun i h => (Nat.not_lt_zero i h).elim), W'.subAt_ge (Nat.zero_le k)]
  | sig A' ih =>
      intro k pre L X W hp hpre hL; cases W
      simp only [Typ.substAll, Typ.subAt]; rw [ih ‹_› hp hpre hL]
  | var i =>
      intro k pre L X W hp hpre hL; cases W; rename_i hik
      simp only [Typ.substAll]
      subst hp
      rcases Nat.lt_trichotomy i pre.length with h | h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, hpre i h,
            List.getD_eq_getElem?_getD, List.getElem?_append_left h, hpre i h]
        simp only [Option.getD]; simp only [Typ.subAt]; rw [if_neg (by omega), if_neg (by omega)]
      · subst h
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero,
            List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero]
        simp [Option.getD, Typ.subAt]
      · have hi1 : i - pre.length - 1 < L.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
            List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
        obtain ⟨d, hd⟩ : ∃ d, i - pre.length = d + 1 := ⟨i - pre.length - 1, by omega⟩
        have hcons : (Typ.var pre.length :: L)[i - pre.length]? = L[i - pre.length - 1]? := by
          rw [hd]; simp [List.getElem?_cons_succ]
        have hcons2 : (X :: L)[i - pre.length]? = L[i - pre.length - 1]? := by
          rw [hd]; simp [List.getElem?_cons_succ]
        rw [hcons, hcons2, List.getElem?_eq_getElem hi1]
        simp only [Option.getD]
        rw [(hL _ (List.getElem_mem hi1)).subAt_ge (Nat.zero_le _)]
  | mu A' ih =>
      intro k pre L X W hp hpre hL; cases W; rename_i W'
      simp only [Typ.substAll, Typ.subAt]
      have hWf' : A'.Wf ((k + 1) + (L.map (Typ.shift 0)).length + 1) := by
        simpa [List.length_map, Nat.add_right_comm, Nat.add_assoc] using W'
      have hpre' : ∀ j, j < k + 1 → (α₀ :: pre.map (Typ.shift 0))[j]? = some (Typ.var j) := by
        intro j hj
        cases j with
        | zero => rfl
        | succ d =>
            simp only [List.getElem?_cons_succ, List.getElem?_map, hpre d (by omega), Option.map_some]
            simp [Typ.shift]
      have hL' : ∀ C ∈ L.map (Typ.shift 0), C.Closed := by
        intro C hC
        simp only [List.mem_map] at hC
        obtain ⟨C', hC', rfl⟩ := hC
        rw [Typ.shift_closed (hL C' hC')]; exact hL C' hC'
      have key := ih (k := k+1) (pre := α₀ :: pre.map (Typ.shift 0))
        (L := L.map (Typ.shift 0)) (X := X.shift 0) hWf' (by simp [List.length_map, hp]) hpre' hL'
      have e : Typ.shift 0 (Typ.var k) = Typ.var (k + 1) := by simp [Typ.shift]
      simp only [List.map_append, List.map_cons, e]
      exact congrArg Typ.mu key

lemma Typ.getElem?_rangeVar_append (c i : Nat) (rest : List Typ) :
    ((List.range c).map Typ.var ++ rest)[i]? =
      if i < c then some (Typ.var i) else rest[i - c]? := by
  by_cases h : i < c
  · rw [if_pos h, List.getElem?_append_left (by simpa using h)]
    simp [List.getElem?_map, List.getElem?_eq_getElem (show i < (List.range c).length by simpa using h),
          List.getElem_range]
  · rw [if_neg h, List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.length_map, List.length_range]

lemma Typ.var0_cons_rangeVar_shift (c : Nat) :
    α₀ :: ((List.range c).map Typ.var).map (Typ.shift 0) = (List.range (c+1)).map Typ.var := by
  simp [List.map_map, List.range_succ_eq_map, Function.comp, Typ.shift]

lemma Typ.shift_shift : ∀ {A : Typ} {d c}, d ≤ c →
    (A.shift d).shift (c+1) = (A.shift c).shift d := by
  intro A
  induction A with
  | unit => intro d c _; rfl
  | prod A1 A2 ih1 ih2 => intro d c h; simp only [Typ.shift]; rw [ih1 h, ih2 h]
  | sum A1 A2 ih1 ih2 => intro d c h; simp only [Typ.shift]; rw [ih1 h, ih2 h]
  | arr A1 A2 ih1 ih2 => intro d c h; simp only [Typ.shift]; rw [ih1 h, ih2 h]
  | delayA A' ih => intro d c h; simp only [Typ.shift]; rw [ih h]
  | delayE A' ih => intro d c h; simp only [Typ.shift]; rw [ih h]
  | chan A' ih => intro d c h; simp only [Typ.shift]; rw [ih h]
  | sig A' ih => intro d c h; simp only [Typ.shift]; rw [ih h]
  | mu A' ih => intro d c h; simp only [Typ.shift]; rw [ih (show d+1 ≤ c+1 by omega)]
  | var i =>
      intro d c h
      by_cases h1 : i < d
      · simp only [Typ.shift, if_pos h1, if_pos (show i < c by omega), if_pos (show i < c+1 by omega)]
      · by_cases h2 : i < c
        · simp only [Typ.shift, if_neg h1, if_pos h2, if_pos (show i+1 < c+1 by omega)]
        · simp only [Typ.shift, if_neg h1, if_neg h2, if_neg (show ¬ i+1 < c+1 by omega),
                     if_neg (show ¬ i+1 < d by omega)]

lemma Typ.shift_substAll' : ∀ {A : Typ} {c} {Es : List Typ},
    (A.shift c).substAll ((List.range c).map Typ.var ++ Typ.var c :: Es.map (Typ.shift c))
      = (A.substAll ((List.range c).map Typ.var ++ Es)).shift c := by
  intro A
  induction A with
  | unit => intro c Es; rfl
  | prod A1 A2 ih1 ih2 => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih1, ih2]
  | sum A1 A2 ih1 ih2 => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih1, ih2]
  | arr A1 A2 ih1 ih2 => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih1, ih2]
  | delayA A' ih => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih]
  | delayE A' ih => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih]
  | chan A' ih => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih]
  | sig A' ih => intro c Es; simp only [Typ.shift, Typ.substAll]; rw [ih]
  | var i =>
      intro c Es
      simp only [Typ.shift]
      by_cases h : i < c
      · rw [if_pos h]
        simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
                   if_pos h, Option.getD_some, Typ.shift]
      · rw [if_neg h]
        obtain ⟨m, rfl⟩ : ∃ m, i = c + m := ⟨i - c, by omega⟩
        simp only [Typ.substAll, List.getD_eq_getElem?_getD, Typ.getElem?_rangeVar_append,
                   if_neg (show ¬ c + m + 1 < c by omega), if_neg (show ¬ c + m < c by omega)]
        rw [show c + m + 1 - c = m + 1 by omega, show c + m - c = m by omega,
            List.getElem?_cons_succ, List.getElem?_map]
        cases hEs : Es[m]? with
        | none => simp [Typ.shift, show ¬ c + m < c by omega]
        | some E => simp
  | mu A' ih =>
      intro c Es
      simp only [Typ.shift, Typ.substAll]
      congr 1
      have hL : α₀ :: ((List.range c).map Typ.var ++ Typ.var c :: Es.map (Typ.shift c)).map (Typ.shift 0)
              = (List.range (c+1)).map Typ.var ++ Typ.var (c+1) :: (Es.map (Typ.shift 0)).map (Typ.shift (c+1)) := by
        have hmap : (Es.map (Typ.shift c)).map (Typ.shift 0) = (Es.map (Typ.shift 0)).map (Typ.shift (c+1)) := by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro E _
          simp only [Function.comp_apply]
          exact (Typ.shift_shift (Nat.zero_le c)).symm
        rw [List.map_append, List.map_cons, ← List.cons_append, Typ.var0_cons_rangeVar_shift, hmap,
            show Typ.shift 0 (Typ.var c) = Typ.var (c+1) by simp [Typ.shift]]
      have hR : α₀ :: ((List.range c).map Typ.var ++ Es).map (Typ.shift 0)
              = (List.range (c+1)).map Typ.var ++ Es.map (Typ.shift 0) := by
        rw [List.map_append, ← List.cons_append, Typ.var0_cons_rangeVar_shift]
      rw [hL, hR]
      exact ih

lemma Typ.substAll_substAll : ∀ {A : Typ} {Cs : List Typ} {Ds},
    A.Wf Cs.length →
    (A.substAll Cs).substAll Ds = A.substAll (Cs.map (·.substAll Ds)) := by
  intro A
  induction A with
  | unit => intro Cs Ds _; rfl
  | prod A1 A2 ih1 ih2 => intro Cs Ds W; cases W; simp only [Typ.substAll]; rw [ih1 ‹_›, ih2 ‹_›]
  | sum A1 A2 ih1 ih2 => intro Cs Ds W; cases W; simp only [Typ.substAll]; rw [ih1 ‹_›, ih2 ‹_›]
  | arr A1 A2 ih1 ih2 =>
      intro Cs Ds W; cases W; rename_i W1 W2
      simp only [Typ.substAll,
        Typ.substAll_id W1 (fun i h => (Nat.not_lt_zero i h).elim), ih2 W2]
  | delayA A' _ => intro Cs Ds W; cases W; rename_i W'; simp only [Typ.substAll, Typ.substAll_id W' (fun i h => (Nat.not_lt_zero i h).elim)]
  | delayE A' _ => intro Cs Ds W; cases W; rename_i W'; simp only [Typ.substAll, Typ.substAll_id W' (fun i h => (Nat.not_lt_zero i h).elim)]
  | chan A' ih =>
      intro Cs Ds W; cases W; rename_i W'
      simp only [Typ.substAll, Typ.substAll_id W' (fun i h => (Nat.not_lt_zero i h).elim)]
  | sig A' ih => intro Cs Ds W; cases W; simp only [Typ.substAll]; rw [ih ‹_›]
  | var i =>
      intro Cs Ds W; cases W; rename_i h
      simp only [Typ.substAll, List.getD_eq_getElem?_getD,
                 List.getElem?_eq_getElem h,Option.getD_some,
                 List.getElem?_eq_getElem (show i < (Cs.map (·.substAll Ds)).length by simpa using h),
                 List.getElem_map]
  | mu A' ih =>
      intro Cs Ds W; cases W; rename_i W'
      simp only [Typ.substAll]
      congr 1
      rw [ih (Cs := α₀ :: Cs.map (Typ.shift 0)) (by simpa using W')]
      have hlist : (α₀ :: Cs.map (Typ.shift 0)).map (·.substAll (α₀ :: Ds.map (Typ.shift 0)))
                 = α₀ :: (Cs.map (·.substAll Ds)).map (Typ.shift 0) := by
        simp only [List.map_cons, List.map_map]
        refine congrArg₂ List.cons ?_ ?_
        · simp [Typ.substAll]
        · apply List.map_congr_left
          intro C _
          simp only [Function.comp_apply]
          exact Typ.shift_substAll' (A := C) (c := 0) (Es := Ds)
      rw [hlist]

-- Substitution along an identity / empty list of types.
lemma Typ.substAll_rangeVar : ∀ {A : Typ} {n},
    A.substAll ((List.range n).map Typ.var) = A := by
  intro A
  induction A with
  | unit => intro n; rfl
  | prod A1 A2 ih1 ih2 => intro n; simp only [Typ.substAll]; rw [ih1, ih2]
  | sum A1 A2 ih1 ih2 => intro n; simp only [Typ.substAll]; rw [ih1, ih2]
  | arr A1 A2 ih1 ih2 => intro n; simp only [Typ.substAll]; rw [ih1, ih2]
  | var i =>
      intro n
      simp only [Typ.substAll]
      rcases Nat.lt_or_ge i n with h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_none (by simpa using h)]; rfl
  | delayA A' ih => intro n; simp only [Typ.substAll]; rw [ih]
  | delayE A' ih => intro n; simp only [Typ.substAll]; rw [ih]
  | chan A' ih => intro n; simp only [Typ.substAll]; rw [ih]
  | sig A' ih => intro n; simp only [Typ.substAll]; rw [ih]
  | mu A' ih =>
      intro n
      simp only [Typ.substAll]
      rw [Typ.var0_cons_rangeVar_shift, ih]

@[simp] lemma Typ.substAll_nil {A : Typ} : A.substAll [] = A := by
  simpa using Typ.substAll_rangeVar (A := A) (n := 0)
