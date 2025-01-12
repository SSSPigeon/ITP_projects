/-
This formalization is based on a part of Introduction to
Homotopy Type Theory by Egbert Rijke.
Chapter 1, Section 7: Modular arithmetic via the Curry-Howard interpretation
-/

import Mathlib.Data.Real.Basic
import Mathlib.Init.Logic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Ring.Defs



/-identity types-/
#check Eq

/-Definition 7.1.2-/
structure div (d n: ℕ) where
 k : ℕ
 mult : Eq n (d*k)

/-propositional truncation-/
#check Nonempty

/-Proposition 7.1.5
--Consider three natural numbers d, x and y. If d divides any
two of the three numbers x, y, and x+y, then it also divides
the third.
-/
def two_div_three_1 (d x y :ℕ)(hx : div d x)(hy:div d y):
Σ' hxy: div d (x+y), hxy.k = hx.k + hy.k := by
    let ⟨ a, ha ⟩ := hx
    let ⟨ b, hb ⟩ := hy
    simp
    refine ⟨⟨a + b, ?_⟩, rfl⟩
    linarith


def two_div_three_2 (d x y :ℕ)(hx : div d x)(hxy : div d (x+y)):
 div d y := by
    let ⟨ a, ha ⟩ := hx
    let ⟨ b, hb ⟩ := hxy
    cases' d with n
    --d=0
    . cases b - a
        --b ≤ a
      . refine ⟨a - b, ?_⟩
        simp; omega
        -- b > a
      . refine ⟨b - a, ?_⟩
        simp; omega
    --d>0
    . refine ⟨b - a, ?_⟩
      calc y = (x + y) - x := by simp
           _ = (n + 1) * b - (n + 1) * a := by rw [hb, ha]
           _ = (n + 1) * (b - a) := by exact (Nat.mul_sub_left_distrib (n + 1) b a).symm


def dista (n m : ℕ) := (n - m) + (m - n)


/-Definition 7.2.2-/
def congr_modulo (k x y :ℕ): Type := div k (dista x y)

/- Proposition 7.2.4
For each k : ℕ, the congruence relation modulo k is an
equivalence relation.
-/

def modulo_refl (n :ℕ): Π x : ℕ, congr_modulo n x x := by
    intro x
    rw [congr_modulo]
    refine ⟨0, ?_⟩
    ring_nf
    cases x
    aesop
    simp [dista]


def modulo_symm (n :ℕ): Π x : ℕ, Π y : ℕ , congr_modulo n x y → congr_modulo n y x := by
    intro x y hxy
    rw [congr_modulo] at *
    refine ⟨ hxy.1, ?_⟩
    have : dista x y = dista y x := by simp[dista, add_comm]
    rw[← this]
    let ⟨k, hkxy⟩ := hxy
    simp
    exact hkxy


def modulo_trans (k :ℕ): Π x : ℕ, Π y : ℕ , Π z : ℕ, congr_modulo n x y → (congr_modulo n y z → congr_modulo n x z) := by
    intro x y z hxy hyz
    rw [congr_modulo] at *
    let ⟨j, hkxy⟩ := hxy
    let ⟨k, hkyz⟩ := hyz
    cases h1 : decide (x<y)
    . simp at h1
      cases h2 : decide (y<z)
      . simp at h2
        refine ⟨ j + k, ?_ ⟩
        have : dista x z = dista x y + dista y z := by
            simp[dista]; omega
        rw [this, mul_add, hkxy, hkyz]
      . simp at h2
        cases h3 : decide (x<z)
        . simp at h3
          refine ⟨ j - k, ?_ ⟩
          have : dista x z = dista x y - dista y z := by
            simp[dista]; omega
          rw [this, Nat.mul_sub_left_distrib n j k, hkxy, hkyz]
        . simp at h3
          refine ⟨ k - j, ?_ ⟩
          have : dista x z = dista y z - dista x y := by
            simp[dista]; omega
          rw [this, Nat.mul_sub_left_distrib n k j, hkxy, hkyz]
    . simp at h1
      cases h2 : decide (y<z)
      . simp at h2
        cases h3 : decide (x<z)
        . simp at h3
          refine ⟨ k - j, ?_ ⟩
          have : dista x z = dista y z - dista x y := by
            simp[dista]; omega
          rw [this, Nat.mul_sub_left_distrib n k j, hkxy, hkyz]
        . simp at h3
          refine ⟨ j - k, ?_ ⟩
          have : dista x z = dista x y - dista y z := by
            simp[dista]; omega
          rw [this, Nat.mul_sub_left_distrib n j k, hkxy, hkyz]
      . simp at h2
        refine ⟨ j + k, ?_ ⟩
        have : dista x z = dista x y + dista y z := by
            simp[dista]; omega
        rw [this, mul_add, hkxy, hkyz]


--Coproduct type
#check Sum
#check Sum.rec

/-Definition 7.3.2
the type family Fin of the standard finite types over ℕ-/
def fin (k : ℕ) : Type :=
    match k with
    | 0 => Empty
    | Nat.succ m => Sum (fin m) Unit

/-Remark 7.3.3-/
def indl (k : ℕ): fin k → fin (k+1) := Sum.inl

def uni (k : ℕ) : fin (k+1) := Sum.inr Unit.unit


/-Definition 7.3.4-/
def ι (k : ℕ) (x : fin k): ℕ :=
    match k, x  with
    | Nat.zero, x => nomatch x
    | Nat.succ n, Sum.inl y => ι n y
    | Nat.succ n, Sum.inr _ => n


/-Lemma 7.3.5-/
def fin_bound (k : ℕ) : Π x : fin k, ι k x < k := by
  intro x
  induction' k with n ih
  . nomatch x
  . match x with
    | Sum.inl y =>
        calc
            ι (n + 1) (Sum.inl y) = ι n y := by simp[ι]
                                _ < n := ih y
                                _ < n+1 := by simp
    | Sum.inr _ => simp [ι]



/-Proposition 7.3.6
    ιk is injective-/
def ιk_inj (k : ℕ) (x y : fin k) : ι k x = ι k y → x = y := by
    induction' k with n ih
    . nomatch x
    . intro h
      match x, y with
      | Sum.inl x', Sum.inl y' =>
        simp [ι] at h
        have : x' = y' := by exact ih x' y' h
        rw[this]
      | Sum.inl x', Sum.inr y' =>
        simp [ι] at h; simp
        have h1: ι n x' < n := fin_bound n x'
        rw [h] at h1
        linarith
      | Sum.inr _, Sum.inl y' =>
        simp [ι] at h; simp
        have h2: ι n y' < n := fin_bound n y'
        rw [← h] at h2
        linarith
      | Sum.inr _, Sum.inr _ =>
        simp [ι] at h; simp


/-Definition 7.4.2(i)-/
def zero'(k : ℕ) : fin (k+1) :=
    match k with
    | Nat.zero => uni 0
    | Nat.succ m => indl (m+1) (zero' m)


/-Definition 7.4.2(ii)-/
def skip_zero (k : ℕ) (x : fin k): fin (k+1) := by
  induction' k with n ih
  . nomatch x
  . match x with
    | Sum.inl y => exact indl (n+1) (ih y)
    | Sum.inr _ => exact uni (n+1)


/-Definition 7.4.2(iii)-/
def succ' (k : ℕ) (x : fin k): fin k :=
  match k, x with
  | Nat.zero, x => nomatch x
  | Nat.succ m, Sum.inl y => skip_zero m y
  | Nat.succ m, Sum.inr _ => zero' m


/-Definition 7.4.3-/
def map_nat_fin (k : ℕ) : (x : ℕ) → fin (k + 1)
  | 0 => zero' k
  | y+1 => succ' (k+1) (map_nat_fin k y)

/-Lemma 7.4.4(i)-/
def zero_idt (k : ℕ) : ι (k+1) (zero' k) = 0 := by
  induction' k with _ ih
  . rfl
  . exact ih

/-Lemma 7.4.4(ii)-/
def skip_zero_eq_succ (k : ℕ)(x : fin k) : ι (k+1) (skip_zero k x)=ι k x + 1 := by
  induction' k with n ih
  . nomatch x
  . match x with
    | Sum.inr _ => rfl
    | Sum.inl y => exact ih y


/-Lemma 7.4.4(iii)-/
def succ_eq_mod (k : ℕ)(x : fin k) : congr_modulo k (ι k (succ' k x)) (ι k x + 1) := by
  induction' k with n
  . nomatch x
  . match x with
    | Sum.inr _ =>
      simp [succ', zero_idt, ι, congr_modulo, dista]
      use 1; simp
    | Sum.inl y =>
      simp [succ', skip_zero_eq_succ, ι]
      exact modulo_refl (n + 1) (ι n y + 1)

/-Lemma for 7.4.5-/
def add_one_mod (k x y : ℕ) : congr_modulo k x y → congr_modulo k (x+1) (y+1) := by
  intro h
  simp[congr_modulo, dista]
  aesop


/-Proposition 7.4.5
For any x : ℕ we have
ι[x]_{k+1} == x mod k +1-/
def ι_mnf_eq (k x: ℕ) : congr_modulo (k+1) (ι (k+1) (map_nat_fin k x)) x := by
  induction' x with x ih
  . simp[map_nat_fin, zero_idt]
    exact modulo_refl (k+1) 0
  . unfold map_nat_fin
    have h1 := succ_eq_mod (k+1) (map_nat_fin k x)
    have h2 : congr_modulo (k + 1) (ι (k + 1) (map_nat_fin k x) + 1) (x+1) :=
      add_one_mod (k + 1) (ι (k + 1) (map_nat_fin k x)) x ih
    exact modulo_trans (k+1) (ι (k + 1) (succ' (k + 1) (map_nat_fin k x))) (ι (k + 1) (map_nat_fin k x) + 1) (x + 1) h1 h2


/-Proposition 7.4.6(i)
For any x < d : ℕ we have d | x ↔ x = 0.
Consequently, for any x y : ℕ such that dist(x,y) < k,
x == y mod k ↔ x=y -/
def lt_mod_iff_zero (x d : ℕ)(h : x < d) : Nonempty (div d x) ↔ x = 0 := by
  constructor
  . intro h
    rcases h with ⟨k, mult⟩
    by_contra h1
    have h2: k > 0 := by
      by_contra h2'
      aesop
    have h3 : x < d * k := by
      calc
        x < d := h
        _ ≤ d * k := Nat.le_mul_of_pos_right d h2
    linarith
  . intro h
    use 0
    simp; exact h

/-Proposition 7.4.6(i)-/
def lt_mod_iff_zero'(x y : ℕ) (h : dista x y < k) :
Nonempty (congr_modulo k x y) ↔ x = y := by
  simp [congr_modulo]
  have := lt_mod_iff_zero (dista x y) k h
  have : dista x y = 0 ↔ x = y := by
    constructor
    . simp[dista]
      intro h1 h2; omega
    . simp[dista]
      omega
  aesop


/-Proposition 7.4.7
For x y : ℕ, [x]_{k+1}=[y]_{k+1} ↔ ι[x]_{k+1}=ι[y]_{k+1}-/
def mnf_mod_eq (k x y : ℕ) : map_nat_fin k x = map_nat_fin k y ↔ Nonempty (congr_modulo (k+1) x y) := by
  have g1: map_nat_fin k x = map_nat_fin k y ↔ ι (k+1) (map_nat_fin k x) = ι (k+1) (map_nat_fin k y) := by
    constructor
    . aesop
    . exact ιk_inj (k+1) (map_nat_fin k x) (map_nat_fin k y)
  have h: dista (ι (k+1) (map_nat_fin k x)) (ι (k+1) (map_nat_fin k y)) < k+1 := by
    have h1 : ι (k+1) (map_nat_fin k x) < k + 1 := by simp[fin_bound]
    have h2 : ι (k+1) (map_nat_fin k y) < k + 1 := by simp[fin_bound]
    simp[dista]; omega
  have g2: Nonempty (congr_modulo (k+1) (ι (k+1) (map_nat_fin k x)) (ι (k+1) (map_nat_fin k y))) ↔
  ι (k+1) (map_nat_fin k x) = ι (k+1) (map_nat_fin k y) :=
    lt_mod_iff_zero' (ι (k+1) (map_nat_fin k x)) (ι (k+1) (map_nat_fin k y)) h
  have g3 := Iff.trans g1 (Iff.symm g2)
  have f1 := modulo_symm (k+1) (ι (k+1) (map_nat_fin k x)) x (ι_mnf_eq k x)
  have f1' := ι_mnf_eq k x
  have f2 := ι_mnf_eq k y
  have f2' := modulo_symm (k+1) (ι (k+1) (map_nat_fin k y)) y (ι_mnf_eq k y)
  have g4 : Nonempty (congr_modulo (k + 1) (ι (k + 1) (map_nat_fin k x)) (ι (k + 1) (map_nat_fin k y))) ↔
  Nonempty (congr_modulo (k+1) x y) := by
    constructor
    . intro f3
      have f4 := modulo_trans (k+1) x (ι (k + 1) (map_nat_fin k x)) (ι (k + 1) (map_nat_fin k y)) f1 (Classical.choice f3)
      have f5 := modulo_trans (k+1) x (ι (k + 1) (map_nat_fin k y)) y f4 f2
      exact Nonempty.intro f5
    . intro f3
      have f4 := modulo_trans (k+1) (ι (k + 1) (map_nat_fin k x)) x y f1' (Classical.choice f3)
      have f5 := modulo_trans (k+1) (ι (k + 1) (map_nat_fin k x)) y (ι (k + 1) (map_nat_fin k y)) f4 f2'
      exact Nonempty.intro f5
  exact Iff.trans g3 g4


/-Proposition 7.4.8
For x : Fin_{k+1}, [ι(x)]_{k+1}=x-/
def mnf_split_surj (k : ℕ)(x : fin (k+1)) : map_nat_fin k (ι (k+1) x) = x := by
  apply ιk_inj (k + 1) (map_nat_fin k (ι (k+1) x)) x
  have h1 : ι (k + 1) (map_nat_fin k (ι (k + 1) x)) < k+1 :=
    fin_bound (k + 1) (map_nat_fin k (ι (k + 1) x))
  have h2 : ι (k + 1) x < k+1 := fin_bound (k + 1) x
  have h3 : dista (ι (k + 1) (map_nat_fin k (ι (k + 1) x))) (ι (k + 1) x) < k+1 := by
    simp[dista]; omega
  apply (Iff.symm (lt_mod_iff_zero' (ι (k + 1) (map_nat_fin k (ι (k + 1) x))) (ι (k + 1) x) h3)).mpr
  exact Nonempty.intro (ι_mnf_eq k (ι (k + 1) x))
