import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02


-- This definition of group is from
-- https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html#algebraic-structures
structure Group₁ (α : Type u) where
  mul : α → α → α
  e : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_identity : ∀ x : α, mul x e = x
  identity_mul : ∀ x : α, mul e x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = e

namespace V₄  -- Klein Four Group

-- The carrier set, as described in
-- https://leanprover-community.github.io/mathematics_in_lean/C06_Structures.html#algebraic-structures
inductive Set where
  | e
  | τ₁
  | τ₂
  | τ₃
deriving Repr

open Set

def mul x y := match x, y with
    | e, e => e
    | τ₁, τ₁ => e
    | τ₂, τ₂ => e
    | τ₃, τ₃ => e
    | e, τ₁ => τ₁
    | τ₁, e => τ₁
    | e, τ₂ => τ₂
    | τ₂, e => τ₂
    | e, τ₃ => τ₃
    | τ₃, e => τ₃
    | τ₁, τ₂ => τ₃
    | τ₁, τ₃ => τ₂
    | τ₂, τ₁ => τ₃
    | τ₂, τ₃ => τ₁
    | τ₃, τ₁ => τ₂
    | τ₃, τ₂ => τ₁

def mul_assoc : ∀ x y z : Set, mul (mul x y) z = mul x (mul y z) := by
  intros x y z
  cases x <;> cases y <;> cases z
  repeat simp [mul]

def mul_identity : ∀ x : Set, mul x e = x := by
  intro x
  cases x
  repeat simp [mul]

def identity_mul : ∀ x : Set, mul e x = x := by
  intro x
  cases x
  repeat simp [mul]

def inv_mul_cancel : ∀ x : Set, mul x x = e := by
  intro x
  cases x
  repeat simp [mul]
-- deriving Fintype, Repr

-- KleinFour Group
instance G : Group₁ (Set)  where
  mul x y := mul x y
  e := e
  inv x := x
  mul_assoc := mul_assoc
  mul_identity := mul_identity
  identity_mul := identity_mul
  inv_mul_cancel := inv_mul_cancel
end V₄


-- The rest of the code uses the Klein Four Group.
#check V₄.G
#check V₄.Set
#check V₄.mul V₄.Set.τ₁ V₄.Set.τ₂

open V₄.Set  -- τ₁ τ₂ τ₃ e
def klein_mul_list : List V₄.Set → V₄.Set
  | [] => V₄.Set.e
  | [x] => x
  | x :: xs => V₄.mul x (klein_mul_list xs)

#eval klein_mul_list [τ₁, τ₂, τ₁, e, τ₃] -- τ₁













structure Group₁Cat where
  α : Type*
  str : Group₁ α

section


variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check f.toFun
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check Equiv.refl
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)

section -- Trying to find an equivalence between ℕ and ℚ.
-- I think the right approach is to use Cantor's pairing function to find
-- a bijection between ℚ and ℤ, and then use another bijection between
-- ℤ and ℕ.
#check Equiv ℕ ℕ
def aaa : Equiv ℕ ℕ := Equiv.refl ℕ
def ratToNat (q : ℚ) : ℕ :=
  let num := q.num.natAbs
  let den := q.den
  let sign := if q.num ≥ 0 then 0 else 1
  2^num * 3^den * 5^sign

def natToRat (n : ℕ) : ℚ :=
  let num : ℚ := n.factorization 2
  let den : ℚ := n.factorization 3
  let sign : ℚ:= n.factorization 5
  let numerator := if sign = 0 then num else -num
  numerator / den

def ratToTupleEncoding (q : ℚ) : ℕ × ℕ × ℕ :=
  let num := q.num.natAbs
  let den := q.den
  let sign := if q.num ≥ 0 then 0 else 1
  (num, den, sign)

def tupleToRat (t : ℕ × ℕ × ℕ) : ℚ :=
  let (num, den, sign) := t
  let numerator : ℤ := if sign = 0 then num else -num
  numerator / den

def tupleToNat (t : ℕ × ℕ × ℕ) : ℕ :=
  let (num, den, sign) := t
  2^num * 3^den * 5^sign

def natToTuple (n : ℕ) : ℕ × ℕ × ℕ :=
  let num : ℕ := n.factorization 2
  let den : ℕ := n.factorization 3
  let sign : ℕ := n.factorization 5
  (num, den, sign)

#eval ratToTupleEncoding (1 / 2)
#eval tupleToNat (ratToTupleEncoding (1/2)) -- 18
#eval natToTuple 18 -- (1, 1, 0)
#eval natToTuple 1 -- (0, 0, 0)
def nat_range : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
#eval nat_range.map λn↦ ((n), (natToTuple n)) -- (0, 0, 0)


-- Equivalence between ℕ and ℤ should be easier.
def f₁ (z : ℤ) : ℕ :=
  if z ≥ 0
    then 2 * z.natAbs
    else 2 * z.natAbs - 1

def g₁ (n : ℕ) : ℤ :=
  -- If n is even, the returned int is non-negative. 2k   ↦  k
  -- If n is odd, the returned int is negative.      2k+1 ↦ -k
  match h : n % 2 with
  | 0 =>   n / 2
  | 1 => - n / 2
  | _ => 9999

#eval g₁ 0


def nat_range₂ : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def int_range : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5]
#eval nat_range₂ |>.map g₁
#eval nat_range₂ |>.map g₁ |>.map f₁
#eval int_range |>.map  f₁ |>.map g₁

#check Equiv ℤ ℕ
variable (f₂ : ℤ ≃ ℕ)
#check f₂.toFun

theorem mod_two_mul_minus_one (n : ℕ) (h: n ≠ 0) : (2 * n - 1) % 2 = 1 := by
  -- 3 cases: n = 0, Even n, Odd n
  let k : ℕ  := 2 * n
  have hk : 2 * n = k := by rfl
  let l : ℕ := k - 1
  have hl : k - 1 = l := by rfl
  have pos_n : n > 0 := by apply Nat.pos_of_ne_zero h
  have n_ge1 : n ≥ 1 := by apply Nat.pos_of_ne_zero h
  have even_2n : Even (2 * n) := by use n; ring
  have odd_2n1 : Odd (2 * n - 1) := by
    use n - 1
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.mul_one]
    rw [hk]
    rw [hk] at even_2n
    have h1 : k ≥ 2 := by
      rw [←hk]
      linarith
    have h2 : k - 2 ≥ 0 := by linarith
    have h3 : k - 1 = k - 2 + 1 := by
      calc k - 1 =
          (k - 1) + (1 - 1) := by ring
          _ = (k - 2) + 1 := by
            have h_sub : k - 1 = (k - 2) + 1 := by
              omega
            exact h_sub
    exact h3
  rw [hk, hl]
  rw [hk, hl] at odd_2n1

  obtain ⟨a, ha⟩ := odd_2n1
  rw [ha]
  omega


instance : Equiv ℤ ℕ where
  toFun := f₁
  invFun := g₁
  left_inv := by
    intro z
    dsimp [f₁]
    rcases le_or_gt 0 z with h | h
    . rw [if_pos h]
      dsimp [g₁]
      -- rw [Int.natAbs_of_nonneg h]
      have h_mod : 2 * z.natAbs % 2 = 0 := by
        apply Nat.mul_mod_right
      rw [h_mod]
      simp
      exact h
    . rw [if_neg (not_le_of_gt h)]
      dsimp [g₁]
      have h_mod : (2 * z.natAbs - 1) % 2 = 1 := by
        apply mod_two_mul_minus_one
        omega
      rw [h_mod]
      simp
      omega
  right_inv := by
    intro n
    dsimp [g₁]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    . rw [h]
      simp
      dsimp [f₁]
      simp
      have h1 : 0 ≤ ↑n / 2 := by
        omega
      rw [if_pos]
      omega
      have h2 : 0 ≤ (n:ℤ) / 2 := by
        omega
      exact h2
    . rw [h]
      dsimp [f₁]
      rw [if_neg]
      have h1 : (-(n:ℤ) / 2).natAbs = (n + 1) / 2 := by
        omega
      rw [h1]
      omega
      have h2 : -((n:ℤ) / 2) ≤ 0 := by omega
      have h3 : n ≠ 0 := by omega
      omega

#check Group
variable (myα: Equiv ℤ ℕ)

#check myα (-5:ℤ)
#check myα.invFun (5:ℕ)

end


example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl

end

example (α : Type*) : Equiv.Perm α = (α ≃ α) := by
  dsimp [· ≃ ·]


def permGroup {α : Type _} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  e := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  identity_mul := Equiv.trans_refl
  mul_identity := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

structure AddGroup₁ (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  zero_add : ∀ x : α, add zero x = x
  add_zero : ∀ x : α, add x zero = x
  add_neg_cancel : ∀ x : α, add (neg x) x = zero


@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point where
  add := add
  zero := zero
  neg := neg
  add_assoc := by
    intros
    ext <;> simp [add, add_assoc]
  zero_add := by
    intro p
    ext <;> simp [add, zero_add]
    repeat rfl
  add_zero := by
    intro p
    ext <;> simp [add, add_zero]
    repeat rfl
  add_neg_cancel := by
    intro p
    ext <;> simp [add, neg, add_neg_cancel]
    repeat rfl
end Point

section
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- group power, defined for any group
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g

end

/-
`structure` creates a new type which holds an ordered, named collection of fields.
`def` creates a particular instance of a structure.
`class` creates a structure that enables class inference
`instance` registers a particular instance.

  `def` is to `structure` as `instance` is to `class`.

-/

class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section


variable {β : Type _} (f g : Equiv.Perm β)
-- variable (f g : Equiv.Perm MyKlein)
#check f


example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end

instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl

instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

def zero_p := (default : Point) + (default : Point)

end

instance hasMulGroup₂ {α : Type _} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type _} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type _} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end

class AddGroup₂ (α : Type*) where
  add : α → α → α
  -- fill in the rest
