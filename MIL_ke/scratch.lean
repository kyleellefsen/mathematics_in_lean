import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factors
-- Mathlib.Data.Nat.Prime.Defs




def double₁: ℕ → ℕ :=
  λ(a:ℕ) ↦ 2 * a

def double₂(n:ℕ) : ℕ := 4 * n + 2


def pow(n:ℕ) : ℕ :=
  match n with
  | 0 => 1
  | (m + 1) => 2 * pow m

#check double₁
#check double₂
#check pow

#eval pow 4


def sum2 (n:ℕ) :=
  match n with
  | 0 => 1
  | m+1 => 2^n + sum2 m

def sum2' (n:ℕ) :=
  2^(n+1) - 1

example : sum2 = sum2' := by
  funext n
  induction n with
  | zero => rfl
  | succ m ih =>
    simp [sum2, sum2', ih]
    ring_nf
    omega





#eval sum2 0
#eval sum2 1
#eval sum2 4
#eval sum2' 4


-- theorem my_theorem (x : ℝ) (hx : x > -1) (n : ℕ): (1+x)^n > n * x := by induction n with
--   | zero => simp
--   | succ n ih =>
--     have h1 : 1 + x > 0 := by linarith
--     have h_pos : 0 < 1 + x := by linarith
--     have new_inequality := (mul_lt_mul_right h1).mpr ih
--     have new_inequality_flipped := gt_iff_lt.mpr new_inequality
--     have h2 : n * x ^ 2 ≥ x := by linarith
--     have h3 := calc
--       (1 + x)^(n + 1) = (1 + x)^n * (1 + x) := by ring
--       _ > (n * x) * (1 + x) := new_inequality_flipped
--       _ = n * x * (1 + x) := by ring
--       _ = n * x + n * x ^ 2 := by ring
--       _ ≥ n * x + x := by linarith
--       _ = (n + 1) * x := by linarith



-- n is a product of primes if all its factors are prime
def isProductOfPrimes (n : Nat) : Prop :=
  n > 1 ∧ ∀ p ∈ n.primeFactorsList, Nat.Prime p

theorem four_is_product_of_primes : isProductOfPrimes 4 := by
  unfold isProductOfPrimes
  constructor
  . norm_num
  . intros p hp
    have h : Nat.primeFactorsList 4 = [2, 2] := by rfl
    rw [h] at hp
    simp at hp
    rw [hp]
    exact Nat.prime_two



structure QuadraticFive where
  -- (a + b√5) / c
  a : ℤ
  b : ℤ
  c : ℕ
  deriving Repr

def QuadraticFive.add (x y : QuadraticFive) : QuadraticFive :=
  ⟨x.a + y.a, x.b + y.b, x.c⟩

instance : Add QuadraticFive where
  add := QuadraticFive.add

def QuadraticFive.sub (x y : QuadraticFive) : QuadraticFive :=
  ⟨x.a - y.a, x.b - y.b, x.c⟩

instance : Sub QuadraticFive where
  sub := QuadraticFive.sub

def QuadraticFive.mul (x y : QuadraticFive) : QuadraticFive :=
  let a := x.a
  let b := x.b
  let c := y.a
  let d := y.b
  let e := x.c * y.c
  ⟨a * c + 5 * b * d, a * d + b * c, e⟩

instance : Mul QuadraticFive where
  mul := QuadraticFive.mul

#eval QuadraticFive.mul ⟨1, 1, 2⟩ ⟨1, 1, 2⟩

def QuadraticFive.pow (x : QuadraticFive) (n : Nat) : QuadraticFive :=
  match n with
  | 0 => ⟨1, 0, 1⟩  -- represents 1
  | n+1 => x * (QuadraticFive.pow x n)

instance : Pow QuadraticFive Nat where
  pow := QuadraticFive.pow

def fibClosed (n : ℕ) : ℕ :=
  let phi : QuadraticFive := ⟨1, 1, 2⟩   -- represents (1 + √5) / 2
  let psi : QuadraticFive := ⟨1, -1, 2⟩  -- represents (1 - √5) / 2
  let num := (phi^n) - (psi^n)
  num.b.toNat / num.c


#eval fibClosed 1 --1
#eval fibClosed 2 -- 1
#eval fibClosed 3 -- 2
#eval fibClosed 9000 -- 346160291286684746313289272940653195821004938840574649197792354882626761451249209476688158830845438584081783077248969641036805567685925275096026379667053520731117017902152350004056055263290740468312565519013758527115134986679500927618960595898784125436743322890902556558480966166842068858827121368084037500398689666218044551350360442646862696279483129043660912539980584260616428129687853518243358544506024804211410314325692133398509706576596745187284000675448960566587838629300214068490071678112576561242120168921521062906855593650494011391615760506296564726181583639595605639315514462323593255726350681177298919692687529131475966996479175735276726414564038873951028105275764984412066591637415934772279139455253087288034009154993561193308269619883651016764739580528775882659332284075160900251889565909001620005955898020498741253426259183467407856451935255744598735677063143605951074135853992415938277666700535092854704966755528337679057697026202081967337389133151551900992563506110333584028337592625787023110008351289364452178195306107056259768301902940710358705695173401175797592063874235214258319794748258830812224447883759078743189231351248058057742818858083652751310389157188583652487191753681908871324452598859106144951594606797195786754559141129782727790928218793262000601818878041232712620482141748965030717911922256234544033929372196985105014830841771293541916105669494308393067698504542986022441130160781328108216014215621166500631310190198456977407701085658980743316402172456165191576635035885104241740897029972735571913355609051794588175072614073380279274977928339443177725603335698391914343325635814053921690136602830888930385122496970174170881935462763316271613842866892088329627160809282789447665993788904319486227140536689107577971883772835153070545678359828373104418268785375257487856252266909918112168299229852218195022374231040315139836301079422737682650129388000

def fib: ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

#eval fib 1 = fibClosed 1
#eval fib 2 = fibClosed 2
#eval fib 3 = fibClosed 3
#eval fib 4 = fibClosed 4
-- #eval fib 30

-- #eval fibClosed 1
-- #eval fibClosed 2
-- #eval fibClosed 2


-- #eval fibClosed 7
-- #eval fib 30
