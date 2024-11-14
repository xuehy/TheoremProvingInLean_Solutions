
section exercise0
namespace Hidden
inductive Bool where
  | false : Bool
  | true  : Bool



def Bool.and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false

def Bool.or (a b : Bool) : Bool := 
  match a with 
  | true => true 
  | false => b 

def Bool.not (a : Bool) : Bool :=   
  match a with 
  | true => false
  | false => true

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b
end Hidden
end exercise0

section exercise1
namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

def prod (m n : Nat) : Nat := by
  cases m 
  case zero => exact Nat.zero 
  case succ m1 => exact add n (prod m1 n)

def pred (m : Nat) : Nat := by 
  cases m 
  case zero => exact Nat.zero 
  case succ m1 => exact m1

def trun_minus (m n : Nat) : Nat := by 
  cases n
  case zero => exact m
  case succ n1 => exact (trun_minus (pred m) n1)


def pow (m n : Nat) : Nat := by 
  cases n 
  . cases m
    case zero => exact Nat.zero
    case succ m1 => exact (Nat.succ Nat.zero)
  case succ n1 => exact prod m (pow m n1)
  
theorem add_zero (m : Nat) : add m Nat.zero = m := rfl
theorem add_succ (m n : Nat) : add m (Nat.succ n) = Nat.succ (add m n) := rfl

theorem zero_add (n : Nat) : add Nat.zero n = n := by
  induction n; rfl; rw [add_succ]; rename_i a; rw [a]

theorem succ_add (m n : Nat) : add (Nat.succ m) n = Nat.succ (add m n) := by
  induction n; rfl; rw [add_succ]; rename_i a; rw [a]; rw [add_succ]

theorem add_comm (m n : Nat) : add m n = add n m := by
  induction n; rw [zero_add, add_zero]; rename_i a; rw [succ_add, add_succ, a]

theorem add_assoc (m n k : Nat) : add (add m  n) k = add m (add n k) := by
  induction k; rw [add_zero, add_zero]; rename_i a; rename_i k; 
  rw [add_succ, add_succ, a]
  rw [add_comm]
  have : add (Nat.succ (add n k)) m = Nat.succ (add (add n k) m) := by rw [succ_add]
  rw [←this]
  apply add_comm 

theorem zero_prod (m: Nat) : prod Nat.zero m = Nat.zero := by 
  rfl

theorem one_prod (m: Nat) : prod (Nat.succ Nat.zero) m = m := by 
  -- what can be proved by directly computation following definition can be proved using rfl tactic
  rfl 

theorem succ_prod (m n: Nat) : prod (Nat.succ m) n = add n (prod m n) := by rfl

theorem prod_zero (m: Nat) : prod m Nat.zero = Nat.zero := by 
  induction m 
  case zero => rw [zero_prod]  
  case succ m1 => rw [succ_prod, m1, add_zero]
 
theorem prod_one (m:Nat) : prod m (Nat.succ Nat.zero) = m := by 
  induction m 
  case zero => rw [zero_prod]
  case succ m1 => rw [succ_prod, m1, succ_add, zero_add] 

theorem prod_succ (m n : Nat) : prod m (Nat.succ n) = add m (prod m n) := by 
  induction m 
  case zero => rw [zero_prod, zero_add, zero_prod]
  case succ m1 ih => 
    rw [succ_prod, succ_add, ih, succ_add, succ_prod, add_comm, add_assoc]
    have : add (prod m1 n) n = add n (prod m1 n) := by rw [add_comm]
    rw [this]


theorem prod_comm (m n : Nat) : prod m n = prod n m := by 
  induction m 
  case zero => rw [zero_prod, prod_zero]
  case succ m1 ih => rw [succ_prod, prod_succ, ih]
    
theorem add_comm1 (a b c d: Nat) : add (add a c) (add b d) = add a (add b (add c d)) := by 
  rw [add_assoc]
  have : add c (add b d) = add b (add c d) := by rw [add_comm, add_assoc, add_comm d]
  rw [this]
    
theorem prod_add (a b c : Nat) : prod a (add b c) = add (prod a b) (prod a c) := by 
  induction a 
  case zero => rw [zero_prod, zero_prod, zero_prod, zero_add]
  case succ pa ih => rw [succ_prod, ih, succ_prod, succ_prod, add_assoc, add_comm1 b] 

theorem add_prod (a b c: Nat) : prod (add a b) c = add (prod a c) (prod b c) := by 
  induction c 
  case zero => rw [prod_zero, prod_zero a, prod_zero b, add_zero]
  case succ pc ih => rw [prod_succ, ih, prod_succ, prod_succ, add_assoc, add_comm b, add_assoc, add_comm b, add_assoc a]

theorem prod_assoc (a b c: Nat) : prod a (prod b c) = prod (prod a b) c := by 
  induction c 
  case zero => rw [prod_comm, prod_zero, zero_prod, prod_comm, zero_prod] 
  case succ c1 ih => rw [prod_succ, prod_succ, <-ih, prod_add]


theorem pow_zero (a : Nat) : a ≠ Nat.zero → pow a Nat.zero = Nat.succ Nat.zero := by 
  intro h 
  induction a 
  case zero => contradiction
  case succ pa _ => rfl

theorem zero_pow (a : Nat) : pow Nat.zero a = Nat.zero := by 
  induction a 
  case zero => rfl 
  case succ pa _ => rfl

theorem pow_succ (a b: Nat) : pow a (Nat.succ b) = prod a (pow a b) := by 
  induction b 
  case zero => rfl 
  case succ pb ih => rw [ih]; rfl

theorem pow_add (a b c : Nat) : a ≠ Nat.zero → pow a (add b c) = prod (pow a b) (pow a c) := by 
  intro h
  induction b 
  case zero => rw [zero_add, pow_zero, succ_prod, zero_prod, add_zero]; exact h 
  case succ pb ih => rw [pow_succ, succ_add, pow_succ, ih, prod_assoc]
    
end Hidden
open Nat

  
end exercise1

section exercise2
variable (α : Type)


theorem len_nil_0 : @List.length α [] = 0 := by 
  apply List.length_nil
  
theorem nil_append : [] ++ x = x := rfl 

theorem add_length (s t : List α) : List.length (s ++ t) = List.length s + List.length t := by 
  induction s 
  case nil => rw [len_nil_0, nil_append, Nat.zero_add]
  case _ => 
       rename_i head tail ih; rw [List.cons_append, List.length_cons, List.length_cons, ih, Nat.add_assoc, Nat.add_assoc];
       have : 1 + List.length t = List.length t + 1 := by rw [Nat.add_comm]
       rw [this] 

theorem length_1 : List.length [head] = 1 := by rfl
theorem add_length_1 : List.length (tail ++ [head]) = List.length tail + List.length [head] := by simp 

example : List.length (List.reverse t) = List.length t := by
  induction t 
  case nil => rw [List.reverse_nil]
  case _ => 
       rename_i head tail ih; rw [List.reverse_cons, List.length_cons]; 
       have : List.length (List.reverse tail ++ [head]) = List.length (List.reverse tail) + 1 := by 
           rw [add_length_1, length_1]
       rw [this, ih]

example : List.reverse (List.reverse t) = t := by 
  induction t 
  case nil => rfl 
  case _ => 
    rename_i head tail ih
    rw [List.reverse_cons, List.reverse_append]
    have : List.reverse [head] = [head] := by rfl 
    rw [this, ih]
    rfl 
end exercise2

section exercise3 
inductive Data1 where 
  | const : Nat → Data1 
  | var : Data1 → Data1
  | plus : Data1 → Data1 → Data1
  | times : Data1 → Data1 → Data1
  deriving Repr


def comp (d : Data1) : Nat := by
  cases d 
  case const n => exact n
  case var d1 => exact (comp d1)
  case plus m n => exact (comp m + comp n)
  case times m n => exact ((comp m) * (comp n))

def compute (d : Data1) : Data1 := Data1.const (comp d)

end exercise3 
