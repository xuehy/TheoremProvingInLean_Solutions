-- chapter 4: Quantifiers and Equality

section exercise1
variable (α: Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x ) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
Iff.intro 
  (λ h: ∀ x, p x ∧ q x => ⟨λ x => (h x).left, λ x => (h x).right⟩)
  (λ h: (∀ x, p x) ∧ (∀ x, q x) => λ x => ⟨h.left x, h.right x⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h: ∀ x, p x → q x => λ h1: ∀ x, p x => λ x => h x (h1 x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h: (∀ x, p x) ∨ (∀ x, q x) => λ x => Or.elim h (λ hl: (∀ x, p x) => Or.inl (hl x)) (λ hr: (∀ x, q x) => Or.inr (hr x))


end exercise1

section exercise2
variable (α: Type) (p q: α → Prop)
variable (r:Prop) 

example : α → ((∀ x:α , r) ↔ r) := λ a:α => Iff.intro 
  (λ h:∀ x:α, r => h a)
  (λ hr: r => λ x:α => hr)

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro 
    (λ h: ∀ x, p x ∨ r => byCases 
      (λ hr: r => Or.inr hr)
      (λ hnr: ¬ r => Or.inl (λ x => byContradiction 
        (λ hnpx: ¬ p x => 
          have hpxr: ¬ (p x ∨ r) := λ hh: p x ∨ r => Or.elim hh hnpx hnr
          have : p x ∨ r := h x
          show False from absurd ‹p x ∨ r› ‹¬ (p x ∨ r)›
        )
      ))
    )
    (
      λ h: (∀ x, p x) ∨ r => Or.elim h 
        (λ hl: ∀ x, p x => λ x => Or.inl (hl x))
        (λ hr: r => λ x => Or.inr hr)
    )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro 
    (λ h: ∀ x, r → p x => λ hr : r => 
      byCases 
      (λ htr: r => λ x => h x htr)
      (λ hnr: ¬ r => show ∀ x, p x from absurd hr hnr)
    )
    (
      λ h: r → ∀ x, p x => λ x => 
        byCases
          (λ hr: r => λ _:r => show p x from h hr x)
          (λ hnr: ¬ r => λ hr:r => show p x from absurd hr hnr)
    )
end exercise2

section exercise3
open Classical
variable (men: Type) (barber: men)
variable (shaves: men → men → Prop)

example (h: ∀ x: men, shaves barber x ↔ ¬ shaves x x) : false :=
  have ha: shaves barber barber ↔ ¬ shaves barber barber := h barber
  have cons := byCases     
      (λ h1: shaves barber barber => show False from ha.mp h1 h1)
      (λ h2: ¬ shaves barber barber => show False from absurd (ha.mpr h2) h2)
  show false from cons.elim
end exercise3

section exercise4
def even (n : Nat) : Prop := ∃ b, n = 2 * b

def prime (n : Nat) : Prop := n = 2 ∨ ∀ x : Nat, x ≥ 2 ∧ x < n → n % x != 0

def infinitely_many_primes : Prop := ∀ x, prime x → ∃ y, y > x ∧ prime y

def Fermat_prime (n : Nat) : Prop := prime (2 ^ (2 ^ n) + 1)

def infinitely_many_Fermat_primes : Prop := ∀ m:Nat, ∃ n > m, Fermat_prime n

def goldbach_conjecture : Prop := ∀ x:Nat, (x > 5 ∧ ¬ even x) → ∃ a b c:Nat, prime a ∧ prime b ∧ prime c ∧ x = a + b + c 

def Goldbach's_weak_conjecture : Prop := ∀ x, x > 7 ∧ ¬ even x → ∃ a b c, prime a ∧ prime b ∧ prime c ∧ ¬ even a ∧ ¬ even b ∧ ¬ even c ∧ x = a + b + c

def Fermat's_last_theorem : Prop := ∀ n, n > 2 → ¬ ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^n + y^n = z^n

end exercise4


section exercise5
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := λ ⟨_, hw⟩ => hw
example (a : α) : r → (∃ x : α, r) := λ hr:r => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro 
    (λ h: ∃ x, p x ∧ r => match h with
    | ⟨x1, hx1⟩ => ⟨⟨x1, hx1.left⟩, hx1.right⟩
    )
    (λ h: (∃ x, p x) ∧ r => match h.left with 
    | ⟨x1, hx1⟩ => ⟨x1, ⟨hx1, h.right⟩⟩
    )

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro 
    (λ h: ∃ x, p x ∨ q x => match h with 
    | ⟨x1, hx1⟩ => Or.elim hx1 
      (λ hpx1: p x1 => Or.inl ⟨x1, hpx1⟩)
      (λ hqx1: q x1 => Or.inr ⟨x1, hqx1⟩)
    )
    (λ h: (∃ x, p x) ∨ (∃ x, q x) => Or.elim h 
      (λ hx: ∃ x, p x => match hx with 
      | ⟨x1, hx1⟩ => ⟨x1, Or.inl hx1⟩ )
      (λ hx: ∃ x, q x => match hx with 
      | ⟨x2, hx2⟩ => ⟨x2, Or.inr hx2⟩)
    )

open Classical
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro 
    (λ h: ∀ x, p x =>
      (λ hx: ∃ x, ¬ p x => match hx with
      | ⟨x1, hx1⟩ => absurd (h x1) (hx1))
    )
    (λ h: ¬ (∃ x, ¬ p x) => λ x:α =>
      byContradiction (λ hnpx:¬ p x =>
        have h1: ∃ x, ¬ p x := ⟨x, hnpx⟩
        absurd h1 h)
    )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro 
    (λ h: ∃ x, p x => match h with 
    | ⟨x1, hx1⟩ => λ h1: ∀ x, ¬ p x => absurd hx1 (h1 x1))
    (λ h: ¬ (∀ x, ¬ p x) => byContradiction
      (λ hnx: ¬ ∃ x, p x => 
        have h2: ∀ x, ¬ p x := λ x:α => (λ h3: p x => absurd ⟨x, h3⟩ hnx)
        absurd h2 h
      )
    )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro 
    (λ h:¬ ∃ x, p x => λ x:α => 
         (λ hpx: p x => show False from absurd ⟨x, hpx⟩ h)
    )
    (λ h:∀ x, ¬ p x => 
      (λ hex: ∃ x, p x => match hex with
      | ⟨x1, hex1⟩ => show False from absurd hex1 (h x1)
      )
    )

theorem lemmaA : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ h:¬ ∀ x, p x => byContradiction
      (λ h1: ¬ ∃ x, ¬ p x => 
        have h2: ∀ x, p x := λ x:α => byContradiction
          (λ hx: ¬ p x => absurd (⟨x, hx⟩) h1)
        absurd h2 h
      )
    )
    (λ h:∃ x, ¬ p x => match h with 
    | ⟨x1, hx1⟩ =>
      (λ h1: ∀ x, p x => absurd (h1 x1) hx1)
    )

example : (∀ x , p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
    (λ h:∀ x, p x → r => λ h1: ∃ x, p x => match h1 with 
    | ⟨x1, hx1⟩ => h x1 hx1
    )
    (λ h:(∃ x, p x) → r => λ x => λ h1 : p x => 
      h ⟨x, h1⟩
    )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ h: ∃ x, p x → r => λ h1: ∀ x, p x => match h with
    | ⟨x1, hx1⟩ => hx1 (h1 x1)
    )
    (λ h: (∀ x, p x) → r => show ∃ x, p x → r from 
      byCases
        (λ hx: ∀ x, p x => 
          have hpar: p a → r := λ _: p a => h hx
          ⟨a, hpar⟩
        )
        (λ hnx:¬ ∀ x, p x =>
          byContradiction
            (λ hnex: ¬ ∃ x, p x → r =>
              have h1: ∀ x, p x :=
                λ x => byContradiction
                  (λ hnp: ¬ p x => 
                    have : ∃ x, p x → r := ⟨x, λ hp => absurd hp hnp⟩
                    show False from absurd ‹∃ x, p x → r› hnex 
                  )
              show False from absurd h1 hnx
            )
        )
    )

example (a:α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro 
    (λ h: ∃ x, r → p x => λ hr: r => match h with 
    | ⟨x1, hx1⟩ => ⟨x1, hx1 hr⟩)
    (λ h: r → ∃ x, p x => byCases 
      (λ hr: r => match (h hr) with 
      | ⟨x1, hx1⟩ => show ∃ x, r → p x from ⟨x1, λ _:r => hx1⟩
      )
      (λ hnr: ¬ r =>
       -- tricky, must remember tightly how to prove from ¬r that r → anything
        have : r → p a := λ hr:r => show p a from absurd hr hnr 
        ⟨a, ‹r → p a›⟩
      )
    )
    
    
end exercise5
