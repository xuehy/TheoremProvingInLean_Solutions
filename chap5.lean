-- Chapter 5: Tactics


section exercise1
variable (p q r: Prop)
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;> repeat intro h ; apply And.intro ; apply h.right ; apply h.left
  
example: p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  repeat {
    intro h
    cases h 
    apply Or.inr; assumption; 
    apply Or.inl; assumption;
  }
   
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro <;> intro h <;> constructor
  apply h.left.left; constructor; apply h.left.right; apply h.right
  constructor; apply h.left; apply h.right.left; exact h.right.right
  
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro <;> intro h
  cases h with 
  | inl hl => cases hl with 
              | inl hhl => apply Or.inl; assumption
              | inr hhr => apply Or.inr; apply Or.inl; assumption
  | inr hr => apply Or.inr; apply Or.inr; assumption
  
  cases h with
  | inl hl => apply Or.inl; apply Or.inl; assumption
  | inr hr => cases hr with 
              | inl hhl => apply Or.inl; apply Or.inr; assumption
              | inr hhr => apply Or.inr; exact hhr

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro <;> intro h

  have hqr : q ∨ r := h.right 
  have hp : p := h.left 
  cases hqr 
  . apply Or.inl; constructor; exact hp; assumption
  . apply Or.inr; constructor; exact hp; assumption
  
  cases h with
  | inl hl =>  constructor; exact hl.left; apply Or.inl; exact hl.right
  | inr hr =>  constructor; exact hr.left; apply Or.inr; exact hr.right



example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  intro h
  constructor
  cases h with 
   | inl hl => constructor; assumption
   | inr hr => apply Or.inr; apply hr.left

  cases h with 
   | inl hl => apply Or.inl; assumption 
   | inr hr => apply Or.inr; exact hr.right
  
  intro h
  have hl : p ∨ q := h.left 
  have hr : p ∨ r := h.right 
    
  cases hl 
  . apply Or.inl; assumption 
  . cases hr 
    . apply Or.inl; assumption 
    . apply Or.inr; constructor; assumption; assumption

example : (p → ( q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro <;> intros h1 h2
  apply h1 
  apply h2.left 
  apply h2.right 
  intro h3 
  apply h1 
  constructor; assumption; assumption


example : ((p ∨ q) → r) ↔ (p → r ) ∧ (q → r) := by
  apply Iff.intro <;> intro h
 
  constructor
  intro hp; apply h; apply Or.inl; assumption
  intro hq; apply h; apply Or.inr; assumption
  
  intro hpq 
  cases hpq
  . apply h.left; assumption
  . apply h.right; assumption

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro <;> intro h
  constructor; 
  intro hp; apply h; apply Or.inl; assumption
  intro hq; apply h; apply Or.inr; assumption
  intro hpq 
  cases hpq 
  . apply h.left; assumption
  . apply h.right; assumption
    
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intros h1 h2
  cases h1 with 
  | inl hl => apply hl; exact h2.left 
  | inr hr => apply hr; exact h2.right 

example : ¬(p ∧ ¬p) := by
  intro h
  apply h.right; apply h.left 

example : p ∧ ¬q → ¬(p → q) := by 
  intros h h1 
  apply h.right
  apply h1; exact h.left
  

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  intro h 
  constructor 
  intro hp; apply h; apply Or.inl; exact hp
  intro hq; apply h; apply Or.inr; exact hq
  
  intro h; intro h1
  cases h1 with 
  | inl hl => apply h.left; assumption
  | inr hr => apply h.right; assumption

example : ¬p ∨ ¬q → ¬(p ∧ q) := by 
  intro h 
  intro h1 
  cases h with 
  | inl hp => apply hp; apply h1.left 
  | inr hq => apply hq; exact h1.right
example : ¬(p ∧ ¬p) := by 
  intro h 
  apply h.right 
  apply h.left 

example : p ∧ ¬q → ¬(p → q) := by
  intro h 
  intro h1 
  apply h.right 
  apply h1 
  apply h.left 

example : ¬p → (p → q) := by 
  intro hnp; intro hp; 
  have hf: False := by apply hnp; apply hp 
  apply False.elim; assumption

example : (¬p ∨ q) → (p → q) := by 
  intro h; intro h1; cases h with 
  | inl hl => apply False.elim; apply hl; assumption
  | inr hr => exact hr 
example : p ∨ False ↔ p := by 
  apply Iff.intro 
  intro h; cases h with 
  | inl hl => exact hl;
  | inr hr => apply False.elim; assumption 
  
  intro h; apply Or.inl; assumption 

example : p ∧ False ↔ False := by
  apply Iff.intro 
  intro h; exact h.right 
  intro h; constructor; apply False.elim; assumption; assumption
example : (p → q) → (¬q → ¬p) := by 
  intro h h1 h2 
  apply h1; apply h; assumption

open Classical

variable (p q r s : Prop)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by 
  intro hh 
  by_cases p 
  have hrs: r ∨ s := by apply hh; assumption
  cases hrs with
  | inl hl => apply Or.inl; intro ; exact hl
  | inr hr => apply Or.inr; intro ; exact hr 
  
  have hnn : p ∧ ¬p → False := by intro h2; apply h2.right; apply h2.left
  have hpr : p → r := by intro hp; apply False.elim; apply hnn; constructor; assumption; assumption
  apply Or.inl; assumption

example : ¬(p ∧ q) → ¬p ∨ ¬q := by 
  intro h; 
  by_cases p 
  show ¬p ∨ ¬ q;
  apply Or.inr
  show ¬q
  intro hq 
  apply h 
  show p ∧ q; 
    constructor; repeat assumption

  show ¬p ∨ ¬ q;
  apply Or.inl; show ¬p; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h 
  show p ∧ ¬q 
  by_cases p

  constructor; assumption; 
  intro hq; apply h; intro; assumption 

  constructor; apply False.elim; apply h; intro hp; apply False.elim; 
  have hnn : p ∧ ¬p → False := by intro h2; apply h2.right; apply h2.left
  apply hnn; constructor; repeat assumption

  intro hq; apply h; intro; exact hq

example : (p → q) → (¬p ∨ q) := by 
  intro h 
  by_cases p 

  apply Or.inr; show q; apply h; assumption 
  apply Or.inl; show ¬p; assumption

example : (¬q → ¬p) → (p → q) := by
  intro h
  intro hp 
  false_or_by_contra 
  have : ¬p := by apply h; assumption 
  apply this; exact hp 

example : p ∨ ¬p := by 
  by_cases p 
  apply Or.inl; assumption
  apply Or.inr; assumption 

example : (((p → q) → p) → p) := by 
  intro h 
  false_or_by_contra
  rename_i a 
  apply a; apply h; intro hp; apply False.elim; apply a; assumption;


example : ¬(p ↔ ¬p) := by 
  intro h
  have hl: ¬p → p := by apply h.mpr 
  have hr: p → ¬p := by apply h.mp 
  have hpf: p → False := by intro hp; apply hr; assumption; assumption
  have hp: p := by apply hl; assumption
  apply hpf; assumption
  
  
-- Quantifiers and Equality
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by 
  apply Iff.intro
  intro h
  constructor; intro x; 
  have pqx: p x ∧ q x := by apply h 
  apply pqx.left; intro x;  have pqx: p x ∧ q x := by apply h 
  apply pqx.right 

  intro h
  intro x 
  constructor; apply h.left; apply h.right

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by 
  intro h 
  intro h1 
  intro x 
  apply h; apply h1; 

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by 
  intro h x 
  cases h with 
  | inl hl => apply Or.inl; apply hl 
  | inr hr => apply Or.inr; apply hr 

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := by 
  intro ha 
  apply Iff.intro   
  intro; 
  have hr : r := by rename_i a; apply a; apply ha 
  apply hr 
  intro hr; intro ; exact hr 

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by 
  apply Iff.intro 
  intro h1 
  by_cases r 
  apply Or.inr; assumption
  apply Or.inl; intro hx; 
  have hpxr : p hx ∨ r := by apply h1 hx 
  cases hpxr with 
  | inl hl => assumption
  | inr hr => 
    rename_i h 
    have hf: False := by apply h; apply hr 
    apply False.elim; assumption

  intro h 
  intro x 
  cases h with 
  | inl hl => apply Or.inl; apply hl 
  | inr hr => apply Or.inr; assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by 
  apply Iff.intro 
  intro h 
  intro hr 
  intro hx 
  apply h; exact hr 
  intro h 
  intro hx 
  intro hr 
  apply h; exact hr

variable (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := by 
  apply False.elim 
  have hr : shaves barber barber → ¬ shaves barber barber := (h barber).mp
  have hl: ¬ shaves barber barber → shaves barber barber := (h barber).mpr 
  have hf : ¬ shaves barber barber := by intro h1; apply hr; apply h1; assumption
  apply hf; apply hl; assumption

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro h 
  cases h 
  assumption

example (a : α) : r → (∃ _ : α, r) := by 
  intro h  
  exists a 
  
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro 
  intro h 
  cases h
  rename_i w; rename_i h 
  constructor; exists h; apply w.left 
  exact w.right 
  intro h 
  have hr: r := h.right 
  have hl: ∃ x, p x := h.left 
  cases hl 
  rename_i w; rename_i h; exists h; 

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by 
  apply Iff.intro 
  intro h 
  cases h 
  rename_i w; rename_i h
  cases w with 
  | inl wl => apply Or.inl; exists h
  | inr wr => apply Or.inr; exists h 

  intro h
  cases h with 
  | inl hl => cases hl; rename_i h; rename_i w; exists w; apply Or.inl; assumption
  | inr hr => cases hr; rename_i h; rename_i w; exists w; apply Or.inr; assumption
      

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro 
  intro h1 
  intro h2
  cases h2; rename_i w; rename_i h; apply w; apply h1 
  
  intro h1 h2
  false_or_by_contra
  apply h1; exists h2 

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by 
  apply Iff.intro 
  intro h1 h2 
  cases h1 
  rename_i w h 
  have : ¬ p w := h2 w 
  apply this; exact h
  intro h1      
  false_or_by_contra
  rename_i a 
  apply h1 
  intro hx 
  false_or_by_contra
  have : ∃ x, p x := by exists hx 
  apply a; exact this 

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by 
  apply Iff.intro 
  
  {
    intro h 
    intro hx 
    intro hpx 
    apply h
    exists hx 
  }

  {
    intro h1 
    intro hex 
    cases hex 
    rename_i w h 
    apply (h1 w)
    exact h 
  }

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by 
  apply Iff.intro 
  {
    intro h 
    false_or_by_contra
    rename_i a 
    apply h
    intro hx 
    false_or_by_contra
    apply a 
    exists hx 
  }

  {
    intro h1    
    intro h2 
    cases h1 
    rename_i w h 
    apply h 
    apply h2 
  }

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by 
  apply Iff.intro 

  {
    intro h1 
    intro hex 
    cases hex 
    rename_i w h 
    apply (h1 w)
    exact h 
  }

  {
    intro h1
    intro hx 
    intro phx 
    apply h1 
    exists hx 
  }

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by 
  apply Iff.intro 
  
  show (∃ x, p x → r) → (∀ x, p x) → r
  {
    intro hex 
    intro hx 
    cases hex
    rename_i w h 
    apply h 
    apply hx
  }
  show ((∀ x, p x) → r) → (∃ x, p x → r)
  {
    intro h1 
    by_cases (∀ x, p x)
    {
      rename_i h 
      have hr : r := by apply h1; assumption
      exists a; intro; exact hr 
    }
    {    
      rename_i h
      false_or_by_contra;
      apply h; 
     
      false_or_by_contra;
      rename_i hnpx 
      rename_i hnex; 
     
      have hpxr : p x → r := by intro hpx; apply False.elim; apply hnpx; exact hpx 
      have hexprxx : ∃ x, p x → r := by exists x
      apply hnex; assumption;
      
    }
  }
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by 
  apply Iff.intro 
  intro h 
  intro hr 
  cases h; rename_i w h
  exists w; apply h; exact hr 

  intro h1 
  by_cases r 
  rename_i h 
  have : ∃ x, p x := by apply (h1 h)
  cases this 
  rename_i w 
  rename_i h 
  exists h; intro; assumption;
  exists a; intro hr; apply False.elim; rename_i h; apply h; apply hr; 

end exercise1



  

    
section exercise2
example (p q r:Prop) (hp: p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor; apply Or.inl; assumption; apply And.intro; apply Or.inr; apply Or.inl; assumption; apply Or.inr; apply Or.inr; assumption
end exercise2
