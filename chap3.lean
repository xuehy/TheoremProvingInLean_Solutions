-- Chapter 3: Propositions and Proofs
section exercise
variable (p q r: Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := Iff.intro
(fun hpq: p ∧ q => ⟨hpq.right, hpq.left⟩)
(fun hqp: q ∧ p => ⟨hqp.right, hqp.left⟩)

example : p ∨ q ↔ q ∨ p :=
Iff.intro 
(fun hpq: p ∨ q => Or.elim hpq Or.inr Or.inl)
(fun hqp: q ∨ p => Or.elim hqp Or.inr Or.inl)

-- associativity of ∧ and ∨
example: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
Iff.intro
(fun hpqr: (p ∧ q) ∧ r => ⟨hpqr.left.left, ⟨hpqr.left.right, hpqr.right⟩⟩)
(fun h2: p ∧ (q ∧ r) => ⟨⟨h2.left, h2.right.left⟩, h2.right.right⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
Iff.intro
(fun hpq_r: (p ∨ q) ∨ r => Or.elim hpq_r 
  (fun hpq: p ∨ q => Or.elim hpq 
    Or.inl 
    (fun hq:q => show p ∨ (q ∨ r) from Or.inr (Or.inl hq))) 
  (fun hr:r => show p ∨ (q ∨ r) from Or.inr (Or.inr hr)))


(fun hp_qr: p ∨ (q ∨ r) => Or.elim hp_qr 
  (fun hp: p => Or.inl (Or.inl hp))
  (fun hqr: q ∨ r => Or.elim hqr 
    (fun hq:q => Or.inl (Or.inr hq))
    (fun hr:r => Or.inr hr)
  )
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
Iff.intro 
  (fun hp_qr: p ∧ (q ∨ r) => 
    have hqr: q ∨ r := hp_qr.right
    have hp: p := hp_qr.left 
    Or.elim hqr (fun hq: q => Or.inl ⟨hp, hq⟩) (fun hr: r => Or.inr ⟨hp, hr⟩))
  (fun hpq_pr: (p ∧ q) ∨ (p ∧ r) =>
    Or.elim hpq_pr 
      (fun hpq: p ∧ q => 
        have hp: p := hpq.left
        have hq: q := hpq.right
        ⟨hp, Or.inl hq⟩)
      (fun hpr: p ∧ r =>
        have hp: p := hpr.left
        have hr: r := hpr.right
        ⟨hp, Or.inr hr⟩) )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
Iff.intro
  (fun hp_qr: p ∨ (q ∧ r) => Or.elim hp_qr 
    (fun hp: p => ⟨Or.inl hp, Or.inl hp⟩)
    (fun hqr: q ∧ r => 
      have hq: q := hqr.left
      have hr: r := hqr.right
      ⟨Or.inr hq, Or.inr hr⟩))
  (fun hpq_pr: (p ∨ q) ∧ (p ∨ r) => 
    have hpq: p ∨ q := hpq_pr.left 
    have hpr: p ∨ r := hpq_pr.right
 
    Or.elim hpq Or.inl (fun hq: q => Or.elim hpr 
      (λ hp: p => Or.inl hp)
      (λ hr: r => Or.inr ⟨hq, hr⟩)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
Iff.intro 
  (λ hpqr: p → (q → r) => λ hpq: p ∧ q => 
    have hp: p := hpq.left 
    have hq: q := hpq.right 
    hpqr hp hq)
  (λ hpqr: p ∧ q → r => λ hp: p => λ hq:q => 
    hpqr ⟨hp, hq⟩)

theorem lemma11 : (p ∨ q) → r ↔ (p → r) ∧ (q → r) := 
Iff.intro 
  (λ hpqr: (p ∨ q) → r => 
    have hpr : p → r := λ hp: p => hpqr (Or.inl hp)
    have hqr : q → r := λ hq: q => hpqr (Or.inr hq)
    ⟨hpr, hqr⟩)
  (λ hprqr: (p → r) ∧ (q → r) => 
    have hpr: p → r := hprqr.left 
    have hqr: q → r := hprqr.right 
    λ hpq: p ∨ q => Or.elim hpq hpr hqr)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := lemma11 p q False

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  λ hnpnq: ¬p ∨ ¬q => λ hpq: p ∧ q => 
    have hp: p := hpq.left 
    have hq: q := hpq.right 
    have hnp : ¬p → False := λ h: p → False => False.elim (h hp)
    have hnq : ¬q → False := λ h: q → False => False.elim (h hq)
    Or.elim hnpnq hnp hnq

example : ¬(p ∧ ¬p) := λ hpnp: p ∧ ¬p => 
  have hp: p := hpnp.left
  have hnp: ¬p := hpnp.right
  hnp hp

example : p ∧ ¬q → ¬(p → q) := λ hpnq: p ∧ ¬q => 
  have hp: p := hpnq.left 
  have hnq: ¬q := hpnq.right 
  λ hpq: p → q => hnq (hpq hp)

-- !!!!!!!!!!!!!!!!!!!!!!!!
example : ¬p → (p → q) :=
  λ hnp: ¬p => 
    λ hp: p => False.elim (hnp hp)

example : (¬p ∨ q) → (p → q) :=
  λ hnpq: ¬p ∨ q => λ hp: p =>
    have h1: ¬p → q := λ hnp: ¬p => False.elim (hnp hp)
    Or.elim hnpq h1 (λ hq: q => hq)

example : p ∨ False ↔ p :=
  Iff.intro 
    (λ hpf: p ∨ False => Or.elim hpf (λ hp: p => hp) (False.elim))
    (λ hp: p => Or.inl hp)

example : p ∧ False ↔ False := 
  Iff.intro
    (λ hpf: p ∧ False => hpf.right)
    (λ hf: False => ⟨False.elim hf, hf⟩)

-- tricky
example : ¬(p ↔ ¬p) := λ hpnp: p ↔ ¬p =>
  have h1: p → ¬ p := Iff.mp hpnp
  have h2: ¬p → p := Iff.mpr hpnp
  have hpf: p → False := λ hp: p => (h1 hp) hp
  hpf (h2 hpf)

example : (p → q) → (¬q → ¬p) := λ hpq: p → q =>
  λ hnq: ¬q => λ hp: p => hnq (hpq hp)

open Classical

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  λ hp_rs: p → r ∨ s => byCases
    (λ hp:p => Or.elim (hp_rs hp) (λ hr:r => Or.inl (λ _: p => hr)) (λ hs:s => Or.inr (λ _: p => hs)))
    (λ hnp:¬p => 
       have hpr: p → r := λ hp:p => False.elim (hnp hp)
       Or.inl hpr)
      
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  λ hnpq: ¬(p ∧ q) => 
    have hpnq: p → ¬q := λ hp: p => byCases
      (λ hq:q => False.elim (hnpq ⟨hp, hq⟩))
      (λ hnq:¬q => hnq)
    byCases 
      (λ hp: p => Or.inr (hpnq hp))
      (λ hnp: ¬p => Or.inl hnp)
      
-- very tricky !!!!
example : ¬(p → q) → p ∧ ¬q := 
  λ hnpq: (p → q) → False =>
    byCases  
      (λ hp: p => byCases 
        (λ hq:q => False.elim (absurd (λ _:p => hq) hnpq))
        (λ hnq:¬q => ⟨hp, hnq⟩)
      )
      (λ hnp:¬p => False.elim (absurd (λ hp:p => absurd hp hnp) hnpq))

example : (p → q) → (¬p ∨ q) := λ hpq: p → q =>
  byCases 
    (λ hp: p => Or.inr (hpq hp))
    (λ hnp: ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) := λ pnqnp: ¬q → ¬p =>
  λ hp: p => byCases 
    (λ hq: q => hq)
    (λ hnq: ¬q => 
      have hnp: ¬p := pnqnp hnq
      absurd hp hnp)
       
example : p ∨ ¬p := em p

-- very tricky!!!!
-- the trick is ¬p → (p → anything) !!!!!!!!!!!!
example : ¬p → (p → q) := λ hnp: ¬p => λ hp:p => absurd hp hnp

example : (((p → q) → p) → p) := λ hpqp: (p → q) → p =>
  byCases 
    (λ hp: p => hp)
    (λ hnp: ¬p => hpqp (λ hp:p => (False.elim (absurd hp hnp))))
   
example: ¬(p ↔ ¬p) := λ h: p ↔ ¬p => 
  have hr: p → ¬p := h.mp 
  have hl: ¬p → p := h.mpr 
  have hnp: ¬p := λ hp: p => hr hp hp 
  hnp (hl hnp) 
end exercise
