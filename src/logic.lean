
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro nop,
  have boom: false := nop p,
  exact boom,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro nnp,
  by_cases h : P, --LEM
  --P
  exact h,
  --¬P
  have boom: false := nnp h,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  exact doubleneg_elim P,
  exact doubleneg_intro P,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pvq,
  cases pvq with p q,
  --Case P
  right,
  exact p,
  --Case Q
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pandq,
  split,
  --Parte Q
  cases pandq with p q,
  exact q,
  --Parte P
  cases pandq with p q,
  exact p,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro nopvq,
  intro p,
  cases nopvq with nop q,
  --case noP
  exfalso,
  have boom: false := nop p,
  contradiction,
  --Case Q
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pvq,
  intro nop,
  cases pvq with p q,
  --Case P
  exfalso,
  have boom: false := nop p,
  exact boom,
  --Case Q
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro noq,
  intro p,
  have q: Q := hpq p,
  have boom: false := noq q,
  exact boom,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  intro hp,
  by_contradiction hboom,
  have hpp: ¬P := h hboom,
  have hpboom: false := hpp hp,
  exact hpboom,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  exact impl_as_contrapositive P Q,
  exact impl_as_contrapositive_converse P Q,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro h,
  have pvnp : P∨¬P,
  right,
  intro nop,
  have pvq : P∨¬P,
  left,
  exact nop,
  contradiction,
  contradiction,
end

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro nop,
  have pq : P → Q,
  intro p,
  contradiction,
  have pp : P := h pq,
  contradiction,
end

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro h,
  intro hnpnq,
  cases hnpnq with hp hq,
  cases h with hp hq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro h,
  intro hnpnq,
  cases h with hp hq,
  cases hnpnq with hp hq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro h,
  split,
  intro p,
  have pvq: P∨Q,
  left,
  exact p,
  contradiction,
  intro q,
  have pvq: P∨Q,
  right,
  exact q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro h,
  intro pvq,
  cases pvq with p q,
  cases h with np nq,
  contradiction,
  cases h with np nq,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro h,
  by_cases hq: Q,
  right,
  intro hp,
  have pandq : (P∧Q),
  split,
  exact hp,
  exact hq,
  contradiction,
  left,
  exact hq,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro h,
  intro hpandq,
  cases hpandq with nq np,
  cases h with noq nop,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  exact demorgan_conj P Q,
  exact demorgan_conj_converse P Q,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  exact demorgan_disj P Q,
  exact demorgan_disj_converse P Q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro h,
  cases h with p qvr,
  cases qvr with q r,
  left,
  split,
  exact p,
  exact q,
  right,
  split,
  exact p,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  cases h with hl hr,
  cases hl with p q,
  split,
  exact p,
  left,
  exact q,
  cases hr with pp r,
  split,
  exact pp,
  right,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro h,
  cases h with p qandr,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qandr with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro h,
  cases h with hl hr,
  cases hl with p q,
  left,
  exact p,
  cases hr with p r,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro h,
  intro hp,
  intro hq,
  have pandq : P∧Q,
  split,
  exact hp,
  exact hq,
  apply h pandq,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hpqr,
  intro hpandq,
  cases hpandq with p q,
  apply hpqr p,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  exact hp,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  exact hp,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  exact hq,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro h,
  cases h with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro h,
  cases h with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro hp,
  cases hp with p pp,
  exact p,
  intro hpp,
  split,
  exact hpp,
  exact hpp,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro h,
  cases h with p pp,
  exact p,
  exact pp,
  intro hp,
  left,
  exact hp,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro he,
  intro x,
  intro p,
  apply he,
  existsi x,
  exact p,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro ha,
  intro he,
  cases he with t ht,
  exact (ha t) ht,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  rw contrapositive_law,
  rw doubleneg_law,
  intro he,
  intro a,
  by_contradiction hboom,
  apply he,
  existsi a,
  exact hboom,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro he,
  intro ha,
  cases he with t ht,
  have pt : P t := ha t,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  exact demorgan_forall U P,
  exact demorgan_forall_converse U P,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  exact demorgan_exists U P,
  exact demorgan_exists_converse U P,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro he,
  intro ha,
  cases he with x he,
  have nhp : ¬P x := ha x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro ha,
  intro he,
  cases he with x he,
  have hp : P x := ha x,
  contradiction, 
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro he,
  intro x,
  by_contradiction px,
  apply he,
  existsi x,
  exact px,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  rw contrapositive_law,
  intro he,
  intro ha,
  apply ha,
  intro t,
  intro pt,
  apply he,
  existsi t,
  exact pt,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  exact forall_as_neg_exists U P,
  exact forall_as_neg_exists_converse U P,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  exact exists_as_neg_forall U P,
  exact exists_as_neg_forall_converse U P,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  cases h with a ha,
  cases ha with hp hq,
  split,
  --Parte P(x)
  existsi a,
  exact hp,
  --Parte Q(x)
  existsi a,
  exact hq,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with a ha,
  cases ha with Pa Qa,
  left,
  existsi a,
  exact Pa,
  right,
  existsi a,
  exact Qa,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro h,
  cases h with Pa Qa,
  cases Pa with a ha,
  existsi a,
  left,
  exact ha,
  cases Qa with a ha,
  existsi a,
  right,
  exact ha,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro h,
  split,
  intro a,
  have ha : P a ∧ Q a := h a,
  cases ha with hl hr,
  exact hl,
  intro a,
  have ha : P a ∧ Q a := h a,
  cases ha with hl hr,
  exact hr,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro h,
  intro a,
  cases h with hl hr,
  split,
  have hp : P a := hl a,
  exact hp,
  have hq : Q a := hr a,
  exact hq,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro h,
  intro a,
  cases h with hl hr,
  have hp : P a := hl a,
  left,
  exact hp,
  have hq : Q a := hr a,
  right,
  exact hq,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
