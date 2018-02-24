(** printing ◊ $\Diamond$ *)
(** printing (◊ $(\Diamond$ *)
(** printing ⇒ $\Rightarrow$ *)
(** printing ∧ $\wedge$ *)
(** printing ∨ $\vee$ *)
(** printing ⊥ $\bot$ *)
(** printing ¬ $\lnot$ *)
(** printing (¬ $(\lnot$ *)
(** printing □ $\square$ *)

(** %\chapter{Formalising the Martin-\Loef{} theorem - Formalisation in CS4+Int}% *)

(** Here a potentially adequate formalisation of the Martin-%\Loef{}% Theorem is explored, a formalisation in the axiom system of CS4 + intuitionistic logic. *)

(** CS4 is `Constructive S4' discussed in Alechina et al (2001)%\cite{alechina}%. Here we consider [◊] to mean `can be known' or `is knowable'. Only one axiom of CS4 is required in the proof of the Martin-%\Loef{}% Theorem. The axiom required is [A -> ◊ A]. Informally: if a formula is true then it is knowable. *)

(** * Axioms *)
(** ** From CS4 *)
(** [◊ T] : [A -> ◊ A] *)
(** ** From intuitionistic logic *)
(** [A1] from Introduction to Intuitionistic Logic%~\cite[p.~18]{stonybrookslides}%:
%\begin{center}% [((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))] %\end{center}%
 *)

(** Property 11 from Introduction to Intuitionistic Logic%~\cite[p.~24]{stonybrookslides}%:
%\begin{center}% [((A ⇒ B) ⇒ ( ¬ B ⇒ ¬ A))] %\end{center}%  *)

(** Modus Ponens: %\begin{center}% if [(A ⇒ B)] and [A] are true, then [B] is true %\end{center}%  *)

(** * Proof of Martin-%\Loef{}%'s Third Law *)

(** The proof below is by Monica Marcus, (personal communication, October 10, 2017). *)

(** %\vspace{1em}% *)

(** 1. [(¬ ◊ p ⇒ ¬ p) ⇒ (( ¬ p ⇒ ◊ (¬ p)) ⇒ (¬ ◊ p ⇒ ◊ (¬ p)))] %\hspace*{\fill}% (A1) *)

(** 2. [p ⇒ ◊ p] %\hspace*{\fill}% ([◊ T] CS4 axiom) *)

(** 3. [(p ⇒ ◊ p) ⇒ (¬ ◊ p ⇒ ¬ p) ] %\hspace*{\fill}% (property 11) *)

(** 4. [ ¬ ◊ p ⇒ ¬ p ] %\hspace*{\fill}% (Modus Ponens, 2, 3) *)

(** 5. [(¬ p ⇒ ◊ (¬ p)) ⇒ (¬ ◊ p ⇒ ◊ (¬ p))] %\hspace*{\fill}% (Modus Ponens 4,1) *)

(** 6. [¬ p ⇒ ◊ (¬ p)] %\hspace*{\fill}% ([◊ T] CS4 axiom) *)

(** 7. [¬ ◊ p ⇒ ◊ (¬ p)] %\hspace*{\fill}% (Modus Ponens 6,7) *)

(** %\vspace{1em}% *)

(** This proves the formula [¬ ◊ p ⇒ ◊ (¬ p)] in CS4 plus a propositional intuitionistic axiom system. *)

(** * Coq definitions *)

(** The next sections form a Coq version of the above proof. The Coq proof assistant checks that the definitions are used correctly and that the steps in the proof ([tactic]s) are correct, giving an even greater level of rigour. *)

(** %\vspace{1em}% *)

(** First it is necessary to define propositional formulas, which can then be reasoned about. *)

(** ** Propositional atoms *)
Inductive Atoms :=
  | a : Atoms
  | S : Atoms -> Atoms.

(** This definition of the type [Atoms] is a straightforward way to capture the notion of there being infinitely many propositional atoms. Here [a], [S a], [S (S a)], ... are all propositional atoms. *)

(** ** Modal formula syntax *)
Inductive modal_formula := 
 | atom : Atoms -> modal_formula
 | and : modal_formula -> modal_formula -> modal_formula
 | or : modal_formula -> modal_formula -> modal_formula
 | implies : modal_formula -> modal_formula -> modal_formula
 | falsum : modal_formula
 | box : modal_formula -> modal_formula
 | dia : modal_formula -> modal_formula.

(** Here the syntax of a modal formula is defined. For example, [or (atom a) (atom (S a))] is a syntactically correct modal formula. As is [implies (dia (atom (S a))) (atom a)].*)

(* begin hide *)
(* To check the above two examples are well-formed: *)
Check or (atom a) (atom (S a)).
Check implies (dia (atom (S a))) (atom a).
(* end hide *)

(** ** Notation *)
(* begin hide *)
Infix "∧" := and (at level 79). 
Infix "∨" := or (at level 79).
Infix "⇒" := implies (at level 99).
Notation "⊥" := falsum.
Notation "¬ A" := (A ⇒ ⊥) (at level 74).
Notation "◊" := dia.
Notation "□" := box.

(* end hide *)
(* For Latex purposes: *)
(** 
Infix "[∧]" := and (at level 79). %\\%
Infix "[∨]" := or (at level 79). %\\%
Infix "[⇒]" := implies (at level 99). %\\%
Notation "[⊥]" := falsum. %\\%
Notation "[¬ A]" := [(A ⇒ ⊥ )] (at level 74). %\\%
Notation "[◊]" := dia. %\\%
Notation "[□]" := box. %\\%
*)

(** Here notation is introduced so that formulas can be written more naturally. Now we can write [(atom a) ∨ (atom (S a))] and also [(◊ (atom (S a))) ⇒ (atom a)].*)

(* begin hide *)
(* To check the above two examples are well-formed: *)
Check (atom a) ∨ (atom (S a)).
Check (◊ (atom (S a))) ⇒ (atom a).
(* end hide *)

(** ** Using Coq's logic as a meta-language *)
(** In Coq, logical statements have the type [Prop]. So in order to use Coq's logic as a meta-language, a predicate of type [modal_formula -> Prop] is needed. This is declared as a [Parameter] (or [Axiom]) which essentially declares that there is a predicate in the Coq meta-language that describes which [modal_formula]s are true. At this stage no [modal_formula]s are considered true, it is only when the axioms below are added that certain [modal_formula]s are considered true. *)

Parameter True : modal_formula -> Prop.

(** ** Axioms in Coq *)

(** Here the same axioms as earlier are defined, however these axioms are now written in Coq. There are other axioms that would be necessary for fully describing CS4 and intuitionistic logic but these have been omitted for brevity and only the axioms relevant to the proof below have been included. *)

(** These axioms declare what is provable in the Coq meta-language with respect to the predicate [True]. *)

Axiom A1 : forall A B C, True (  ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))).
Axiom diaT : forall A, True (A ⇒ (◊ A)).
Axiom property11_p24 : forall A B, True (  ((A ⇒ B) ⇒ ( ¬ B ⇒ ¬ A))  ).
Axiom mp : forall {A} {B}, True (A ⇒ B) -> (True A) -> True B.

(** * Proof of Martin-%\Loef{}%'s Third Law *)

(** Martin-%\Loef{}%'s Third Law states that %\emph{"From the unknowability of the truth of a proposition, its falsity may be inferred"}%%~\cite[p.~12]{ml}%. Using [◊] to represent `can be known', we can formulate the Third Law as [(( ¬ ( ◊ p))) ⇒ (( ◊ (¬ p)))]. Below is a Coq proof of the Third Law formulated in a way that mirrors the structure of Marcus' proof from earlier in this chapter.  *)

(** ** Proof mirroring the structure of Marcus' proof *)

Lemma mlThirdLaw_forwards_reasoning : forall p, True ((( ¬ ( ◊ p))) ⇒ (( ◊ (¬ p)))).
Proof.
intro p.
pose proof (A1 (¬ ( ◊ p)) (¬ p) ( ◊ (¬ p)) ) as Line1.
pose proof (diaT p) as Line2.
pose proof (property11_p24 p ( ◊ p)) as Line3.
pose proof (mp Line3 Line2) as Line4.
pose proof (mp Line1 Line4) as Line5.
pose proof (diaT ( ¬ p)) as Line6.
pose proof (mp Line5 Line6) as Line7.
exact Line7.
Qed.

(** At each line in the above proof, the output from Coq when stepped through interactively is exactly each line from Marcus' original proof. For instance after "[pose proof (diaT p) as Line2.]" the output is "[Line2 : True (p ⇒ ◊ p)]". The reasoning is also mirrored, with [Line2] in Coq containing "[diaT]" where Marcus' proof contained "[◊ T] CS4 axiom" for example. *)

(** ** Alternate proof of Martin-%\Loef{}%'s Third Law *)

(** Here an alternate version of the above proof is given. It uses a more typical Coq proof structure, reasoning backwards from the goal rather than takings steps towards the goal. *)

Lemma mlThirdLaw_backwards_reasoning : forall p, True ((( ¬ ( ◊ p))) ⇒ (( ◊ ( ¬ p)))).
Proof.
intros.
apply @mp with (A:=( ¬ p ⇒ ◊ (¬ p))).
 - apply @mp with (A:=( ¬ (◊ p)) ⇒ (¬ p)) .
     + apply A1.
     + apply @mp with (A:= (p ⇒ ◊ p)).
          * apply property11_p24.
          * apply diaT.
 - apply diaT.
Qed.

(** * Reasonableness of the axioms *)

(** The purpose of considering the statements and lemmas below is to test whether "can be known" is an adequate interpretation for [◊]. *)

(** ** Considering the axioms themselves *)

(** [
Axiom diaT : forall A, True (A ⇒ (◊ A)).
] *)

(** This axiom claims that for all propositions in CS4 and intuitionistic logic, that if they are true then they can be known. This seems reasonable, however at the same time it also seems very close to saying there are no undecidable propositions (if everything that is true can be known then surely nothing is unknowable). So perhaps the axiom is stating too much. *)

(** %\vspace{1em}% *)

(** [
Axiom A1 : forall A B C, True (  ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))).
] *)

(** This axiom appears to be similar to the cut elimination rule. It seems acceptable and does not directly refer to [◊]. It appears to be unlikely to cause any issues relating to the interpretation of [◊] as "can be known". *)

(** %\vspace{1em}% *)

(** [
Axiom property11_p24 : forall A B, True (  ((A ⇒ B) ⇒ ( ¬ B ⇒ ¬ A))  ).
] *)

(** This axiom, stating that an implication implies its contrapositive is unlikely to have any impact on the reasonableness of treating [◊] as "can be known". *)

(** %\vspace{1em}% *)

(** [
Axiom mp : forall {A} {B}, True (A ⇒ B) -> (True A) -> True B.
] *)

(** The axiom of Modus Ponens is very unlikely to affect the reasonableness of treating [◊] as "can be known". *)

(** %\vspace{1em}% *)

(** So, the main axiom that requires consideration is [diaT] which states [forall A, True (A ⇒ (◊ A))]. *)

(** ** Considering some lemmas *)

(** The goal of considering these lemmas is to test the reasonableness of treating [◊] as "can be known". The focus will be on the [diaT] axiom which was identified above as the axiom which is likely to require the most consideration. *)

Lemma Lemma_one : forall A, True ((( ◊ (◊ (◊ A)))) ⇒ (◊ (◊ (◊ (◊ A))))).
Proof. intro. apply diaT. Qed.

(** This lemma states that for all propositions, if it can be known that it can be known that it can be known then it can be known that it can be known that it can be known that it can be known. More generally, it should be provable that for any length of n "can be known" repeats one further repeat would also be true. This seems reasonable, although the case [A ⇒ ◊ A] still may be stating too much. For this lemma however, treating [◊] as "can be known" seems to be fine. *)

Lemma Lemma_two : forall A, True ( ¬ A ⇒ ◊ (¬ A)).
Proof. intro. apply diaT. Qed.

(** This lemma states that for all propositions, if their negation is true then the negation can be known. This seems to fit well with the interpretation of [◊] as "can be known". However it may be stating too much. [¬ A] being true is essentially the definition of [A] being false and so this lemma states that if any statement is false then it is knowable that it is false. This seems to indicate that the axiom [diaT] is too strong. *)

(** * Extending to Martin-%\Loef{}%'s Theorem *)

(** In order to prove Martin-%\Loef{}%'s Theorem, two additional axioms are required. They are Fact 2 and Fact 4 from Martin-%\Loef{}%'s argument as discussed in chapter 2 and in the Logicomp 301 slides%~\cite{crisslides}%. *)

(** Fact 2 states: %\emph{"If $A$ can be known to be true and $B$ can be known to be true, then $A\wedge B$ can be known to be true."}% It can be formalised as given below. *)

Axiom fact_2 : forall A B, (True A /\ True B) <-> True (A ∧ B).

(** Fact 4 states: %\emph{"One and the same proposition $A$ cannot both be known to be true and  be known to be false."}% It can be formalised as given below. *)

Axiom fact_4 : forall A, ~ (True (A ∧ (¬ A))).

(** Note here that the outermost [~] is in the Coq meta-language and captures the meaning of "cannot" in Fact 4, whereas the innermost [¬] is part of a [modal_formula] and captures the meaning of "to be false". *)

(** Both Fact 2 and Fact 4 are now axioms added to Coq (as [fact_2] and [fact_4]). They are needed in the proof of Martin-%\Loef{}%'s Theorem, [ml_theorem_backwards_reasoning/forwards_reasoning], below. *)

(** Fact 1 is Martin-%\Loef{}%'s Third Law which states: %\emph{"From the unknowability of the truth of a proposition, its falsity may be inferred"}%. This has been proven earlier. *)

Definition fact_1 := mlThirdLaw_forwards_reasoning.

(** Here is a Coq-style proof of Martin-%\Loef{}%'s Theorem which states %{\em "There is no proposition  which can neither be known to be true nor be known to be false, i.e.~there is no absolutely unprovable proposition."}%  *)

Theorem ml_theorem_backwards_reasoning : forall A, ~ True (( ¬ (◊ A) ∧ (¬ (◊ (¬ A))))).
Proof.
intro.
unfold not.
intro.
apply fact_2 in H. destruct H.
apply (fact_4 (◊ (¬ A))).
apply fact_2.
exact ((conj (mp  (mlThirdLaw_forwards_reasoning A) H) H0)).
Qed.

(* begin hide *)
Print Assumptions ml_theorem_backwards_reasoning.
(* end hide *)

(** 
Axioms used in the above proof:
[[
property11_p24 : forall A B : modal_formula, True ((A ⇒ B) ⇒ (¬ B ⇒ ¬ A))
mp : forall A B : modal_formula, True (A ⇒ B) -> True A -> True B
fact_4 : forall A : modal_formula, ~ True (A ∧ ¬ A)
fact_2 : forall A B : modal_formula, True A /\ True B <-> True (A ∧ B)
diaT : forall A : modal_formula, True (A ⇒ ◊ A)
True : modal_formula -> Prop
A1 : forall A B C : modal_formula, True ((A ⇒ B) ⇒ ((B ⇒ C) ⇒ (A ⇒ C)))
]] 
*)

(** %\vspace{1em} *)

(** Here is another proof of the Martin-%\Loef{}% Theorem which has a more similar structure to the informal proof given in the Logicomp 301 slides%~\cite{crisslides}%. *)

Lemma ml_theorem_forwards_reasoning : forall A, ~ True (( ¬ (◊ A) ∧ (¬ (◊ (¬ A))))).
Proof.
intro.

(** "If [A] is a proposition which cannot be known to be true, then by Fact 1, [A] can be known to be false, ..." *)

assert (True (¬ (◊ A) ⇒ (◊ (¬ A)))). apply fact_1.
unfold not. intro. apply fact_2 in H0. destruct H0. apply (mp H) in H0.

(** "... a contradiction." *)

pose proof (fact_2 (◊ (¬ A)) ( ¬ (◊ (¬ A))) ).
pose proof (conj H0 H1). apply H2 in H3.
apply fact_4 in H3.
contradiction.
Qed.

(** The two proofs above prove the Martin-%\Loef{}% theorem in this system, CS4 + intuitionistic propositional logic + [fact_2] + [fact_4]. It should be possible to derive [fact_2] and [fact_4] from intuitionistic logic, this could be verified in the future. *)