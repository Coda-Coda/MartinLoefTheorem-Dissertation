(** printing Falsum $\bot$ *)
(** printing False $\bot$ *)
(** printing ⇒ $\Rightarrow$ *)
(** printing ∧ $\wedge$ *)
(** printing ∨ $\vee$ *)
(** printing ⊥ $\bot$ *)
(** printing ¬ $\lnot$ *)

(** %\chapter{Formalising the Martin-\Loef{} Theorem - Formalisation of Intuitionistic Logic}% *)

(** * Motivation and background *)
(** The Martin-%\Loef{}% theorem involves intuitionistic logic and so a technique for formalising the theorem could be to formalise an embedding of intuitionistic logic in Coq and then use Coq as a meta-language to prove results about intuitionistic logic. This technique is explored in this chapter. The Third Law and the Martin-%\Loef{}% Theorem are both proved in this formalisation. %\par% *)

(** This technique has some similarities to the bi-modal logic embedding in Coq in that an embedding of a logic is defined with Coq as the meta-language. *)

(** * Defining an embedding of intuitionistic logic *)

(** ** Atoms *)

(** Here we define a countably infinite set of atoms. *)

Inductive Atoms := 
  | a : Atoms
  | S : Atoms -> Atoms.

Parameter AtomValuation : Atoms -> bool. (** Here we assume a valuation for the atoms exists. *)

(** ** Propositions *)

(** Here we define the syntax of a [proposition]. *)

Inductive proposition :=
  | Atom : Atoms -> proposition
  | Implies : proposition -> proposition -> proposition
  | Or : proposition -> proposition -> proposition
  | And : proposition -> proposition -> proposition
  | Falsum : proposition
  | Not : proposition -> proposition
  | K : proposition -> proposition. (** "[K]" for representing `can be known' or `knowable' is included here. *)

(** No notations have yet been defined so each [proposition] must be written in prefix notation, for example [Implies (S S a) (And a (S a))] rather than [(S S a) -> (a /\ (S a))]. *)

(** ** Proofs *)

(** Next we define what constitutes a proof of a [proposition]. *)

(** Due to complications discussed below, the rules for what constitutes a proof of an implication must be defined in a roundabout manner. First, we assume the existence of a predicate in the Coq meta-language of arity 2 named [Implication_Is_True]. An axiom will be added later to define the meaning of [Implication_Is_True]. *)

Parameter Implication_Is_True : proposition -> proposition -> Prop.

(** Now we define what constitutes a proof of a [proposition]. By using an inductively defined proposition, the notion that these rules are the only possible ways to obtain a proof is captured. *)

Inductive Proof : proposition -> Prop :=
  | atom_ev : forall (A:Atoms), AtomValuation A = true -> Proof (Atom A)
  | and_ev  : forall (p q : proposition), Proof p -> Proof q -> (Proof (And p q))
  | orl_ev  : forall (p q : proposition), Proof p -> (Proof (Or p q))
  | orr_ev  : forall (p q : proposition), Proof q -> (Proof (Or p q))
  | not_ev : forall (p : proposition), Proof (Implies p Falsum) -> (Proof (Not p))
  | K_ev : forall (p : proposition), Proof p -> (Proof (K p))
  | implies_ev : forall (p q : proposition), Implication_Is_True p q -> (Proof (Implies p q)).


Axiom implies_ev' : forall p q, Implication_Is_True p q <-> (exists (f: Proof p -> Proof q), True ).
(** Here we declare that a [proposition] of the form [Implies a b] has a proof iff there exists a function which takes a proof of [a] to a proof of [b]. This defines the meaning of [Implication_Is_True]. *)


(** The rule for [Implies] is added as an extra axiom because Coq gives the error "Non strictly positive occurrence ..." when trying to add it to the above definition of [Proof]. Further work is needed to ensure that adding this axiom ([implies_ev']) and the [Implication_Is_True] predicate as done here does not give rise to a contradiction or other unintended consequences. *)

(** %\newpage% *)
(** -------------- *)
(** In a similar way to the bi-modal logic embedding, the definitions required to embed intuitionistic logic are now all defined. Only notation, lemmas and theorems are defined below and these do not alter what propositions are expressible and provable in this embedding of intuitionistic logic in Coq. *)
(** -------------- *)

(** ** Notation *)

(* begin hide *)
Infix "∧" := And (at level 79). 
Infix "∨" := Or (at level 79).
Infix "⇒" := Implies (at level 99).
Notation "⊥" := Falsum.
Notation "¬ A" := (A ⇒ ⊥) (at level 74).
(* end hide *)
(* For Latex purposes: *)
(** 
Infix "[∧]" := And (at level 79). %\\%
Infix "[∨]" := Or (at level 79). %\\%
Infix "[⇒]" := Implies (at level 99). %\\%
Notation "[⊥]" := Falsum. %\\%
Notation "[¬ A]" := [(A ⇒ ⊥ )] (at level 74). %\\%
*)

(** ** Lemmas *)

(** With an embedding of intuitionistic logic now defined, we can prove some relevant results. *)

Lemma falsum_unprovable : ~ (Proof Falsum).
Proof.
unfold not.
intros.
inversion H. (** In our inductive definition for [Proof] we did not include a case where [Falsum] was provable. As a result we can use the tactic [inversion] to obtain a contradiction from a hypothetical Coq proof of [Proof Falsum]. *)

Qed.

(** Using similar methods we can prove that we cannot have a proof of a proposition and its negation. *)

Lemma non_contradiction : forall A, ~ (Proof A /\ Proof (Not A)).
Proof.
unfold not.
intros.
destruct H.
inversion H0.
inversion H2.
apply implies_ev' in H4.
destruct H4.
apply falsum_unprovable.
apply x. 
apply H.
Qed.

(** Here Fact 2 from Cristian Calude's explanation of the Martin-%\Loef{}% Theorem in chapter 2 is proven. Fact 2 states that "If $A$ can be known to be true and $B$ can be known to be true, then $A\wedge B$ can be known to be true."%~\cite{crisslides}% *)

Lemma fact_2 : forall A B, Proof (K A) /\ Proof (K B) -> Proof (K (A ∧ B)).
Proof.
intros.
destruct H.
apply K_ev.
apply and_ev.
inversion H. exact H2.
inversion H0. exact H2.
Qed.

(** It will also be useful to prove the similar statement [fact_2'] which states that for all propositions [A] and [B], there is a proof for A and a proof for B if and only if there is a proof for [(A ∧ B)]. *)

Lemma fact_2' : forall A B, Proof (A) /\ Proof (B) <-> Proof ((A ∧ B)).
Proof.
intros.
split.
 - intro.
   destruct H.
   apply and_ev.
     exact H.
     exact H0.
 - intro.
   inversion H.
   split.
   exact H2.
   exact H3. 
Qed.

(** Here is a proof of Fact 3, which states that "The proposition [Falsum] cannot to be known to be true."%~\cite{crisslides}% *)

Lemma fact_3 : ~ Proof (K Falsum).
Proof.
unfold not. intros.
inversion H.
inversion H1.
Qed.

(** Here Fact 4 is proven. It states "One and the same proposition $A$ cannot both be known to be true and  be known to be false."%~\cite{crisslides}% *)

Lemma fact_4 : forall A, ~ ((Proof (K A)) /\ Proof (K ( ¬ A))).
Proof.
intro.
unfold not.
intro.
destruct H.
inversion H. clear H1. clear p. 
inversion H0. clear H1. clear p.
apply not_ev in H3.
apply (non_contradiction A).
split. exact H2. exact H3.
Qed.

(** * Proof of Martin-%\Loef{}%'s Third Law *)

Lemma ml3rdLaw : forall p, Proof (Not (K p)) -> Proof (K (Implies p Falsum)) .
Proof.
intro p.
intros.
apply K_ev. apply implies_ev. apply implies_ev'.
inversion H. inversion H1. apply implies_ev' in H3.
destruct H3.
assert(Proof p -> Proof (K p)).
intros. apply K_ev in H5. exact H5.
assert(Proof p -> Proof Falsum).
intros.
apply x.
apply H5.
exact H6.
exists H6.
apply I.
Qed.

(** * Proof of the Martin-%\Loef{}% Theorem *)

(** We can now prove the Martin-%\Loef{}% Theorem which states, in one rendering, that "it is impossible to find a counterexample to the law of the excluded middle in its positive formulation"%~\cite[p.~14]{ml}%. Here this is rendered as `for all propositions, it is not the case that it is provable that the proposition both cannot be known to be true and cannot be known to be false'. *)

Theorem MLTheorem : forall A, ~ Proof (( ¬ (K A) ∧ ( ¬ (K ( ¬ A))))).
Proof.
intro.
unfold not.
intro.
apply fact_2' in H. destruct H.
apply (non_contradiction (K ( ¬ A))).
split.
 - apply ml3rdLaw. 
   apply not_ev.
   exact H.
 - apply not_ev.
   exact H0.
Qed.

(** * Comments on this formalisation *)

(** A key advantage of this formalisation is that it does not rely on axioms other than those fundamental to intuitionistic logic. The only two non-standard axioms are found in the definition of what constitutes a proof in the system. %\\%
[K_ev] is essentially an axiom which states that %$$%[forall (p : proposition), Proof p -> (Proof (K p))].%$$%This potentially does not capture the notion of knowability properly. It is part of an inductive definition, so implicit in the axiom is that the _only_ way one can show that a proposition is knowable is by exhibiting a Coq proof for [Proof p]. It may be that there are other ways of knowing that are not captured by this axiom. For instance we may be able to know by analysing the axioms of intuitionistic logic that double negation elimination, [ ~ ~ q -> q], is not knowable, yet we would not be able to prove [Proof ~ (K ( ~ ( ~ q) -> q))]. %\\%
The second non-standard axiom is that the only way to show that [Proof (A ⇒ B)] is true is to show that [(exists (f: Proof p -> Proof q), True )]. This can be simplified to [Proof p -> Proof q]. A possible concern with this axiom is it allows [Proof (A ⇒ B)] to be proven whenever the implication [Proof p -> Proof q] is true rather than when there is indeed a function that takes a proof of [p] and returns a proof of [q]. This means that alterations to the meta-language logic could sometimes filter down into the embedding of intuitionistic logic, potentially causing issues. %\\%
Overall however, this formalisation does a good job at capturing certain elements from Martin-%\Loef{}%'s proof and is useful for gaining a deeper understanding of the Martin-%\Loef{}% Theorem. *)