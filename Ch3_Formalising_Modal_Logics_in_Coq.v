(** printing False $\bot$ *)
(** printing dia $\Diamond$ *)
(** printing box $\square$ *)

(** %\chapter{Formalising Modal Logics in Coq}% *)

(** * Motivation and background *)
(** The Martin-%\Loef{}% Theorem includes the notion of knowledge as well as the notion of possibility in key ways. Both possibility and knowledge have been modelled using modal logics for many years, and so it seemed likely that incorporating or adapting some of those techniques would be useful in formalising the Martin-%\Loef{}% theorem and its proof. *)

(** ** The Benzmuller and Paleo paper *)
(** The paper `Interacting with Modal Logics in the Coq Proof Assistant'%~\cite{benzmuller}% sets out a useful way to embed modal logics in the Coq proof assistant. The approach they put forward in their paper is also extensible and so had the potential to be adapted as necessary when formalising the Martin-%\Loef{}% Theorem. Their work was very helpful. %\par%*)
(** In their paper they state: %\emph{"the main contribution described in this paper - convenient techniques for leveraging a powerful proof assistant such as Coq for interactive reasoning for modal logics - may serve as a starting point for many interesting projects."} \cite[p.~2]{benzmuller}%.*)


(** ** Bi-modal logic *)
(** One of the approaches was to formalise the theorem in a bi-modal logic, representing knowability and possibility as modal operators. This approach is shown below, based almost entirely on the Coq code from the Benzmuller paper, with some minor adaptations for it to be bi-modal logic. *)


(** * Coq formalisation of modal logic *)
(** Here the approach to formalising $K5$ given in the Benzmuller and Paleo paper is outlined and explored with reference to exercises and examples from First-Order Modal Logic (Fitting and Mendelsohn, 1998)%\cite{fitting&mendelsohn}%. The purpose of this section is to explore the Benzmuller and Paleo approach when applied to standard modal logics before extending it to handle bi-modal logic. *)
(* begin hide *)
Module Modal.
(*end hide *)
(** ** Defining an embedding of modal logic in Coq *)
(** %\emph{The Coq code in this subsection is directly from the Benzmuller and Paleo Paper~\cite{benzmuller}, the comments have been added.}% *)

(** It is worth noting that to check the trustworthiness of any theorem using the techniques from the Benzmuller and Paleo paper, it is necessary to check the trustworthiness of the user code defining the modal logic embedding (below), and especially the impact of any adaptations to their original technique such as the adaptation to bi-modal logic later in this chapter. *)


(** *** Worlds, objects, modal propositions and the accessibility relation *)

Parameter i: Type. (** Here we declare/assume a type [i] as the type for worlds. *)

Parameter u: Type. (** Here we declare/assume a type [u] as the type for objects/individuals. *)

Definition o := i -> Prop. (** Here we define [o] to be the type which takes a world and gives a meta-language proposition. [o] then, is the type of modal propositions, which when given a world are then a meta-language proposition. %\par% *)

(** The intended usage is to have a modal formula, say [p] (with type [o]), with the meaning of [(p w)] to be that the modal proposition represented by [p] is true at world [w] (where [w] is a world, with type [i]). %\par% *)

(** The meanings of the definitions of [i], [u] and [o] are fixed further by their usage in the next definitions. It is also worth noting that the reason why undescriptive names are used is because [i], [u] and [o] will need to be written often and it would be inconvenient if their names were long. *)


Parameter r: i -> i -> Prop.  (** Here we declare/assume a function/predicate of arity 2 defined over worlds, to be the accessibility relation for worlds. *)


(** *** Connectives *)

(** Here the lifted connectives are defined. Each lifted connective (except [mnot]) takes two modal propositions (with type [o]) and a world (with type [i]) and gives a `meta-language' proposition (with the standard Coq type [Prop]) reflecting the meaning of the connective. *)

Definition mnot (p: o)(w: i) := ~ (p w).
Definition mand (p q:o)(w: i) := (p w) /\ (q w).
Definition mor (p q:o)(w: i) := (p w) \/ (q w).
Definition mimplies (p q:o)(w:i) := (p w) -> (q w).
Definition mequiv (p q:o)(w:i) := (p w) <-> (q w).
Definition mequal (x y: u)(w: i) := x = y.

(** Here we define a more natural prefix and infix notation for the lifted connectives. *)

(* begin hide *)
(* Hidden because coqdoc's default rendering doesn't give the desired latex result for these lines *)
Notation "m~ p" := (mnot p) (at level 74, right associativity).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).
Notation "p m\/ q" := (mor p q) (at level 79, right associativity).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).
Notation "p m<-> q" := (mequiv p q) (at level 99, right associativity).
Notation "x m= y" := (mequal x y) (at level 99, right associativity).
(* end hide *)
(* For latex output: *)
(** 
[Notation] "[m~ p]" [:= (mnot p) (at level 74, right associativity).]

[Notation] "[p m/\ q]" [:= (mand p q) (at level 79, right associativity).]

[Notation] "[p m\/ q]" [:= (mor p q) (at level 79, right associativity).]

[Notation] "[p m-> q]" [:= (mimplies p q) (at level 99, right associativity).]

[Notation] "[p m<-> q]" [:= (mequiv p q) (at level 99, right associativity).]

[Notation] "[x m= y]" [:= (mequal x y) (at level 99, right associativity).]
*)

(** Note that the notation for each of the connectives in the embedded modal logic is an `m' followed by the connective. So there is [m~] and [m\/] for example. Also, below [mforall] and [mexists] are defined. *)

(** *** Quantifiers *)

(** Here the lifted versions of the quantifiers are defined. The quantifiers take a type, a function/predicate which takes elements of that type and gives a modal proposition, and a world, and gives a `meta-language' proposition' (with type [Prop]) reflecting the meaning of the quantifier. *)

Definition A {t: Type}(p: t -> o)(w: i) := forall x, p x w.
Definition E {t: Type}(p: t -> o)(w: i) := exists x, p x w.

(** If a world is not given, then [A t p] will have type [i -> Prop] and so it will be a modal proposition itself. This will allow the expression of modal formulae such as $\forall x, \box P(x) \rightarrow P(x)$. In this formula $P$ would correspond to [p] in the definitions above. *)

(** %\vspace{0.2cm}% *)

(** Here more natural notations for [A] and [E] are defined. The definitions for [A] and [E] make use of Coq's type inference ability so [t] doesn't need to be explicitly entered (in many cases [t] would be the type for objects/individuals [u]), it is inferred from the type of [p]. *)

Notation "'mforall' x , p" := (A (fun x => p))
(at level 200, x ident, right associativity) : type_scope.
Notation "'mforall' x : t , p" := (A (fun x:t => p))
(at level 200, x ident, right associativity,
format "'[' 'mforall' '/ ' x : t , '/ ' p ']'") : type_scope.
Notation "'mexists' x , p" := (E (fun x => p))
(at level 200, x ident, right associativity) : type_scope.
Notation "'mexists' x : t , p" := (E (fun x:t => p))
(at level 200, x ident, right associativity,
format "'[' 'mexists' '/ ' x : t , '/ ' p ']'") : type_scope.

(** *** Modalities *)

Definition box (p: o) := fun w => forall w1, (r w w1) -> (p w1).
Definition dia (p: o) := fun w => exists w1, (r w w1) /\ (p w1).

(** [box] is defined as a function which takes a modal proposition and a world, and returns a `meta-level' proposition stating that for all worlds related to that world the modal proposition is true at those worlds. *)

(** [dia] is defined similarly as a function which takes a modal proposition and a world, and returns a `meta-level' proposition stating that there exists a world related to that world, where the modal proposition is true. *)

(** Since the type of both [dia] and [box] when applied to a modal proposition, is [i -> Prop], then [box p] and [dia p] are of type [o] (the type of modal propositions). *)

(** *** Validity *)
Definition V (p: o) := forall w, p w. (** Here the definition of validity for a modal formula is given. [V] is defined as a function/predicate that takes a modal proposition and gives a `meta-level' proposition stating that the given modal proposition is true at all worlds. So for any modal proposition [p], at the meta-level [V p] is true iff [p] is valid. *)

Notation "[ p ]" := (V p). (** Here a notation is defined so that we can write "[p] is valid" as [[p]] rather than [(V p)]. *)

(** -------------- *)
(** The definitions required to embed modal logic are now all defined. The tactics defined below only add to the usability of the above definitions and do not alter what propositions are expressible and provable in this embedding of modal logic in Coq like each of the definitions above have. *)
(** -------------- *)

(** ** Increasing the usability by defining tactics *)

(** The tactics defined below allow proofs to be carried out without dealing directly with the intricate aspects of the definitions of the embedding. Instead, the familiar technique of working with introduction and elimination rules can be used. Only some new tactics are needed, as the standard Coq tactics work fine with many of the defined notions. Below a brief example of each new tactic is given; for a comprehensive explanation of these definitions see section 3 of the Benzmuller and Paleo paper%~\cite[p.~5]{benzmuller}%. *)


(** *** Modal validity *)
Ltac mv := match goal with [|- (V _)] => intro end.

(** Here the [mv] tactic is defined such that when the proof state requires proving that a modal formula is valid, applying [mv] will introduce a new arbitrary world and the goal of the proof state will then be to prove that the modal formula is true at the new world. *)

Example mv_eg : [mforall p, box p m-> p].
Proof.
mv.

(** The proof state goal is now: [(mforallp:o, box p m-> p) w] %\par% *)
Abort.

(** *** Box introduction *)
Ltac box_i := let w := fresh "w" in let R := fresh "R"
in (intro w at top; intro R at top).

Example box_i_eg : [ mforall p, box p ].
Proof.
mv.
intro. (** Here the standard Coq tactic [intro] is sufficient for handling [mforall]. *)

box_i.
(** The goal is now: [(x w0)] with [r w w0] as one of the assumptions, where both [w] and [w0] are arbitrary. *)

Abort.

(** *** Box elimination *)
Ltac box_elim H w1 H1 := match type of H with
((box ?p) ?w) => cut (p w1);
[intros H1 | (apply (H w1); try assumption)] end. (** [box_elim] is an auxiliary tactic for [box_e], not intended to be directly called by the user. *)

Ltac box_e H H1:= match goal with | [ |- (_ ?w) ] => box_elim H w H1 end.

Example box_e_eg : forall w1 w2 p, r w1 w2 -> (box p) w1 -> p w2.
Proof.
intros.
box_e H0 H1.
(** The call of [box_e] adds [p w2] to the list of hypothesis, and the requirement [r w1 w2] is automatically solved. *)

exact H1.
Qed.

(** *** Diamond introduction *)
Ltac dia_i w := (exists w; split; [assumption | idtac]).

Example dia_i_eg : forall w1 w2, forall p:o, r w1 w2 -> p w2 -> (dia p) w1.
Proof.
intros.
dia_i w2.
(** The call of [dia_i] transforms the goal from [dia p w1] to [p w2], automatically checking that [w2] is reachable from [w1]. *)

exact H0.
Qed.

(** *** Diamond elimination *)
Ltac dia_e H := let w := fresh "w" in let R := fresh "R" in
(destruct H as [w [R H]]; move w at top; move R at top).

Example dia_e_eg : forall p w, (dia p) w -> exists w0, p w0.
Proof.
intros.
dia_e H.
(** The call of [dia_e] introduces a new arbitrary world [w], and another arbitrary world [w0] accessible from [w] where [p] is true. *)

exists w0.
exact H.
Qed.

(** ** Examples *)
(** With the embedding as well as useful tactics defined, standard modal logic lemmas can now be proven here. *)

Lemma example1 : forall p q, [box ( p m/\ q ) m<-> (box p m/\ box q)].
Proof.
intros.
mv.
split.
  - intros.
    split.
      + box_i.
        box_e H H1.
        destruct H1.
        exact H0.
      + (** Similarly, *) box_i. box_e H H1. destruct H1. exact H1.
  - split.
      + destruct H. box_e H H2. exact H2.
      + (** Similarly, *) destruct H. box_e H1 H2. exact H2.
Qed.

(** %\vspace{0.4cm}%*)

Lemma example2 : [mforall p, dia p m-> (m~ (box (m~ p)))].
Proof.
mv.
intro.
intro.
dia_e H.
intro.
assert( (m~ x) w0).
box_e H0 H1.
exact H1.
contradiction.
Qed.

(* begin hide *)
End Modal.
(* end hide *)
(** * Coq formalisation of bi-modal logic *)
(** %\emph{The formalisation given below relates to an early unsuccessful version of our attempt to formalise the Martin-\Loef{} Theorem.}% *)
(* begin hide *)
Module BiModal.
(* end hide *)

(** The modal logic described in the Benzmuller and Paleo paper was adapted to be a bi-modal logic in line with the intention to formalise the Martin-%\Loef{}% theorem. *)

(** ** Defining the embedding of bi-modal logic in Coq *)

(** All the definitions from the Benzmuller and Paleo modal logic embedding%~\cite{benzmuller}% in the previous section are used, in addition to new definitions which extend it to a bi-modal logic. *)

(* begin hide *)
Parameter i: Type. (** Type for worlds *)
Parameter u: Type. (** Type for individuals *)
Definition o := i -> Prop. (** Type of modal propositions *)

Parameter r: i -> i -> Prop. (** Accessibility relation for worlds (possible,necessary) *)

Definition mnot (p: o)(w: i) := ~ (p w).
Notation "m~ p" := (mnot p) (at level 74, right associativity).
Definition mand (p q:o)(w: i) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).
Definition mor (p q:o)(w: i) := (p w) \/ (q w).
Notation "p m\/ q" := (mor p q) (at level 79, right associativity).
Definition mimplies (p q:o)(w:i) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).
Definition mequiv (p q:o)(w:i) := (p w) <-> (q w).
Notation "p m<-> q" := (mequiv p q) (at level 99, right associativity).
Definition mequal (x y: u)(w: i) := x = y.
Notation "x m= y" := (mequal x y) (at level 99, right associativity).

Definition A {t: Type}(p: t -> o)(w: i) := forall x, p x w.
Notation "'mforall' x , p" := (A (fun x => p))
(at level 200, x ident, right associativity) : type_scope.
Notation "'mforall' x : t , p" := (A (fun x:t => p))
(at level 200, x ident, right associativity,
format "'[' 'mforall' '/ ' x : t , '/ ' p ']'")
: type_scope.
Definition E {t: Type}(p: t -> o)(w: i) := exists x, p x w.
Notation "'mexists' x , p" := (E (fun x => p))
(at level 200, x ident, right associativity) : type_scope.
Notation "'mexists' x : t , p" := (E (fun x:t => p))
(at level 200, x ident, right associativity,
format "'[' 'mexists' '/ ' x : t , '/ ' p ']'")
: type_scope.

Definition box (p: o) := fun w => forall w1, (r w w1) -> (p w1).
Definition dia (p: o) := fun w => exists w1, (r w w1) /\ (p w1).

Definition V (p: o) := forall w, p w. (** Validity *)

Notation "[ p ]" := (V p).

(** Tactics: *)

Ltac box_i := let w := fresh "w" in let R := fresh "R"
in (intro w at top; intro R at top).

Ltac box_elim H w1 H1 := match type of H with
((box ?p) ?w) => cut (p w1);
[intros H1 | (apply (H w1); try assumption)] end.
Ltac box_e H H1:= match goal with | [ |- (_ ?w) ] => box_elim H w H1 end.

Ltac dia_e H := let w := fresh "w" in let R := fresh "R" in
(destruct H as [w [R H]]; move w at top; move R at top).

Ltac dia_i w := (exists w; split; [assumption | idtac]).

Ltac mv := match goal with [|- (V _)] => intro end.
(* end hide *)

(** The following definitions are added to extend the logic to be bi-modal. The definitions for [K] and [B] mirror [box] and [dia] respectively. *)

Parameter rkb : i -> i -> Prop. (** Similarly to with [r], here we declare/assume a function/predicate of arity 2 defined over worlds, to be the accessibility relation for for worlds, for knowledge and belief. For bi-modal logic, [r] is the accessibility relation just for [box] and [dia]. *)

Definition K (p: o) := fun w => forall w1, (rkb w w1) -> (p w1).
Definition B (p: o) := fun w => exists w1, (rkb w w1) /\ (p w1).

(** Axioms about the accessibility relation are also added to match definitions in the model. *)
Axiom reflexivity: forall w, r w w.
Axiom reflexivitykb: forall w, rkb w w.
Axiom RksubsetRbox: forall w1 w2, rkb w1 w2 -> r w1 w2.
Axiom accurate_reasoner: forall w, forall p:o, B p w -> p w.

(** --------------- *)
(** As before, only the definitions above affect what propositions can be expressed and proven in this embedding of a bi-modal logic. The tactics below only increase the usability. *)
(** --------------- *)


(** ** Increasing usability by defining tactics *)
(** The tactics defined here mirror those defined for [box] and [dia] and would be used similarly. *)


Ltac K_i := let w := fresh "w" in let R := fresh "R"
in (intro w at top; intro R at top).

Ltac K_elim H w1 H1 := match type of H with
((K ?p) ?w) => cut (p w1);
[intros H1 | (apply (H w1); try assumption)] end.
Ltac K_e H H1:= match goal with | [ |- (_ ?w) ] => K_elim H w H1 end.

Ltac B_e H := let w := fresh "w" in let R := fresh "R" in
(destruct H as [w [R H]]; move w at top; move R at top).

Ltac B_i w := (exists w; split; [assumption | idtac]).

(** ** Examples *)
Lemma example1 : forall p, [K p m-> p]. (** i.e. [K p -> p] is valid. *)

Proof.
intro.
mv.
intro.
K_e H H1.
exact H1.
apply reflexivitykb.
Qed.

(* %\vspace{0.4cm}% *)

Lemma example2 : forall p w1, (B p) w1 -> exists w2, (dia p) w2. (** i.e. if [B p] is true at some world then there exists a world where [dia p] is true. *)

Proof.
intros.
B_e H.
apply RksubsetRbox in R.
exists w1.
dia_i w.
exact H.
Qed.

(** ** The Third Law *)

(** The Third Law of the Martin-%\Loef{}% theorem can be expressed in this bi-modal logic as below. An important consideration is whether the definitions above capture the meaning of the theorem, in particular whether the formally defined meanings of [dia] and [K] when used together capture the notion "can be known". *)

(** Informally, Martin-%\Loef{}%'s Third Law states %\emph{"From the unknowability of the truth of a proposition, its falsity may be inferred"}%%~\cite[p.~12]{ml}%. This can potentially be captured formally as given below. *)

(** Tentative *) Theorem Third_Law : [mforall A, m~ (dia (K A)) m-> (dia (K (m~ A)))].
Proof.
Abort. (** A proof is not given here, further work may resolve whether this is provable. *)

(* begin hide *)
End BiModal.
(* end hide *)
