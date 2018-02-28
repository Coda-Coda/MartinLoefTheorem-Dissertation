(** printing False $\bot$ *)
(** printing dia $\Diamond$ *)
(** printing box $\square$ *)

(** %\chapter{Formalising the Martin-\Loef{} Theorem - Challenges and Failed Attempts}% *)

(** * A challenge - double negation elimination and the completeness of intuitionistic logic *)

(** The completeness theorems for intuitionistic logic can easily be thought to imply that for every intuitionistic formula, there either exists a proof of it, or a proof of its negation. This is what one might expect from the notion of completeness for classical propositional logic, for example, but this is not something that the completeness theorems for intuitionistic logic imply. *)

(** We can best demonstrate this by noting that neither [( ~ ~ q -> q)] nor [ ~ ( ~ ~ q -> q)] are intuitionistically provable. Thus there is a formula for which neither it nor its negation is intuitionistically provable. *)

(** Below, further details are given to show this is the case, and then the completeness theorems for intuitionistic logic are discussed in relation to this. We find that the intuitionistic completeness theorems do not mean that there don't exist formulae with neither a proof of themselves nor of their negation, so in some sense these theorems are weaker than their classical counterparts. *)

(** ** Example: double negation elimination *)

(** *** [ ( ~ ~ q ->  q) ] is not intuitionistically provable *)

(** This we know because of an understanding of the definitions of the inference rules of intuitionistic logic, or by formal analysis of what is provable using some semantics. Essentially, if it were intuitionistically provable, then intuitionistic logic would be no different from classical logic in what is provable. Double negation elimination is equivalent (both classically and intuitionistically) to the law of the excluded middle, which is commonly pointed to as specifically something that is not intuitionistically provable and which separates intuitionistic logic from classical logic. *)

(** Because of such reasons, it is clear that [ ( ~ ~ q ->  q) ] is not intuitionistically provable. *)

(** *** [ ~ ( ~ ~ q ->  q) ] is not intuitionistically provable *)

(** There are a number of ways to show this, a few are given here. *)

(** %\vspace{1em}% *)
(** (1) %\emph{%Because if it were, then %$\bot{}$% would be provable:%}% *)

(** For example, below is a Coq proof of [ ( ~ ( ~ ~ q ->  q) ) -> False ]. *)

Parameter q:Prop. (** Let [q] be an arbitrary proposition. %\\% *)
Lemma double_neg_example : ( ~ ( ~ ~ q ->  q) ) -> False.
Proof. firstorder. Qed. (** Coq is able to automatically verify this lemma. Note that Coq's core logic which is being used here is intuitionistic. %\\% *)

(** We can do the same proof more manually using Coq as shown below.  %\\%  *)
Lemma double_neg_example' : ( ~ ( ~ ~ q ->  q) ) -> False.
Proof.
unfold not.
intros. apply H.
intros. exfalso. apply H0.
intros. apply H.
intros. apply H1.
Qed.

(** (2) %\emph{%As an alternative, here is a natural deduction-style proof of the same result:%}%  *)

(** The natural deduction-style proof below mimics the reasoning of the Coq proof above. It makes use only of intuitionistically valid inference rules. *)

(** %
\begin{figure}[H]
  \centering
	\includegraphics[width=0.6\linewidth]{ndproof1}
	\caption{NJ proof, created using the Natural Deduction Planner by Declan Thompson~\cite{ndplanner}.}
	\label{NJ proof}
\end{figure}
% *)


(** The above three proofs show that [ ~ ~ ( ~ ~ q ->  q) ] is intuitionistically provable. This implies that [ ~ ( ~ ~ q ->  q) ] is not intuitionistically provable because if it were, we would clearly then have a proof for %$\bot$% which is not possible. Thus [ ~ ( ~ ~ q ->  q) ] is not intuitionistically provable. %\\% *)

(** (3) %\emph{%Other results which show that double negation elimination is unprovable intuitionistically: %}%  %\vspace{0.2cm}%  *)


(** We can also see this is the case using the fact that every intuitionistic tautology is a classical tautology, and so if [ ~ ( ~ ~ q ->  q) ] was intuitionistically provable then it would be classically provable, but it is classically false. Thus [ ~ ( ~ ~ q ->  q) ] is not intuitionistically provable. %\\% *)
(** One additional way, would be to use Glivenko's Theorem%~\cite{intuitionisticLogicStanford}%, using the fact that [p] is classically true iff [ ~ ~ p] is intuitionistically provable. Thus [ ~ ~ ( ~ ~ q ->  q) ] is intuitionistically provable, because [( ~ ~ q ->  q) ] is a classical tautology. So as before, [~ ( ~ ~ q ->  q) ] is not intuitionistically provable. *)


(** ** Completeness theorems *)

(** Completeness is a notion which in some sense does differ in meaning between classical%~\cite[p.~46]{completenessGodel, completenessBritannica, completenessDirk}% and intuitionistic%~\cite[p.~171]{intuitionisticLogicStanford, completenessDirk}% contexts, although it also retains many aspects of its meaning. One example of a difference is that in classical logic if some system is complete, then we can conclude that for every formula either it or its negation is provable. This however, is not the definition of completeness, but rather a consequence of it in classical contexts. For instance, in classical propositional logic, the fact that it is complete is generally defined to mean that every formula that is valid semantically is provable. For classical logic this then means that if we take an arbitrary formula, we can show that either it or its negation must be provable as follows, the key being the fact that $p \vee \lnot p$ is valid in classical logic for all propositions. %\\% *)

(** Consider classical propositional logic, with semantics and provability (or deduction) defined such as in the Stanford Encyclopedia of Philosophy article on classical logic%~\cite{sep-logic-classical}%. %\\%
Here, if a formula [p] is valid semantically this is denoted by $\vDash p$. If a formula [q] is provable this is denoted $\vdash q$. *)

(** %\vspace{1em}%
Classical propositional logic is complete, so every valid formula is provable, if $\vDash p$ then $\vdash p$.
%\begin{enumerate} \setlength{\itemsep}{0pt} \setlength{\parskip}{0pt}%
  %\item% Let $p$ be an arbitrary propositional formula.
  %\item% [p \/ ~p] is valid, $\vDash$ [(p \/ ~p)]
  %\item% Thus, by the definition of satisfaction, $\vDash$ [p] or $\vDash$ [~p]
  %\item% Suppose $\vDash$ [p]
     %\vspace{-0.5\topsep} \begin{enumerate} \setlength{\itemsep}{0pt} \setlength{\parskip}{0pt}%
     %\item[a.]% Then, by completeness we have that $\vdash$ [p] so [p] is provable. We are done. (Either [p] or [~p] is provable.)
     %\end{enumerate}%
  %\item% Suppose $\vDash$ [~p]
     %\vspace{-0.5\topsep} \begin{enumerate} \setlength{\itemsep}{0pt} \setlength{\parskip}{0pt}%
     %\item[a.]% Then, by completeness we have that $\vdash$ [~p] so [~p] is provable. We are done. (Either [p] or [~p] is provable.)
     %\end{enumerate}%
  %\item% Therefore either [p] or [~p] is provable.
%\end{enumerate}%
 *)

(** We see here that completeness for classical logic implies that for every $p$, either $p$ or $ \lnot p$ is provable.
For intuitionistic logic however, since we relied on $p \vee \lnot p$ as being valid in step 2 the above reasoning would not work since $p \vee \lnot p$ is not valid in intuitionistic logic. %\\% 
Clarifying this was helpful in the process of gaining a greater understanding of the key notions of the Martin-%\Loef{}% Theorem.

*)

(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)
(* --------------------------------- *)


(** * Failed attempts *)

(** The Martin-%\Loef{}% theorem considers all notions with regards to "the intuitionistic conception"%~\cite[p.~4]{ml}% and so it seems plausible that formalising the theorem in a way which works solely with intuitionistic proofs might best capture the ideas in Martin-%\Loef{}%'s proof. Coq's core logic itself is intuitionistic and embodies many of the notions expressed in relation to the Martin-%\Loef{}% theorem. This section explores two failed attempts at using Coq's default intuitionistic logic to formalise key notions of the Martin-%\Loef{}% Theorem. *)

(** ** A failed Coq formalisation that oversimplifies the notion `undecidable' *)
(** In Martin-%\Loef{}%'s paper%~\cite{ml}%, the conclusion is that there are no absolutely undecidable propositions, on the intuitionistic interpretation. A key step in formalising the theorem is to adequately represent the statement of the conclusion formally. *)


(** *** A possible definition of `absolutely undecidable': *)

(* begin hide *)
Module definition1.
(* end hide *)

(** **** An absolutely undecidable proposition has no proof or disproof. *)

(** This appears to be the most natural way to define `absolutely undecidable', but it is important to bear in mind the proposition [ ~ ~ q -> q ] as discussed in section 4.1. In Coq this definition could be formalised as follows: *)


Definition absolutely_undecidable (p : Prop) : Prop := ~ ((exists (pf : p), True) \/ (exists (pf : ~ p), True)).

(** An immediate issue with this formalisation of the notion `absolutely undecidable' is that in Coq (by default) the negation is intuitionistic. As a result the definition above does not correctly capture the meaning of `no' in the notion `no proof or disproof'. *) 

(** Another possible issue is that the definition is very similar to [forall p, ~ (p \/ ~ p)] which seems to oversimplify the notion it is attempting to capture. This is shown by the lemmas below. *)

(** First we proof that there exists a proof of [p] if and only if [p] is true. *)

Lemma proof_exists_iff_true : forall p:Prop, (exists pf:p, True) <-> p.
Proof.
split.
 - intros. destruct H. exact x.
 - intros. exists H. apply I.
Qed.

(* begin hide *)
Require Import Setoid.
(* end hide *)

(** Now we can show that [absolutely_undecidable p] is equivalent to [~ (p \/ ~ p)]. This is not necessarily a problem, as it may only be showing that [absolutely_undecidable p] is false (since [~ (p \/ ~ p)] is false). But of concern is the simplicity of the proof, which highlights that [absolutely_undecidable p] may have a similar _meaning_ to [~ (p \/ ~ p)]. This would seem to be an oversimplification of the intended meaning of the notion `absolutely undecidable'. *)

Lemma absolutely_undecidable_is_oversimplified : 
  forall p, absolutely_undecidable p <-> ~ (p \/ ~ p).
Proof.
intros. 
unfold absolutely_undecidable.
rewrite! proof_exists_iff_true.
split. intros. exact H. intros. exact H.
Qed.

(** We can define here the conclusion of the Martin-%\Loef{}% Theorem: that there are no absolutely undecidable propositions. However, as shown below, in this formalisation the statement is equivalent to [forall p, ~ ( ~ (p \/ ~ p))] by a fairly simple proof. This, again, appears to potentially hint that the notion it is trying to formalise has been oversimplified. The meaning of the statement of the Martin-%\Loef{}% Theorem in this formalisation would be just the meaning of [forall p, ~ ( ~ (p \/ ~ p))] or close to it. *)

Definition ML_theorem := forall p, ~ (absolutely_undecidable p).

Lemma ML_theorem_equivalence : ML_theorem <-> forall p, ~ ( ~ (p \/ ~ p)).
Proof.
unfold ML_theorem.
split.
 - intros. pose proof H p. rewrite absolutely_undecidable_is_oversimplified in H0. exact H0.
 - intros. rewrite absolutely_undecidable_is_oversimplified. apply H.
Qed.

(** Further work would be needed to confirm that this oversimplification is definitely an issue, but it does seem to be problematic. *)


(** ** A failed Coq formalisation that oversimplifies the notion `knowable' *)

(** Here a formalisation is given of the key notion of knowability. This is then extended to a formalisation of Martin-%\Loef{}%'s Third Law. The key issue is that the meaning of the Third Law in this formalisation is closest to "if a proposition is false then that proposition is false" rather than it's expected meaning: "if a proposition cannot be known to be true then it can be known to be false."%~\cite[p.~10]{ml}% *)


(** *** Definitions *)
(** In Coq and in intuitionistic logic more generally, a proposition is true, by definition, iff there exists a proof for it. The precise meaning of "exists" can be debated, but the general idea remains. So a Coq lemma of the form [forall p q, p <-> q] can be taken to mean for all propositions [p] is true iff [q] is true, or it can be taken to mean [p] has a proof iff [q] has a proof. (Or a mixture: [p] is true iff [q] has a proof). %\par% *)
(** With this in mind, we can define knowability, [K], as follows *)

Definition K (p : Prop) : Prop := p. (** Meaning, [K(p)] = `[p] has a proof.' *)

(** This definition of [K] means [ ~ K(p)] = `[(p -> False)] has a proof' as shown in the lemma below. *)

Lemma not_Kp : forall p, ( ~ K p) = (p -> False).
Proof. firstorder. (** Trivially. *) Qed.

(** That [p -> False] has a proof means that we have an algorithm which takes a proof of [p] and gives a proof of [False]. So, [ ~ K(p)] means there is an algorithm which takes a proof of [p] and gives a proof of [False]. %\par% *)
(** It is important to note that [ ~ K(p) ] $\neq$ `p has no proof', because, as mentioned before, it is possible for a formula to have no proof and also its negation to have no proof (e.g. [ ~ ~ q -> q ] ). *)

(** Martin-%\Loef{}%'s Third Law can be formalised using these definitions, however issues arise as discussed below. The Third Law states that "if a proposition cannot be known to be true then it can be known to be false."%~\cite[p.~10]{ml}% *)


Definition ML_Third_Law := forall p, ( ~ K p) -> K ( ~ p).

Lemma problem_with_MLThirdLaw : ML_Third_Law = forall p, ( ~ p -> ~ p).
Proof. 
unfold ML_Third_Law.
unfold K.
reflexivity.
Qed.

(** The above lemma shows that the [ML_Third_Law] statement is in fact the _same_ proposition as [forall p, ( ~ p -> ~ p )] (not merely equivalent to it). When the definition of [K] is unpacked the statement of the theorem becomes exactly [forall p, ( ~ p -> ~ p )]. This shows that the meaning of the [ML_Third_Law] in this formalisation is that if there exists a proof for [ ~ p] then there exists a proof for [ ~ p]. This appears to be much weaker than the intended meaning: "if a proposition cannot be known to be true then it can be known to be false."%~\cite[p.~10]{ml}% %\par% *)
