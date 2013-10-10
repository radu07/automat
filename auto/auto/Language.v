Load FinSets.
Require Import Bool. 
Require Import Arith. 
Require Import List.
Require Import Notations.
 
(*A finite set is described using an inductive definition, using 2 constructors.*)

Definition El:=Fin. 

(*A word is a list of elements *)
Variable Alphabet : nat.
(*Variable Sigma : Alphabet. *) 
(*A word is a list of elements *)
Definition Word := list (El Alphabet).

Definition Language := Word  -> Prop.
(**empty word/string *)
Definition eps :Word :=nil.

(**empty word/string *)
Definition lang_conc(l1:Language)(l2:Language):Language :=
    fun w:Word => exists w1:Word, exists w2:Word,  w1 ++ w2=w /\ l1 w1 /\ l2 w2.

Definition lang_union (l1:Language)(l2:Language):Language :=
    fun w:Word =>  l1 w \/ l2 w.

(* empty language imply [False] *)
Definition empty_lang :Language:= fun w:Word=>False.


(** A language included into another language *)
Definition Included (l1:Language)(l2:Language) :Prop := forall (w:Word), l1 w -> l2 w.
Check Included.

Definition eps_lang :Language := fun w:Word => match w with 
   |nil => True
  | _  => False
   end.

(* L1 conc empty = empty *)
Lemma empty_lr : forall (l1:Language)(w:Word) ,  (lang_conc l1 empty_lang) w<->  empty_lang w.
intros.
unfold iff.
split.
simpl.
intro.
unfold lang_conc in H.
destruct H.
destruct H.
destruct H.
destruct H0.
simpl.
simpl in H1.
unfold empty_lang.
unfold empty_lang in H1.
destruct H1.
intro.

unfold empty_lang in H.
destruct H.
Qed.

Definition In_lang(w:Word)(l:Language) := l w.
(* use the properties of existence quantifier to attribute the right values
to the words *)

(** distributivity property *)
Lemma distrib : forall (l1 l2 l3 :Language) (w:Word), In_lang w (lang_conc l1 (lang_union l2 l3)) <-> In_lang w (lang_union (lang_conc l1 l2) (lang_conc l1 l3)).
(** -> *)

intros.
unfold iff.
split.
intro.
unfold In_lang.
unfold In_lang in H.
unfold lang_conc.
unfold lang_union.
unfold lang_conc in H.
unfold lang_union in H.
destruct H.
destruct H.
destruct H.

(* use the properties of existence quantifier to attribute the right values
to the words *)
destruct H0.
destruct H1.
left.
exists x.
exists x0.
split.
assumption.
split.
assumption.
assumption.
right.
exists x.
exists x0.
split.
exact H.
split.
assumption.
assumption.

(**  <- *)
intro.
unfold In_lang in H.
unfold lang_union in H.
unfold lang_conc in H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
unfold In_lang.
unfold lang_conc.
unfold lang_union.
exists x.
exists x0.
split.
exact H.
split.
exact H0.
left.
exact H1.


destruct H.
destruct H.
destruct H.
destruct H0.
unfold In_lang.
unfold lang_conc.
exists x.
exists x0.
split.
exact H.
split.
exact H0.
unfold lang_union.
right.
exact H1.
Qed.

Variable x:Word.

Lemma eps_implies_nil : forall (w:Word) , eps_lang w -> w=nil.
intros.
induction w.
reflexivity.
unfold eps_lang in H.
destruct H.
Qed.
(** Found in the List library *)
Theorem app_l_nil :  forall (A : Set)(l : list A),
  l ++ nil = l.
intros A l.
induction l.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

(* L conc epsilon = L *)

Theorem lang_conc_neutral_left : forall (l:Language)(w:Word), In_lang w (lang_conc l eps_lang) <-> In_lang w l.
intros.
unfold iff.
split.
intro.
unfold In_lang.
unfold In_lang in H.
unfold lang_conc in H.
destruct H.
destruct H.
destruct H.
destruct H0.
rewrite <-H.
assert (x1 = nil).
apply eps_implies_nil.
exact H1.
rewrite H2.
simpl.
rewrite app_l_nil.
exact H0.

intro.
unfold In_lang.
unfold In_lang in H.
unfold lang_conc.
exists w. 
exists nil.
split.
rewrite app_l_nil.
reflexivity.
split.
exact H.
split.
Qed.


(** epsilon language belongs to L*, if L belongs to the powerset of the word , L* bleongs to the
powerset of the word (using concatenation) *)

Inductive Star(x:Language) : Language := 
  | nil0: (Star x) nil
  | cons0 : forall (a: Word)(b:Word),Star x a /\ x b -> Star x (app a b).


(** the power of a language L : L^n = LLLL...L n times *)
Fixpoint lang_power (l:Language)(n:nat) : Language := 
     match n with 
     | 0 => eps_lang
     | S n => lang_conc l (lang_power l n)
     end.

(** L1 conc(L2 conc L3) =(L1 conc L2) conc L3 
assume w= v0++ v1, v0 in L1
v1 in L2 conc L3
v1 = v2++v3,
v2 in L2 /\ v3 in L3,
w = v0++(v2++v3) = (v0++ v2)++v3 (associativity of lists) in L1 L2 L4
*)
Axiom app_ao : forall (A:Set)(l1 l2 l3 : list A) , l1 ++ app l2 l3 = (l1 ++ l2) ++ l3.
Lemma ab : forall (A:Set) (l1 l2 : list A) ,  app l1 l2 = l1 ++ l2.
intros.
reflexivity.
Qed.
Lemma abc : forall (A:Set) (l1 l2 l3: list A), app l1 l2 ++ l3 = l1 ++ (l2 ++l3).
intros.
simpl.
admit.
Qed.
Lemma lang_assoc : forall (l1 l2 l3:Language)(w:Word), In_lang w (lang_conc l1 (lang_conc l2 l3)) <-> In_lang w (lang_conc (lang_conc l1 l2) l3).


intros.
unfold iff.
split.
intro.
unfold In in H.

unfold In_lang.
unfold lang_conc.
unfold lang_conc in H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
assert( In_lang x1 (lang_conc l2 l3)).
unfold In_lang.
unfold lang_conc.
exists x2.
exists x3.
split.
exact H1.
split.
assumption.
assumption.
rewrite <-H1 in H.


rewrite app_ao in H.
exists (x0 ++ x2).
exists x3.
split.

rewrite <-H.
simpl.
admit.
(* Coq does not recognise app x0 x2 ++ x3 as (x0 ++ x2) ++ x3 ??*)
split.
exists x0.
exists x2.
split.
reflexivity.
split.
assumption.
assumption.
exact H3.

intro.
unfold In.
unfold In in H.
unfold lang_conc.
unfold lang_conc in H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H2.

rewrite <-H0 in H.
rewrite abc in H.
exists x2.
exists (x3++ x1).
split. (* x2 ++ app x3 x1 *)
admit. 
split.
exact H2.

exists x3.
exists x1.
split.
reflexivity.
split.
assumption.
assumption.
Qed.

(** Star (Star L) = Star l.  we will prove this by using *) 
 Lemma kleene1 : forall (l:Language) (w:Word), In_lang w (Star l) ->In_lang w (Star (Star l)).

unfold In_lang.
intros.
rewrite <- app_nil_l.
assert (Star (Star l) nil).
apply (nil0 ).
assert ((Star (Star l) nil) /\ ((Star l) w)).
split.
assumption.
assumption.
apply (cons0) in H1.
exact H1.
Qed.

Axiom nil_O_r : forall (A:Set)(l:list A), l++nil = l.
Lemma lem : forall ( l:Language) (a b : Word) , In_lang a (Star l) /\ In_lang b (Star l) -> In_lang (a ++ b) (Star l).

intros.
unfold In_lang.
unfold In_lang in H.
destruct H.
induction H0.
simpl.
rewrite nil_O_r.
assumption.
Print Star.
assert(Star l (a0 ++b )).
apply cons0.
assumption.
destruct H0.



intros.
unfold In_lang in H.
unfold In_lang.
destruct H.

induction H.
simpl.
exact H0.

Print Star.

assert(Star l (a++b0)).
apply cons0.
exact H.
destruct H.
assert (Star l b0).

Print Star.
(*induction H0.
simpl.
admit.
simpl.


apply cons0.
split.
destruct H.
exact H.
destruct H.*) 
admit.
Qed.

Lemma kleene2: forall (l:Language)(w:Word), In_lang w (Star(Star l)) -> In_lang w (Star l).
intros.
unfold In_lang.
unfold In_lang in H.
induction w.
simpl.
apply nil0.
destruct H.
apply nil0.
destruct H.

apply cons0.
split.


induction H.


apply nil0.
destruct H.



 
assert(Star (Star l) (a++b)).
apply cons0.
split.
assumption.
assumption.
assert(Star(Star l) b).
apply kleene1.
unfold In_lang.
exact H0.
induction H.
simpl.
assumption.
destruct H.
assert (Star l (b0 ++ b)).
apply lem.
unfold In_lang.
split.
assumption.
assumption.



induction a.
simpl.
exact H4.

Print Star.

destruct H.
simpl.
assumption.
destruct H.



induction H0.
simpl.
assert(a++nil = a).
admit.
rewrite H0.

induction H.







induction H.
exact (nil0 l).
assert(Star (Star l ) (a++b)).
apply cons0.
assumption.

Print Star.

destruct H.
induction H.
simpl.
assumption.
destruct H.
assert(Star l (b0++b)).
apply lem.
unfold In_lang.
split.
assumption.
assumption.
admit.
(*
induction H0.
assert (a++ nil = a).
admit.
rewrite H0.
induction H.
apply nil0.
apply cons0.
split. *)


induction H.
simpl.
exact H0.
Print Star.

assert(Star l (a++b0)).
destruct H.


assert (Star (Star l) (a ++ b0)).
apply cons0.
exact H.
Print Star.

assert (Star (Star l) b).
apply kleene1.
unfold In_lang.
exact H0.
Print Star.



induction H.
simpl.
exact H0.

apply cons0.
