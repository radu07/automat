Require Import Bool.
 
(*Load Arith.*)
Require Import Arith.
Require Import Mult.
Require Import List.
Require Import Logic.

Set Implicit Arguments.
Definition Alphabet := nat.
Inductive Fin : nat -> Type :=
| f0 : forall n, Fin (S n)
| fs : forall n, Fin n -> Fin (S n).

Lemma fin_isnotzero : forall (n:nat), Fin n -> match n with 
                                   | 0 => False
                                   | _ => True
                                       end.
intros.
induction H.
split.
split.
Qed.

Lemma fin0empty : Fin 0 -> False.
intro.
apply(fin_isnotzero H).
Qed.

(**  * Coproducts : *)
Definition addfin : forall (m n : nat) , Fin m + Fin n -> Fin (m+n).
intros.
destruct H.
induction f.
simpl.
apply (f0 (n0+ n)).
simpl.
apply (f0 (n0+n)).
simpl.
induction n.
apply fin0empty in f.
destruct f.
simpl.
assert(m+S n = S(m+n)).
auto.
rewrite H.
apply (f0 (m+n)).

Defined.



Definition addfin1 : forall (m n : nat), Fin (m+n) -> Fin m + Fin n.
induction n.
intros.
simpl.
assert(  m + 0 = m).
auto with arith.
rewrite H0 in H.
tauto.

(*
exact(inl H). *)
intros.
Check (f0 n).
simpl in *.
assert(m+S n = S(m+n)).
auto.

rewrite H0 in H.
assert (Fin (S n)).
apply (f0 n).
Check inr.
tauto.

(*

apply (inr (H1)). *)
Defined. 

Definition isoadd1 : forall (m n :nat),
    (Fin m + Fin n -> Fin (m+n)) -> (Fin (m+n) -> Fin m+ Fin n) -> (Fin m+ Fin n -> Fin m + Fin n).

intros.
apply H0.
apply H.
assumption.
Qed.


Definition isoadd2: forall (m n:nat),
  (Fin (m+n) -> Fin m + Fin n) -> (Fin m+Fin n-> Fin (m+n)) -> (Fin (m+n) -> Fin (m+n)).
intros.
apply H0.
apply H.
exact H1.
Qed. 

Definition finl : forall (m n : nat) , Fin m -> Fin (m+n).
intros.
induction n.
simpl.
rewrite<- plus_n_O.
exact H.
simpl.
rewrite<-plus_n_Sm.
exact (fs IHn).
Defined.
Definition finr : forall ( m n : nat), Fin n -> Fin (m+n).
intros.
induction m.
simpl.
exact H.
simpl.
apply (fs IHm).
Defined.

  Inductive FinPlus ( m n: nat) : Fin (m + n) -> Set:=
         | fsinl : forall i: Fin m , (FinPlus m n (finl n i))
         | fsinr : forall j: Fin n, FinPlus m n (finr m j) .

Print FinPlus.


(** * Products *)
Definition fst : forall (m n : nat) , Fin (m*n)-> Fin m.
intros.
induction m.
rewrite mult_0_l in H.
exact H.
simpl in H.
exact (f0 m).
Defined.

Definition snd: forall (m n : nat) , Fin (m*n) -> Fin n.
intros.
induction n.
rewrite  mult_0_r in H.
assumption.
exact (f0 n).
Defined.
Print fst.
Print snd.
Definition timesfin : forall (m n : nat) , Fin m * Fin n -> Fin (m*n) .

intros.
destruct H.

induction m.

rewrite mult_0_l .
exact f.
simpl.
apply finl.
exact f1.
Defined.

Definition timesfin1: forall (n m : nat) , Fin (m*n) -> Fin m * Fin n.
induction n.
simpl.
simpl.
intro.
assert(m*0 =0).
auto with arith.
rewrite H.
intro.
apply fin0empty in H0.
destruct H0.
intros.
assert(Fin m).
apply (fst  m (S n)).
exact H.
Show Proof.
intuition.
Show Proof.
apply (snd m (S n)).
exact H.
Defined.

Definition isomul1 : forall (m n: nat),
   (Fin m * Fin n -> Fin (m*n)) -> (Fin (m*n) -> Fin m * Fin n) -> (Fin m * Fin n -> Fin m * Fin n).

intros.
apply H0.
apply H.
exact H1.
Qed.

Definition isomul2 : forall (m n : nat),
   (Fin (m*n) ->Fin m * Fin n) -> (Fin m * Fin n -> Fin (m*n)) -> (Fin (m*n) -> Fin (m*n)).
intros.
apply H0.
apply H.
exact H1.
Qed.


Definition fincase : forall (m n p: nat) , (Fin m -> Fin p) -> (Fin n -> Fin p ) ->(Fin (m+n) -> Fin p). 

intros.
apply addfin1 in H1.
destruct H1.
apply H.
exact f.
apply H0.
exact f.
Defined.

(** Function composition *)
Lemma comp : forall (m n p :nat) , (Fin m ->Fin m + Fin n) -> (Fin m+ Fin n -> Fin p) ->
         (Fin m -> Fin p).
intros m n p in1 fg f.
apply fg.
apply in1.
exact f.
Defined.

  

Lemma comp1 : forall (m n p:nat), (Fin n ->Fin m + Fin n) ->
    (Fin m+ Fin n-> Fin p) -> (Fin n -> Fin p).
intros m n p in2 fg g.
apply fg.
apply in2.
exact g.
Defined.

(** Distributivity law *)
Definition dist: 
       forall (m n p :nat), Fin ( m * ( n+ p)) -> Fin ( m* n + m * p).
induction m.
intros.
simpl in *.
apply fin0empty in H.
destruct H.
intros.

apply addfin.
rewrite mult_plus_distr_l in H.
apply addfin1 in H.
assumption.
Defined.

Definition dist2 :
    forall (m n p : nat), Fin (m * n + m* p ) -> Fin (m * (n + p)).
induction m.
intros.
simpl in *.
apply fin0empty in H.
destruct H.
intros.
apply addfin1 in H.
rewrite mult_plus_distr_l.
apply addfin.
assumption.
Qed.

(*
 Lemma fin_inl_inject : forall (n m : nat) (i j : Fin n), 
       finl m i = finl m j -> i = j.
induction i.
intros.

simpl in *.
assert( Fin (S n)).

apply (f0 n).

admit.
intros.
assert ( Fin ( m) -> Fin (m + ( n))).
apply (f0 n) .
induction H.

discriminate H.
Lemma finlinj : forall (m n : nat) (i j : Fin n), 
       finl m i = finl n j -> i = j.





*)


Fixpoint exps  (x n :nat):nat :=

       match n with 
       | 0  => 1 
       | S n' =>   mult x (exps x n') 
       end.
Eval compute in (exps 3 2).

Notation " x ^ y " := (exps x y). 
Eval compute in (0 ^9).

Definition existsf1   (n:nat)(p:Fin n -> bool) : bool.
induction n .
exact false.
exact( p (f0 n) || IHn (fun m : Fin n => p (fs m))).
Defined.
Print existsf1.
Check In.


(** Here, we prove the correctness of the existsf1 predicate , by evaluating it to the value
of the exists quantifier in coq. we will also use proving by contradiction, as well as case analysis,
due to the disjunction [p(f0 n) || IHn (fun m : Fin n => p(fs m))] *)


Lemma exss : forall (n:nat)(p:Fin n -> bool), existsf1 p = true -> exists q:Fin n , p q =true.
intros.
induction n.
simpl.
simpl in H.
discriminate H.
simpl in  H.


case_eq ( p (f0 n)).
intro.
exists( f0 (n)).
exact H0.
intro.
rewrite H0 in H.
simpl in H.
apply IHn in H.
destruct H.
exists (fs x).
exact H.
Qed.


Lemma exs : forall (n:nat)(p:Fin n -> bool),(exists q :Fin n, p q = true) ->  existsf1 p = true.
intros.
destruct H.
simpl.
induction x.
simpl.
rewrite H.
simpl.
reflexivity.

case_eq (p (f0 n)).
intro.
simpl.
rewrite H0.
simpl.
reflexivity.
intro.
simpl.
rewrite H0.
simpl.
apply IHx.
exact H.
Qed.
(*

Definition isoex1 :forall (n:nat) (p:Fin n -> bool) *)
(*Definition isoex1 : forall (n : nat)(p : Fin n -> bool)(x: exists q:Fin n , p q = true) ,

   exss  p (exs p x) =x.
intros.
simpl in *.
set (exs p x ).
set (exss p e).

assert(existsf1 p =true -> exists q:Fin n , p q =true).
intros.
exact x.
assert((exists q :Fin n , p q =true) -> existsf1 p = true).
intros.
apply e.
set(exss p e).
intuition.
rewrite H0 in x.
rewrite e0 in x. 



assert( exss p (exs p x) = exists q :Fin n , p q =true).
intros.
Definition isoex1 : forall (n:nat)(p:Fin n -> bool) ,

   (existsf1 p =true -> exists q:Fin n , p q =true) ->

  ((exists q:Fin n , p q = true) -> existsf1 p =true) -> (existsf1 p = true -> existsf1 p = true).
intros.

trivial.

apply H0.


intros.
simpl in *.



*)


    
       
            
(*We eill prove the isomorphism between tha fact that in our proof we can feed into 2 finite 
sets [(Fin m -> Fin n)] and obtain a new finite set with cardinality [Fin (n^m)]

*)


Definition  allexp : forall(m n :nat) , (Fin m -> Fin n ) -> Fin ( n^m).
intros.
induction m.

simpl.
exact (f0 (pred 0)).
(*base case *)
simpl.
eapply timesfin.
(*use the definition of the product Fin m *FIn n -> Fin (m*n)*)
simpl.
induction n.
simpl.
apply timesfin1.
simpl.
apply H.
exact (f0 m).
apply timesfin1.
simpl.
apply finl.
apply IHm.
intro.
apply H.
exact (f0 m).
Defined. 
Print allexp.

Definition es : forall (a b : nat) , Fin (b^a) -> (Fin a -> Fin b ).
intros.
simpl.
induction a.
apply fin0empty in H0.
destruct H0.
simpl in H.
apply timesfin1 in H.
destruct H.
exact f.
Defined.

(*Define an isomorphism between a predicate which contains n elements and the finite set with 2^n elements.
This is used when generating the power automaton. We will apply the lemmas that we have done before. *)

Definition allexp1 : forall (n : nat) , (Fin n -> bool) -> Fin (2^n).
intros.
apply allexp.
intro.
exact (f0 1).
Defined.

Definition allexp2 : forall (n : nat) , Fin (2^n) -> (Fin n -> bool).
intros.
apply (es  2) in H.
exact true.
apply allexp.
intro.
exact (f0 1).
Defined.



Fixpoint equalsf (n m:nat) (p :Fin n) (q: Fin m) : bool := 
    match p with
 | f0 _ => match q with 
          | f0 _ => true
          | _ => false
          end
 | fs _ p' => match q with 
           | f0 _ => false
           | fs _ q' =>  equalsf p' q' 
         end
      end.
Print equalsf.

Definition eqf (n : nat) (p q : Fin n) : bool := equalsf p q.  

Definition eqftoprop (n:nat)(p q :Fin n) : Prop := 
       match eqf p q with 
     | true => True
     | false => False
     end.
(** Apply a finite set case analysis taking 2 functions and check whether is there the element for the [Fin m],

or the element from [Fin n] , that will be selected. From mapping two functions, 
[Fin m -> Fin p] and [Fin n -> Fin p] is a way of "choosing" and therefore we need to use a set
that has cardinality m+n, and see if it will be mapped on Fin p.

*)

Definition finmn : forall (m n :nat), (Fin m + Fin n -> bool ) -> Fin (m+n) -> bool.
intros.
apply H.
apply addfin1 in H0.
assumption.
Defined.
Definition finsum : forall (m n :nat),  Fin m ->  Fin n -> Fin m + Fin n.
intros.
induction m.
apply fin0empty in H.
destruct H.
apply (inl H).
Defined.


Definition finbool :forall (m n :nat), (Fin m -> bool) -> (Fin n -> bool) ->
          Fin (m+n) -> bool.
intros.
induction m.
simpl in *.
exact true.
apply H.
exact (f0 m).
(*
apply IHm.
intro.
apply H.
exact (f0 m).
apply addfin1 in H1.
admit.*)
Defined.

 
Definition finmbool : forall (a:Alphabet) (m n: nat), 
   (Fin m -> bool) -> (Fin (m+n) -> bool).
intros.
induction m.
exact false.
apply H.
exact (f0 m).

Qed.
Definition finpp : forall (a:Alphabet)(m n :nat),
  (Fin m -> Fin a -> Fin (2^m)) ->
      (Fin n -> Fin a -> Fin (2^n)) ->
      Fin (2^ (m+n)).
intros.
apply allexp1.
intro.
apply addfin1 in H1.
induction m.
simpl in H1.
exact false.
apply IHm.
intros.
apply allexp1.
intro.
exact true.
intuition.
apply addfin1.
admit.
Qed.



(*
Definition finpp : forall (a:Alphabet)(m n : nat),
   (Fin m-> Fin a -> Fin (2^m)) ->( Fin n -> Fin a -> Fin (2^n)) ->
   Fin (2 ^m + 2 ^n). 
intros.

induction m.
simpl.
exact (f0 (2^n)).
induction n.
simpl .
simpl in *.
simpl.
simpl.
admit.



intros.
simpl.
induction n.
simpl.
assert (2^m+1 = S(2^m)).
admit.
rewrite H1.
exact (f0 (2^m)).
simpl.
induction m.
simpl.
exact (f0 (add (2^n) (add (2^n) 0))).
simpl.


*)
