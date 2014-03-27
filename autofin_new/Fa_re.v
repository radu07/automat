Section Fatore.

Load Regular.
Set Implicit Arguments.
(** We will use the so-called "Transitive closure" method. We believe that this would be one
of the most viable methods to convert to an algorithm.

The transitive closure method will recursively construct a regular expression that is equivalent
to the given automaton.  We give a regular expression to describe a path between any two states
x and y. Let us consider X to be the set of states to which the automaton is allowed to run
in order to get from x to y. 
If the set X is empty, we consider two cases: 
 - if x<>y , then every transition from x to y contains a singleton word.
The corresponding regular expression consists in the disjunction of all transitions from x to y.
 - if x=y , then the corrseponding regular expression consists in the disjunction of all transition from x to y and
we also have to include epsilon, the empty word.

If the set X is not empty, we will pick an element p from X ; therefore, any run in the path from x 
to y will either pass through p , or will not go through p. If it goes through p, the cases will be split in 3 parts:

  
 *)

(** Let [w] be a word and x in Q. We define the state sequence x1...xn the run from x to w 
if *)

Check (fun a:Alphabet => list(RegExp a)).

Fixpoint foldr1 (a:Alphabet)(f:RegExp a-> RegExp a-> RegExp a)(i:RegExp a) (il : list (RegExp a))  :=
      match il with
        | nil => i
        | cons x il' => f x (foldr1 f i il')
      end.
Check foldr1.
Fixpoint foldr (A B :Type)(f:A ->B->  B) (z:B) (xs: list A) :=

      match xs with
        | nil => z
        | cons x xs' => f x (foldr f z xs')
      end.

Check foldr.
Definition regplus (a:Alphabet)(rs:list(RegExp a)) := foldr (@Plus _)(Empty _)   rs.
(** Compute a function that returns a list of characters that contains all transitions from x to y*)
Check regplus.
Definition trans_dfa (a:Alphabet)(n:nat)(d:dfa n a)(x:Fin n) (y: Fin n) : list(RegExp a):=
      nil.
Check trans_dfa.
Check map.
Definition R0 (n:nat)(a:Alphabet)(d:dfa n a)(x:Fin n) (y:Fin n) := let r:=regplus (trans_dfa d x y) in 
      if eqf x y  then Plus r (Epsilon _) else r.
Definition empset := Fin 0 -> bool.


Fixpoint belast (n:nat)(xs: list (Fin n)) :=
    match xs with
      | nil => nil
      | a:: nil => nil
      | x::xs => x::(belast xs)
    end.
Check all.
Check belast.

(** Let w be a word . Let X be a subset of Q and x,y belong to X*)
Definition forallf1   (n:nat)(p:Fin n -> bool) : bool.
Proof.
induction n.
exact true. (*/false*)
exact( p (f0 n) && IHn (fun m : Fin n => p (fs m))).
Qed.


Definition allbool (n:nat)(p:Fin n-> bool) := forallf1 p.


(*forall x:Fin n , p x = true.  *)
Check allbool.
Check andb.
Definition andbool (xs:list bool)  := foldr (andb) true xs.

Definition allb (n:nat)(p:Fin n -> bool) (xs:list(Fin n)) := andbool (map p xs).
Check allb.
Definition allbutlast (n:nat)(p:Fin n -> bool)(xs:list(Fin n)) :bool := allb p (belast xs).
Check last.

Definition membfin (n:nat) (X:Fin n -> bool): Fin n -> bool := fun x =>if X x then true else false.

Fixpoint dfa_seq (a:Alphabet)(n:nat)(d:dfa n a)(x:Fin n)(w:Word a) : list(Fin n) :=
    match w with 
   | nil => nil
   | a :: es => delta d x a :: dfa_seq d ( delta d x a) es
    end.


Definition last (A:Type)(x:A)(xs:list A) :A := 
     match xs with 
   | nil => x
   | p:: xs' => last xs' x
   end.



Definition L(a:Alphabet)(n:nat)(d:dfa n a)(X:Fin n->bool)(x y:Fin n) : Language a := 
           fun w:Word a =>if (  eqf (last x (dfa_seq d x w)) y &&  allbutlast (membfin X) (dfa_seq d x w)) then True else False.
Check In.


  Notation "'L^' X" := (L X) (at level 8).


Inductive inlist (A:Type)(a:A):list A->Prop :=
  | in_n : forall l:list A, inlist a (a::l)
  | in_tl : forall (l:list A) (b:A), In a l -> inlist a (b :: l).  (** possibly useful function*)
Check length.

Lemma seq_split: forall (a:Alphabet)(n:nat)(d:dfa n a)( x z:Fin n)(w:Word a), In z (dfa_seq d x w ) ->
    exists (w1 w2: Word a), w = w1 ++ w2 /\ length w2 < length w /\  ~ In z (belast (dfa_seq d x w1)) /\
      last x (dfa_seq d x w1) = z.
Proof.
intros.
simpl in *.
intuition.
simpl in *.
induction w.
simpl in *.
destruct H.
simpl in *.
destruct H .
simpl in *.
unfold belast in IHw.
admit.
(*
exists nil.
simpl in *.
exists w.
split.
reflexivity.
split.

induction n.
simpl in *.
unfold In in H.
*)


admit.
Qed.

(**  Let X included in Q and x,y,z in Q. Let w in the language defined by L^X U {z} _x,y. 

 The property states that  either the word w is in the language L^X  _x,y OR

     there exist the words w1 and w2  s.t

      w = w1 ++ w2  /\ length (w2) < length w /\ w1 in L^X _x,z  /\ w2 in L^X _z,y*)

Definition Union (n:nat) (A B : Fin n -> bool) : Fin n -> bool := fun x : Fin n=> A x || B x. 
Definition Singleton (n:nat) (x:Fin n): Fin n -> bool :=fun w => if eqf x w then true else false  .  (**????*)
Check (fun x:Fin 5 =>Singleton (x)).  (*??*)
(*Inductive Singleton (n:nat) (x:Fin n) :  Fin n ->bool :=  
   | in_sing : (Singleton  x) x. *)

Definition add_element (n:nat)(x:Fin n)(A:Fin n -> bool):= Union (Singleton x) A.
(** Implement some haskell prelude functions *)
Check orb.
Print orb.

Definition orbool  (xs: list (bool)) : bool := foldr (orb ) false xs.
Check orb.
Definition anyl (A:Type)(p:A->bool)(xs:list A):bool := orbool( map p xs).
Check anyl.


(** Definition of a language to be MONOTONE: A set X is included in X U {z} , trivially. *)


(** Consider a word w. Let x,z in Q, set of states of the automaton. Let deltah be a run of w in the DFA starting in x.

Let z be the state reachable by using all but the last characters of the word w in the transition function. 

Then, there exist the words w1 and w2, such that:

w = w1++w2 /\ length(w2)<length(w) /\ { z not in deltah x (w minus last character) } /\ z =  *)


Definition elem (n:nat)(x:Fin n)(xs:list (Fin n)) :bool := anyl ( eqf x) xs.


Definition In_bool (n:nat) (x:Fin n)(xs: list (Fin n)) : bool := elem x xs.
Check In_bool.

Lemma  langinc: forall (a:Alphabet)(n:nat)(x y z :Fin n)(d:dfa n a)(X:Fin n -> bool) (w:Word a),

          L^d X x y w   -> L^d (add_element z X) x y w.
intros.
simpl in *.
unfold add_element in *.
unfold L in H.
simpl in H.
unfold L.
simpl in *.
admit.
(*
assert (allbutlast (membfin X) (dfa_seq d x w) 
unfold Union in *.
unfold Singleton in *.
simpl in *.
admit.*)
Qed.

Lemma L_cat : forall (a:Alphabet)(n:nat)(d:dfa n a) (X:Fin n -> bool)(w1 w2:Word a)(x y z :Fin n)(w:Word a),
     X z =true -> (L^d X x z) w1 -> (L^d X x z) w2 -> (L^ d X x y)(w1 ++ w2).


Lemma L_split1: forall (a:Alphabet)(n:nat)(d:dfa n a) (X:Fin n ->bool)(x y z : Fin n) (w:Word a) , 
    (L^ d (add_element z X) x y) w -> (L^ d X  x y) w \/ exists (w1 w2:Word a), 

     w = w1 ++ w2 /\ length w2 < length w /\  (L^ d X x z) w1 /\ (L^ d(add_element z X) z y) w2   .
Proof.
(** idea : first eliminate the case of z in X, make a case analysis taking the membership of z *)
intros.

case_eq( In_bool z (belast (dfa_seq d x w))).
intros.
right.
left.
simpl in *.
assert (L^d (add_element z X) x y w ->L^d X x y w).
apply langinc.
apply H1.
exact H.

intros.
apply langinc in H.
right.
red in *.
simpl in *. 



  Lemma L_rec :forall (a:Alphabet)(n:nat)(d:dfa n a) (X:Fin n ->bool)(x y z : Fin n) (w:Word a) , 
    L^ d (add_element z X) x y w  -> plus (conc (L^d X x z) (conc (Starl (L^ d X z z)) (L^ d X z y)))
                      (L^X x y).
(*Definition L(a:Alphabet)(n:nat)(d:dfa n a)(X:Fin n->bool)(x y:Fin n) : Language a := 
           fun w:Word a =>if (  eqf (deltah d x w) y &&  allbutlast (membfin X) (dfa_seq d x w)) then True else False.


*)
Check L.




fun w => True.

Inductive card  (n:nat) (X :Fin n ->bool): nat -> Prop :=
   |card_empty0 : card 0 empset 0
   | card_add0 : forall (X:Fin n->bool) 

Notation 
Definition cardinal (X:Fin n -> bool) : nat :=
Function R(a:Alphabet)(n:nat)(X: Fin n -> bool) (x y : Fin n) 
     {measure (fun X => 

Lemma R0_correct : forall (a:Alphabet)(n:nat)(d:dfa n a)(x:Fin n)(y:Fin n)(w:Word a),
  ( (w = nil /\ eqf x y = true) \/ exists a: Fin a, (w = a::nil) /\ delta d x a = y)
       -> 
       .
Proof.
intros. 
admit.
(*
right.
left.
split.*) 

Qed.
Function R 

Definition f(n:nat)(a:Alphabet)(p q : Fin (S n)): Prop :=  .

End Fatore.