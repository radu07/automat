Section  Myhill_nerode.
Set Implicit Arguments.
Load Automata.
Require Import Logic.

Definition surj (X Y :Type)  (f :X-> Y) :=
 
   forall y:Y,  exists x:X, f(x) = y.
Print deltah.

Definition collapse_rel (a:Alphabet)(n:nat)(d:dfa n a )(x y : states d) :=


   forall w:Word a , final d(deltah d x w)=true <-> final d(deltah d y w) =true. 


Record Fin_Equiv (A:Set) := make_eq {
rel :> A->A->Prop;

 Eq_refl : forall x:A, rel x x;
 
 Eq_trans : forall (x y z :A), rel x y -> rel y z -> rel x z;
 Eq_sym  : forall (x y :A) , rel x y -> rel y x
 
} .


Record fin_eq_class (a:Alphabet)(n:nat) :=

 {
     fin_func :> Word a -> Fin n;
    
     fin_surj : surj  (fin_func)


 }.

(*Right congruence property *)
Definition congruence (a:Alphabet) (X:Type) (f : Word a-> X)


     :=  forall (x y  w:Word a), f x = f y -> f (x++ w) = f (y++ w).


Definition belongs (a:Alphabet)(X:Type) (f: Word a -> X)(l:Language a) := forall (x y aa:Word a),

    f x = f y -> l x =l y.

(** We will split the Myhill_nerode theorem into several parts . Let us define 

    a record for a specific type of relation, that satisfies right_invariant property [congruence],
    
    and also has the property of equality of the mapping on the words [x] and [y],

    implying that they  *)

Record Myhill_rel (a:Alphabet)(n:nat)(L:Language a):=

   {
      myhill_func :> fin_eq_class a n;

     myhill_congruent : congruence myhill_func;
     myhill_belongs : belongs (myhill_func ) L


    }.

Definition exP (n:nat)( P: Fin n -> bool):= existsf1(fun x :Fin n=>P x).

Check (fun a:Alphabet=> fun n:nat =>fun f:fin_eq_class  a n=> fin_surj f).
Print surj.

Variable A B :Type.
Definition funchoice := forall R: A->B->Prop, 
                         
                      (forall x:A, exists y:B, R x y)->

                  (exists f:A->B, forall x:A, R x (f x)).  


Definition choose(n:nat)(a:Alphabet) (P:fin_eq_class a n-> Prop):= exists x:fin_eq_class a n, P x.


(*
Check (fun (a:Alphabet)(n:nat) => fun f:fin_eq_class a n=> choose(fin_surj f)).
Definition xchoose (n:nat)(a:Alphabet)(P:fin_eq_class a n-> Prop) (p:existsf1(fun x:Fin n => P x)) :=
     
Definition canon_repr (a:Alphabet)(n:nat)( f: fin_eq_class a n) :=
*)

Definition suffix_congruence (a:Alphabet)(u v :Word a)(l:Language a):= 

  forall ( w :Word a) , l (u ++ w) = l(v++w).

Definition eq_suffix_cong (a:Alphabet) (X:Type) (f :Word a -> X) (l:Language a):=

    forall (u v :Word a) , f u = f v <-> suffix_congruence u v l.


Definition eq_suffix_cong1 (a:Alphabet)(X:Type) (f:Word a -> X) (l:Language a):=
   forall (u v :Word a), f u =f v -> suffix_congruence u v l.

Record Nerode_rel (a:Alphabet)(n:nat) (L:Language a) :=
   {
      nerode_func :> fin_eq_class a n ; 

      nerode_equiv : eq_suffix_cong nerode_func L
    


   }.
(*
Lemma nerode1 : forall (a:Alphabet)(n:nat)(L:Language a)
 
        (f:Nerode_rel a n)(w:Word a),  *)

Record Nerode_rel_weak (a:Alphabet)(n:nat) (L:Language a) :=

   { nerode_func_weak :> fin_eq_class a n;
     

     nerode_equiv_weal:eq_suffix_cong1 nerode_func_weak L

   }.
Print isconnected.

(* to complete *)

(** 1) Language L is accepted by a dfa
    2) we are able to construct a Myhill relation for L
    3) we can construct a weak nerode relation for L
    *)

(* 2 => 3 *)
Lemma myhill_to_wkner: forall (a:Alphabet)(n:nat)(l:Language a)(f: Myhill_rel n l),

       eq_suffix_cong1 f l.
intros.
unfold eq_suffix_cong1.
induction f.
simpl in *.
intros.
unfold suffix_congruence.
unfold iff.
intros.

unfold belongs in myhill_belongs0.
unfold congruence in myhill_congruent0.
apply (myhill_congruent0 u v w)in H.
apply myhill_belongs0 in H.
exact H.
exact w.
Qed. 

Lemma myhill_weak_ner : forall (a:Alphabet)(n:nat)(l:Language a) (f:Myhill_rel n l),
     Nerode_rel_weak  n l.
intros.
exact {|
        nerode_func_weak := f;
        nerode_equiv_weal := myhill_to_wkner  f 
      |}.
Qed.



(** Language L is accepted by a dfa -> we are able to construct a myhill relation for l *)

(** Let us construct a function which we later on we prove to be surjective. Our 

  final goal is to create a relation from the language accepted *)

Definition dfa_connected (a:Alphabet)(n:nat)(d:dfa n a) := isconnected d.


Definition func_dfa (a:Alphabet)(n:nat)(d:dfa n a ) := fun w:Word a =>
                deltah d(q0 d) w.

Print deltah.
Lemma deltah_is_surj : forall (a:Alphabet) (n:nat)(d:dfa n a), surj (deltah d (q0 d)).
intros.
unfold surj.
intro.

(*apply y in w.
exists w.
(*rewrite y.
exists (q0 d).*) *)
admit.
Qed.

(* We will define the equivalence relation by using the fact that the extended

   transition function is surjective.

   The extended function will describe an equivalence relation and it will have to be 


   able to have the properties of a right-invariant, as well as the property of 

   the fact that two words are equivalent, and one of them belong to the language [L],

  then they both belong to the same language .*)

Definition deltah_fin_eq_class (a:Alphabet)(n:nat)(d:dfa n a): fin_eq_class a n:=

   {| fin_func := deltah d (q0 d);

     fin_surj := deltah_is_surj d

   |}.

(* Now we show that the relation has the property of right-invariance (congruence) *)
Check deltah_prop.
Lemma right_congruent1 : forall (a:Alphabet)(n:nat)(d:dfa n a), 
                     congruence (deltah d (q0 d)).
intros.
unfold congruence.
intros.
assert (deltah d (q0 d) (x++w ) = deltah d (deltah d (q0 d) (x) ) w ).
apply deltah_prop.

assert (deltah d (q0 d) (y ++ w ) = deltah d (deltah d (q0 d) y ) w ).
apply deltah_prop.
rewrite H1.
rewrite <-H.
apply deltah_prop.
Qed.

(* Once we have proven that the extended transition function is right invariant, 
we will prove that it also have the following property : *)

Check dfa_lang.
Lemma belongs1 : forall (a:Alphabet) (n:nat) (d:dfa n a), 

       belongs (deltah d (q0 d) ) (dfa_lang d) .
intros.
unfold belongs.
intros.
unfold dfa_lang.
rewrite H.
reflexivity.
Qed.


Definition dfa_rel  (a:Alphabet)(n:nat) (d:dfa n a): Myhill_rel n (dfa_lang d):=
   {|  myhill_func := deltah_fin_eq_class d ;
       myhill_congruent := right_congruent1 d;

       myhill_belongs := belongs1 d
   |}.

Definition equal_language (a:Alphabet)(L1 L2:Language a) :=
   forall w:Word a , L1 w = L2 w.
Lemma lang_myh_equiv : forall (a:Alphabet)(n:nat)(l1 l2 :Language a),
 
       equal_language l1 l2 -> Myhill_rel n l1 -> Myhill_rel n l2.
intros.

unfold iff in H.
induction H0.
unfold equal_language in H.
unfold congruence in myhill_congruent0.
unfold belongs in myhill_belongs0.
assert(fin_eq_class a n).
exact myhill_func0.

(** We will consider to take the same function [myhill_func0] that we will use

   for the language [l2], and prove the relation of [myhill_belongs0] using the 

   property [l1 w = l2 w] *)
(*
assert (forall x y w :Word a, H0 x = H0 y ->
      H0 (x++w) = H0 (y++w)).
intros. *)

assert ( forall x y :Word a, Word a -> myhill_func0 x = myhill_func0 y ->
      l2 x = l2 y).
intros.
assert(l1 x = l1 y).

apply (myhill_belongs0 x y H1 H2).
assert(l1 x = l2 x).
apply H.
assert(l1 y = l2 y).
apply H.
assert (l2 x = l1 y).

rewrite H3 in H4.
symmetry.
exact H4.
rewrite <-H6 in H5.
assumption.

admit.

(* TO DO *)

Qed.


Print nil.

Print eps.
Check (fun (n:nat)(a:Alphabet)(l:Language a)(f:Nerode_rel n l) => f (eps a)).
Print dfa_connected.


(** Transform a nerode relation into a deterministic finite automaton *)
(*Definition choose_from (a:Alphabet)(n:nat)(f:Nerode_rel n a)(exP :exists x:Word a, f x)  := 

*)
(*We must use for equivalent classes the canonical form : every object under consideration
is equivalent to exactly one object in canonical form;  in other words, the canoninal forms of set [M]
represent the equivalence classes once and only once *)

Lemma can_repr : forall(a:Alphabet)(n:nat)(f:fin_eq_class a n)(x:Word a)(e:exists y:Fin n , f x =y)  , Word a.
intros.
admit.
Qed.

Check (fun (a:Alphabet)(n:nat)(l:Language a)(f:Nerode_rel  n l)(x:Word a) => 
           can_repr f x ).

Definition ner_to_autom (a:Alphabet)(n:nat)(l:Language a)(f:Nerode_rel a n l) :=

   {| 
       delta :=  fun xs :Fin n => fun c: Fin a =>

         allexp1 (fun xss:Fin n => eqf xss xs && 

         exists t:Word a , (f t) = xs 

         existsf1(fun tt:Word a => can_repr(f t)) ;
       
      q0 := f (eps a);
   
      final := fun xs :Fin n => 

   |}.
existsf1(t:Word a=> eqf (f t) x && f (rc(can_repr f t))
Lemma autom_rel : forall (a:Alphabet)(n:nat) (d:dfa n a) , Myhill_rel n (dfa_lang d).
intros.
unfold dfa_lang.
Require Import List.


(* From automaton section - reachability *)

Lemma reachable0 : forall (a:Alphabet) (n:nat) (d:dfa n a),

         reachable d(q0 d).
intros.
unfold reachable.
exists nil.
simpl.
reflexivity.
Qed.

Lemma reachable_step : forall (a:Alphabet) (n:nat) (d:dfa n a)(x:Fin n)(c:Fin a) ,
         reachable d (x) -> reachable d (delta d x c).

intros.
unfold reachable in *.
destruct H.
induction x0.
simpl in *.

exists (c::nil).
simpl in *.
rewrite H.
reflexivity.

?
simpl in *.
simpl in H.
inversion H.
simpl in *.

exists (a0::x0 ++(c ::nil)).
simpl.

admit.
(* true *)
(* !!!*)

Qed.



(** Minimization : merge equivalence classes *)
Lemma myhill_suffix : forall (a:Alphabet) (L:Language a), 



Definition ff (a:Alphabet)(n:nat)(d:dfa n a):= fun w:Word a=> (q0 d).


End Myhill_nerode.