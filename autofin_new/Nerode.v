Section  Myhill_nerode.
Set Implicit Arguments.
Load Automata.

Definition surj (X Y :Type)  (f :X-> Y) :=
 
   forall y:Y,  exists x:X, f(x) = y.


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


Definition congruence (a:Alphabet) (X:Type) (f : Word a-> X)


     :=  forall (x y  aa:Word a), f x = f y -> f (x++ aa) = f (y++ aa).


Definition belongs (a:Alphabet)(X:Type) (f: Word a -> X)(l:Language a) := forall (x y aa:Word a),

    f x = f y -> l x = l y.



Record Myhill_rel (a:Alphabet)(n:nat)(L:Language a):=

   {
      myhill_func :> fin_eq_class a n;

     myhill_congruent : congruence myhill_func;
     myhill_belongs : belongs (myhill_func ) L


    }.

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

Definition dfa_connected (a:Alphabet)(n:nat)(d:dfa n a) := isconnected d.

Print dfa_connected.
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
Lemma myhill_suffix : forall (a:Alphabet) (L:Language a), 



Definition ff (a:Alphabet)(n:nat)(d:dfa n a):= fun w:Word a=> (q0 d).


End Myhill_nerode.