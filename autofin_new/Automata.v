  
(** %\chapter{%#<H0>#Finite automata%}%#</H0># *)

(* Proofs *)
 Section Automata.
(*Load FinSets.*)
Load Finitesets.
Require Import List.

Set Implicit Arguments.


(*Definition Alphabet := nat.*)
(*Variable Sigma : Alphabet. *) 

(** * Introduction 

  In finite automata theory, the basic element that we need to use in order  to reason about the behaviour of an automaton is the _word_ . 

  By definition, we call  a word to be a list of _symbols_. 

    
  - A symbol is an element of an alphabet( usually denoted as $\Sigma $ ).

  - A set of words is defined to be called a _language_ .

  In our implementation , a language is represented as a function that takes a word 

  and decides whether it is a member of the set (type [Prop]).

      *)
Definition Word(x:Alphabet) := list (Fin x).

Definition Language (a:Alphabet):= Word a -> Prop.



Inductive Starl(c:Alphabet)(x:Language c) : Language c := 
  | nil0: (Starl x) nil
  | cons0 : forall (a: Word c)(b:Word c),Starl x a /\ x b -> Starl x (app a b).


(** An empty word is defined as the [nil] list constructor *)



Definition eps (a:Alphabet):Word a:=nil.



(**  * Deterministic finite automata 

  As in "Automata and theory of computation"(J.Hopcroft), a deterministic finite automaton
  
 (DFA) is defined a 5-uple (Q,$\Sigma $ , $\sigma $, ${q}_{0}$, F)

  - A finite set of states Q (here denoted by [states])

  - A set of symbols ([Fin a])

  - A transition function $\sigma $ : Q * $\Sigma $ -> Q , denoted by [delta]

  - An initial state ${q}_{0}$

  - A set of final states F .

*)

Record dfa (n:nat) (a:Alphabet) :Type:= DFA {  
  states :=  Fin n; (*finite sets*) 
  symbol := Fin a;  
  delta : Fin n ->Fin a  -> Fin n; 
  q0 : Fin n ; (*only 1 initial state*)
  final :Fin n -> bool (*multiple states*)
}.
Check dfa.

(** * Language of a finite deterministic automaton *)


(*Definition is_accepting (n:nat)(a:Alphabet)(d:dfa n a)(q: states d)  := In q (final d).*)

(** Below, we have the extended transition function for a DFA , [deltah] : *)


Fixpoint deltah (n:nat)(a:Alphabet)(d: dfa n a)(q: Fin n) (w: Word a) : (Fin n):=
  match w with
     | nil => q
     | h :: t => (deltah d (delta  d q h ) t) 
  end.
Lemma deltah_prop:
  forall (a:Alphabet)(n:nat)(q:Fin n) (d:dfa n a) (xs ys :Word a),
   deltah d (q) (xs++ ys) = deltah d (deltah d (q) xs) ys.

induction xs.
simpl in *.
reflexivity.
simpl in *.

intros.
simpl in *.
(*induction ys.
simpl in *.
assert (xs++nil = xs).
intuition.
rewrite H.
reflexivity.
simpl in *.
intuition. *)
admit.
Qed.
Lemma deltah_property :
    forall (a:Alphabet)(n:nat) (d:dfa n a)(q:Fin n)(xs ys zs :Word a) ,
   deltah d (q) (xs ++ ys ++ zs) =
    deltah d(deltah d (deltah d (q) xs) ys ) zs.
induction xs.
simpl.
induction ys.
simpl in *.
reflexivity.
simpl in *.
apply deltah_prop.


simpl in *.
intros.
assert (xs ++ ys ++ zs = (xs ++ ys)++ zs).
auto with *.
admit.



(*simpl in *.
induction xs.


induction zs.
simpl in *.
intuition.
assert (ys ++ nil = ys).
intuition.
 (*very well known property*)
rewrite H.
reflexivity.
simpl in *. *)

Qed.


Notation " x ^ y " := (exps x y).

Definition dfa_lang1 (n:nat)(a:Alphabet)(d: dfa n a) :Language a := 
  fun w:Word a => final  d (deltah  d(q0 d ) w)=true.


(** The actual definition of the language of a DFA *)

Definition dfa_lang (n:nat)(a:Alphabet)(d: dfa n a) :Language a := 
  fun w:Word a => match  final  d (deltah  d(q0 d ) w)  with 
              | true => True
              | false => False
             end.

Check dfa_lang.
Check tt.



(** Empty automaton : a (initial )state with no final states*)


Definition dfa_void(q:Fin 1)(a:Alphabet) : dfa 1 a := 
          DFA (fun x:Fin 1 => fun b:Fin a => q ) q (fun x:Fin 1 => false).

Print dfa_void.

(** The empty automaton will not accept any word *)

Definition empty_lang (a:Alphabet):Language a:= fun w:Word a=>False.

Definition isNil (a:Alphabet) (w:Word a): Prop :=
    match w with  |nil => True
                  | _  => False
                              end. 

Definition eps_lang (a:Alphabet) :Language a := 

             fun w:Word a=> w=nil.

              (*fun w:Word a => match w with  |nil => True
                                            | _  => False
                              end. *)

Definition eps_lang1 (a:Alphabet) :Language a := 
        fun w:Word a => w =nil.


Lemma dfa_void_correct: forall (a:Alphabet)(q:Fin 1) (w:Word a),
     dfa_lang (dfa_void q a) w -> empty_lang w.
intros.
unfold dfa_lang in H.
unfold empty_lang.
simpl in H.

auto with *.
Qed.

(*The automaton that will take the epsilon language *)

Print option.
Check (S (S 0)).
Definition dfa_epsilon (q:Fin 1)(a:Alphabet) : dfa (1) a := 
   DFA( fun _:Fin 1 => fun _:Fin a=> q) q   (fun x:Fin 1 => eqf q x).

Print dfa_epsilon.

Definition dfa_compl (a:Alphabet)(n:nat)(d:dfa n a) : dfa n a :=

   DFA( delta d) (q0 d) (fun q : Fin n=> 

    negb (final d q)).
Inductive empty :Set := .
Inductive singleton :Set := emptyx : singleton. 
Print emptyx.



(** Remove states that are unreachable !!! *)


Definition reachable_immediate (a:Alphabet) (n:nat) (d: dfa n a)(x y :Fin n)  :=

  exists c:Fin a,   (delta d x c) = y.


Definition reachable (a:Alphabet)(n:nat) (d:dfa n a) (y:Fin n) :=

   exists w:Word a , deltah d ( q0 d)w = y.


Definition isconnected (a:Alphabet)(n:nat) (d:dfa n a) :=

    forall (x:Fin n), exists w:Word a, deltah d (q0 d) w = x.

(** * Nondeterministic finite automaton 

   A _nondeterministic finite automaton_ (NFA) A is defined as a 5-uple Q,$\Sigma $ , $\sigma $, S, F), 
   where :

   - [Q] represent a finite set of initial states ( [nstates])

   - A set of symbols $\Sigma $ ([Fin a])

   - A transition function $\sigma $ : Q * $\Sigma $ -> $P (Q)$ ([ndelta])

   - A set of initial states [S] , denoted by [ninitial]

   - A set of final states [F], denoted by [nfinal].

   
*)


Record nfa (n:nat)(a:Alphabet) := NFA {
   
   nstates :=Fin n; 
   nsymbol := Fin a; 
   ndelta : Fin n-> Fin a  ->Fin (2^n); 
   ninitial : Fin n -> bool (* multiple states*);
   nfinal : Fin n -> bool
 }.
Check nfa.

(** We want to generate the union of 2 sets, taking into account the isomorphism [(Fin n -> bool) <-> Fin (2^n)], proven in the library of

    finite sets. *)


Definition unionf (n:nat) (sets : (Fin n -> bool) -> bool) (x:Fin n) : bool := 
  existsf1 (fun q : Fin (2^n) => sets( allexp2 q) && allexp2 q x).

Definition prepare (n:nat)(a:Alphabet) (nr:nfa n a)(states : Fin (2^n)) (x:Fin a)  : (Fin n -> bool)  :=
   fun s : Fin n  => existsf1 (fun st : Fin n => allexp2 (states) (st) &&  allexp2(ndelta  nr st x) s). 


(** The extended transition function for an NFA  [ndeltah]: *)

Fixpoint ndeltah (n : nat) (a:Alphabet) (nr: nfa n a) (qs : (Fin (2^ n))) (w:Word a) :(Fin (2^n)) :=
       match w with 
     | nil    =>  qs
     | h :: t =>  (ndeltah nr (allexp1 (prepare nr qs h)) t)   
       end.
(*Definition nfa_lang (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a => (existsf1(fun q :Fin n=>( allexp2(ndeltah nr (allexp1 (ninitial nr) ) w)) q && (nfinal  nr q)))=true. 
*)
Definition nfa_lang (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a => match (existsf1(fun q :Fin n=>( allexp2(ndeltah nr (allexp1 (ninitial nr) ) w)) q && (nfinal  nr q))) with
                   | true => True
                  | false => False
                   end .
Definition nfa_lang1 (n:nat)(a:Alphabet) (nr: nfa n a) :Language a := 
  fun w :Word a => (existsf1(fun q :Fin n=>( allexp2(ndeltah nr (allexp1 (ninitial nr) ) w)) q && (nfinal  nr q)))=true. 

(** * The subset construction *)

(*Convert a dfa to an nfa: *)

Definition dfa2nfa (n:nat) (a:Alphabet) (d:dfa n a): nfa n a :=
    NFA(fun k : Fin n => fun a : Fin a => 
    
     (allexp1 ( fun x:Fin n => eqf x (delta d k a) ))) (fun x:Fin n => eqf x (q0 d)) (final d).




(* union of ndelta *)

  
Definition nfa2dfa (n:nat) (a:Alphabet) (nr: nfa n a) : dfa (2^n) a :=

 DFA (fun k:Fin (2^n)=> fun a : Fin a => allexp1 (prepare nr k a)) (allexp1 (ninitial nr )) 
    (fun k:Fin (2^n)=>existsf1(fun q:Fin n=> (allexp2 k q ) && nfinal nr  q)).

Definition nfa_void (a:Alphabet) : nfa 1 a :=
  NFA(fun x:Fin 1 => fun a:Fin a=> allexp1 (fun y:Fin 1 => false)) 
      (fun x:Fin 1 =>existsf1 (fun y:Fin 1 => eqf x y))
       (fun x:Fin 1 =>existsf1 (fun y:Fin 1 => false)).

Lemma nfa_void_lang :  forall (a:Alphabet)(w:Word a),
     nfa_lang (nfa_void a) w -> empty_lang w.
intros.
unfold empty_lang.
unfold nfa_lang in H.
simpl in H.
auto with *.

Qed.
Print eps.
(*
Definition chec (a:Alphabet) (p :Fin a) :=

 if (p::nil)=eps a then true else false.*)

Definition nfa_eps(a:Alphabet):nfa 1 a :=

  NFA(fun x:Fin 1 => fun a0:Fin a => allexp1 (fun y:Fin 1 => eqf x  y))
   (fun x:Fin 1 => true ) (fun x:Fin 1 => true).


Print nfa_eps.

Print option.

Lemma nfa_eps_lang1 : forall (a:Alphabet)(w:Word a) ,
     eps_lang w -> nfa_lang (nfa_eps a) w.
intros.
unfold eps_lang in H.
unfold nfa_lang.
simpl.
split.
Qed.
Lemma nfa_eps_lang :forall (a:Alphabet) (w:Word a) ,
   nfa_lang (nfa_eps a) w -> eps_lang w.
intros.
unfold eps_lang.

unfold nfa_lang in H.
simpl in *.

admit.
Qed.

(*
Definition nfa_var (a:Alphabet) :=

   NFA (fun xs : Fin 2 => fun c:Fin a => 

     allexp1 (fun ys : Fin 2 => eqf xs ys =false) )

     (fun xs :Fin 2 =>   *)

Definition nfa_var(a:Alphabet)(cc:Fin a)  :=
    NFA( fun it :Fin 2 => fun aa :Fin a =>  allexp1 (fun final:Fin 2=>if negb (eqf it final)&& eqf cc aa then true  else  false ))
      (fun x : Fin 2 => existsf1 (fun y: Fin 2 => eqf x y) )
    (fun x:Fin 2 => existsf1 ( fun y :Fin 2 => eqf x y)).

Print nfa_var.
(*
Definition nfa_var1(a:Alphabet)(x:Fin a) : nfa 2 a:=

   NFA (fun xs :Fin 2 => fun c :Fin a => allexp1(existsf1(fun y:Fin 2 =>
           end))) tt tt. *)
  

Definition single_lang (a:Alphabet):Language a:=
  fun w => 

match w with 
        | a::nil => True
        | _ => False
     end.
Print single_lang.

Definition single_lang1 (a:Alphabet)(x:Fin a) :Language a :=
  fun w : Word a => match w with 
    
     | p :: nil => if eqf p x then True else False
     | _ => False
    end. 
Lemma nfa_var_lang : forall (a:Alphabet)(w:Word a)(cc:Fin a) , 
    nfa_lang (nfa_var  cc) w -> single_lang1 cc w.
intros.
unfold nfa_lang in H.
(*intuition.
(*We want to prove that in an nfa with the epsilon language does not accept a word
different from <nil>  useful in the theorem of correctness nfa_eps_lang *)
rewrite H0 in H.
assert(False). *)
unfold nfa_var in *.
simpl in *.
unfold single_lang1.
simpl.
admit.
Qed.
Print nfa_var.

Print sum.
Print prod.



Definition condition1 (a:Alphabet)(p q :nat) (c:Fin a) (n1:nfa p a)(n2:nfa q a) (xd : Fin (p+q)) : bool :=

         match (addfin1 p q xd) with 
        | inl x => existsf1 (fun tx:Fin(2^p) => eqf tx (ndelta n1 x c))

        | inr y => existsf1 (fun ty :Fin (2^q) => eqf ty (ndelta n2 y c))

       end.
       

Definition nfa_disj (a:Alphabet)(p q :nat) (n1:nfa p a)(n2:nfa q a) : nfa(p+q) a :=

    NFA( fun xs : Fin (p+q) => fun c:Fin a => 

    allexp1 (fun xss :Fin (p+q) => eqf xs xss &&  condition1 c n1 n2 xss))
   
    (fun xs :Fin (p+q) =>

       match (addfin1 p q xs) with 
    
          | inl x => ninitial n1 x

          | inr y => ninitial n2 y

     end)


    (fun xs :Fin (p+q)  =>

       match (addfin1 p q xs) with 
    
          | inl x => nfinal n1 x

          | inr y => nfinal n2 y

     end) .

Definition lang_conc(a:Alphabet)(l1:Language a)(l2:Language a):Language a:=
    fun w:Word a=> exists w1:Word a, exists w2:Word a,  w1 ++ w2=w /\ l1 w1 /\ l2 w2.

Definition lang_union(a:Alphabet) (l1:Language a )(l2:Language a):Language a:=
    fun w:Word a=>  l1 w \/ l2 w.
Print nfa_lang1.
Lemma nfa_disj_lang : forall (a:Alphabet) (p q:nat) (n1: nfa p a) (n2: nfa q a) (w:Word a), 

        nfa_lang1 ( nfa_disj n1 n2 ) w -> lang_union (nfa_lang1 n1  ) (nfa_lang1 n2 ) w.
intros.
unfold lang_union.
unfold nfa_lang1 in *.
simpl.
simpl in *.
set( PP:= fun qx :Fin (p+q) => match addfin1 p q qx with 
  | inl x => nfinal n1 x
 
  | inr y => nfinal n2 y end).

left.
admit.
Qed.

Lemma nfa_disj_lang1 : forall (a:Alphabet) (p q:nat) (n1: nfa p a) (n2: nfa q a) (w:Word a), 

       lang_union (nfa_lang1 n1  ) (nfa_lang1 n2 ) w -> nfa_lang1 ( nfa_disj n1 n2 ) w.
intros.
unfold lang_union in *.
unfold nfa_lang1 in *.
destruct H.
simpl in *.
set( PP:= fun qx :Fin (p+q) => match addfin1 p q qx with 
  | inl x => nfinal n1 x
 
  | inr y => nfinal n2 y end).

set (pp:= fun q :Fin p => nfinal n1 q).
admit.

simpl in *.
admit.

(*
intros.
unfold lang_union.
unfold nfa_lang.
simpl in *.
unfold nfa_lang in H.
simpl in *.
left.
case_eq( existsf1(fun q1:Fin p => nfinal n1 q1)).
intro.
split.
intro.


left.*)

Qed.

Eval compute in existsf1( fun y: Fin 3=>(existsf1 (fun x:Fin 2 => true&& false))).

Print sum.

(*Inductive empty :Set := .*)
(**For a set with a single element, we consider an element x defined itself on  the singleton.

*)
(*Inductive singleton :Set := emptyx : singleton.  *)

Check (inr  emptyx).
Check existsf1(fun (t:Fin 2)=> existsf1 (fun o : Fin 2 => eqf t o )).

Print nfa_disj.

Check ( fun (c:Fin 2) => fun (d:Fin 3)=> inr (Fin 3) c).


Definition nfa_conc(a:Alphabet)(p q:nat) (n1:nfa p a) (n2:nfa q a) : nfa( p+q) a:=

    NFA( fun xs:(Fin (p+q)) => fun c:Fin a=>
  ( allexp1( fun xss:Fin (p+q) => eqf xss xs && (  existsf1 (fun x:Fin p=> existsf1(fun y:Fin q =>

          (*
      match addfin1 x , addfin1 y with 

      | inl x , inl y =>  existsf1 (fun t:Fin (2^p) => (eqf(ndelta n1 x c) t))

      | inl x, inr y =>  (nfinal n1 x) && ndelta (n2) *)
  
      
         match (addfin1 p q xs) with
       | inl  x => existsf1 (fun t:Fin (2^p) => (eqf(ndelta n1 x c) t)) ||

                          existsf1 (fun q'': Fin q => existsf1 (fun q' :Fin p => 

                     existsf1 (fun tx:Fin (2^p)=>

                        (nfinal n1 q') && (ninitial n2 q'') && (allexp2 (ndelta n1 x c) q'))))

       | inr  y => existsf1( fun tr: Fin (2^q) => (eqf(ndelta n2 y c) tr))

        end ))))))
      (fun xs :Fin (p+q) =>
          existsf1(fun x:Fin p => existsf1(fun y:Fin q =>

           match  (addfin1 p q xs) with
         | inl x =>  ninitial n1 x

         | inr y => nfinal n2 y && existsf1( fun t: Fin p => ninitial n1 t && nfinal n1 t)

         end)))

     (fun xs :Fin (p+q) =>
        existsf1 (fun x:Fin p=> existsf1(fun y:Fin q =>
           match  (addfin1 p q xs) with

         | inl x =>  false

         | inr y => nfinal n2 y 
        end ))).
         
    
Print nfa_conc.


Lemma nfa_conc1 : forall (a:Alphabet) (p q:nat)
        (n1 :nfa p a) (n2 : nfa q a)  (w:Word a) ,

   nfa_lang1 (nfa_conc n1 n2) w -> lang_conc (nfa_lang1 n1) (nfa_lang1 n2) w.

intros.
unfold lang_conc in *.
unfold nfa_lang1 in *.
simpl in *.
admit . (*??*)
Qed.
Definition nfa_star (a:Alphabet) (p:nat) (n1:nfa p a) : nfa (p+1) a := 

    NFA( fun xs:Fin (p+1) => fun c:Fin a=>  

    allexp1 (fun xss:Fin(p+1) => eqf xs xss && existsf1( fun _:Fin p =>

        match (addfin1 p 1 xs) with

     | inl x => existsf1 (fun tx:Fin (2^p) => eqf tx (ndelta n1 x c)) ||

                existsf1 (fun q' :Fin p => existsf1 (fun tx:Fin (p) =>

                           (ninitial n1 q') &&  (allexp2  (ndelta n1 x c) tx )&& (nfinal n1 tx)))

     | inr y => false

   end )))
    
    (fun xs:Fin (p+1) => 

        match (addfin1 p 1 xs) with

    | inl x => ninitial n1 x
   
    | inr y => true
 

       end)

     (fun xs:Fin (p+1) => 

        match (addfin1 p 1 xs) with

    | inl x => nfinal n1 x
   
    | inr y => true
 

       end) .

    


     

     
Lemma nfa_eps_lang12 :  forall (a:Alphabet)(w:Word a),
     nfa_lang1 (nfa_eps a) w -> eps_lang1 w.

intros.
unfold nfa_lang1 in H.

unfold eps_lang1.

simpl in *.
destruct w.
split.
inversion H.
induction w.
simpl.

simpl. (*
rewrite IHw.

simpl in H.
simpl in IHw.
inversion H.
simpl in IHw.
unfold isNil in IHw.*)
(*induction w.
split.
simpl in H.
simpl in IHw.
apply IHw in H.
simpl in H. *)

admit.
admit.
Qed. 
Check negb.
Print negb.
Check inl.


Lemma dfa2nfa_correct2 : forall (n:nat)(a:Alphabet)(w:Word a)(d:dfa n a), 
              dfa_lang d w-> nfa_lang (dfa2nfa d)w.
intros.
unfold dfa_lang in H.
unfold nfa_lang.
simpl.
      

case_eq (existsf1 (fun q:Fin n => final d q)).
intros.
split.
intro.
assert( final d (deltah d (q0 d) w)=false).
admit.

(*must prove that if there is no state that is final, then 
also the initial state cannot be final, taken as a particular case of the problem *)

rewrite H1 in H.
destruct H.
(*reflexivity.*)
Qed.

Lemma dfa2nfa_correct1 : forall (n:nat)(a:Alphabet)(w:Word a)(d:dfa n a), 
               nfa_lang (dfa2nfa d)w-> dfa_lang d w .
(*intros.
unfold nfa_lang1 in *.
unfold dfa_lang1 in *.
simpl in *.*)




intros.
unfold nfa_lang in H.
simpl in H.
unfold dfa_lang.
simpl.
simpl in H.
case_eq (existsf1 (fun q:Fin n => final d q)).
intro.
simpl.
simpl in *.
rewrite H0 in H.

case_eq (final d (deltah d (q0 d) w)).
split.
intro.
admit.
intro.

rewrite H0 in H.
destruct H.
Qed.


Theorem nfa2dfa_correct1 :forall (n:nat)(a:Alphabet)(w:Word a) (nr:nfa n a),
       dfa_lang (nfa2dfa nr) w -> nfa_lang nr w.
Proof.
intros.
unfold dfa_lang in H.
unfold nfa_lang.
simpl in H.
simpl.
exact H.
Qed.

Theorem nfa2dfa_correct2: forall (n:nat)(a:Alphabet)(w:Word a) (nr:nfa n a),
       nfa_lang nr w -> dfa_lang (nfa2dfa nr) w.
Proof.
intros.
unfold dfa_lang.
unfold nfa_lang in H.
simpl.
simpl in H.
assumption.
Qed.

(*Lemma for the equivalence of extended transition functions of a DFA and an NFA*)
Lemma eqref: forall (n:nat) (p :Fin n)  , equalsf p p =true.
intros.
induction n.
simpl.

assert (False).
apply fin0empty.
exact p.
destruct H.

unfold equalsf.
unfold equalsf in IHn.
simpl.
admit. (*prove inductive step *)
Qed.
Lemma ext_delta_coincide: forall (n:nat)(a:Alphabet) (nr:nfa n a)(w:Word a) , 
    eqf (ndeltah nr  (allexp1(ninitial nr)) w)(deltah (nfa2dfa nr) (q0 (nfa2dfa nr)) w)=true.

intros.
unfold eqf.
simpl.
induction w.
simpl.
rewrite eqref.


reflexivity.

set(P:=deltah (nfa2dfa nr) (allexp1 (ninitial nr )) w).

assert(deltah (nfa2dfa nr) (allexp1 (ninitial nr)) (a0:: w) = 

      (deltah (nfa2dfa nr) (delta  (nfa2dfa nr) (allexp1 (ninitial nr)) a0 ) w)).
simpl. 
reflexivity.
simpl.
trivial.

Qed.
 




End Automata.