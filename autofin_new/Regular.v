
(** %\chapter{%#<H0>#Regular expressions and languages%}%#</H0># *)
Section Reg_expression.
Require Import List.
Load Automata.
 
(** * Regular expressions *)

(** The _regular expressions_ are defined as simple expressions that denote the languages
    accepted by finite automata. 

    We would like to define the three operations on languages that the operators of
    regular expressions represent. 

    - The _union_ of two languages L and M , denoted %L\cup M%, is the set of strings that
      are either in L or in M, or in both. As a simple example, if L= { 1,01,013} and 
      M = {10,2} , then %L\cup M% = {1,01,013,10,2}. In Coq notation, it is defined as:
      
      << 
     Definition lang_union (a:Alphabet)(l1:Language a)(l2:Language a):Language a :=
         fun w:Word a =>  l1 w \/ l2 w.
      >>

    - The _concatenation_ of languages L and M is the set of words that can be formed by taking 
      any string in L and concatenating it with any string in M. For example, if 
      [L= {101, 23, 9)] and [M={3,4}] , then [L * M = {1013, 1014, 233, 234, 93, 94}]. In Coq, we represent it as :
      
      <<
      Definition lang_conc(a:Alphabet)(l1:Language a)(l2:Language a):Language a :=
    fun w:Word a => exists w1:Word a, exists w2:Word a,  w1 ++ w2=w /\ l1 w1 /\ l2 w2.
      >>

    

    - The _Kleene operator_  (closure) represents the set of words that  can be produced by taking any number
      of words from L, and concatenating all of them. 

     L* = L( L^2) (L^3) (.... L^n ...
     
     In the _Languages_ section, we have proved some useful properties concerning concatenation as
     well as union and Kleene operator 



*)

(** Defining the regular expression as an inductive term .
   
    Below, we make use of 7 constructors according to specific rules . The explanation are
    as follows:



    - the _[empty]_ expression represents a regular expression and denotes the empty set
   
    - [epsilon] is a regular expression and denotes the set [{epsilon}]
   
    - For each [a : Alphabet ] , _a_ is a regular expression and denotes the set [{a}]

    - If [r] and [s] are regular expressions, then [r+s] is a regular expression denoting
     the _union_ of L(r) and L(s), i.e L(r+s) = %L(r)\cup L(s)% . 

    - If [r] and [s] are regular expressions, then [rs] is a regular expression , denoting the
     _concatenation_ of [L(r)] and [L(s)] i.e L(rs) = $L(r) \cap L(s)$

    - If [r] is a regular expression, then [r*] is a regular expression, denoting the closure of
      [L(r)] . That is, [L(r* )= L(r)]
    
    - If [r] is a regular expression, then [(r)] is also a regular expression, denoting the exactly
      the same language like [r]. I.e, [L((r)) = L(r)]

*)

Inductive RegExp (a:Alphabet) :Set :=
| Empty : RegExp a 

| Epsilon : RegExp a

| Var : Fin a -> RegExp a

| Plus : RegExp a -> RegExp a -> RegExp a

| Conc : RegExp a -> RegExp a -> RegExp a

| Starex : RegExp a-> RegExp a

| Paren : RegExp a-> RegExp a.  

Print nfa_void.

Print nfa_eps.
Print nfa_var.
Check Type.
Check ex.
Print ex.
(*
Definition exas (a:Alphabet)(n:nat) :nfa n a.
induction n.
simpl in *.
intuition.
destruct H.
simpl in *. *)

Fixpoint re_nr (a:Alphabet) (r:RegExp a) : nat :=

match r with 

| Empty => 1

| Epsilon => 1
| Var xs => 2
|  Plus xs ys => re_nr xs + re_nr ys

| Conc xs ys => re_nr xs + re_nr ys
| Starex xs => re_nr xs + 1

| Paren xs  => re_nr xs
end.


Fixpoint re_to_nfa(a:Alphabet)(r:RegExp a ) : nfa (re_nr r) a :=

 match r with
| Empty => nfa_void a
| Epsilon => nfa_eps a

| Var xs => nfa_var xs

|  Plus xs ys => nfa_disj (re_to_nfa xs) (re_to_nfa ys)

| Conc xs ys => nfa_conc (re_to_nfa xs) (re_to_nfa ys)

| Starex xs => nfa_star (re_to_nfa xs)

| Paren xs => re_to_nfa xs


end.
Inductive Star (a:Alphabet) (l:Language a) : Language a:= 
  | nil0: (Star l) nil
  | cons0 : forall (x: Word a)(y:Word a),Star l x /\ l y -> Star l (app x y).


(*Definition single_lang1 (a:Alphabet)(x:Fin a):Language a:=

 fun w => w = nil.*)

Print single_lang.
Fixpoint reg2lang (a:Alphabet)(r : RegExp a) : Language a :=
 match r with 
 | Empty => fun w:Word a =>False
 | Epsilon => fun w => w = nil (* fun w:Word a => match w with  |nil => True
                                            | _  => False
                              end *)
 | Var e => single_lang1 e
 | Plus e1 e2 => lang_union (reg2lang e1) (reg2lang e2)
 | Conc e1 e2 => lang_conc (reg2lang e1) (reg2lang e2)
 | Starex e => Star (reg2lang e)
 | Paren e => reg2lang e
  end.

Print nfa_eps.
Lemma klth : forall (a:Alphabet)(w:Word a) (r:RegExp a) , nfa_lang (re_to_nfa r) w -> reg2lang r w.
Proof.
intros.
simpl in *.
induction r.
simpl in *.
unfold nfa_void in H.
simpl in H.
trivial.
simpl in *.
apply nfa_eps_lang in H.
unfold eps_lang in H.
exact H.

simpl in *.
apply nfa_var_lang.

exact H.
(*intuition.
(*We want to prove that in an nfa with the epsilon language does not accept a word
different from <nil>  useful in the theorem of correctness nfa_eps_lang *)
rewrite H0 in H.
assert(False). *)


simpl in *.

admit.
admit.
admit.
admit.
Qed.
(*
apply nfa_disj_lang in H.
admit.
destruct H1.
simpl in *.
unfold single_lang1.
unfold nfa_var in *.
simpl in *.
assert(reg2lang(Paren r) w).
simpl in *.
assert(nfa_lang(nfa_eps a) (a0::w) -> False).
intro.
unfold nfa_eps in H1.

admit.
simpl in *.
unfold single_lang1.
unfold nfa_var in H.
simpl in *. *)
Lemma klth1 :forall (a:Alphabet)(w:Word a)(r:RegExp a), reg2lang r w -> nfa_lang (re_to_nfa r) w.
intros.
induction r.
simpl in *.
destruct H.
simpl in *.
unfold nfa_eps.
simpl.
admit.
admit.
admit.
admit.
admit.
simpl in *.
apply IHr.
exact H.
Qed.





    



End Reg_expression.