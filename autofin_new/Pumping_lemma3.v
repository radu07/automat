
(** %\chapter{%#<H0>#Properties of regular languages%}%#</H0># *)


Section Pump.
(** * The pumping lemma for regular languages *)

(** In automata theory, one primary question when we discuss about a language is the
     property of regularity: "Given L a language, is L regular?" This has a very meaningful
    effect on the capabilities of the representation of a word from a
    a language on an automaton. 

    In our approach, we try to formalize the two main theorems that solve the issue of 
    regularity or non-regularity of a language : _the pumping lemma_ and _the Myhill-Nerode theorem_

*)
Load Automata.
Require Import List.
Require Import Notations.
(**
    Let us state the _Pumping lemma for regular languages_ : Let L be a regular language. Then, there exists a constant n,(depending
    on L, such that for any string w s.t length w >= n, we can break it into 3 strings, [u1], [u2] and [u3], in a way such that 
       [w = u1++ u2++u3] , and the following properties are simultaneously satisfied: 
       - [length u2 > 0]
       - [length(u1 ++ u2) <= n]
       - forall k>= 0, the string [w' = u1++(u2)^k ++ u3] is also in [L].

*)


(**  ** Informal proof.

   Let us consider that [L] is a _regular_ language. Therefore, by definition, a regular language can
   be represented on an appropriate deterministic finite automaton, A. We consider the DFA A to
   have [n] states.

   Let us define the word [w] to be under the form : [w] = [x(1) ++ x(2) ++... + x(m) ] , 
   where [m] $\ge $ [n] , each [x(i)] being an input symbol. We consider a state 
   [t(i)] to be the state at which the deterministic automaton is situated after reading the first
   i symbols from the word w. Mathematically defined, it is clear that the extended transition function will produce state
   [t(i)] if from starting at the initial state ${q}_{0}$, we advance with the reading of each of the [i] symbols.
   
   We observe that at the beginning, [t(0) = q(0)]. 
   
   The pigeonhole principle states that it is not possible for [n+1]  states ${p}_{i}$
   to be distinct, because of the fact that there are only [n] different states. Therefore,
   we may find 2 different integers [i], [j], [0 <= i < j <= n], in such a way that 
    [t(i) = t(j)] . At this point, we are able to break [w] into 3 parts:

     - [u1 = x(1) ++ x(2) ++ ... + x(i)]

     - [u2 = x(i+1) ++ x(i+2) ++ ... + x(j) ]

     - [u3 = x(j+1) ++ x(j+2) ++ ... + x(m) ]

    We may observe that the substring [u1] from the word [w] will go to state [t(i)] of the
    finite automaton. The substring [u2], from its construction, due to the fact that [t(i) = t(j)] ,
    will go into a loop at the state [t(i)]. The substring [u3] is the remainder of the word [w]. 
    
    As an observation, if [i = 0], then [u1] is empty (nil). Likewise, if [u2] has length 0, then
    [j = m = n] . The strict condition [i < j] states that [u2] cannot be empty.

    
    If the automaton receives an input [u1 ++ (u2 ^k) ++ u3],we have to analyze the following situations.

    - [k=0]. Therefore, [w = u1 ++ u3]. The DFA starts at [q0](initial state) and after reading substring [u1],
    the automaton is situated in state [t(i)].  But we know that [p(i) = p(j)], using the pigeonhole principle stated above .
    As a consequence, [p(i)] is already in state [p(j)]. Thus, if we read [u3], the DFA
    will go into the accepting state. 

    - [k>0]. Therefore, [w= u1 ++ (u2 ^k) ++ u3].  After reading [u1], the automaton will go from the initial state [q0] to 
      state [t(i)]. Then, it will loop into this state [k] times, in order to read [(u2) ^k].
      After reading [u3], the automaton will go into the accepting state.

    For any [k>= 0], [w = u1 ++ (u2 ^k) ++ u3] is also _accepted_ , i.e [w] is in [L].
    
*)


(** The inductive definition below will check the membership of an element of type [Fin n] into
    a list *)

Inductive in_list(n:nat) (q:Fin n) : list (Fin n) -> Prop :=
 | in0 : forall (ls: list (Fin n)), in_list q (q :: ls)
 | ins : forall (x:Fin n)(ls : list (Fin n)), in_list q ls -> in_list q (x:: ls).

Lemma app_l_nil: forall {X:Type} (l: list X),
  l ++ nil = l.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.

(** Correctness lemmas : if an element [x] is situated in list [xs] and is also a member of a list
    [ys], then [x] is also member of the concatenation of those 2 lists, [xs++ ys].

*)

Lemma in_list2: forall (n:nat) (x:Fin n)(xs ys : list (Fin n)) , 
     in_list x xs \/ in_list x ys -> in_list x (xs ++ ys).
(* optional :intros.
destruct H.
induction xs.
simpl.
inversion H.
simpl.
apply in0.
simpl.
apply ins.
simpl. *)
admit.
Qed.

(** Converse of the lemma stated above : not necessary *)
Lemma in_list1  :forall (n:nat) (q:Fin n)(xs ys : list(Fin n)),
       in_list q (xs ++ ys ) -> in_list q xs \/ in_list q ys.
(*intros .
induction xs.
simpl.
simpl in H.
right.
assumption.
inversion H.
left.
apply (in0 a).

apply IHxs in H1.


right.
induction xs.
simpl.


assumption.
apply IHxs.
simpl. *)
admit.
Qed.


(** This predicate will check whether a list contains repeated states

 *)
Inductive Rep (n:nat) : list (Fin n) -> Prop :=
 | rep0 : forall (x:Fin n)(l:list(Fin n)) , Rep l -> Rep (x:: l)
 | reps : forall (x:Fin n) (l:list(Fin n)) , in_list x l -> Rep (x:: l).

(** In every list of states, if [x] is a member of list [l], then we can always find
    a way to partition the list into 2 subslists and append [x] to the head of the second
    sublist.

*)



Lemma in_listdecomp : forall (n:nat)(x:Fin n)(l:list(Fin n)) ,
    in_list x l -> exists (l1 l2:list (Fin n)), l = l1 ++ (x:: l2).

intros.
induction H.
simpl.
exists nil.
exists ls.
simpl.
reflexivity.
destruct IHin_list.
destruct H0.
exists(x0:: x1).
exists x2.
simpl.
rewrite H0.
reflexivity.
Qed.

(**  

    This lemma is similar to the decomposition property listed above, with the mention that
    now we want the fact that if we know that a list contains repeated states, then
    we may decompose the list of state into 3 sublists , the last 2 containing the repeated
    state 

    The purpose of using this procedure will help us in the decomposure of the 3 words described in the pumping lemma.
    
    In that statement, we choose the second substring, i.e [u2] to be describing a loop alongside 
    a state [t(i)].


*)
Lemma rep_decomp : forall (n:nat) (l:list (Fin n)),
    Rep l ->  exists (a:Fin n), exists (xs ys zs: list (Fin n)), 
    l= xs ++ (a::ys) ++ (a:: zs).
intros n l H.
induction H.
destruct IHRep as [x0].
destruct H0 as [xs].
destruct H0 as [ys].
destruct H0 as [zs].
rewrite H0.
exists x0.
exists (x:: xs).
exists ys.
exists zs.
simpl.
reflexivity.
apply in_listdecomp in H.
destruct H as [l1].

destruct H as [l2].
rewrite H.

exists x.
exists nil.
exists l1.
simpl.
exists l2.
reflexivity.
Qed.

(** The lemma below states that if we make an application of a property ( function ) [f] on a list [lss],
    and the result can be partitioned into 2 lists, then there exists a way of 
    creating 2 additional lists which combined together form the original one - 
    we observe that to each list we may map property [f] in order to produce the original 2 partitions.



*)

Lemma map1 : forall (X Y : Type) (f:X->  Y)(lss:list X) ,
    forall (xs ys :  (list Y)) ,
    map f lss = xs++ ys -> exists (ms ns : list X) ,
   lss = ms ++ ns /\ map f ms = xs /\ map f ns = ys.
Proof.
intros a n f.
induction lss.
simpl.
exists nil.
exists nil.
simpl in H.
split.
simpl.
reflexivity.

split.
assert(xs=nil).
destruct xs.
reflexivity.
inversion H.
simpl.
rewrite H0.
reflexivity.
assert(xs=nil).
destruct xs.
reflexivity.
inversion H.

simpl.
rewrite H0 in H.
simpl in H.
rewrite H.
reflexivity.
intros.
simpl in H.
destruct xs.
simpl in H. 
simpl.
destruct ys.
simpl.
inversion H.
assert (map f lss= ys).
simpl.
inversion H.
reflexivity.

set (P:= IHlss nil ys H0).
destruct P.
destruct H1.
destruct H1.
destruct H2.
exists nil.
simpl.
exists (a0:: lss).
split.
reflexivity.
split.
reflexivity.
simpl.
exact H.
simpl in H.
assert(map f lss = xs ++ys).
simpl.
inversion H.
reflexivity.

assert(exists ms ns :list (a), 
    lss = ms++ns /\ map f ms = xs /\ map f ns = ys).
apply IHlss.
assumption.
destruct H1 as [ms'].
destruct H1 as [ns'].
destruct H1.
destruct H2.
exists (a0::ms').
exists (ns').
split.
simpl.
rewrite H1.
reflexivity.
split.
simpl.
inversion H.
rewrite H2.
reflexivity.
rewrite H3.
reflexivity.

Qed.


(** The reasoning is similar to lemma [map1]. In this case, the list is splitting in 3
    substrings. This we be useful when we reason about the splitting of the word, described in the pumping lemma. 


*)

Lemma map2: forall (X Y :Type) (f:X -> (Y))(lss:list(X)) ,
    forall (xs ys zs :  (list Y)) ,
    map f lss = xs++ ys++ zs -> exists (ms ns ps:list X) ,
  lss = ms ++ ns++ ps /\ map f ms = xs /\ map f ns = ys /\ map f ps =zs.

intros.
apply map1 in H.
destruct H  .
destruct H .

destruct H.
destruct H0.
exists x.
apply map1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
exists x1.
exists x2.
split.
rewrite H1 in H.
assumption.
split.
assumption.
split.
assumption.
assumption.
Qed.


(** This function will make n copyes of the exact same word. In mathematical language, it is translated as
    [ l ^k] , where [l] is a word and [k] is a natural number.

*)

Fixpoint wmult (a:Alphabet)(n: nat) (l: Word a) : Word a :=
  match n with
  | O => nil
  | S n' => l ++ wmult n' l
  end.


(** The [generate_state] function will produce for a word the following outcome :
    - generate_state ("abc") = a :: ab :: abc:: nil
    
    We will like to use this function in order to keep in memory at which state the automata is .

*)

(**  

*)
Fixpoint generate_state (a:Alphabet) (l:Word a) : list (Word a) :=
   match l with 
| nil => nil :: nil 
 | x:: xs => nil :: map (cons x) (generate_state  xs)
  end.


(** The following lemma will 

*)
Lemma gen1 : forall (alph:Alphabet)(x t:(Word alph))(xs ys :  (list (Word alph))),
     generate_state x = xs ++ (t::ys) -> 
  exists (zs :Word alph), x = t ++ zs.
intros alph x.
induction x. 
intros.
simpl in H.
simpl in H.
assert (xs=nil).
destruct xs.
reflexivity.
simpl.
destruct xs.
simpl.

simpl in H.
inversion H.
simpl in H.
inversion H.

rewrite H0 in H.
simpl in H.
inversion H.
exists nil.
simpl.
reflexivity.
intros.
simpl in H.

destruct xs.
simpl in H.
assert( t=nil).

inversion H.
reflexivity.
assert (ys= map (cons a) (generate_state x)).
inversion H.
reflexivity.
exists (a::x).
rewrite H0.
simpl.
reflexivity.
inversion H.
Print cons.

apply map1 in H2.

destruct H2.
destruct H0.
destruct H0.
destruct H2.
simpl in H.

inversion H.
destruct x1.
simpl in H0.
inversion H3. 
simpl in H3.
apply IHx in H0.
destruct H0.
inversion H3.
simpl.
exists x2.
rewrite H0.
reflexivity.
Qed.
Eval compute in (length (nil)).
Lemma gen2 : forall (n:nat)(ls ys zs: list (Fin n)) (pps qqs  rrs: list(list (Fin n))),
  generate_state ls = pps ++ (ys :: qqs) ++ (zs:: rrs) ->
     exists fs :list(Fin n), zs = ys ++ fs /\ length fs >0.
intros n ls.
induction ls.
intros.
destruct pps.
simpl in H.
inversion H.
rewrite<- H1 in H.
simpl in H.
simpl.


destruct qqs.
simpl.


inversion H2.
inversion H2.
simpl.
simpl in H.
inversion H.
rewrite <-H1 in H.
simpl in H.
inversion H.
destruct pps.
simpl in H.
simpl in H.
simpl in H2.
simpl in H3.
inversion H2.
clear H3.
simpl in H.
simpl in H2.
inversion H2. 


destruct ls.
intros.
simpl in H. 
simpl in IHls.

destruct pps.
simpl in H.
inversion H.
rewrite <-H1 in  H.
clear H1.
simpl in H.
inversion H.

destruct qqs.
simpl in H1.
simpl in H.
inversion H1.
exists zs.
simpl.
split.
assumption.
rewrite<-H3.
simpl.
simpl.
auto. (*proof that 0< 1*)


inversion H1.
simpl in H2.
simpl in H.
simpl in H1.
destruct qqs.

simpl in H.
simpl in H1.
clear H2.
inversion H4.

simpl in *.
inversion H4.
simpl in *.

inversion H.
simpl in H. 
simpl in H2.

destruct pps.
simpl in *.
inversion H2.


destruct qqs.
simpl in *.
inversion H4.

inversion H2.
destruct pps.
simpl in H2.
simpl in H.
inversion H.
inversion H.

intros.
remember(f::ls) as t.
simpl in H.
set(HL := f :: ls).
destruct pps.
simpl in H.
inversion H.
exists zs.
split.
simpl.
reflexivity.
simpl.
apply map1 in H2.
destruct H2.
destruct H0.
destruct H0.
destruct H2.


destruct x0.
simpl in *.
inversion H3.
inversion H3.
simpl.


simpl in H2.
simpl in H.
admit. (*Proof that S(length ( ) >0 , obvious *)

inversion H.
rewrite <-H1 in H.
simpl in H.
simpl in H.


assert(map (cons a) (generate_state t) =pps ++ (ys::qqs) ++zs :: rrs).
simpl.
assumption.
clear H2.
apply map2 in H0.

destruct H0 as [ ms].
destruct H0 as [ns].
destruct H0 as [ps].
destruct H0.
destruct H2.

destruct H3.
destruct ns.
simpl in *.
inversion H3.
inversion H3.
destruct ps.
simpl in *.
inversion H4.
inversion H4.
simpl in *.

apply IHls in H0.
destruct H0.
destruct H0.
exists x.
split.
rewrite H0.
reflexivity.
assumption.
Qed.

Lemma generate0 : forall (n:nat)(ls ps qs: list(Fin n)) (xss yss zss: list(list(Fin n))),

      generate_state ls = xss ++  (ps::yss) ++ (qs::zss) ->
 
           (exists (fs  : list(Fin n)) ,qs = ps++ fs /\ 
    length fs > 0   ) /\  exists (gs:list (Fin n)),ls = qs ++ gs.

intros.
assert(generate_state ls = xss ++ (ps :: yss) ++ qs :: zss).
assumption. 
apply gen2 in H.
destruct H as [fs].
destruct H.
split.
exists fs.
split.
assumption.
assumption.
rewrite app_assoc in H0.
apply gen1 in H0.
destruct H0.
exists x.
exact H0.
Qed. 

Definition state_from_word (a:Alphabet)( n:nat) (d:dfa n a)(w:Word a):=
  map (deltah d (q0 d)) (generate_state w).
Print state_from_word.

Lemma pigeonhole: forall (n:nat)(l: list (Fin n)), length l > n ->
  Rep l.
intros.
simpl.
induction n.
simpl.
induction l.
simpl.
simpl in H.
red in H.
red in H.
assert (False).
admit.
destruct H0.
simpl.
admit.
admit.
Qed.
Lemma loop : 
    forall (a:Alphabet)(n:nat)(k:nat)(d:dfa n a)(q:Fin n)(w:Word a), 
   deltah d (q) w = q -> deltah d (q) (wmult k w)=q.
induction k.
simpl.

intros.
reflexivity.
intros.
simpl.
rewrite deltah_prop.
simpl.
rewrite H.
apply IHk.
exact H.
Qed.

(**  We will use first a slightly modified version of the pumping lemma, considering a word accepted by a deterministic automaton.
     Implicitly, words encoded on finite automata form regular languages. 

     The statement of the modified pumping lemma is presented below. The idea is similar to the 
     description found in the beginning of this chapter. 
     

*)
Theorem pump_lemma0 : forall (alph:Alphabet)(n:nat)(d:dfa n alph),
  forall (w:Word alph), dfa_lang1 d w -> length w >= n-> 
       
   exists (xs ys zs : Word alph),
        w = xs ++ ys ++ zs /\ (length ys > 0) /\ 

    forall (k:nat), dfa_lang1 d (xs ++ (wmult k ys) ++ zs)/\ length (xs++ys) <= n.

Proof.
(* We will consider to have a DFA that accepts a word w and proceed with the statement 

*)
intros.
unfold dfa_lang1 in H.
simpl in H.
(*  *)


set (reachable_states:= state_from_word d w).
assert (p:length reachable_states > n).
unfold reachable_states.
assert(length (reachable_states) = S( length w)).
unfold reachable_states.
simpl.
admit.
(*?*)
unfold reachable_states in H1.
rewrite H1.
simpl.
auto with *.



assert(Rep reachable_states).
apply pigeonhole.
exact p.
set(I:= rep_decomp H1 ).
destruct I as [a].
destruct H2 as [xs].
destruct H2 as [ys].
destruct H2 as [zs].

unfold reachable_states in H2.
unfold state_from_word in H2.
set(P:= map2 (deltah d (q0 d)) (generate_state w) xs (a::ys) (a::zs)).
apply P in H2.
destruct H2 as [ms].
destruct H2 as [ns].
destruct H2 as [ps].
destruct H2.
destruct H3.
clear P.
destruct H4.
destruct ns. 
inversion H4.
destruct ps.
inversion H5.
assert(generate_state w = ms ++ (w0 :: ns) ++ w1 :: ps).
assumption.
apply generate0 in H6.
destruct H6.
destruct H6 as [fs].
destruct H7 as [gs].
destruct H6.

exists w0.
exists fs.
exists gs.
split.
rewrite H7.
rewrite H6.
simpl.
rewrite app_assoc.
reflexivity.
simpl in *.
split.
assumption.
split.
unfold dfa_lang1.
simpl in *.

assert(deltah d (q0 d) (w0++(wmult k fs) ++ gs ) = 
     deltah d (q0 d) w).
simpl.
rewrite deltah_property.
simpl in *.
inversion H4.
simpl in H5.
inversion H5.

assert( deltah d (deltah d (q0 d) w0) fs =deltah d (q0 d) w0  ).
simpl.
pattern (deltah d (q0 d) w0) at 2.
rewrite H10.
rewrite <-H12.
rewrite H6.
rewrite deltah_prop.
reflexivity.
rewrite loop.
rewrite H7.
rewrite H6.
simpl.
assert( (w0 ++ fs) ++ gs =
   (w0 ++ fs ++ gs)   ).
simpl.
auto with *.

rewrite H14.

rewrite deltah_property.
rewrite H9.
reflexivity.
rewrite H9.
reflexivity.
rewrite H9 .

simpl.
exact H.
assert( deltah d (deltah d (q0 d) w0) fs =deltah d (q0 d) w0  ).
admit.

admit.

Qed.


Theorem pump_lemma : forall (a:Alphabet)(l:Language a),
   exists (n:nat),forall (w:Word a), l w /\  length w >= n /\ 
   exists (xs ys zs : Word a),
        w = xs ++ ys ++ zs /\ length (xs++ys) <= n .
intros.
assert( dfa : nfa2dfa 
(** Proof identical to pump_lemma0, by applying that given a regular language,

we may find an nfa, (kleene lemma klth1 from Regular file) and convert it using

to nfa2dfa function *)

End Pump.