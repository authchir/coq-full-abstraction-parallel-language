(* It would be desirable to follow the article and formalize for every possible
   Id, Exp and Bexp. We just need to assert their properties. *)
Axiom Id : Set.
Axiom Exp : Set.
Axiom Bexp : Set.

Inductive Com : Set :=
| cskip : Com
| cassign : Id -> Exp -> Com
| cseq : Com -> Com -> Com
| cif : Bexp -> Com -> Com -> Com
| cwhile : Bexp -> Com -> Com
| cpar : Com -> Com -> Com
| cawait : Bexp -> Com -> Com.

Require Import Coq.MSets.MSets.

(* To define a weak finite set of [Id], it has to be decidable. Is there a way
   to assert the existance of a module with some signature? Should I just
   formalize the article inside of a functor with a [DecidableType] parameter? *)
Module IdDec <: DecidableType.
  Definition t := Id.
  Axiom eq : t -> t -> Prop.
  Declare Instance eq_equiv : Equivalence eq.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ (eq x y) }.
End IdDec.

Module IdSet := MSetWeakList.Make IdDec.
Module IdSetProps := Properties IdSet.

(* Those axioms are ok, they are only require because we want to keep the [Exp]
   and [Bexp] abstract. *)
Axiom freeE : Exp -> IdSet.t.
Axiom freeB : Bexp -> IdSet.t.
Fixpoint freeC (c : Com) : IdSet.t :=
  match c with
  | cskip => IdSet.empty
  | cassign x e => IdSet.add x (freeE e)
  | cseq c1 c2 => IdSet.union (freeC c1) (freeC c2)
  | cif b c1 c2 => IdSet.union (freeB b) (IdSet.union (freeC c1) (freeC c2))
  | cwhile b c => IdSet.union (freeB b) (freeC c)
  | cpar c1 c2 => IdSet.union (freeC c1) (freeC c2)
  | cawait b c => IdSet.union (freeB b) (freeC c)
  end.

(*
In the article, it is defined as following:
Let S = Id ->p N denote the set of states, ranged over by s.
Does ->p means it is a partial function?
In this case, the definition should probably be the following:
Definition S := Id -> option nat.
*)
Definition S := Id -> nat.

(*
If I represent S as a Coq function, how can I define the [dom] function?
*)
Axiom dom : S -> IdSet.t.

Definition S_add (x : Id) (n : nat) (s : S) :=
  fun y => if IdDec.eq_dec x y then n else s y.

Definition defined_onE (e : Exp)  (s : S) := IdSet.Subset (freeE e) (dom s).
Definition defined_onB (b : Bexp) (s : S) := IdSet.Subset (freeB b) (dom s).
Definition defined_onC (c : Com)  (s : S) := IdSet.Subset (freeC c) (dom s).

(* Those correspond to the following in the article (§3):
   When s is a state defined on (at least the free identifiers of E, we write
   <E,s> ->* n to indicate that E evaluates to n in state s. Similarly for
   boolean expressions. *)
(* Is it a good idea to use a dependent pair? *)
Definition ExpS := {x : Exp * S | prod_curry defined_onE x}.
Definition mk_ExpS (e : Exp) (s : S) (P : defined_onE e s) : ExpS :=
  exist (prod_curry defined_onE) (e, s) P.
Axiom evalE : ExpS -> nat.

Definition BexpS := {x : Bexp * S | prod_curry defined_onB x}.
Definition mk_BexpS (e : Bexp) (s : S) (P : defined_onB e s) : BexpS :=
  exist (prod_curry defined_onB) (e, s) P.
Axiom evalB : BexpS -> bool.

(* I don't know how to represent the semantic functions E and B (§3) for
   expressions and boolean expressions. It should be a function with type
   [Exp -> set { (s, n) : S * nat | evalE (mk_ExpS e s P) = n }]
   But I cannot use a [MSets] since those are finite and the semantics functions
   return an infinite set of states and results.
*)

Definition closed (c : Com) := IdSet.Empty (freeC c).

Lemma defined_onC_closed_term : forall (c : Com) (s : S),
  closed c ->
  defined_onC c s.
Proof.
  intros.
  unfold defined_onC.
  apply IdSetProps.empty_is_empty_1 in H.
  rewrite H.
  apply IdSetProps.subset_empty.
Qed.

Definition Conf := { p : Com * S | prod_curry defined_onC p }.
Definition mk_Conf (c : Com) (s : S) (P : defined_onC c s) : Conf :=
  exist (prod_curry defined_onC) (c, s) P.
Definition mk_closed_Conf (c : Com) (s : S) (H : closed c) : Conf :=
  mk_Conf c s (defined_onC_closed_term _ s H).

(* BEGIN BORING FUNCTIONS *)
(* It would be nice to hide them somewhere since they are unimportant... *)
Lemma lift : forall (e : Exp) (s : S) (x : Id),
  defined_onE e s ->
  IdSet.In x (dom s) ->
  defined_onC (cassign x e) s.
Proof.
  unfold defined_onE, defined_onC.
  intros. simpl.
  auto using IdSetProps.subset_add_3.
Qed.

Lemma cskip_closed :
  closed cskip.
Proof.
  exact IdSet.empty_spec.
Qed.

Lemma merge_par : forall (c1 c2 : Com) (s : S) (P1 : defined_onC c1 s)
  (P2 : defined_onC c2 s),
  defined_onC (cpar c1 c2) s.
Proof.
  unfold defined_onC.
  intros. simpl.
  auto using IdSetProps.union_subset_3.
Qed.

Lemma merge_seq : forall (c1 c2 : Com) (s : S) (P1 : defined_onC c1 s)
  (P2 : defined_onC c2 s),
  defined_onC (cseq c1 c2) s.
Proof.
  unfold defined_onC.
  intros. simpl.
  auto using IdSetProps.union_subset_3.
Qed.

Lemma merge_if : forall (b : Bexp) (c1 c2 : Com) (s : S) (Pb : defined_onB b s)
  (P1 : defined_onC c1 s) (P2 : defined_onC c2 s),
  defined_onC (cif b c1 c2) s.
Proof.
  unfold defined_onB, defined_onC.
  intros. simpl.
  auto using IdSetProps.union_subset_3.
Qed.

Lemma merge_while : forall (b : Bexp) (c : Com) (s : S) (Pb : defined_onB b s)
  (P : defined_onC c s),
  defined_onC (cwhile b c) s.
Proof.
  unfold defined_onB, defined_onC.
  intros. simpl.
  auto using IdSetProps.union_subset_3.
Qed.

Lemma merge_await : forall (b : Bexp) (c : Com) (s : S) (Pb : defined_onB b s)
  (P : defined_onC c s),
  defined_onC (cawait b c) s.
Proof.
  unfold defined_onB, defined_onC.
  intros. simpl.
  auto using IdSetProps.union_subset_3.
Qed.

(* END BORING FUNCTIONS *)


(* There are two different relations:
   - the subset of successfully terminated configuations [term] and;
   - a [transition] relation. *)

Inductive term : Conf -> Prop :=
| term_skip : forall (s : S),
    term (mk_closed_Conf cskip s cskip_closed)

| term_par : forall (c1 c2 : Com) (s : S) (P1 : defined_onC c1 s)
  (P2 : defined_onC c2 s),
    term (mk_Conf c1 s P1) ->
    term (mk_Conf c2 s P2) ->
    term (mk_Conf (cpar c1 c2) s (merge_par _ _ _ P1 P2)).

Inductive transition : Conf -> Conf -> Prop :=
| tassign : forall (x : Id) (e : Exp) (s : S) (P : defined_onE e s) (n : nat)
  (DOM : IdSet.In x (dom s)),
    evalE (mk_ExpS e s P) = n ->
    transition
      (mk_Conf (cassign x e) s (lift e s x P DOM))
      (mk_closed_Conf cskip (S_add x n s) cskip_closed)

| tseq_step : forall (c1 c1' c2 : Com) (s s' : S) (P1 : defined_onC c1 s)
  (P1' : defined_onC c1' s') (P2 : defined_onC c2 s) (P2' : defined_onC c2 s'),
    transition (mk_Conf c1 s P1) (mk_Conf c1' s' P1') ->
    transition
      (mk_Conf (cseq c1 c2) s (merge_seq _ _ _ P1 P2))
      (mk_Conf (cseq c1' c2) s' (merge_seq _ _ _ P1' P2'))

| tseq_term : forall (c1 c2 : Com) (s : S) (P1 : defined_onC c1 s)
  (P2 : defined_onC c2 s),
    term (mk_Conf c1 s P1) ->
    transition
      (mk_Conf (cseq c1 c2) s (merge_seq _ _ _ P1 P2))
      (mk_Conf c2 s P2)

| tif_true : forall (b : Bexp) (c1 c2 : Com) (s : S) (Pb : defined_onB b s)
  (P1 : defined_onC c1 s) (P2 : defined_onC c2 s),
    evalB (mk_BexpS b s Pb) = true ->
    transition
      (mk_Conf (cif b c1 c2) s (merge_if _ _ _ _ Pb P1 P2))
      (mk_Conf c1 s P1)

| tif_false : forall (b : Bexp) (c1 c2 : Com) (s : S) (Pb : defined_onB b s)
  (P1 : defined_onC c1 s) (P2 : defined_onC c2 s),
    evalB (mk_BexpS b s Pb) = false ->
    transition
      (mk_Conf (cif b c1 c2) s (merge_if _ _ _ _ Pb P1 P2))
      (mk_Conf c2 s P2)

| twhile : forall (b : Bexp) (c : Com) (s : S) (Pb : defined_onB b s)
  (P : defined_onC c s),
    let Pwhile := merge_while _ _ _ Pb P in
    let Pseq := merge_seq _ _ _ P Pwhile in
    let Pskip := defined_onC_closed_term cskip s cskip_closed in
    let Pif := merge_if _ _ _ _ Pb Pseq Pskip in
    transition
      (mk_Conf (cwhile b c) s Pwhile)
      (mk_Conf (cif b (cseq c (cwhile b c)) cskip) s Pif)

| tpar1 : forall (c1 c1' c2 : Com) (s s' : S) (P1 : defined_onC c1 s)
  (P1' : defined_onC c1' s') (P2 : defined_onC c2 s) (P2' : defined_onC c2 s'),
    transition (mk_Conf c1 s P1) (mk_Conf c1' s' P1') ->
    transition
      (mk_Conf (cpar c1 c2) s (merge_par _ _ _ P1 P2))
      (mk_Conf (cpar c1' c2) s' (merge_par _ _ _ P1' P2'))

| tpar2 : forall (c1 c2 c2' : Com) (s s' : S) (P1 : defined_onC c1 s)
  (P1' : defined_onC c1 s') (P2 : defined_onC c2 s) (P2' : defined_onC c2' s'),
    transition (mk_Conf c2 s P2) (mk_Conf c2' s' P2') ->
    transition
      (mk_Conf (cpar c1 c2) s (merge_par _ _ _ P1 P2))
      (mk_Conf (cpar c1 c2') s' (merge_par _ _ _ P1' P2'))

| tawait_true : forall (b : Bexp) (c c' : Com) (s s' : S) (Pb : defined_onB b s)
  (P : defined_onC c s) (P' : defined_onC c' s'),
    evalB (mk_BexpS b s Pb) = true ->
    transition_star (mk_Conf c s P) (mk_Conf c' s' P') ->
    term (mk_Conf c' s' P') ->
    transition
      (mk_Conf (cawait b c) s (merge_await _ _ _ Pb P))
      (mk_Conf c' s' P')

| tawait_false : forall (b : Bexp) (c c' : Com) (s s' : S) (Pb : defined_onB b s)
  (P : defined_onC c s) (P' : defined_onC c' s'),
    evalB (mk_BexpS b s Pb) = false ->
    let conf := mk_Conf (cawait b c) s (merge_await _ _ _ Pb P) in
    transition conf conf

(* Reflexive transitive closure of the [transition] relation *)
with transition_star : Conf -> Conf -> Prop :=
| transition_refl : forall (conf : Conf),
    transition_star conf conf

| transition_step : forall (conf1 conf2 conf3 : Conf),
    transition conf1 conf2 ->
    transition_star conf2 conf3 ->
    transition_star conf1 conf3.
