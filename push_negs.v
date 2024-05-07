From MetaCoq.Template Require Import Loader All Checker.
From Coq Require Import List.
Import MCMonadNotation.
Open Scope bs.


(***********************************************************************)
From MetaCoq.Template Require Import All Checker Reduction.

Notation "'$quote' x" := ltac:((let p y := exact y in
                             quote_term
                             x
                             p)) (at level 0).

Notation "'$run' f" := ltac:(let p y := exact y in
                             run_template_program 
                             f
                             p) (at level 0).

Notation "'$quote_rec' x" := ($run (tmQuoteRec x)) (at level 0).

Notation "'$unquote' x" := ltac:((let p y := match y with
                                               existT_typed_term ?T ?b => exact b
                                             end in
                             run_template_program 
                             (tmUnquote x)
                             p)) (at level 0).

Notation "'$unquote' x : T" := ($run (tmUnquoteTyped T x)) (at level 0, T at level 100, x at next level).

Definition unfold_toplevel {A} (x : A) :=
  tmBind (tmQuote x) (fun y => 
                        match y with
                        | tConst na _ =>
                            tmEval (unfold na) x
                        | y => tmReturn x
                        end).

Notation "'$Quote' x" := ($run (tmBind (unfold_toplevel x) (tmQuote))) (at level 0).

Definition term_eqb (t1 t2 : term) :=
  @eq_term config.default_checker_flags init_graph t1 t2.

Notation "t == u" := (term_eqb t u) (at level 70).

Open Scope bs.
Open Scope bool.
Open Scope list.

Definition tLam x A b :=
  tLambda {| binder_name := nNamed x; binder_relevance := Relevant |} A b.

Definition tLet x A t b :=
  tLetIn {| binder_name := nNamed x; binder_relevance := Relevant |} t A b.

Definition tImp A B := 
  tProd {| binder_name := nAnon; binder_relevance := Relevant |} A B.

Require Import Nat.

Notation "'__'" := (hole) (no associativity, at level 0).

Notation "f <<< g" := (fun x => f (g x)) (at level 80).
Notation "f >>> g" := (fun x => g (f x)) (at level 80).


(***********************************************************************)

(** A binder kind. *)
Inductive bkind := Exist | Forall.

(** A binary logical connective. *)
Inductive conn := And | Or | Imp.

Inductive form := 
  | FAtom : Prop -> form
  | FTrue : form
  | FFalse : form 
  | FNot : form -> form
  | FConn : conn -> form -> form -> form
  (* We remember the original binder name so that when we 
     evaluate the formula to a Prop, we can reuse the original binder. *)
  | FBind : bkind -> aname -> forall A, (A -> form) -> form.

(***********************************************************************)
(* Reifying. *)

(** Same as [lift n k t], but substracts [n] instead of adding it. *)
Fixpoint lower n k t : term :=
  match t with
  | tRel i => tRel (if Nat.leb k i then i - n else i)
  | tEvar ev args => tEvar ev (List.map (lower n k) args)
  | tLambda na T M => tLambda na (lower n k T) (lower n (S k) M)
  | tApp u v => tApp (lower n k u) (List.map (lower n k) v)
  | tProd na A B => tProd na (lower n k A) (lower n (S k) B)
  | tCast c kind t => tCast (lower n k c) kind (lower n k t)
  | tLetIn na b t b' => tLetIn na (lower n k b) (lower n k t) (lower n (S k) b')
  | tCase ind p c brs =>
    let k' := List.length (pcontext p) + k in
    let p' := map_predicate id (lower n k) (lower n k') p in
    let brs' := map_branches_k (lower n) k brs in
    tCase ind p' (lower n k c) brs'
  | tProj p c => tProj p (lower n k c)
  | tFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lower n k) (lower n k')) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let k' := List.length mfix + k in
    let mfix' := List.map (map_def (lower n k) (lower n k')) mfix in
    tCoFix mfix' idx
  | tArray u arr def ty =>
    tArray u (List.map (lower n k) arr) (lower n k def) (lower n k ty)
  | x => x
  end.

(** Lower all the free variables of [t] by [n]. *)
Definition lower0 n t := lower n 0 t.

(** The input [t] is a term corresponding to a [Prop] we want to reify. *)
Fixpoint reify (t : term) : TemplateMonad term := 
  (* Fallback case : just wrap [t] as [FAtom t]. *)
  let atom t := tmReturn (mkApp ($quote FAtom) t) in
  match t with 
  | tConst _ _ => 
      (* [FTrue] *)
      if t == $quote True then tmReturn ($quote FTrue)
      (* [FFalse] *)
      else if t == $quote False then tmReturn ($quote FFalse) 
      else atom t
  | tApp f [t1] => 
      (* [FNot] *)
      if f == $quote not then 
        t1' <- reify t1 ;;
        tmReturn (mkApp ($quote FNot) t1')
      else atom t
  | tApp f [t1; t2] => 
      (* [FConn And] *) 
      if f == $quote and then
        t1' <- reify t1 ;;
        t2' <- reify t2 ;;
        tmReturn (mkApps ($quote FConn) [$quote And; t1'; t2'])
      (* [FConn Or] *)
      else if f == $quote or then 
        t1' <- reify t1 ;;
        t2' <- reify t2 ;;
        tmReturn (mkApps ($quote FConn) [$quote Or; t1'; t2'])
      (* [FBind Exist] *)
      else if f == $quote ex then 
        match t2 with 
        | tLambda aname ty body => 
            body' <- reify body ;;
            let func := tLambda aname ty body' in
            aname <- tmQuote aname ;;
            tmReturn (mkApps ($quote FBind) [$quote Exist; aname; ty; func])
        | _ => tmReturn t (* This should not happen. *)
        end
      else atom t
  | tProd aname t1 t2 =>
      match (binder_name aname) with 
      (* [FConn Imp] *)
      | nAnon => 
          t1' <- reify t1 ;;
          t2' <- reify t2 ;;
          (* We have to lower [t2'] because we removed the (anonymous) binder. *)
          tmReturn (mkApps ($quote FConn) [$quote Imp; t1'; lower0 1 t2'])
      (* [FBind Forall] *)
      | nNamed _ =>
          t2' <- reify t2 ;;
          aname' <- tmQuote aname ;;
          tmReturn (mkApps ($quote FBind) [$quote Forall; aname'; t1; tLambda aname t1 t2'])
      end
  | _ => atom t 
  end.


(***********************************************************************)
(* Evaluating. *)

(** We use a trick to preserve binders : we define two ways of evaluating 
    a formula to a Prop. 
    - A pure, "reference" implementation [eval]. 
      This is simple to write, we can prove the necessary properties about it 
      (since it is just a Coq function), but sadly it does not 
      (and can't be made to) preserve binder names.
    - A meta-program implementation [eval_meta].
      This manipulates the syntax of terms directly, and is a bit
      more tricky to write. As it is a meta-program (it runs in the TemplateMonad),
      we can't prove any properties about it. It's only advantage is 
      that is does preserve binder names. 
  
    The connection between the two implementations is a bit tricky :
    remember that we can't prove anything about [eval_meta]. 
    The solution is to write [eval_meta] carefully so that the result 
    of [tmQuote f >>= eval_meta >>= tmUnquoteTyped Prop] is 
    beta-equivalent to [eval f] : this way we can use the [change] tactic
    to evaluate [eval f], instead of using [cbn eval].   

    Also, since we keep track of the binders explicitly in [FBind],
    we don't have to apply the same methodology when manipulating [form]s
    (e.g. when writing [push_f] and [push_neg_f]). 
    We simply have to propagate the binders of [FBind]. 
*)

(** The pure implementation (which does not preserve binder names). *)
Fixpoint eval (f : form) : Prop :=
  match f with 
  | FAtom atom => atom
  | FTrue => True 
  | FFalse => False 
  | FNot f => not (eval f)
  | FConn And f1 f2 => eval f1 /\ eval f2
  | FConn Or f1 f2 => eval f1 \/ eval f2
  | FConn Imp f1 f2 => eval f1 -> eval f2
  | FBind Forall _ ty func => forall x : ty, eval (func x)  
  | FBind Exist _ ty func => @ex ty (eval <<< func)
  end.

(** The meta-program implementation. *)
Fixpoint eval_meta (t : term) : TemplateMonad term := 
  match t with 
  | tApp head [] => 
      (* FTrue *)
      if head == $quote FTrue then tmReturn ($quote True)
      (* FFalse *)
      else if head == $quote FFalse then tmReturn ($quote False)
      else tmReturn t
  | tApp head [arg] =>
      (* FAtom *) 
      if head == $quote FAtom then tmReturn arg
      (* FNot *)
      else if head == $quote FNot then 
        arg' <- eval_meta arg ;;
        tmReturn (mkApp ($quote not) arg')
      else tmReturn t
  | tApp head [conn; t1; t2] =>
      if head == $quote FConn then 
        (* FConn And *)
        if conn == $quote And then 
          t1' <- eval_meta t1 ;; 
          t2' <- eval_meta t2 ;; 
          tmReturn (mkApps ($quote and) [t1'; t2'])
        (* FConn Or *)
        else if conn == $quote Or then 
          t1' <- eval_meta t1 ;; 
          t2' <- eval_meta t2 ;; 
          tmReturn (mkApps ($quote or) [t1'; t2'])
        (* FConn Imp *)
        else if conn == $quote Imp then 
          let aname := {| binder_name := nAnon; binder_relevance := Relevant |} in
          t1' <- eval_meta t1 ;; 
          t2' <- eval_meta t2 ;;
          (* We are adding a binder over [t2], 
             so don't forget to lift the free variables of [t2] by 1. *)
          (*tmReturn (tProd aname t1' (lift0 1 t2'))*)
          tmReturn (tProd aname t1' t2')
        else tmReturn t
      else tmReturn t
  | tApp head [bkind; x; _; func] =>
      if head == $quote FBind then 
        (* FBind Forall *)
        if bkind == $quote Forall then 
          match func with 
          | tLambda _ ty body => 
              x' <- tmUnquoteTyped aname x ;;
              body' <- eval_meta body ;;
              tmReturn (tProd x' ty body')
          | _ => tmReturn t (* This case should not happen*)
          end
        (* FBind Exit *)
        else if bkind == $quote Exist then 
          match func with 
          | tLambda _ ty body => 
              x' <- tmUnquoteTyped aname x ;;
              body' <- eval_meta body ;;
              tmReturn (mkApps ($quote ex) [ty ; tLambda x' ty body'])
          | _ => tmReturn t (* This case should not happen*) 
          end
        else tmReturn t
      else tmReturn t
  | _ => tmReturn t
  end.

(***********************************************************************)
(* The algorithm on reified formulas. *)

Fixpoint push_f (f : form) : form := 
  match f with 
  | FAtom atom => FAtom atom
  | FTrue => FTrue 
  | FFalse => FFalse 
  | FNot f => push_neg_f f
  | FConn conn f1 f2 => FConn conn (push_f f1) (push_f f2)
  | FBind kind aname ty func => FBind kind aname ty (push_f <<< func)  
  end
  
with push_neg_f (f : form) : form := 
  match f with 
  | FAtom atom => FAtom (~atom)
  | FTrue => FFalse 
  | FFalse => FTrue 
  | FNot f => push_f f
  | FConn And f1 f2 => FConn Or (push_neg_f f1) (push_neg_f f2)
  | FConn Or f1 f2 => FConn And (push_neg_f f1) (push_neg_f f2)
  | FConn Imp f1 f2 => FConn And (push_f f1) (push_neg_f f2)
  | FBind Forall aname ty func => FBind Exist aname ty (push_neg_f <<< func)
  | FBind Exist aname ty func => FBind Forall aname ty (push_neg_f <<< func)  
  end.

Require Import Coq.Logic.Classical.

Lemma aux {A} (P Q : A -> Prop) : 
  (forall x, P x /\ Q x) <-> (forall x, P x) /\ (forall x, Q x).
Proof. intuition. Qed.

Lemma push_push_neg_f_spec (f : form) : 
  (eval (push_f f) <-> eval f) /\ (eval (push_neg_f f) <-> ~ (eval f)).
Proof. 
induction f ; simpl.
- tauto.
- tauto.
- tauto.
- destruct IHf as [-> ->]. tauto.
- case c ; simpl.
  + destruct IHf1 as [-> ->]. destruct IHf2 as [-> ->]. tauto.
  + destruct IHf1 as [-> ->]. destruct IHf2 as [-> ->]. tauto.
  + destruct IHf1 as [-> _]. destruct IHf2 as [-> ->]. tauto.
- rewrite aux in H. destruct H as [H1 H2]. case b ; simpl.
  + setoid_rewrite H1. setoid_rewrite H2. 
    split ; [tauto |].
    split ; [now apply all_not_not_ex | now apply not_ex_all_not].
  + setoid_rewrite H1. setoid_rewrite H2.
    split ; [tauto |].
    split ; [now apply ex_not_not_all | now apply not_all_ex_not].
Qed.

Lemma push_spec (f : form) : eval (push_f f) <-> eval f.
Proof.
destruct (push_push_neg_f_spec f) as [H1 H2]. exact H1.
Qed.

(***********************************************************************)
(* Gluing everything in Ltac. *)

Ltac push_negs :=
  match goal with  
  | [ |- ?g ] => 
      match type of g with 
      | Prop => 
          (* Reify. *)
          let f := constr:($run (tmQuote g >>= reify >>= tmUnquoteTyped form)) in
          (* Change the goal to [eval [reify goal]]. *)
          change (eval f) ;
          (* Apply push_spec. *)
          rewrite <-push_spec ;
          (* Compute [push_f] and [push_neg_f]. *)
          cbn [push_f push_neg_f] ;
          (* Compute [eval] using [eval_meta] so that we preserve binders. *)
          match goal with 
          | [ |- eval ?f' ] => 
              change ($run (tmQuote f' >>= eval_meta >>= tmUnquoteTyped Prop))
          | _ => fail "goal has wrong shape"
          end
      | _ => fail "expected a goal of type Prop" 
      end 
  end.

Ltac push_negs_in hyp_name := 
  match goal with 
  | [ hyp_name : ?h |- _ ] => 
      match type of h with 
      | Prop => 
          (* Reify. *)
          let f := constr:($run (tmQuote h >>= reify >>= tmUnquoteTyped form)) in
          (* Change the hypothesis to [eval [reify goal]]. *)
          change (eval f) in hyp_name ;
          (* Apply push_spec. *)
          rewrite <-push_spec in hyp_name ;
          (* Compute [push_f] and [push_neg_f]. *)
          cbn [push_f push_neg_f] in hyp_name ;
          (* Compute [eval] using [eval_meta] so that we preserve binders. *)
          match goal with 
          | [ hyp_name : eval ?f' |- _ ] => 
              change ($run (tmQuote f' >>= eval_meta >>= tmUnquoteTyped Prop)) in hyp_name
          | _ => fail "hypothesis has wrong shape"
          end
      | _ => fail "expected a hypothesis of type Prop" 
      end
  end.

Tactic Notation "push_negs" "in" hyp(H) := push_negs_in H.

(***********************************************************************)
(* An example. *)

Lemma test (n : nat) (H : ~ forall yy, True -> exists my_name, False -> (my_name = n /\ n = yy)) : True.
Proof. push_negs in H. Admitted.
