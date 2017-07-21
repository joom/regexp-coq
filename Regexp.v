Require Import Ascii.
Require Import List.

Inductive reg_exp : Type :=
| EmptySet : reg_exp
| Epsilon : reg_exp
| Lit : ascii -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

Inductive std_reg_exp : Type :=
| SEmptySet : std_reg_exp
| SLit : ascii -> std_reg_exp
| SApp : std_reg_exp -> std_reg_exp -> std_reg_exp
| SUnion : std_reg_exp -> std_reg_exp -> std_reg_exp
| SPlus : std_reg_exp -> std_reg_exp.

Inductive inL : list ascii -> reg_exp -> Prop :=
| inEpsilon : inL nil Epsilon
| inLit : forall c, inL (c :: nil) (Lit c)
| inApp : forall l1 l2 r1 r2,
    inL l1 r1 -> inL l2 r2 -> inL (l1 ++ l2) (App r1 r2)
| inUnion : forall l r1 r2,
    inL l r1 /\ inL l r2 -> inL l (Union r1 r2)
| inStar0 : forall r, inL nil r -> inL nil (Star r)
| inStar : forall l1 l2 r,
    inL l1 r -> inL l2 (Star r) -> inL (l1 ++ l2) (Star r).

Inductive inLS : list ascii -> std_reg_exp -> Prop :=
| inLitS : forall c, inLS (c :: nil) (SLit c)
| inAppS : forall l1 l2 r1 r2,
    inLS l1 r1 -> inLS l2 r2 -> inLS (l1 ++ l2) (SApp r1 r2)
| inUnionS : forall l r1 r2,
    inLS l r1 /\ inLS l r2 -> inLS l (SUnion r1 r2)
| inPlus1S : forall l r, inLS l r -> inLS l (SPlus r)
| inPlusS : forall l1 l2 r,
    inLS l1 r -> inLS l2 (SPlus r) -> inLS (l1 ++ l2) (SPlus r).

Lemma nil_append : forall l1 l2 : list ascii,
    l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof. intros. induction l1. induction l2.
  auto.
  + simpl in *. auto.
  + simpl in *. inversion H.
Qed.

Lemma non_empty : forall r, ~ (inLS nil r).
Proof. intros r i. induction r.
  + inversion i.
  + inversion i.
  + inversion i. subst. destruct (nil_append l1 l2 H).
    subst. auto.
  + inversion i. destruct H1. auto.
  + inversion i.
    - auto.
    - destruct (nil_append l1 l2 H). subst. auto.
Qed.

(* Suffix *)

Inductive suffix : list ascii -> list ascii -> Prop :=
| stop : forall x xs, suffix xs (x :: xs)
| drop : forall y xs ys, suffix xs ys -> suffix xs (y :: ys).

Lemma suffix_trans : forall xs ys zs,
    suffix xs ys -> suffix ys zs -> suffix xs zs.
Proof. intros. induction H0; constructor; auto. Qed.

Lemma suffix_nil_cons : forall x xs, suffix nil (x :: xs).
Proof. intros x xs.
  generalize dependent x.
  induction xs as [|y ys].
  + constructor.
  + intro x. constructor. apply (IHys y).
Qed.

(* Recursion permission *)

Inductive recursion_permission : list ascii -> Prop :=
| can_rec : forall ys, (forall xs, suffix xs ys -> recursion_permission xs)
          -> recursion_permission ys.

Lemma perm_suffix_nil : forall xs,
    suffix xs nil -> recursion_permission xs.
Proof. intros xs sf. inversion sf. Qed.

Lemma perm_suffix : forall y xs ys,
    suffix xs (y :: ys)
    -> recursion_permission ys
    -> recursion_permission xs.
Proof. intros y xs ys sf perm.
  remember sf as wit1 in sf.
  destruct sf eqn:wit3.
  Admitted.

Lemma well_founded : forall ys, recursion_permission ys.
Proof. intros ys. induction ys; constructor.
  + apply perm_suffix_nil.
  + intros xs sf. apply (perm_suffix _ _ _ sf IHys).
Qed.

(* Matcher *)

Definition bmatch : forall (r : std_reg_exp) (s : list ascii),
                    ({s' | suffix s' s} -> bool)
                  -> recursion_permission s
                  -> bool.
Proof. intros r.
  induction r.
  + (* EmptySet *) intros. apply false.
  + (* Lit *) intros s k perm.
    induction s as [|x xs].
    - apply false.
    - destruct (ascii_dec x a).
      * apply k. exists xs. apply stop.
      * apply false.
  + (* App *) intros s k perm.
    apply (IHr1 s).
    - intros [s' sf].
      apply (IHr2 s').
      * intros [s'' sf'].
        apply k. exists s''. apply (suffix_trans s'' s' s); auto.
      * destruct perm as [ys f]. auto.
    - apply perm.
  + (* Union *)intros s k perm.
    apply (orb (IHr1 s k perm) (IHr2 s k perm)).
  + (* Plus *) intros s k perm.
    apply (orb (IHr s k perm)).
    (* Plus multiple case *)
    apply (IHr s).
    - intros [s' sf].
      apply (IHr s').
      * intros [s'' sf'].
        apply k. exists s''. apply (suffix_trans s'' s' s); auto.
      * destruct perm as [ys f]. auto.
    - apply perm.
Qed.

Theorem match_soundness : forall r s k perm,
     bmatch r s k perm = true
     -> exists p, exists s', exists sf,
          (p ++ s' = s) /\ (inLS p r) /\ (k (exist _ s' sf) = true).
Proof. intros r s k perm eq.
  induction r.
  + destruct s as [|x xs].
    -
Admitted.

Conjecture match_completeness : forall r s k perm,
      (exists p, exists s', exists sf,
          (p ++ s' = s) /\ (inLS p r) /\ (k (exist _ s' sf) = true))
     -> bmatch r s k perm = true.

Definition null (l : list ascii) : bool :=
  match l with | nil => true | _ :: _ => false end.

Definition acceptsS (r : std_reg_exp) (s : list ascii) : bool :=
  bmatch r s (fun H => let (s', _) := H in null s') (well_founded s).


Theorem acceptsS_soundness : forall r s,
    acceptsS r s = true
    -> inLS s r.
Proof. intros r s eq.
  destruct (match_soundness r s _ _ eq)
        as [p [s' [sf [app [i keq]]]]].
  assert (emp : s' = nil).
  Focus 2.
  subst. rewrite (app_nil_r p). assumption.
  destruct s' as [|b bs]. auto. inversion keq.
Qed.

Theorem acceptsS_completeness : forall r s,
    inLS s r
    -> acceptsS r s = true.
Proof. intros r s i. destruct s as [|x xs].
  + destruct (non_empty r i).
  + apply match_completeness.
    exists (x :: xs). exists nil. exists (suffix_nil_cons _ _).
    split. apply (app_nil_r _). auto.
Qed.