(** * Lógica Computacional 1 - 2021-2 *)
(** ** Equivalência entre o Princípio da Indução Matemática (PIM) e o Princípio da Indução Forte (PIF) *)

From Coq Require Import Arith.Arith.
From Coq Require Import Lia.


(** Seja [P] uma propriedade sobre os números naturais. O PIM pode ser enunciado da seguinte forma: *)

Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall n, P n -> P (S n)) ->
    forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O PIF pode ser enunciado da seguinte forma:  *)

Definition PIF :=
  forall Q: nat -> Prop,
    (forall n, (forall m, m<n -> Q m) -> Q n) ->
    forall n, Q n.

(** Prove que PIM e PIF são equivalentes, ou seja, prove os lemas e o teorema a seguir: *)

Lemma PIF_to_PIM: PIF -> PIM.
Proof.
unfold PIM.
intros.
apply H. destruct n0.
  - intro. assumption.
  - intro. apply H1. apply H2. unfold lt. apply le_n. 
Qed.

Lemma strong_induction :
PIM -> PIF.
Proof.
unfold PIF.
intros HPIM Q HPIF n. apply HPIF. induction n. 
  - lia. 
  - intros m Hm. apply HPIF. intros k Hk. apply IHn. lia. 
Qed. 
Search (?m < ?n -> ?Q ?m).
Lemma strong_induction' :
PIM -> PIF.
Proof.
unfold PIF. 
intros HPIM Q HPIF n. apply HPIM.  
  - apply HPIF. lia. 
  - intros m Hm. apply HPIF.  intros k Hk.   
Admitted.

Lemma IND_TO_STRONG: PIM -> PIF.
Proof.
  unfold PIM, PIF.
  intros ind Q prog n.
  cut (forall m, m <= n -> Q m). (* [1] *)
  - intro. apply H. apply le_n. 
  - generalize dependent n.
    apply (ind (fun n => forall m, m <= n -> Q m)). (* [2] *)
    + intuition. apply le_n_0_eq in H. inversion H. apply prog. lia.
    + intuition. apply prog. intros. apply H. lia.
Qed.

Lemma strong_induction'' :
  PIF.
Proof.
  unfold PIF.
  intros P HPIF n.
  assert (forall k, k < n -> P k).
  { induction n as [|n' IHn'].
    - intuition. lia.
    - intros m Hm. apply HPIF. intros k Hk. apply IHn'. lia. 
  } 
  - apply HPIF. assumption.
Qed.

Lemma PIM_to_PIF: PIM -> PIF.
Proof. 
intros ind Q prog n. apply (ind (fun k => k <= n -> Q k)).
  - intros. apply prog. destruct m; lia.
  - intros.  apply ind. 
    + apply prog. lia.
    +    admit.
  - lia.
Admitted.




Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  split.
    - apply PIM_to_PIF.
    - apply PIF_to_PIM.
Qed.