Require Import
  Setoid Morphisms
  Unicode.Utf8
  canonical_names
  universal_algebra.

Section contents.

  Variable Sorts: Set.

  Section map_op.

    (* Given maps between two realizations of the sorts, there are maps between the corresponding op_types*)

    Context {A B: Sorts → Type}
      `{Π a, Equiv (A a)} `{Π a, Equiv (B a)}
      (ab: Π a, A a → B a)
      (ba: Π a, B a → A a)
      `{Π a, Proper (equiv ==> equiv) (ab a)}
      `{Π a, Proper (equiv ==> equiv) (ba a)}.

    Fixpoint map_op {o: OpType Sorts}: op_type A o → op_type B o :=
      match o return op_type A o → op_type B o with
      | ne_list.one u => ab u
      | ne_list.cons _ _ => λ x y => map_op (x (ba _ y))
      end.

    Global Instance map_op_proper o: Proper ((=) ==> (=)) (@map_op o).
    Proof. unfold equiv. induction o; simpl; firstorder. Qed.
      (* todo: can't we make this nameless? *)

  End map_op.

  (* If the maps between the sorts are eachother's inverse, then so are the two generated op_type maps: *)

  Context {A B: Sorts → Type} {e: Π a, Equiv (B a)} `{Π b, Equivalence (e b)} 
   (ab: Π a, A a → B a) (ba: Π a, B a → A a).

  Implicit Arguments ab [a].
  Implicit Arguments ba [a].

   Context `(iso: Π a (x: B a), ab (ba x) = x).

  Lemma map_iso o (x: op_type B o) (xproper: Proper (=) x):
    map_op ab ba (map_op ba ab x) = x.
  Proof with auto; try reflexivity.
   induction o; simpl; intros...
   intros x0 y H0.
   change (map_op ab ba (map_op ba ab (x (ab (ba x0)))) = x y).
   transitivity (x (ab (ba x0))).
    apply IHo, xproper...
   apply xproper. rewrite iso, H0...
  Qed.

End contents.
