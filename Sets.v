(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* A set with elements in U, is defined by its belonging relation,      *)
(* the equality is defined by the extensionality axiom.                 *)

(* The following notions are defined :                                  *)
(*      - U_set :  set with elements in U,                              *)
(*      - U_set_eq : 2 sets with same elements are equals,              *)
(*      - Empty :  set with no elements,                                *)
(*              no constructors                                         *)
(*      - Full :  set with all the elements,                            *)
(*              constructor : In_full                                   *)
(*      - Single : set with a unique element {x},                       *)
(*              constructor : In_single                                 *)
(*      - Included : like imply,                                        *)
(*      - Union : binary operation like or,                             *)
(*              constructors : In_left, In_right.                       *)
(*      - Inter : binary operation like and,                            *)
(*              constructors : In_inter.                                *)

Require Export Omega.
Require Export Peano_dec.

Section U_SETS.

Variable U : Set.

Definition U_set := U -> Prop.

Axiom U_set_eq : forall E F : U_set, (forall x : U, E x <-> F x) -> E = F.

Lemma U_eq_set : forall E F : U_set, E = F -> forall x : U, E x -> F x.
Proof.
        intros; rewrite <- H; trivial.
Qed.

Lemma U_set_eq_commut : forall E F : U_set, E = F -> F = E.
Proof.
        auto.
Qed.

Lemma U_set_diff_commut : forall E F : U_set, E <> F -> F <> E.
Proof.
        intros; red in |- *; intros.
        elim H; apply U_set_eq_commut; trivial.
Qed.

Inductive Empty : U_set :=.

Inductive Full : U_set :=
    In_full : forall x : U, Full x.

Inductive Single (x : U) : U_set :=
    In_single : Single x x.

Lemma Single_equal : forall x y : U, Single x y -> x = y.
Proof.
        intros; inversion H; trivial.
Qed.

Lemma Single_equal_single : forall x y : U, Single x = Single y -> x = y.
Proof.
        intros; generalize (U_eq_set _ _ H x).
        intros; elim H0.
        trivial.

        apply In_single.
Qed.

Lemma Empty_nothing : forall x : U, ~ Empty x.
Proof.
        tauto.
Qed.

Lemma U_set_diff : forall E F : U_set, (exists x : U, E x /\ ~ F x) -> E <> F.
Proof.
        intros; red in |- *; intros.
        elim H; intros.
        elim H1; intros.
        elim H3; rewrite <- H0; auto.
Qed.

        Section INCLUSION.

Definition Included (E F : U_set) : Prop := forall x : U, E x -> F x.

Lemma Included_single :
 forall (E : U_set) (x : U), E x -> Included (Single x) E.
Proof.
        unfold Included in |- *; intros.
        inversion H0; rewrite <- H1; trivial.
Qed.

        End INCLUSION.

        Section UNION.

Inductive Union (E F : U_set) : U_set :=
  | In_left : forall x : U, E x -> Union E F x
  | In_right : forall x : U, F x -> Union E F x.

Lemma Union_eq :
 forall E F E' F' : U_set, E = E' -> F = F' -> Union E F = Union E' F'.
Proof.
        intros; elim H.
        elim H0; trivial.
Qed.

Lemma Union_neutral : forall e : U_set, Union Empty e = e.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        inversion H0.

        trivial.

        apply In_right; trivial.
Qed.

Lemma Union_commut : forall e1 e2 : U_set, Union e1 e2 = Union e2 e1.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; [ apply In_right | apply In_left ]; trivial.

        inversion H; [ apply In_right | apply In_left ]; trivial.
Qed.

Lemma Union_assoc :
 forall e1 e2 e3 : U_set, Union (Union e1 e2) e3 = Union e1 (Union e2 e3).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        inversion H0.
        apply In_left; trivial.

        apply In_right; apply In_left; trivial.

        apply In_right; apply In_right; trivial.

        inversion H.
        apply In_left; apply In_left; trivial.

        inversion H0.
        apply In_left; apply In_right; trivial.

        apply In_right; trivial.
Qed.

Lemma Not_union :
 forall (E1 E2 : U_set) (x : U), ~ E1 x -> ~ E2 x -> ~ Union E1 E2 x.
Proof.
        intros; red in |- *; intros.
        inversion H1.
        elim H; trivial.

        elim H0; trivial.
Qed.

Lemma Union_dec :
 forall (e1 e2 : U_set) (x : U),
 {e1 x} + {~ e1 x} -> {e2 x} + {~ e2 x} -> Union e1 e2 x -> {e1 x} + {e2 x}.
Proof.
        intros; case H.
        left; trivial.

        intros; case H0; intros.
        right; trivial.

        absurd (Union e1 e2 x).
        apply Not_union; trivial.

        trivial.
Qed.

Lemma Included_union : forall E F : U_set, Included E (Union E F).
Proof.
        unfold Included in |- *; intros.
        apply In_left; trivial.
Qed.

Lemma Union_absorb : forall E F : U_set, Included E F -> Union E F = F.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0; auto.

        apply In_right; trivial.
Qed.

        End UNION.

        Section INTERSECTION.

Inductive Inter (E F : U_set) : U_set :=
    In_inter : forall x : U, E x -> F x -> Inter E F x.

Lemma Inter_eq :
 forall E F E' F' : U_set, E = E' -> F = F' -> Inter E F = Inter E' F'.
Proof.
        intros; elim H.
        elim H0; trivial.
Qed.

Lemma Inter_neutral : forall e : U_set, Inter Full e = e.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; trivial.

        apply In_inter.
        apply In_full; trivial.

        trivial.
Qed.

Lemma Inter_empty : forall e : U_set, Inter e Empty = Empty.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; trivial.

        inversion H.
Qed.

Lemma Inter_commut : forall e1 e2 : U_set, Inter e1 e2 = Inter e2 e1.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; apply In_inter; trivial.

        inversion H; apply In_inter; trivial.
Qed.

Lemma Inter_assoc :
 forall e1 e2 e3 : U_set, Inter (Inter e1 e2) e3 = Inter e1 (Inter e2 e3).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; inversion H0.
        apply In_inter; trivial.
        apply In_inter; trivial.

        inversion H; inversion H1.
        apply In_inter; trivial.
        apply In_inter; trivial.
Qed.

Lemma Not_inter : forall (E1 E2 : U_set) (x : U), ~ E1 x -> ~ Inter E1 E2 x.
Proof.
        intros; red in |- *; intros.
        inversion H0.
        elim H; trivial.
Qed.

Lemma Included_inter : forall E F : U_set, Included (Inter E F) E.
Proof.
        unfold Included in |- *; intros.
        inversion H; trivial.
Qed.

Lemma Inter_absorb : forall E F : U_set, Included E F -> Inter E F = E.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0; auto.

        apply In_inter; auto.
Qed.

        End INTERSECTION.

        Section DIFFERENCE.

Inductive Differ (E F : U_set) : U_set :=
    In_differ : forall x : U, E x -> ~ F x -> Differ E F x.

Lemma Differ_E_E : forall E : U_set, Differ E E = Empty.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        absurd (E x); trivial.

        inversion H.
Qed.

Lemma Differ_empty : forall E : U_set, Differ E Empty = E.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; trivial.

        apply In_differ.
        trivial.

        tauto.
Qed.

Lemma Union_differ_inter :
 forall E F : U_set,
 (forall x : U, {F x} + {~ F x}) -> Union (Differ E F) (Inter E F) = E.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0.
        inversion H1; trivial.

        inversion H1; trivial.

        case (H x); intros.
        apply In_right; apply In_inter; trivial.

        apply In_left; apply In_differ; trivial.
Qed.

        End DIFFERENCE.

        Section MIXED_PROPERTIES.

Lemma Distributivity_inter_union :
 forall E F G : U_set, Inter E (Union F G) = Union (Inter E F) (Inter E G).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H; inversion H1.
        apply In_left; apply In_inter; auto.

        apply In_right; apply In_inter; auto.

        inversion H; inversion H0.
        apply In_inter.
        trivial.

        apply In_left; trivial.

        apply In_inter.
        trivial.

        apply In_right; trivial.
Qed.

Lemma Distributivity_union_inter :
 forall E F G : U_set, Union E (Inter F G) = Inter (Union E F) (Union E G).
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H.
        apply In_inter; apply In_left; trivial.

        inversion H0; apply In_inter; apply In_right; trivial.

        inversion H.
        inversion H0.
        apply In_left; trivial.

        inversion H1.
        apply In_left; trivial.

        apply In_right; apply In_inter; trivial.
Qed.

Lemma Union_inversion :
 forall E F G : U_set,
 Inter E F = Empty -> Inter E G = Empty -> Union E F = Union E G -> F = G.
Proof.
        intros; apply U_set_eq; split; intros.
        generalize (In_right E F x H2).
        rewrite H1; intros.
        inversion H3.
        absurd (Inter E F x).
        rewrite H; tauto.

        apply In_inter; auto.

        trivial.

        generalize (In_right E G x H2).
        rewrite <- H1; intros.
        inversion H3.
        absurd (Inter E G x).
        rewrite H0; tauto.

        apply In_inter; auto.

        trivial.
Qed.

Lemma Union_inversion2 :
 forall E F G H : U_set,
 Inter E F = Empty ->
 Inter E G = Empty ->
 Inter G H = Empty -> Union E F = Union G H -> F = Union G (Inter F H).
Proof.
        intros; apply U_set_eq; split; intros.
        generalize (In_right E F x H4).
        rewrite H3; intros.
        inversion H5.
        apply In_left; trivial.

        apply In_right; apply In_inter; trivial.

        inversion H4.
        generalize (In_left G H x H5).
        rewrite <- H3; intros.
        inversion H7.
        absurd (Inter E G x).
        rewrite H1; tauto.

        apply In_inter; trivial.

        trivial.

        inversion H5; trivial.
Qed.

Lemma Single_disjoint :
 forall (x : U) (E : U_set), ~ E x -> Inter (Single x) E = Empty.
Proof.
        intros; apply U_set_eq; split; intros.
        inversion H0.
        inversion H1; absurd (E x).
        trivial.

        rewrite H4; trivial.

        inversion H0.
Qed.

Lemma Single_single_disjoint :
 forall x y : U, x <> y -> Inter (Single x) (Single y) = Empty.
Proof.
        intros; apply Single_disjoint.
        red in |- *; intros H0; elim H; inversion H0; trivial.
Qed.

Lemma Union_single_single :
 forall (e : U_set) (x y : U),
 x <> y ->
 ~ e y -> Union (Single x) (Single y) = Union (Single y) e -> e = Single x.
Proof.
        intros; symmetry  in |- *; apply (Union_inversion (Single y)).
        apply Single_single_disjoint; auto.

        apply Single_disjoint; trivial.

        rewrite Union_commut; trivial.
Qed.

        End MIXED_PROPERTIES.

End U_SETS.
