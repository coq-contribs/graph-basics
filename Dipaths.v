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



(* Different definitions of pathes in a directed graph.                 *)

(* The following notions are defined :                                  *)
(*      - D_walk : list of vertices joined one by one by arcs,          *)
(*                constructors : DW_null, DW_step;                      *)
(*      - D_trail : walk without repetition of arcs,                    *)
(*              constructors : DT_null, DT_step;                        *)
(*      - D_path : trail without repetition of inner vertices,          *)
(*              constructors : DP_null, DP_step;                        *)
(*      - D_closed_walk, D_closed_trail, D_cycle.                       *)

Require Import Digraphs.

Section DIRECTED_PATHES.

Variable v : V_set.

Variable a : A_set.

Inductive D_walk : Vertex -> Vertex -> V_list -> A_list -> Set :=
  | DW_null : forall x : Vertex, v x -> D_walk x x V_nil A_nil
  | DW_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_walk y z vl al ->
      a (A_ends x y) -> D_walk x z (y :: vl) (A_ends x y :: al).

Definition D_closed_walk :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_walk x x vl al.

Inductive D_trail : Vertex -> Vertex -> V_list -> A_list -> Set :=
  | DT_null : forall x : Vertex, v x -> D_trail x x V_nil A_nil
  | DT_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_trail y z vl al ->
      a (A_ends x y) ->
      ~ In (A_ends x y) al -> D_trail x z (y :: vl) (A_ends x y :: al).

Definition D_closed_trail :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_trail x x vl al.

Inductive D_path : Vertex -> Vertex -> V_list -> A_list -> Set :=
  | DP_null : forall x : Vertex, v x -> D_path x x V_nil A_nil
  | DP_step :
      forall (x y z : Vertex) (vl : V_list) (al : A_list),
      D_path y z vl al ->
      a (A_ends x y) ->
      ~ In y vl ->
      (In x vl -> x = z) ->
      ~ In (A_ends x y) al -> D_path x z (y :: vl) (A_ends x y :: al).

Definition D_cycle :=
  forall (x : Vertex) (vl : V_list) (al : A_list), D_path x x vl al.


Lemma D_trail_isa_walk :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (t : D_trail x y vl al),
 D_walk x y vl al.
Proof.
        intros x y vl al t; elim t; intros.
        apply DW_null; trivial.

        apply DW_step; trivial.
Qed.

Lemma D_path_isa_trail :
 forall (x y : Vertex) (vl : V_list) (al : A_list) (p : D_path x y vl al),
 D_trail x y vl al.
Proof.
        intros x y vl al p; elim p; intros.
        apply DT_null; trivial.

        apply DT_step; trivial.
Qed.

End DIRECTED_PATHES.
