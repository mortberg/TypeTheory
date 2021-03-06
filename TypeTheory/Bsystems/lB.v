(** * The type of the unital lB-systems

By Vladimir Voevodsky, started on Jan. 18, 2015 *)


Require Import UniMath.Foundations.All.

Require Import TypeTheory.Csystems.hSet_ltowers.
Require Export TypeTheory.Bsystems.lB_non_unital.
Require Export TypeTheory.Bsystems.lB0.


(** *** Condition dltT *)

Definition dltT_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.dltT_type ( @T_ax0 BB ) ( @T_ax1b BB ) ( @Tt_op BB ) ( dlt_ax1 dlt ) . 

(** *** Condition dltS *)

Definition dltS_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.dltS_type ( @T_ax1b BB ) ( @S_ax0 BB ) ( @St_op BB ) ( dlt_ax1 dlt ) .


(** *** Condition SdltT *)

Definition SdltT_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.SdltT_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( dlt_ax1 dlt ) ( @S_op BB ) .

(** *** Condition StdltTt *)

Definition StdltTt_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.StdltTt_type ( @T_ax0 BB ) ( @T_ax1a BB ) ( dlt_ax1 dlt ) ( @Tt_ax1 BB ) ( @St_op BB ) .

(** *** Condition dltSid *)

Definition dltSid_type { BB : lB_nu } ( dlt : dlt_layer ( @T_op BB ) ) :=
  dlt.dltSid_type ( @T_ax1b BB ) ( dlt_ax1 dlt ) ( @St_op BB ) .


(** *** Unital lB-system *)

Definition lB :=
  ∑ (BB : lB_nu) (dlt : dlt_layer ( @T_op BB )),
               ( ( ( dltT_type dlt ) × ( dltS_type dlt ) ) ×
                 ( ( SdltT_type dlt ) × ( StdltTt_type dlt ) ) )
               × ( dltSid_type dlt ).

(** This definition corresponds to the addition of Definition 3.2 in arXiv:1410.5389v1
    of the axioms, only the packaging order is different in irrelevant ways
    ([lB_to_lB0] below is not just a projection). *)



Definition lB_to_lB_nu : lB -> lB_nu := pr1 .
Coercion lB_to_lB_nu : lB >-> lB_nu .

Definition lB_to_lB0 ( BB : lB ) : lB0system :=
  tpair ( fun BB : lB0system_non_unital => dlt_layer ( @T_op BB ) ) BB ( pr1 ( pr2 BB ) ) . 
Coercion lB_to_lB0 : lB >-> lB0system .


Definition dltT { BB : lB } : dltT_type BB := pr1 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition dltS { BB : lB } : dltS_type BB := pr2 ( pr1 ( pr1 ( pr2 ( pr2 BB ) ) ) ) .

Definition SdltT { BB : lB } : SdltT_type BB := pr1 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition StdltTt { BB : lB } : StdltTt_type BB := pr2 ( pr2 ( pr1 ( pr2 ( pr2 BB ) ) ) ) . 

Definition dltSid { BB : lB } : dltSid_type BB := pr2 ( pr2 ( pr2 BB ) ) . 








(* End of the file lB.v *)
