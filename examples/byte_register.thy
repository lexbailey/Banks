(*
This is the byte register example from Michael Banks's PhD thesis [On Confidentiality and Formal
Methods] Section 3.4.3, page 37

This is a register that stores a byte value and an error bit. It also defines a double operation
which doubles the value in the register, if possible.
*)

theory byte_register
  imports "HOL-Library.Word" "../Banks/banks"  (*NO_CI*)
  (*CI_ONLY imports "HOL-Library.Word" "Banks.banks"  CI_ONLY*)
begin

unbundle UTP_Syntax
unbundle Expression_Syntax

type_synonym bit = "1 word"

alphabet \<alpha>ST = 
  reg :: "8 word"
  err :: bit

alphabet \<alpha>H =
  reg\<^sub>H :: "4 word"
  err\<^sub>H :: bit

alphabet \<alpha>L =
  reg\<^sub>L :: "4 word"
  err\<^sub>L :: bit

(* ST defines what states are valid *)
(*
definition ST
  where "ST = (reg \<ge> 0 \<and> reg \<le> 255 \<and> err \<ge> 0 \<and> err \<le> 1)\<^sub>e"
*)

(* DBL doubles the number, if it is low enough to double without overflow *)
definition DBL
(*  where "DBL = (reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e"*)
  where "DBL = (reg \<ge> 0 \<and> reg \<le> 127 \<and> err = 0) \<turnstile>\<^sub>n (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e"

(* A view of the high nibble *)
definition Hv
  where "Hv = OK (((vu:reg\<^sub>H = (ucast (drop_bit 4 sys:reg))) \<and> (vu:err\<^sub>H = sys:err))\<^sub>e \<up> \<^bold>v\<^sub>D)"

(* A view of the low nibble *)
definition Lv
  where "Lv = OK (((vu:reg\<^sub>L = (ucast (take_bit 4 sys:reg))) \<and> (vu:err\<^sub>L = sys:err))\<^sub>e \<up> \<^bold>v\<^sub>D)"

(* These are both healthy *)
lemma hv_is_vhd: "Hv is VHD"
  by (pred_auto_banks add: Hv_def)

lemma lv_is_vhd: "Lv is VHD"
  by (pred_auto_banks add: Lv_def)

(*
Consider an example where the register stores the value 60

60(b10) = 111100(b2)

Here is an observation on the final state, with this value
*)

definition \<Phi> where "\<Phi> = (reg = 60 \<and> err = 0)\<^sub>e"

(*
  Hv and Lv extract the high nibble and low nibble, respectively
  ..111100(b2)
  HHHH     = 11(b2)   = 3(b10)
      LLLL = 1100(b2) = 12(b10)
*)

lemma "(((L (Hv \<down> \<^bold>v\<^sub>D) (\<Delta> \<Phi>))) \<down> vu\<^sup>2) = \<Delta> (reg\<^sub>H = 3 \<and> err\<^sub>H = 0)\<^sub>e"
  by (pred_auto_banks add: Hv_def \<Phi>_def)

lemma "(((L (Lv \<down> \<^bold>v\<^sub>D) (\<Delta> \<Phi>))) \<down> vu\<^sup>2) = \<Delta> (reg\<^sub>L = 12 \<and> err\<^sub>L = 0)\<^sub>e"
  by (pred_auto_banks add: Lv_def \<Phi>_def)

definition Loc_H_DBL where "Loc_H_DBL = (L\<^sub>D (Hv) (DBL))"
definition Loc_L_DBL where "Loc_L_DBL = (L\<^sub>D (Lv) (DBL))"

lemma drop_word_lt_div: "(r :: 8 word) \<le> a \<longrightarrow> (drop_bit k r) \<le> a div 2^k"
  by (simp add: drop_bit_eq_div word_le_nat_alt unat_div_distrib div_le_mono)

term "pre\<^sub>D(Loc_H_DBL)"

lemma "pre\<^sub>D(Loc_H_DBL) = true"
  apply (subst Loc_H_DBL_def)
  apply (subst pre_design_def)
  apply (subst banks_defs Hv_def DBL_def)+
  apply (pred_simp add: banks_defs)
  apply pred_auto

(*lemma "pre\<^sub>D(Loc_H_DBL) = \<Delta> ((reg\<^sub>H \<ge> 0 \<and> reg\<^sub>H \<le> 7 \<and> err\<^sub>H = 0)\<^sub>e \<up> vu)"*)
lemma "(pre\<^sub>D(Loc_H_DBL) \<down> vu\<^sup>2) = ((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e)"
  apply (subst Loc_H_DBL_def)
  apply (subst pre_design_def)
  apply (subst banks_defs Hv_def DBL_def)+
  apply (pred_simp add: drop_word_lt_div)
    apply transfer
  apply (simp add: drop_bit_eq_div word_le_nat_alt unat_div_distrib div_le_mono)
  apply auto


  value "take_bit 2 4::(4 word)"

lemma "(take_bit 2 3::(4 word)) = 3"
  apply unat_arith
  apply smt

lemma "pre\<^sub>D(Loc_L_DBL) = false"
  apply (subst Loc_L_DBL_def)
  apply (subst pre_design_def)
  apply (subst banks_defs Lv_def DBL_def)+
  apply pred_auto
  apply unat_arith
  apply simp
  apply smt
  

(* TODO is this right? *)
lemma
 "
  (L\<^sub>D (Hv) (DBL))
  =
  (as_design_view(
    ((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e)
     \<turnstile>\<^sub>r
     ((((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> err\<^sub>H\<^sup>> = 0)\<^sub>e)
  ))
  "
  apply (unfold DBL_def)
  apply (subst view_local_design)
    apply (fact hv_is_vhd)
   apply (simp add: Hv_def banks_defs)
   apply pred_simp
  
  apply (pred_auto_banks add: Hv_def DBL_def)
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
          apply (transfer, auto) defer
  apply smt




lemma " (as_design_view(
    ((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e)
     \<turnstile>\<^sub>r
     ((((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> err\<^sub>H\<^sup>> = 0)\<^sub>e)
  )) (
   \<lparr> ok\<^sub>v = True, \<dots> = \<lparr> sys\<^sub>v = \<lparr> reg\<^sub>v = 255, err\<^sub>v = 0 \<rparr>, vu\<^sub>v = \<lparr> reg\<^sub>H\<^sub>v = 0, err\<^sub>H\<^sub>v = 0 \<rparr> \<rparr>  \<rparr>
  ,\<lparr> ok\<^sub>v = False, \<dots> = \<lparr> sys\<^sub>v = \<lparr> reg\<^sub>v = 255, err\<^sub>v = 0 \<rparr>, vu\<^sub>v = \<lparr> reg\<^sub>H\<^sub>v = 0, err\<^sub>H\<^sub>v = 0 \<rparr> \<rparr>  \<rparr>
  )"
  apply (pred_auto_banks add: Hv_def DBL_def)


lemma "
  (L ((Hv \<down> \<^bold>v\<^sub>D)) (DBL \<down> \<^bold>v\<^sub>D\<^sup>2)) \<down> vu\<^sup>2
  =
  (
    ((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e)
     \<turnstile>\<^sub>r
     ((((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> err\<^sub>H\<^sup>> = 0)\<^sub>e)
  ) \<down> \<^bold>v\<^sub>D\<^sup>2
  "
  apply (pred_auto_banks add: Hv_def DBL_def)

  nitpick



term pre_design

lemma loc_l_dbl_pre_false: "(pre\<^sub>D(LocLDBL)) = false"
  apply (subst LocLDBL_def, subst pre_design_def, subst L\<^sub>D_def)
  apply (pred_auto_banks)
  apply (pred_auto_banks add: DBL_def Lv_def LocLDBL_def)

lemma "LocLDBL = true"
proof -
  have "LocLDBL = false \<turnstile> a"
    apply (pred_auto_banks add: loc_l_dbl_pre_false)
  apply (subst LocLDBL_def)
  apply (subst L\<^sub>D_def)

(* DBL2 doubles the number, if it is low enough to double without overflow, but unlike DBL, it
explicitly defines the behaviour in the overflow case. If overflow is detected, then the err bit is
set and the register contains an arbitrary value.*)
definition DBL2
  where "DBL2 = (
    (reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 255 \<and> err\<^sup>< = 0)\<^sub>e
    \<turnstile>\<^sub>r
    ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0) \<lhd> (reg \<le> 127) \<rhd> (reg\<^sup>> \<ge> 0 \<and> reg\<^sup>> \<le> 255 \<and> err\<^sup>> = 0))\<^sub>e
  )"

(* DBL is refined by DBL2 *)
lemma "DBL \<sqsubseteq> DBL2"
  apply (pred_auto_banks add: DBL_def DBL2_def)
  by (transfer;auto)+
    

end
