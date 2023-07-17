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
  reg :: nat
  err :: bit

alphabet \<alpha>H =
  reg\<^sub>H :: nat
  err\<^sub>H :: bit

alphabet \<alpha>L =
  reg\<^sub>L :: nat
  err\<^sub>L :: bit

(* ST defines what states are valid *)

definition ST
  where "ST = (reg \<ge> 0 \<and> reg \<le> 255 \<and> err \<ge> 0 \<and> err \<le> 1)\<^sub>e"


(* DBL doubles the number, if it is low enough to double without overflow *)
definition DBL
(*  where "DBL = (reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e"*)
  where "DBL = (reg \<ge> 0 \<and> reg \<le> 127 \<and> err = 0) \<turnstile>\<^sub>n (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e"

lemma DBL_r_design: "DBL = (reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e"
  by (expr_simp add: DBL_def)

lemma DBL_design: "DBL = ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2) \<turnstile> ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2)"
  by (pred_simp add: DBL_def DBL_r_design)

(* A view of the high nibble *)
definition Hv
  where "Hv = ((vu:reg\<^sub>H = (drop_bit 4 sys:reg)) \<and> (vu:err\<^sub>H = sys:err))\<^sub>e"

(* A view of the low nibble *)
definition Lv
  where "Lv = ((vu:reg\<^sub>L = (take_bit 4 sys:reg)) \<and> (vu:err\<^sub>L = sys:err))\<^sub>e"

(* These are both healthy *)
lemma hv_is_vhd: "Hv is VH"
  by (pred_auto_banks add: Hv_def)

lemma lv_is_vhd: "Lv is VH"
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

lemma "(((L (Hv) (\<Delta> \<Phi>))) \<down> vu\<^sup>2) = \<Delta> (reg\<^sub>H = 3 \<and> err\<^sub>H = 0)\<^sub>e"
  by (pred_auto_banks add: Hv_def \<Phi>_def)

lemma "(((L (Lv) (\<Delta> \<Phi>))) \<down> vu\<^sup>2) = \<Delta> (reg\<^sub>L = 12 \<and> err\<^sub>L = 0)\<^sub>e"
  by (pred_auto_banks add: Lv_def \<Phi>_def)

definition Loc_H_DBL where "Loc_H_DBL = (L\<^sub>D (Hv) (DBL))"
definition Loc_L_DBL where "Loc_L_DBL = (L\<^sub>D (Lv) (DBL))"


lemma drop_8word_lt_div:
  assumes "(r :: 8 word) \<le> a"
  shows "(drop_bit k r) \<le> a div 2^k"
  using assms
  by (simp add: drop_bit_eq_div word_le_nat_alt unat_div_distrib div_le_mono)

lemma drop_8word_lt_div_inv:
  assumes "(drop_bit k r) < a div 2^k"
  shows "(r :: 8 word) < a"
  using assms
  by (metis drop_8word_lt_div drop_bit_eq_div linorder_not_less)

lemma drop_4_8_128:
  assumes "drop_bit 4 r < (8::8 word)"
  shows "r < 128"
proof -
  have expand_8: "(8 :: 8 word) = (128 div (2^4))" by simp
  from assms show ?thesis
    apply (subst (asm) expand_8)
    by (erule_tac drop_8word_lt_div_inv)
qed

lemma le_to_lt127: "(x \<le> (127 :: 8 word)) = (x < (128 :: 8 word))"
   apply transfer
   by auto

lemma le_to_lt7: "(x \<le> (7 :: 8 word)) = (x < (8 :: 8 word))"
   apply transfer
   by auto

lemma drop_4_le_7_127:
  assumes "drop_bit 4 r \<le> (7::8 word)"
  shows "r \<le> (127 :: 8 word)"
  using assms
  apply (subst le_to_lt127)
  apply (subst (asm) le_to_lt7)
  apply (simp add: assms drop_4_8_128)
  dones

declare [[smt_trace = true]]
declare [[smt_oracle = true]]

(*
lemma loc_l_dbl_simp: "Loc_L_DBL = ((\<not>L\<^sub>D (Lv) (\<not> ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e  \<up> \<^bold>v\<^sub>D\<^sup>2)))) \<turnstile> ((L\<^sub>D (Lv) ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2)))"
  by (pred_auto_banks add: Lv_def DBL_def Loc_L_DBL_def)

lemma "Loc_H_DBL = ((\<not>L\<^sub>D (Hv) (\<not> ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e  \<up> \<^bold>v\<^sub>D\<^sup>2)))) \<turnstile> ((L\<^sub>D (Hv) ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2)))"
  by (pred_auto_banks add: Hv_def DBL_def Loc_H_DBL_def)

lemma "Loc_L_DBL = true"
  apply (pred_auto_banks add: Lv_def DBL_def Loc_L_DBL_def)
  by smt
*)

lemma loc_l_dbl_simp: "Loc_L_DBL = 
    (\<not>L (Lv) (\<not> ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e )))
   \<turnstile>\<^sub>r 
    (L (Lv) ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e ))
  "
  by (pred_auto_banks add: Lv_def DBL_def Loc_L_DBL_def)

lemma 
  assumes "V is VH"
  shows "\<not>(L V (\<not>Pre\<^sup><)) = (\<forall> x \<Zspot> (V) \<longrightarrow> (Pre \<up> sys))"
  apply pred_auto_banks

lemma "(\<not>L (Lv) (\<not> ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e ))) = false"
  apply (subst L_def)
  apply (pred_auto_banks add: Lv_def)
  nitpick
  

lemma "Loc_L_DBL = true"
  apply (subst loc_l_dbl_simp)
  apply (subst Lv_def)
  apply (subst L_def)
  apply (pred_auto_banks add: Lv_def DBL_def Loc_L_DBL_def)
   apply transfer
   apply auto
   



declare [[smt_solver = cvc4]]
(* TODO get H working *)


lemma "Loc_H_DBL = ((vu:reg\<^sub>H\<^sup>< \<ge> 0 \<and> vu:reg\<^sub>H\<^sup>< \<le> 7 \<and> vu:err\<^sub>H\<^sup>< = 0)\<^sub>e) \<turnstile>\<^sub>r (((vu:reg\<^sub>H\<^sup>> = vu:reg\<^sub>H\<^sup>< * 2) \<or> (vu:reg\<^sub>H\<^sup>> = (vu:reg\<^sub>H\<^sup>< * 2) + 1)) \<and> vu:err\<^sub>H\<^sup>> = 0)\<^sub>e"
  apply (subst Loc_H_DBL_def)
  apply (pred_auto_banks add: DBL_def Hv_def)
             apply (simp add: drop_4_le_7_127)




(* Attempt to split out a smaller proof *)

lemma "((\<not>L\<^sub>D (Hv) (\<not> ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e  \<up> \<^bold>v\<^sub>D\<^sup>2)))) = ((vu:reg\<^sub>H\<^sup>< \<ge> 0 \<and> vu:reg\<^sub>H\<^sup>< \<le> 7 \<and> vu:err\<^sub>H\<^sup>< = 0)\<^sub>e  \<up> \<^bold>v\<^sub>D\<^sup>2)"
  apply (pred_auto_banks add: Hv_def)
  defer
  defer
  quickcheck

lemma "((\<not>L\<^sub>D (Hv) (\<not> ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e  \<up> \<^bold>v\<^sub>D\<^sup>2)))) = true"
  apply (subst L\<^sub>D_def)
  apply (simp)
  apply (subst \<Delta>\<^sub>D_def)
  apply (subst to_viewed_design_def)
  apply (simp)
  apply (subst pair_map_def)
  apply (subst Hv_def)+
  apply (subst OK_def)+
  apply (subst id_def)+
  apply expr_simp
  apply pred_simp
  

lemma "((L\<^sub>D (Hv) ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2))) = (((((vu:reg\<^sub>H\<^sup>> = vu:reg\<^sub>H\<^sup>< * 2) \<or> (vu:reg\<^sub>H\<^sup>> = (vu:reg\<^sub>H\<^sup>< * 2) + 1)) \<and> vu:err\<^sub>H\<^sup>> = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2))"
  apply (pred_auto_banks add: Hv_def)


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


(* Increments the register value as long as it is less than 16 *)
definition TestSys
  where "TestSys = (
    true
    \<turnstile>\<^sub>r
    (reg\<^sup>> = reg\<^sup>< + 1)\<^sub>e
  )"

definition Loc_L_TestSys where
  "Loc_L_TestSys = L\<^sub>D (Lv) (TestSys)"



lemma
  fixes a :: "(('a \<alpha>ST_scheme, 'b \<alpha>L_scheme, 'c) viewed_system_scheme des_vars_ext * ('a \<alpha>ST_scheme, 'b \<alpha>L_scheme, 'c) viewed_system_scheme des_vars_ext)"
  assumes "(to_viewed_design TestSys) a"
  assumes "(\<Delta>\<^sub>D Lv) a"
  shows "Loc_L_TestSys a = (true \<turnstile> ((vu:reg\<^sub>L\<^sup>> = (vu:reg\<^sub>L\<^sup>< + 1))\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>2)) a"
  apply (subst Loc_L_TestSys_def)
  apply (subst TestSys_def)
  apply (subst Lv_def)
  apply (subst L\<^sub>D_def)
  apply (subst \<Delta>\<^sub>D_def)
  apply (subst to_viewed_design_def)
  apply simp
  apply (subst pair_map_def)
  apply expr_simp
  apply pred_simp
  (*apply (pred_auto_banks add: Loc_L_TestSys_def Lv_def TestSys_def)
  quickcheck
*)
end
