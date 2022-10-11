(*
This is the byte register example from Michael Banks's PhD thesis [On Confidentiality and Formal
Methods] Section 3.4.3, page 37

This is a register that stores a byte value and an error bit. It also defines a double operation
which doubles the value in the register, if possible.
*)

theory byte_register
  imports Main "../Banks/banks" (*NO_CI*)
  (*CI_ONLY imports Main "Banks.banks" CI_ONLY*)
begin

alphabet \<alpha>ST = 
  reg :: int
  err :: int

alphabet \<alpha>H =
  reg\<^sub>H :: int
  err\<^sub>H :: int

alphabet \<alpha>L =
  reg\<^sub>L :: int
  err\<^sub>L :: int

(* ST defines what states are valid *)
definition ST
  where "ST = (reg \<ge> 0 \<and> reg \<le> 255 \<and> err \<ge> 0 \<and> err \<le> 1)\<^sub>e"

(* DBL doubles the number, if it is low enough to double without overflow *)
definition DBL
  where "DBL = (reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e"

(* A view of the high nibble *)
definition Hv
  where "Hv = OK (vu:reg\<^sub>H = floor (sys:\<^bold>v\<^sub>D:reg / 16) \<and> vu:err\<^sub>H = sys:\<^bold>v\<^sub>D:err)\<^sub>e"

(* A view of the low nibble *)
definition Lv
  where "Lv = OK (vu:reg\<^sub>L = sys:\<^bold>v\<^sub>D:reg mod 16 \<and> vu:err\<^sub>L = sys:\<^bold>v\<^sub>D:err)\<^sub>e"

(*
Consider an example where the register stores the value 60

60(b10) = 111100(b2)

Here is an observation on the final state, with this value
*)

definition \<Phi> where "\<Phi> = (reg = 60 \<and> err = 0)\<^sub>e \<up> \<^bold>v\<^sub>D\<^sup>>"

(*
  Hv and Lv extract the high nibble and low nibble, respectively
  ..111100(b2)
  HHHH     = 11(b2)   = 3(b10)
      LLLL = 1100(b2) = 12(b10)
*)

lemma "(L Hv \<Phi>) = (reg\<^sub>H = 3 \<and> err\<^sub>H = 0)\<^sub>e \<up> vu\<^sup>>"
  by (expr_simp_banks add: Hv_def \<Phi>_def)

lemma "(L Lv \<Phi>) = (reg\<^sub>L = 12 \<and> err\<^sub>L = 0)\<^sub>e \<up> vu\<^sup>>"
  by (expr_simp_banks add: Lv_def \<Phi>_def)

term "(Hv \<and> (ST \<up> \<^bold>v\<^sub>D \<up> sys))"

term "((L (Hv \<and> (ST \<up> \<^bold>v\<^sub>D \<up> sys)) (DBL)) \<down> vu\<^sup>2)"

term "(((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> err\<^sub>H\<^sup>> = 0)\<^sub>e)) \<down> \<^bold>v\<^sub>D\<^sup>2"

term "
  (L (Hv \<and> (ST \<up> \<^bold>v\<^sub>D \<up> sys)) DBL \<down> vu\<^sup>2)
  =
  ((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> err\<^sub>H\<^sup>> = 0)\<^sub>e) \<down> \<^bold>v\<^sub>D\<^sup>2
  "

lemma "
  (L (Hv \<and> (ST \<up> \<^bold>v\<^sub>D \<up> sys)) DBL \<down> vu\<^sup>2)
  =
  ((reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> err\<^sub>H\<^sup>> = 0)\<^sub>e) \<down> \<^bold>v\<^sub>D\<^sup>2
  "
  apply (expr_simp_banks)
  apply pred_auto

  term "DBL"
  term "L (Lv \<and> (ST \<up> \<^bold>v\<^sub>D \<up> sys)) DBL"

lemma "
  (L (Lv \<and> (ST \<up> \<^bold>v\<^sub>D \<up> sys)) (DBL))
  =
  true
  "
  apply (expr_simp_banks)
  apply pred_auto

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
  by (expr_simp_banks add: DBL_def DBL2_def, pred_auto)

end
