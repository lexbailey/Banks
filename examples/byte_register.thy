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
  where "DBL = Sys ((reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 127 \<and> err\<^sup>< = 0)\<^sub>e \<turnstile>\<^sub>r (reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0)\<^sub>e)"

(* A view of the high nibble *)
definition Hv
  where "Hv = OK (vu:\<^bold>v\<^sub>D:reg\<^sub>H = floor (sys:\<^bold>v\<^sub>D:reg / 16) \<and> vu:\<^bold>v\<^sub>D:err\<^sub>H = sys:\<^bold>v\<^sub>D:err)\<^sub>e"

(* A view of the low nibble *)
definition Lv
  where "Lv = OK (vu:\<^bold>v\<^sub>D:reg\<^sub>L = sys:\<^bold>v\<^sub>D:reg mod 16 \<and> vu:\<^bold>v\<^sub>D:err\<^sub>L = sys:\<^bold>v\<^sub>D:err)\<^sub>e"

(*
Consider an example where the register stores the value 60

60(b10) = 111100(b2)

Here is an observation on the final state, with this value
*)
definition \<Phi> where "\<Phi> =  ((Sys1 ((reg = 60 \<and> err = 0)\<^sub>e \<up> \<^bold>v\<^sub>D))\<^sup>>)\<^sub>e"

(*
  Hv and Lv extract the high nibble and low nibble, respectively
  ..111100(b2)
  HHHH     = 11(b2)   = 3(b10)
      LLLL = 1100(b2) = 12(b10)
*)
lemma "(L Hv \<Phi>) = ((Vu1 ((reg\<^sub>H = 3 \<and> err\<^sub>H = 0)\<^sub>e \<up> \<^bold>v\<^sub>D))\<^sup>>)\<^sub>e"
  by (expr_simp_banks add: Hv_def \<Phi>_def)

lemma "(L Lv \<Phi>) = ((Vu1 ((reg\<^sub>L = 12 \<and> err\<^sub>L = 0)\<^sub>e \<up> \<^bold>v\<^sub>D))\<^sup>>)\<^sub>e"
  by (expr_simp_banks add: Lv_def \<Phi>_def)

(* DBL2 doubles the number, if it is low enough to double without overflow, but unlike DBL, it
explicitly defines the behaviour in the overflow case. If overflow is detected, then the err bit is
set and the register contains an arbitrary value.*)
definition DBL2
  where "DBL2 = Sys (
    (reg\<^sup>< \<ge> 0 \<and> reg\<^sup>< \<le> 255 \<and> err\<^sup>< = 0)\<^sub>e
    \<turnstile>\<^sub>r
    ((reg\<^sup>> = reg\<^sup>< * 2 \<and> err\<^sup>> = 0) \<lhd> (reg \<le> 127) \<rhd> (reg\<^sup>> \<ge> 0 \<and> reg\<^sup>> \<le> 255 \<and> err\<^sup>> = 0))\<^sub>e
  )"

(* DBL is refined by DBL2 *)
lemma "DBL \<sqsubseteq> DBL2"
  by (expr_simp_banks add: DBL_def DBL2_def, pred_auto)

term Lv


term "(reg\<^sub>L \<ge> 0 \<and> reg\<^sub>L \<le> 7 \<and> err\<^sub>L = 0)\<^sub>e"

term "(((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> (err\<^sub>H\<^sup>> = 0))\<^sub>e"

term "L (Hv \<and> Sys1 (ST \<up> \<^bold>v\<^sub>D)) DBL"

term "L (Hv \<and> Sys1 (ST \<up> \<^bold>v\<^sub>D)) DBL"

term "(((vu:\<^bold>v\<^sub>D:reg\<^sub>H\<^sup>> = (vu:v\<^sub>D:reg\<^sub>H\<^sup>< * 2)) \<or> (vu:v\<^sub>D:reg\<^sub>H\<^sup>> = ((vu:v\<^sub>D:reg\<^sub>H\<^sup>< * 2) + 1))) \<and> (vu:v\<^sub>D:err\<^sub>H\<^sup>> = 0))\<^sub>e"

term "(Vu1 (reg\<^sub>H \<ge> 0 \<and> reg\<^sub>H \<le> 7 \<and> err\<^sub>H = 0)\<^sub>e)\<^sup><"
term "
  (Vu1 (\<^bold>v\<^sub>D:reg\<^sub>H \<ge> 0 \<and> \<^bold>v\<^sub>D:reg\<^sub>H \<le> 7 \<and> \<^bold>v\<^sub>D:err\<^sub>H = 0)\<^sub>e)\<^sup><
  \<turnstile>\<^sub>r
  (((vu:\<^bold>v\<^sub>D:reg\<^sub>H\<^sup>> = (vu:v\<^sub>D:reg\<^sub>H\<^sup>< * 2)) \<or> (vu:v\<^sub>D:reg\<^sub>H\<^sup>> = ((vu:v\<^sub>D:reg\<^sub>H\<^sup>< * 2) + 1))) \<and> (vu:v\<^sub>D:err\<^sub>H\<^sup>> = 0))\<^sub>e
"

term "(L (Hv \<and> Sys1 (ST \<up> \<^bold>v\<^sub>D)) DBL) =(
  (reg\<^sub>H\<^sup>< \<ge> 0 \<and> reg\<^sub>H\<^sup>< \<le> 7 \<and> err\<^sub>H\<^sup>< = 0)\<^sub>e
  \<turnstile>\<^sub>r
  (((reg\<^sub>H\<^sup>> = (reg\<^sub>H\<^sup>< * 2)) \<or> (reg\<^sub>H\<^sup>> = ((reg\<^sub>H\<^sup>< * 2) + 1))) \<and> (err\<^sub>H\<^sup>> = 0))\<^sub>e)
"


term "(Sys1 (ST \<up> \<^bold>v\<^sub>D))\<^sup><"


term "(Lv \<and> Sys1 (ST \<up> \<^bold>v\<^sub>D))"

term "L (Lv \<and> Sys1 (ST \<up> \<^bold>v\<^sub>D)) DBL2"

term "(reg\<^sub>L \<ge> 0 \<and> reg\<^sub>L \<le> 15 \<and> err\<^sub>L = 0)\<^sub>e"

term "((reg\<^sub>L\<^sup>> = (reg\<^sub>L\<^sup>< * 2) mod 16 \<and> err\<^sub>L\<^sup>> = 0) \<or> (reg\<^sub>L\<^sup>> \<ge> 0 \<and> reg\<^sub>L\<^sup>> \<le> 15 \<and> err\<^sub>L\<^sup>> = 1))\<^sub>e"


lemma "L (Lv \<and> Sys1 (ST \<up> \<^bold>v\<^sub>D)) DBL2"

end
