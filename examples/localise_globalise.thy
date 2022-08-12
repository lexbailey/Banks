theory localise_globalise
  imports Main "../banks"
begin

alphabet sys_vars =
  x :: int
  y :: int

alphabet v1_view_vars =
  a1 :: int
  b1 :: int

type_synonym v1_al = "(sys_vars, v1_view_vars) viewed_system"

definition V1 where "V1 = (
    vu:a1 = sys:x \<and> vu:b1 = sys:y
  )\<^sub>e"

typ "(sys_vars, v1_view_vars) viewed_system \<Rightarrow> \<bool>"

alphabet v2_view_vars =
  c2 :: int

definition V2 where "V2 = (
    vu:c2 = max (sys:x) (sys:y)
  )\<^sub>e"

alphabet v3_view_vars =
  d3 :: int
  e3 :: int



definition V3 where "V3 = (vu:d3 = sys:x \<and> (if sys:x < sys:y then (vu:e3 = 0) else vu:e3 = 1))\<^sub>e"

definition ExSys where "ExSys = (sys:x\<^sup>> \<ge> 0 \<and> sys:y\<^sup>> \<ge> 0 \<and> sys:x\<^sup>> + sys:y\<^sup>> = 10)\<^sub>e"

definition ExSys_one_alpha where "ExSys_one_alpha = (sys:x \<ge> 0 \<and> sys:y \<ge> 0 \<and> sys:x + sys:y = 10)\<^sub>e"

definition ExSys_two_delta where "ExSys_two_delta = (sys:x \<ge> 0 \<and> sys:y \<ge> 0 \<and> sys:x + sys:y = 10)\<^sub>e"

definition foo:: "('a sys_vars_scheme, 'b v1_view_vars_scheme, 'c) viewed_system_scheme \<times> ('a sys_vars_scheme, 'b v1_view_vars_scheme, 'c) viewed_system_scheme \<Rightarrow> \<bool>" where "foo = ExSys"

lemma v1_healthy1: "V1 = VH1 V1"
  by (expr_simp2 add: V1_def VH1_def)

lemma v2_healthy1: "V2 = VH1 V2"
  by (expr_simp2 add: V2_def VH1_def)

lemma v3_healthy1: "V3 = VH1 V3"
  by (expr_simp2 add: V3_def VH1_def)

definition Loc1 where "Loc1 = L V1 ExSys"

lemma localise_v1 : "Loc1 = (vu:a1\<^sup>> \<ge> 0 \<and> vu:b1\<^sup>> \<ge> 0 \<and> vu:a1\<^sup>> + vu:b1\<^sup>> = 10)\<^sub>e"
  by (expr_simp2 add: Loc1_def V1_def ExSys_def)

definition Loc2 where "Loc2 = L V2 ExSys"

lemma localise_v2 : "Loc2 = (vu:c2\<^sup>> \<ge> 5 \<and> vu:c2\<^sup>> \<le> 10)\<^sub>e"
  apply (expr_simp2 add: Loc2_def V2_def ExSys_def)
  by presburger

definition Loc3 where "Loc3 = L V3 ExSys"

definition Loc3_one_alpha where "Loc3_one_alpha = L_one_alpha V3 ExSys_one_alpha"

definition Loc3_two_delta where "Loc3_two_delta = L_two_delta V3 ExSys_two_delta"

lemma localise_v3 : "Loc3 = (
    (vu:d3\<^sup>> \<ge> 0 \<and> vu:d3\<^sup>> < 5 \<and> vu:e3\<^sup>> = 0)
   \<or>(vu:d3\<^sup>> \<ge> 5 \<and> vu:d3\<^sup>> \<le> 10 \<and> vu:e3\<^sup>> = 1)
  )\<^sub>e"
  apply (expr_simp2 add: Loc3_def V3_def ExSys_def)
  apply presburger+
  done

lemma localise_v3_two_delta : "Loc3_two_delta = 
 \<Delta> ((vu:d3 \<ge> 0 \<and> vu:d3 < 5 \<and> vu:e3 = 0)
   \<or>(vu:d3 \<ge> 5 \<and> vu:d3 \<le> 10 \<and> vu:e3 = 1))\<^sub>e"
  apply (expr_simp2 add: Loc3_two_delta_def V3_def ExSys_two_delta_def)
  apply presburger+
  done

lemma localise_v3_one_alpha : "Loc3_one_alpha = (
    (vu:d3 \<ge> 0 \<and> vu:d3 < 5 \<and> vu:e3 = 0)
   \<or>(vu:d3 \<ge> 5 \<and> vu:d3 \<le> 10 \<and> vu:e3 = 1)
  )\<^sub>e"
  apply (expr_simp2 add: Loc3_one_alpha_def V3_def ExSys_one_alpha_def)
  apply presburger+
  done

lemma "(G V1 Loc1) =  (sys:x\<^sup>> \<ge> 0 \<and> sys:y\<^sup>> \<ge> 0 \<and> sys:x\<^sup>> + sys:y\<^sup>> = 10)\<^sub>e"
  by (expr_simp2 add: G_def Loc1_def V1_def ExSys_def)

lemma "(G V2 Loc2) =  ((max (sys:x\<^sup>>) (sys:y\<^sup>>) \<ge> 5) \<and> (max (sys:x\<^sup>>) (sys:y\<^sup>>) \<le> 10))\<^sub>e"
  apply (expr_simp2 add: G_def Loc2_def V2_def ExSys_def)
  by presburger

lemma "(G V3 Loc3) =  ( if sys:x\<^sup>> < sys:y\<^sup>> then sys:x\<^sup>> \<ge> 0 \<and> sys:x\<^sup>> < 5 else sys:x\<^sup>> \<ge> 5 \<and> sys:x\<^sup>> \<le> 10)\<^sub>e"
  apply (expr_simp2 add: G_def Loc3_def V3_def ExSys_def)
  by presburger

end