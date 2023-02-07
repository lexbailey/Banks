theory localise_globalise
  imports Main "../Banks/banks" (*NO_CI*)
  (*CI_ONLY imports Main "Banks.banks" CI_ONLY*)
begin

alphabet sys_vars =
  x :: int
  y :: int

alphabet v1_view_vars =
  a1 :: int
  b1 :: int

definition V1 where "V1 = (
    vu:a1 = sys:x \<and> vu:b1 = sys:y
  )\<^sub>e"

alphabet v2_view_vars =
  c2 :: int

definition V2 where "V2 = (
    vu:c2 = max (sys:x) (sys:y)
  )\<^sub>e"

alphabet v3_view_vars =
  d3 :: int
  e3 :: int

definition V3 where "V3 = (vu:d3 = sys:x \<and> (if sys:x < sys:y then (vu:e3 = 0) else vu:e3 = 1))\<^sub>e"

definition ExSys where "ExSys = (x\<^sup>> \<ge> 0 \<and> y\<^sup>> \<ge> 0 \<and> x\<^sup>> + y\<^sup>> = 10)\<^sub>e"

lemma v1_healthy1: "V1 is VH1"
  by (pred_auto_banks add: V1_def)

lemma v2_healthy1: "V2 is VH1"
  by (pred_auto_banks add: V2_def)

lemma v3_healthy1: "V3 is VH1"
  by (pred_auto_banks add: V3_def)

definition Loc1 where "Loc1 = L V1 ExSys"

lemma localise_v1 : "Loc1 = (a1 \<ge> 0 \<and> b1 \<ge> 0 \<and> a1 + b1 = 10)\<^sub>e \<up> vu\<^sup>>"
  by (pred_auto_banks add: Loc1_def V1_def ExSys_def)

definition Loc2 where "Loc2 = L V2 ExSys"

lemma localise_v2 : "Loc2 = (c2 \<ge> 5 \<and> c2 \<le> 10)\<^sub>e \<up> vu\<^sup>>"
  apply (pred_auto_banks add: Loc2_def V2_def ExSys_def)
  by presburger+

definition Loc3 where "Loc3 = (L V3 ExSys)"

lemma localise_v3 : "Loc3 = (
    (d3 \<ge> 0 \<and> d3 < 5 \<and> e3 = 0)
   \<or>(d3 \<ge> 5 \<and> d3 \<le> 10 \<and> e3 = 1)
  )\<^sub>e \<up> vu\<^sup>>"
  apply (pred_auto_banks add: Loc3_def V3_def ExSys_def)
  tr

lemma localise_v3 : "Loc3 = (
    (d3 \<ge> 0 \<and> d3 < 5 \<and> e3 = 0)
   \<or>(d3 \<ge> 5 \<and> d3 \<le> 10 \<and> e3 = 1)
  )\<^sub>e \<up> vu\<^sup>>"
  apply (pred_auto_banks add: Loc3_def V3_def ExSys_def)
  tr
  by presburger+

lemma "(G V1 Loc1) =  (x \<ge> 0 \<and> y \<ge> 0 \<and> x + y = 10)\<^sub>e \<up> sys\<^sup>>"
  by (pred_auto_banks add: Loc1_def V1_def ExSys_def)

lemma "(G V2 Loc2) =  ((max x y \<ge> 5) \<and> (max x y \<le> 10))\<^sub>e  \<up> sys\<^sup>>"
  apply (pred_auto_banks add: Loc2_def V2_def ExSys_def)
  by presburger

lemma "(G V3 Loc3) =  ( if x < y then (x \<ge> 0 \<and> x < 5) else (x \<ge> 5 \<and> x \<le> 10))\<^sub>e  \<up> sys\<^sup>>"
  apply (pred_auto_banks add: Loc3_def V3_def ExSys_def)
  by presburger+

end
