theory alice_guessing
  imports Main "../banks"
begin

alphabet \<alpha>Guess = 
  n :: int
  g :: int
  r :: int

alphabet \<alpha>Alice =
  ga :: int
  ra :: int

definition Guess0
  where "Guess0 = Sys (
    n\<^sup>< \<ge> 1 \<and> n\<^sup>< \<le> 10
    \<and> g\<^sup>< \<ge> 1 \<and> g\<^sup>< \<le> 10

    \<and> g\<^sup>< > n\<^sup>< \<longrightarrow> r\<^sup>> > 0
    \<and> g\<^sup>< = n\<^sup>< \<longrightarrow> r\<^sup>> = 0
    \<and> g\<^sup>< < n\<^sup>< \<longrightarrow> r\<^sup>> < 0
  )\<^sub>e"

(*
Alternative definition with sys lens manually expanded:

definition Guess0
  where "Guess0 = (
    sys:n\<^sup>< \<ge> 1 \<and> sys:n\<^sup>< \<le> 10
    \<and> sys:g\<^sup>< \<ge> 1 \<and> sys:g\<^sup>< \<le> 10

    \<and> sys:g\<^sup>< > sys:n\<^sup>< \<longrightarrow> sys:r\<^sup>> > 0
    \<and> sys:g\<^sup>< = sys:n\<^sup>< \<longrightarrow> sys:r\<^sup>> = 0
    \<and> sys:g\<^sup>< < sys:n\<^sup>< \<longrightarrow> sys:r\<^sup>> < 0
  )\<^sub>e"
*)

definition Alice
  where "Alice = (vu:ga = sys:g \<and> vu:ra = sys:r)\<^sub>e"

definition tA where "tA = \<lparr> ga\<^sub>v = 7, ra\<^sub>v = 1 \<rparr>"
definition tG where "tG = \<lparr> n\<^sub>v = 9, g\<^sub>v = 7, r\<^sub>v = 1 \<rparr>"

definition tVals where "tVals = \<lparr> vu\<^sub>v = tA, sys\<^sub>v = tG \<rparr>"

value "Guess0 (tVals, tVals)"
value "Alice tVals"

lemma alice_is_healthy: "VH Alice = Alice"
  by (expr_simp add: Alice_def VH_def VH1_def VH2_def)

lemma
  "\<forall> x . (((\<Delta> Alice) x) \<and> (Guess0 x)) \<longrightarrow> (
    ((infer (Guess0) (Alice) (Vu (ga\<^sup>< = 7 \<and> ra\<^sup>> > 0)\<^sub>e)) x)
    =
    (Sys (g\<^sup>< = 7 \<and> r\<^sup>> > 0 \<and> n\<^sup>< \<ge> 8 \<and> n\<^sup>< \<le> 10)\<^sub>e x)
  )"
  apply (expr_simp_banks add: Alice_def Guess0_def)
  apply safe
  


end