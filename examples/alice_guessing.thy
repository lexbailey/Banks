(*
This is the guessing game from Michael Banks's PhD thesis [On Confidentiality and Formal Methods]
Example 3.30 in Section 3.3.4 on page 33
*)

theory alice_guessing
  imports Main "../Banks/banks" (*NO_CI*)
  (*CI_ONLY imports Main "Banks.banks" CI_ONLY*)
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

    \<and> (g\<^sup>< > n\<^sup>< \<longrightarrow> r\<^sup>> > 0)
    \<and> (g\<^sup>< = n\<^sup>< \<longrightarrow> r\<^sup>> = 0)
    \<and> (g\<^sup>< < n\<^sup>< \<longrightarrow> r\<^sup>> < 0)
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

lemma alice_is_healthy: "VH Alice = Alice"
  by (expr_simp_banks add: Alice_def)

(*
  In Banks's thesis there is a slight error.
  where the proof says "r' > 0", it should say "r' < 0".
  Alternatively: "n \<in> 8..10" could be changed to say "n \<in> 1..6"
*)
lemma
  "(
    (infer (Guess0) (Alice) (Vu
      (ga\<^sup>< = 7 \<and> ra\<^sup>> < 0)\<^sub>e
    ))
    =
    (Sys
      (g\<^sup>< = 7 \<and> r\<^sup>> < 0 \<and> n\<^sup>< \<ge> 8 \<and> n\<^sup>< \<le> 10)\<^sub>e
    )
  )"
  apply (expr_simp_banks add: Alice_def Guess0_def)
  by auto


end
