(*
This is the guessing game from Michael Banks's PhD thesis [On Confidentiality and Formal Methods]
Example 3.30 in Section 3.3.4 on page 33

Alice plays a guessing game.

An integer n in the range 1 to 10 is chosen arbitrarily. Alice can guess the value of n. Her guess
is the integer g.
Alice can observe her own guess (of course), and also the value of r. r indicates if the guess was
correct, too low, or too high:
r > 0 \<Rightarrow> guess too high
r = 0 \<Rightarrow> guess correct
r < 0 \<Rightarrow> guess too low

The example shows how alice can use the "infer" function to determine the possible values of n given
the guess g and the result r.

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
  where "Guess0 = (
    n\<^sup>< \<ge> 1 \<and> n\<^sup>< \<le> 10
    \<and> g\<^sup>< \<ge> 1 \<and> g\<^sup>< \<le> 10

    \<and> (g\<^sup>< > n\<^sup>< \<longrightarrow> r\<^sup>> > 0)
    \<and> (g\<^sup>< = n\<^sup>< \<longrightarrow> r\<^sup>> = 0)
    \<and> (g\<^sup>< < n\<^sup>< \<longrightarrow> r\<^sup>> < 0)
  )\<^sub>e \<up> sys\<^sup>2"

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
    (infer (Guess0) (Alice) (
      (ga\<^sup>< = 7 \<and> ra\<^sup>> < 0)\<^sub>e \<up> vu\<^sup>2
    ))
    =
    (g\<^sup>< = 7 \<and> r\<^sup>> < 0 \<and> n\<^sup>< \<ge> 8 \<and> n\<^sup>< \<le> 10)\<^sub>e  \<up> sys\<^sup>2
  )"
  by (pred_auto_banks add: Alice_def Guess0_def)

end
