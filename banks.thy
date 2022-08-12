theory banks
  imports Main UTP2.utp "Shallow-Expressions.Shallow_Expressions"
begin

(* slight variation on the Isabelle/UTP expr_simp method *)
method expr_simp2 uses add = 
  ((simp add: expr_simps add)? \<comment> \<open> Perform any possible simplifications retaining the lens structure \<close>
   ;((simp add: fun_eq_iff prod.case_eq_if alpha_splits expr_defs lens_defs add)? ; \<comment> \<open> Explode the rest \<close>
     (simp add: expr_defs lens_defs add)?))

instantiation int :: default
begin
definition "default_int = (0 :: int)"
instance ..
end

alphabet 's obligation_wrapper =
  obs :: 's
  fog :: 's

alphabet ('s, 'v) viewed_system =
  vu :: 'v
  sys :: 's

alphabet ('s, 'v) viewed_design = "('s, 'v) viewed_system" +
  ok :: bool
  vok :: bool

(* liberate1 is used to define VH3. it is like liberate, except that is uses "there exists one"
 instead of "there exists" *)
consts liberate1 :: "'p \<Rightarrow> 's scene \<Rightarrow> 'p"

definition liberate1_expr :: "('s \<Rightarrow> bool) \<Rightarrow> 's scene \<Rightarrow> ('s \<Rightarrow> bool)" where
[expr_defs]: "liberate1_expr P x = (\<lambda> s. \<exists>! s'. P (s \<oplus>\<^sub>S s' on x))"

adhoc_overloading liberate1 liberate1_expr

syntax
  "_liberate1" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "!\\" 80)

translations
  "_liberate1 P x" == "CONST liberate1 P x"
  "_liberate1 P x" <= "_liberate1 (P)\<^sub>e x"

expr_ctr liberate1 (0)

lemma unrest_liberate1: "a \<sharp> P !\\ a"
  by (expr_simp)

lemma liberate1_false [simp]: "(False)\<^sub>e !\\ a = (False)\<^sub>e"
  by (expr_simp, auto)

(* healthiness conditions for views*)
(*
definition VH1
  where "VH1 P = (P \\ $vu \<longrightarrow> P)\<^sub>e"
*)

definition VH1
  where "VH1 V = ((\<exists> vu \<Zspot> V) \<longrightarrow> V)\<^sub>e"

term VH1

(* VH2 is not required here, since it has been made impossible to construct a view that doesn't
conform to VH2 by using a slightly different type to Banks' views. The type system prevents us
from writing a VH2-unhealthy view because the view type only ranges over a single instance of the
view variables and system variables. There is no "before" and "after", there is only "now", or in
other words, there's no dashed variables, only undashed variables. Trying to use dashed variables
in a view definition will result in a type error from isabelle at some point.

For completeness, we have a definition for VH2, but it's just the identity function
*)

definition VH2 where "VH2 = id"

definition VH3
  where "VH3 P = (P !\\ $vu \<longrightarrow> P)\<^sub>e"

(* VH is simply both of the healthiness conditions *)
definition VH where "VH = VH1 \<circ> VH2"

expr_ctr VH

lemma VH1_idempotent: "VH1 \<circ> VH1 = VH1"
  by (expr_simp add: VH1_def)

(*
lemma VH3_idempotent: "VH3 \<circ> VH3 = VH3"
  apply (expr_auto add: VH3_def)
  *)

lemma VH_idempotent: "VH \<circ> VH = VH"
  by (expr_simp add: VH_def VH1_def VH2_def)

(* These lemmas are present in Banks work, but are trivial here for the reasons mentioned above.
They are only here for completeness *)
lemma "VH1 \<circ> VH = VH"
  by (expr_simp add: VH_def VH1_def)

lemma "VH2 \<circ> VH = VH"
  by (expr_simp add: VH1_def VH2_def VH_def)

lemma conj_preserve_vh:"
    (\<lambda> a . ((VH v1) a \<and> (VH v2) a)) b
    \<longrightarrow>
    (VH (\<lambda> a. (v1 a) \<and> (v2 a))) b
  "
  by (expr_simp add: VH_def VH1_def VH2_def, auto)

(*
lemma VH3_implies_VH1: "((VH3 v) a) \<longrightarrow> ((VH1 v) a)"
  apply (expr_simp add: VH1_def VH3_def)
  apply auto
*)

declare [[show_types]]

definition U :: "('s \<Rightarrow> bool) \<Rightarrow> ('s obligation_wrapper \<Rightarrow> bool)"
  where "U P = ((P\<up>obs) \<and> (P\<up>fog))\<^sub>e"

definition D where "D Q = (Q \\ $fog \<down> obs)\<^sub>e"

expr_ctr U D

lemma p1: "((P \<up> obs \<and> P \<up> fog) \\ $fog)\<^sub>e = ((P \<up> obs) \\ $fog \<and> (P \<up> fog) \\ $fog)\<^sub>e"
  by expr_simp

lemma "(U (P1 \<and> P2)\<^sub>e) = ((U P1) \<and> (U P2))\<^sub>e"
  apply (simp add: U_def)
  apply expr_simp
  by auto

lemma "(D (P1 \<or> P2)\<^sub>e) = ((D P1) \<or> (D P2))\<^sub>e"
  apply (simp add: D_def)
  by expr_simp

lemma aext_liberate_indep:
  fixes e :: "_ \<Rightarrow> _"
  assumes "mwb_lens y" "x \<bowtie> y"
  shows "(e \<up> x)\<^sub>e \\ $y = (e \<up> x)"
  using assms by expr_simp

lemma "D (U P) = P"
  apply (simp add: D_def U_def p1 aext_liberate_indep)
  apply expr_auto  
  done

definition \<Delta> :: "(_ \<Rightarrow> bool) \<Rightarrow> _"
  where "\<Delta> V = (V\<^sup>< \<and> V\<^sup>> )\<^sub>e"

expr_ctr \<Delta>

declare \<Delta>_def [simp]

lemma \<Delta>_conj_refine: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((\<Delta> V) \<and> P1)\<^sub>e \<sqsubseteq> ((\<Delta> V) \<and> P2)\<^sub>e"
  apply (expr_simp2)
  by (smt (verit, ccfv_SIG) ref_by_fun_def ref_preorder.eq_refl)

term "((\<Delta> V) \<and> P1)\<^sub>e"

lemma  ex_conj_refine: "(V \<and> P1)\<^sub>e \<sqsubseteq> (V \<and> P2)\<^sub>e \<longrightarrow> (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (V \<and> P1))\<^sub>e \<sqsubseteq> (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (V \<and> P2))\<^sub>e"
  apply (expr_simp2)
  by (smt (z3) prod.sel(1) prod.sel(2) ref_by_fun_def ref_preorder.order_refl)

(*option 3*)
definition L
  where "L V P = (\<exists> (sys\<^sup><, sys\<^sup>>, vu\<^sup><) \<Zspot> (\<Delta> V \<and> P))\<^sub>e"

(*option 1*)
definition L_two_delta
  where "L_two_delta V P = (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (\<Delta> V \<and> \<Delta> P))\<^sub>e"

(*option 2*)
definition L_one_alpha
  where "L_one_alpha V P = (\<exists> sys \<Zspot> (V \<and> P))\<^sub>e"

typ "(('a, 'b) viewed_system \<Rightarrow> \<bool>) \<Rightarrow> (('a, 'b) viewed_system \<Rightarrow> \<bool>) \<Rightarrow> ('a, 'b) viewed_system \<Rightarrow> \<bool>"

expr_ctr L
expr_ctr L_two_delta
expr_ctr L_one_alpha

declare L_def [simp]
declare L_two_delta_def [simp]
declare L_one_alpha_def [simp]

(* Localisation is disjunctive *)
lemma l_disj: "(L v (P1 \<or> P2)\<^sub>e)\<^sub>e = ((L v P1) \<or> (L v P2))\<^sub>e"
  by (expr_simp2, blast)

term ex

find_theorems "(\<sqsubseteq>)"

lemma l_monotonic: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((L v P1) \<sqsubseteq> (L v P2))"
  (* TODO can I speed up this proof using \<Delta>_conj_refine and ex_conj_refine*)
  by (smt (z3) L_def SEXP_def ex_expr_def ref_by_fun_def ref_preorder.eq_refl)

definition G
  where "G v u = (\<forall> (vu\<^sup><, vu\<^sup>>) \<Zspot> (\<Delta> v) \<longrightarrow> u)\<^sub>e"

expr_ctr G

definition IR
  where "IR V = \<Delta> (U V)"

expr_ctr IR

(* note: delta is in this definition, which I think is correct, but it's not in Banks' definition *)
definition UI :: "_ \<Rightarrow> (_ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> bool)"
  where "UI V P = (\<Delta> (U P) \<and> IR V)\<^sub>e"

definition infer
  where "infer P V \<psi> = (P \<and> \<not>(G V (\<lambda> a . (\<not> (\<psi> a)))))\<^sub>e"

expr_ctr infer

lemma "(VH3 V = V) \<longrightarrow> infer P V \<psi> = (P \<and> (\<exists> (vu\<^sup><, vu\<^sup>>) \<Zspot> \<Delta> V \<and> \<psi>))\<^sub>e"
  by (expr_simp add: infer_def G_def VH3_def)


(* Instantiate default for views *)
instantiation viewed_system_ext :: (default, default, default) default
begin
definition default_viewed_system_ext :: "('a, 'b, 'c) viewed_system_scheme" where 
"default_viewed_system_ext =  \<lparr> vu\<^sub>v = default, sys\<^sub>v = default, \<dots> = default \<rparr>"
instance ..
end

definition OK
  where "OK v = (v \<and> (vok = ok))\<^sub>e"

expr_ctr OK

definition VHD
  where "VHD v = (VH v \<and> OK v)\<^sub>e"

definition local_design   
where "local_design c_pre c_post = (
    (vok\<^sup>< \<and> c_pre) \<longrightarrow> (vok\<^sup>> \<and> c_post)
  )\<^sub>e"

(*
#######################
  examples
#######################
*)

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

(* Conditional syntax copied from Simon's UTP Practical Session (Pr19, PROF) *)
definition cond :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)" where
[expr_defs]: "cond P b Q = (P \<and> b \<or> Q \<and> \<not>b)\<^sub>e"

syntax "_cond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
translations "_cond P b Q" == "CONST cond (P)\<^sub>e (b)\<^sub>e (Q)\<^sub>e"

expr_ctr cond
(* TODO if-then-else utp style syntax pull request*)

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