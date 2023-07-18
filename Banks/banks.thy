theory banks
  imports Main UTP2.utp "Shallow-Expressions.Shallow_Expressions" "UTP-Designs.utp_des_healths" "UTP2.utp_healthy"
begin

text "
An encoding of Banks's confidentiality framework for UTP.

Citation: Banks, M.J.: On Confidentiality and Formal Methods. University of York. http://etheses.whiterose.ac.uk/2709/ (2012).

This theory file refers to the definitions, laws, lemmas, etc in the above thesis by their numbers in the thesis.
 "

(* slight variation on the Isabelle/UTP expr_simp method *)
(* TODO pull request to add this to base isabelle/UTP*)
method expr_simp2 uses add = 
  ((simp add: expr_simps add)? \<comment> \<open> Perform any possible simplifications retaining the lens structure \<close>
   ;((simp add: fun_eq_iff prod.case_eq_if alpha_splits expr_defs lens_defs add)? ; \<comment> \<open> Explode the rest \<close>
     (simp add: expr_defs lens_defs add)?))

named_theorems banks_defs
named_theorems banks_lenses

alphabet 's obligation_wrapper =
  obs :: 's
  fog :: 's

alphabet ('s, 'v) viewed_system =
  sys :: 's
  vu :: 'v

lemma [banks_defs]: "mwb_lens vu"
  by simp
lemma [banks_defs]: "mwb_lens sys"
  by simp
lemma [banks_defs]: "mwb_lens obs"
  by simp
lemma [banks_defs]: "mwb_lens fog"
  by simp

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

expr_constructor liberate1 (0)

lemma unrest_liberate1: "a \<sharp> P !\\ a"
  by (expr_simp)

lemma liberate1_false [simp]: "(False)\<^sub>e !\\ a = (False)\<^sub>e"
  by (expr_simp, auto)

(* healthiness conditions for views*)

text "Definition 3.3"
definition VH1
  where [banks_defs]: "VH1 V = ((\<exists> vu \<Zspot> V) \<longrightarrow> V)\<^sub>e"

(* VH2 is not required here, since it has been made impossible to construct a view that doesn't
conform to VH2 by using a slightly different type to Banks' views. The type system prevents us
from writing a VH2-unhealthy view because the view type only ranges over a single instance of the
view variables and system variables. There is no "before" and "after", there is only "now", or in
other words, there's no dashed variables, only undashed variables. Trying to use dashed variables
in a view definition will result in a type error from isabelle at some point.

For completeness, we have a definition for VH2, but it's just the identity function
*)

text "Definition 3.7"
definition VH2 where [banks_defs]: "VH2 = id"

text "Definition 3.15"
definition VH3
  where [banks_defs]: "VH3 P = (P !\\ $vu \<longrightarrow> P)\<^sub>e"

text "Definition 3.11"
(* VH is simply both of the healthiness conditions *)
definition VH where [banks_defs]: "VH = VH1 \<circ> VH2"

text "Law 3.8"
lemma VH1_idempotent[banks_defs]: "VH1 \<circ> VH1 = VH1"
  by (expr_simp add: VH1_def)

text "Law 3.9 (trivial because id is clearly idempotent and VH2 is just id)"
lemma VH2_idempotent[banks_defs]: "VH2 \<circ> VH2 = VH2"
  by (expr_simp add: VH2_def)

(*
text "Law 3.10 (trivial because VH2 is id)"
lemma VH1_2_non_commute: "(VH2 \<circ> VH1) V \<sqsubseteq> (VH1 \<circ> VH2) V"
  by (expr_simp add: VH2_def)
*)

text "Our VH2 simplification strengthens law 3.10"
lemma VH1_2_commute: "(VH2 \<circ> VH1) = (VH1 \<circ> VH2)"
  by (expr_simp add: VH2_def)

(* A simplification rule that is not present in Banks's work, it's only valid here because of the
VH2 simplifications *)
lemma VH_is_VH1[banks_defs]: "VH v = VH1 v"
  by (simp add: VH_def VH2_def)

lemma VH3_idempotent[banks_defs]: "VH3 \<circ> VH3 = VH3"
  by (expr_auto add: VH3_def)

text "Corollary 3.12, once again trivial because of VH2 simplification"
lemma VH_idempotent[banks_defs]: "VH \<circ> VH = VH"
  by (expr_simp add: VH_def VH1_def VH2_def)

text "Lemma 3.13"
(* This currently requires defining a new alphabet to be able to describe disjoint views*)
alphabet ('a, 'b) twoparts =
  twopart_a ::'a
  twopart_b ::'b

(* now we can show lemma 3.13 on a pair of disjoint views *)
lemma conj_preserve_vh[banks_defs]:
  (* views are healthy *)
  assumes "(v1 :: ('a,('b,'c) twoparts) viewed_system \<Rightarrow> bool) is VH"
  assumes "(v2 :: ('a,('b,'c) twoparts) viewed_system \<Rightarrow> bool) is VH"
  (* views are disjoint *)
  assumes "$vu:twopart_a \<sharp> v1"
  assumes "$vu:twopart_b \<sharp> v2"
  (* conjunction of views is still healthy *)
  shows"(v1 \<and> v2)\<^sub>e is VH"
  using assms
  apply (pred_auto add: VH_def VH1_def VH2_def)
  by meson+

definition U
  where [banks_defs]: "U P = ((P\<up>obs) \<and> (P\<up>fog))"

definition D where [banks_defs]: "D Q = (Q \\ $fog \<down> obs)\<^sub>e"

expr_constructor U D

lemma p1: "((P \<up> obs \<and> P \<up> fog) \\ $fog)\<^sub>e = ((P \<up> obs) \\ $fog \<and> (P \<up> fog) \\ $fog)\<^sub>e"
  by (pred_auto)

lemma "(U (P1 \<and> P2)\<^sub>e) = ((U P1) \<and> (U P2))\<^sub>e"
  by (pred_auto add: U_def)

lemma "(D (P1 \<or> P2)\<^sub>e) = ((D P1) \<or> (D P2))\<^sub>e"
  apply (simp add: D_def)
  by expr_simp

lemma aext_liberate_indep:
  fixes e :: "_ \<Rightarrow> _"
  assumes "mwb_lens y" "x \<bowtie> y"
  shows "(e \<up> x)\<^sub>e \\ $y = (e \<up> x)"
  using assms by expr_simp

lemma "D (U P) = P"
  by (pred_auto add: D_def U_def p1 aext_liberate_indep)

text "Definition (unnumbered, defined just after definition 3.7 (VH2)"
definition \<Delta> :: "(_ \<Rightarrow> bool) \<Rightarrow> _"
  where [banks_defs]: "\<Delta> V = (V\<^sup>< \<and> V\<^sup>>)"

text "Variant of the above definition with different type"
definition \<Delta>\<^sub>D :: "(_ \<Rightarrow> bool) \<Rightarrow> _"
(*  where [banks_defs]: "\<Delta>\<^sub>D V = ((ok\<^sup>< \<and> V\<^sup><) \<longrightarrow> (ok\<^sup>> \<and> V\<^sup>>))"*)
  where [banks_defs]: "\<Delta>\<^sub>D = \<Delta>"


expr_constructor \<Delta> \<Delta>\<^sub>D

definition DVH1 where "DVH1 V = ((\<exists> (vu\<^sup><, vu\<^sup>>) \<Zspot> V) \<longrightarrow> V)\<^sub>e"

lemma \<Delta>_conj_refine[banks_defs]: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((\<Delta> V) \<and> P1)\<^sub>e \<sqsubseteq> ((\<Delta> V) \<and> P2)\<^sub>e"
  apply (expr_simp2 add: \<Delta>_def)
  by (smt (verit, ccfv_SIG) ref_by_fun_def ref_preorder.eq_refl)

lemma \<Delta>\<^sub>D_conj_refine[banks_defs]: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((\<Delta>\<^sub>D V) \<and> P1)\<^sub>e \<sqsubseteq> ((\<Delta>\<^sub>D V) \<and> P2)\<^sub>e"
  apply (expr_simp2 add: \<Delta>\<^sub>D_def)
  by (smt (verit, ccfv_SIG) ref_by_fun_def ref_preorder.eq_refl)

lemma  ex_conj_refine[banks_defs]: "(V \<and> P1)\<^sub>e \<sqsubseteq> (V \<and> P2)\<^sub>e \<longrightarrow> (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (V \<and> P1))\<^sub>e \<sqsubseteq> (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (V \<and> P2))\<^sub>e"
  apply (expr_simp2)
  by (smt (z3) prod.sel(1) prod.sel(2) ref_by_fun_def ref_preorder.order_refl)

text "Definition 3.17"
definition L
  where [banks_defs]: "L V P = (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (\<Delta> V \<and> P \<up> sys\<^sup>2 ))\<^sub>e"

(*Alternative L definition option 1*)
(*
definition L_two_delta
  where "L_two_delta V P = (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (\<Delta> V \<and> \<Delta> P))\<^sub>e"

expr_constructor L_two_delta
*)

(*Alternative L definition option 2*)
(*
definition L_one_alpha
  where "L_one_alpha V P = (\<exists> sys \<Zspot> (V \<and> P))\<^sub>e"

expr_constructor L_one_alpha
*)

text "Type variation of definition 3.17"
definition L\<^sub>P
  where [banks_defs]: "L\<^sub>P V P = ((\<exists> (sys) \<Zspot> ( V \<and> P \<up> sys )))\<^sub>e"

expr_constructor L
expr_constructor L\<^sub>P

text "Law 3.19"
lemma l_disj: "(L v (P1 \<or> P2)\<^sub>e) = ((L v P1) \<or> (L v P2))\<^sub>e"
  by (expr_simp2 add: L_def, blast)

text "Law 3.20"
lemma l_monotonic: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((L v P1) \<sqsubseteq> (L v P2))"
  by (pred_auto add: L_def)

text "Law 3.20 for the differently-typed Lp"
lemma lp_monotonic: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((L\<^sub>P v P1) \<sqsubseteq> (L\<^sub>P v P2))"
  by (pred_auto add: L\<^sub>P_def)

(* TODO Law 3.21 is really fun, prove it here *)

text "Definition 3.22"
definition G
  where [banks_defs]: "G v u = (\<forall> (vu\<^sup><, vu\<^sup>>) \<Zspot> ((\<Delta> v) \<longrightarrow> u))\<^sub>e"

definition IR
  where [banks_defs]: "IR V = \<Delta> (U V)"

expr_constructor G IR
(*
text "Lemma 3.24"
lemma g_not:
  assumes "V is VH3"
  shows "G V P = (\<not> (G V (\<not> P)))"
  apply (pred_auto add: banks_defs)
  sorry

lemma
  assumes "V is VH3"
  shows "G V P = (\<exists> (vu\<^sup><, vu\<^sup>>) \<Zspot> \<Delta> V \<and> P)\<^sub>e"
  apply (pred_auto add: banks_defs)
  sorry
*)
(* note: delta is in this definition, which I think is correct, but it's not in Banks' definition *)
definition UI :: "_ \<Rightarrow> (_ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> bool)"
  where [banks_defs]: "UI V P = (\<Delta> (U P) \<and> IR V)\<^sub>e"

text "Definition 3.28"
definition infer
    where [banks_defs]: "infer P V \<psi> = (P \<and> \<not> G V (\<not> \<psi>))\<^sub>e"

expr_constructor infer

text "Corollary 3.29"
lemma
  assumes "V is VH3"
  shows "infer P V \<psi> = (P \<and> (\<exists> (vu\<^sup><, vu\<^sup>>) \<Zspot> \<Delta> V \<and> \<psi>))\<^sub>e"
  by (pred_simp add: infer_def G_def VH3_def \<Delta>_def)

(* Instantiate default for views *)
instantiation viewed_system_ext :: (default, default, default) default
begin
definition default_viewed_system_ext :: "('a, 'b, 'c) viewed_system_scheme" where 
"default_viewed_system_ext =  \<lparr> sys\<^sub>v = default, vu\<^sub>v = default, \<dots> = default \<rparr>"
instance ..
end

definition pair_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a * 'a) \<Rightarrow> ('b * 'b)"
  where [banks_defs]:"pair_map f p = (f (fst p), f (snd p))"

text "Definition 3.32"
(* Like with VH2, this healthiness condition is not particularly useful to us in this implementation
of Banks's work. OK does not need to do anything, since we simply ignore the variable ok\<^sub>v.
This is safe to do because there is no mechanism to inspect or assign to ok\<^sub>v. No predicate could
refer to ok\<^sub>v in an unhealthy way, because no predicate can refer to ok\<^sub>v at all.  *)
definition OK :: "((('a, 'b, 'c) viewed_system_scheme) des_vars_scheme \<Rightarrow> bool) \<Rightarrow> ((('a, 'b, 'c) viewed_system_scheme) des_vars_scheme \<Rightarrow> bool)"
  where [banks_defs]: "OK = id"
 (* where [banks_defs]: "OK V = (if ($ok \<sharp> V) then V else true)"*)
(*  where [banks_defs]: "OK V = (ok \<longrightarrow> V)\<^sub>e"*)

expr_constructor OK

text "Definition 3.33"
(* as such, VHD is also just VH *)
definition VHD
  where [banks_defs]: "VHD V = (
    if (V is OK) \<and> ((V \<down> \<^bold>v\<^sub>D) is VH)
    then V
    else true
  )"

expr_constructor VHD

(*
lemma "(V is VHD) = ((V is OK) \<and> ((V \<down> \<^bold>v\<^sub>D) is VH))"
  apply (pred_auto add: banks_defs)
   apply (metis des_vars.cases_scheme viewed_system.cases_scheme)
  apply (metis)
  done
*)
(* Some simplifications around healthiness conditions *)
(*
lemma [banks_defs]: "a is OK" (* everything is OK *)
  by (pred_auto add: OK_def)

lemma [banks_defs]: "VHD V = (if (V \<down> \<^bold>v\<^sub>D) is VH then V else true)"
  by (pred_auto add: VHD_def VH_def VH1_def VH2_def OK_def)
*)

definition view_des_cond :: "(('a, 'b, 'c) viewed_system_scheme \<Rightarrow> \<bool>) \<Rightarrow> ('a des_vars_scheme, 'b, 'c) viewed_system_scheme \<Rightarrow> \<bool>"
  where [banks_defs]: "view_des_cond v = (\<lambda> a .
    ((ok)\<^sub>e (get\<^bsub>sys\<^esub> a)) \<and> (
    v \<lparr>
      sys\<^sub>v = get\<^bsub>\<^bold>v\<^sub>D\<^esub> (get\<^bsub>sys\<^esub> a)
      ,vu\<^sub>v = get\<^bsub>vu\<^esub> a
      ,\<dots> = get\<^bsub>viewed_system.more\<^sub>L\<^esub> a
    \<rparr>)
  )"

term " (\<Delta>\<^sub>D (V:: (('a, 'b, 'c) viewed_system_scheme des_vars_ext \<Rightarrow> \<bool>)))"

text "A deviation from Banks's work, to work around the issue with lemma 3.35"

definition L\<^sub>D
  where [banks_defs]: "L\<^sub>D V P = (\<not> L\<^sub>P  V (\<not> pre\<^sub>D(P)\<^sup><)) \<turnstile> (L V (post\<^sub>D(P)))"

text "Type variation of law 3.20"

term "P is \<^bold>H"

find_theorems "\<^bold>H"

lemma ld_monotonic: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((L\<^sub>D v P1) \<sqsubseteq> (L\<^sub>D v P2))"
  oops

lemma "(\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> V) = (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> V \<up> \<^bold>v\<^sub>D\<^sup>2) \<down> \<^bold>v\<^sub>D\<^sup>2"
  by pred_auto

lemma ok_indep: "($\<^bold>v\<^sub>D) \<sharp> (ok)\<^sub>e"
  by (simp add: unrest_var_single)

named_theorems indep_extra

lemma before_ok_indep [indep_extra]: "($\<^bold>v\<^sub>D\<^sup><) \<sharp> (ok\<^sup><)\<^sub>e"
  by (smt (verit, best) SEXP_apply des_vars.indeps(2) des_vars.more\<^sub>L_vwb_lens expr_pre fst_lens_def fst_vwb_lens lens.simps(2) lens_comp_def ns_alpha_def ns_alpha_mwb prod.case_eq_if subst_app_def subst_ext_def unrest_lens unrest_var_single vwb_lens.axioms(2))

lemma after_ok_indep [indep_extra]: "($\<^bold>v\<^sub>D\<^sup>>) \<sharp> (ok\<^sup>>)\<^sub>e"
  by (smt (verit) SEXP_def des_vars.indeps(2) des_vars.more\<^sub>L_vwb_lens lens.simps(1) lens.simps(2) lens_comp_def ns_alpha_def ns_alpha_mwb prod.case_eq_if prod.sel(2) snd_lens_def snd_vwb_lens subst_app_def subst_ext_def unrest_lens unrest_var_single vwb_lens.axioms(2))

lemma mixed_ok_indep1 [indep_extra]: "($\<^bold>v\<^sub>D\<^sup>>) \<sharp> (ok\<^sup><)\<^sub>e"
  by (smt (verit, ccfv_threshold) SEXP_apply des_vars.more\<^sub>L_vwb_lens expr_pre fst_lens_def lens.simps(1) lens.simps(2) lens_comp_def ns_alpha_def ns_alpha_mwb prod.case_eq_if snd_lens_def snd_vwb_lens subst_app_def subst_ext_def unrest_lens vwb_lens.axioms(2))

lemma mixed_ok_indep2 [indep_extra]: "($\<^bold>v\<^sub>D\<^sup><) \<sharp> (ok\<^sup>>)\<^sub>e"
  by (smt (verit, del_insts) SEXP_apply des_vars.more\<^sub>L_vwb_lens fst_lens_def fst_vwb_lens lens.simps(1) lens.simps(2) lens_comp_def ns_alpha_def ns_alpha_mwb prod.case_eq_if prod.sel(2) snd_lens_def subst_app_def subst_ext_def unrest_lens vwb_lens.axioms(2))

lemma [indep_extra]: "($\<^bold>v\<^sub>D\<^sup><) \<sharp> (\<not>ok\<^sup><)\<^sub>e"
  using before_ok_indep unrest_not by fastforce

lemma [indep_extra]: "($\<^bold>v\<^sub>D\<^sup>>) \<sharp> (\<not>ok\<^sup>>)\<^sub>e"
  using after_ok_indep unrest_not by fastforce

lemma [indep_extra]: "($\<^bold>v\<^sub>D\<^sup>>) \<sharp> (\<not>ok\<^sup><)\<^sub>e"
  using mixed_ok_indep1 unrest_not by fastforce

lemma [indep_extra]: "($\<^bold>v\<^sub>D\<^sup><) \<sharp> (\<not>ok\<^sup>>)\<^sub>e"
  using mixed_ok_indep2 unrest_not by fastforce


named_theorems bdefs2

definition OK2 where [bdefs2]:"OK2 v = ((v \<and> \<^bold>v\<^sub>D:vu:ok\<^sup>< = ok\<^sup>< \<and> \<^bold>v\<^sub>D:vu:ok\<^sup>> = ok\<^sup>>) \<longrightarrow> v)\<^sub>e"

definition VH12 where [bdefs2]:"VH12 v = ((\<exists> (\<^bold>v\<^sub>D:vu\<^sup><, \<^bold>v\<^sub>D:vu\<^sup>>) \<Zspot> v) \<longrightarrow> v)\<^sub>e"
definition VH22 where [bdefs2]:"VH22 v = ((\<exists> (\<^bold>v\<^sub>D:sys\<^sup>>, \<^bold>v\<^sub>D:vu\<^sup>>) \<Zspot> v) \<longrightarrow> v)\<^sub>e"

definition VHtwo where [bdefs2]:"VHtwo = VH12 \<circ> VH22"

definition VHD2 where [bdefs2]:"VHD2 v = (OK2 (VHtwo v))"

definition L2 where [bdefs2]:"L2 v p = (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> v \<and> p)"

definition design_v where [bdefs2]: "design_v P Q = ((\<^bold>v\<^sub>D:vu:ok\<^sup>< \<and> P) \<longrightarrow> (\<^bold>v\<^sub>D:vu:ok\<^sup>> \<and> Q))\<^sub>e"

lemma a1: "(L2 V (pre' \<turnstile> post')) = ((\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> ((\<not> ok\<^sup><) \<or> (\<not> pre'))\<^sub>e) \<or> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> (ok\<^sup>> \<and> post')\<^sub>e))"
proof -
  have "(L2 V (pre' \<turnstile> post')) = (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> (ok\<^sup>< \<and> pre' \<longrightarrow> ok\<^sup>> \<and> post')\<^sub>e)"
    apply (subst L2_def)
    apply (subst design_def)
    by simp
  also have "... = (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> ((\<not> ok\<^sup><) \<or> (\<not> pre') \<or> (ok\<^sup>> \<and> post'))\<^sub>e)"
    by (pred_auto)
  also have "... = ((\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> ((\<not> ok\<^sup><) \<or> (\<not> pre'))\<^sub>e) \<or> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> (ok\<^sup>> \<and> post')\<^sub>e))"
    apply (pred_auto)
    by fastforce+
  finally show ?thesis
    by (pred_auto)
qed

lemma a2:
  assumes "\<Delta> V is VHD2"
  shows "(design_v (\<not>L2 V (\<not>pre'))) ((L2 V post')) = ((\<not> (\<^bold>v\<^sub>D:vu:ok\<^sup><) \<or> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> \<not> pre')) \<or> (\<^bold>v\<^sub>D:vu:ok\<^sup>>) \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post'))"
proof -
  have "(design_v(\<not>L2 V (\<not>pre'))) ((L2 V post')) = ((\<^bold>v\<^sub>D:vu:ok\<^sup><) \<and> \<not> (L2 V (\<not> pre')) \<longrightarrow> (\<^bold>v\<^sub>D:vu:ok\<^sup>>) \<and> (L2 V post'))"
    apply (subst design_v_def)
    by (pred_auto)
  also have "... = (\<not>((\<^bold>v\<^sub>D:vu:ok\<^sup><) \<and> \<not> (L2 V (\<not> pre'))) \<or> (\<^bold>v\<^sub>D:vu:ok\<^sup>>) \<and> (L2 V post'))"
    by (pred_auto)
  also have "... = ((\<not>(\<^bold>v\<^sub>D:vu:ok\<^sup><) \<or> (L2 V (\<not> pre'))) \<or> (\<^bold>v\<^sub>D:vu:ok\<^sup>>) \<and> (L2 V post'))"
    by (pred_auto)
  also have "... = ((\<not> (\<^bold>v\<^sub>D:vu:ok\<^sup><) \<or> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> \<not> pre')) \<or> (\<^bold>v\<^sub>D:vu:ok\<^sup>>) \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post'))"
    apply (subst L2_def)
    apply (subst L2_def)
    by simp
  finally show ?thesis
    by simp
qed

lemma a3:
  assumes "\<Delta> V is VHD2"
  assumes "((\<exists> (\<^bold>v\<^sub>D:vu\<^sup><, \<^bold>v\<^sub>D:vu\<^sup>>) \<Zspot> post') \<longrightarrow> post') = post'"
  shows  "((\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> (ok\<^sup>> \<and> post')\<^sub>e)) = ((\<^bold>v\<^sub>D:vu:ok)\<^sup>> \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post'))"
  using assms
   apply (expr_simp add: banks_defs bdefs2)
  try

  sorry

lemma "((\<Delta>
         ((\<lambda>x. False)
        (\<lparr>ok\<^sub>v = True, sys\<^sub>v = a\<^sub>1, vu\<^sub>v = \<lparr>ok\<^sub>v = True, \<dots> = a\<^sub>1\<rparr>, \<dots> = a\<^sub>1\<rparr> := True, \<lparr>ok\<^sub>v = True, sys\<^sub>v = a\<^sub>1, vu\<^sub>v = \<lparr>ok\<^sub>v = False, \<dots> = a\<^sub>1\<rparr>, \<dots> = a\<^sub>1\<rparr> := True,
         \<lparr>ok\<^sub>v = False, sys\<^sub>v = a\<^sub>1, vu\<^sub>v = \<lparr>ok\<^sub>v = True, \<dots> = a\<^sub>1\<rparr>, \<dots> = a\<^sub>1\<rparr> := True, \<lparr>ok\<^sub>v = False, sys\<^sub>v = a\<^sub>1, vu\<^sub>v = \<lparr>ok\<^sub>v = False, \<dots> = a\<^sub>1\<rparr>, \<dots> = a\<^sub>1\<rparr> := True))) is VHD2)"
  apply (pred_simp add: banks_defs bdefs2)
  try


lemma a1_2:
  assumes "\<Delta> V is VHD2"
  assumes "((\<exists> (\<^bold>v\<^sub>D:vu\<^sup><, \<^bold>v\<^sub>D:vu\<^sup>>) \<Zspot> post') \<longrightarrow> post') = post'"
  shows "(L2 V (pre' \<turnstile> post')) = ((\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> ((\<not> ok\<^sup><) \<or> (\<not> pre'))\<^sub>e) \<or> ((\<^bold>v\<^sub>D:vu:ok)\<^sup>> \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post')))"
  using assms
  apply (subst a1)
  apply (subst a3)
   apply simp
   apply simp
  apply simp
  done

lemma
  assumes "\<Delta> V is VHD2"
  assumes "((\<exists> (\<^bold>v\<^sub>D:vu\<^sup><, \<^bold>v\<^sub>D:vu\<^sup>>) \<Zspot> post') \<longrightarrow> post') = post'"
  shows "(L2 V (pre' \<turnstile> post')) = ((\<not>L2 V (\<not>pre'))) \<turnstile> ((L2 V post')) \<longleftrightarrow> (
      ((\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> ((\<not> ok\<^sup><) \<or> (\<not> pre'))\<^sub>e)   \<or>   (\<^bold>v\<^sub>D:vu:ok)\<^sup>> \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post'))  
    = ((\<not> (ok)\<^sup>< \<or> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> \<not> pre'))      \<or>   (\<^bold>v\<^sub>D:vu:ok)\<^sup>> \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post')) 
  )"
  using assms
  apply -
  apply (simp add: a1_2 a2)
  apply auto

lemma
  assumes "v is VHD2"
  shows "((\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> ((\<not> ok\<^sup><) \<or> (\<not> pre'))\<^sub>e)   \<or>   (ok)\<^sup>> \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post'))  
    \<noteq> ((\<not> (ok)\<^sup>< \<or> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> \<not> pre'))      \<or>   (ok)\<^sup>> \<and> (\<exists> (\<^bold>v\<^sub>D:sys\<^sup><, \<^bold>v\<^sub>D:sys\<^sup>>) \<Zspot> \<Delta> V \<and> post'))"
  apply (cases "$ok = True")
  apply expr_simp
  

    apply pred_auto
  
  

text "Lemma 3.35, but better"
lemma view_local_design2 [banks_defs] :
  fixes V :: "('a, 'b, 'c) viewed_system_scheme \<Rightarrow> \<bool>"
  assumes "V is VH"
  shows "(L\<^sub>D V (pre' \<turnstile>\<^sub>r post')) = ((\<not>L V (\<not>pre'))) \<turnstile>\<^sub>r ((L V post'))"
  apply (simp add: banks_defs)
  by (pred_auto)

(* simplify with banks' definitions *)
method expr_simp_banks uses add = ((expr_simp2 add: banks_defs add)?)
method pred_auto_banks uses add = ((pred_auto add: banks_defs add)?)

end