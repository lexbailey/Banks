theory banks
  imports Main UTP2.utp "Shallow-Expressions.Shallow_Expressions" "UTP-Designs.utp_des_healths"
begin

(* slight variation on the Isabelle/UTP expr_simp method *)
method expr_simp2 uses add = 
  ((simp add: expr_simps add)? \<comment> \<open> Perform any possible simplifications retaining the lens structure \<close>
   ;((simp add: fun_eq_iff prod.case_eq_if alpha_splits expr_defs lens_defs add)? ; \<comment> \<open> Explode the rest \<close>
     (simp add: expr_defs lens_defs add)?))

named_theorems banks_defs

alphabet 's obligation_wrapper =
  obs :: 's
  fog :: 's

alphabet ('s, 'v) viewed_system =
  sys :: 's
  vu :: 'v

term viewed_system_ext

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
(*
definition VH1
  where "VH1 P = (P \\ $vu \<longrightarrow> P)\<^sub>e"
*)


definition VH1
  where [banks_defs]: "VH1 V = ((\<exists> vu \<Zspot> V) \<longrightarrow> V)\<^sub>e"

term VH1

(* VH2 is not required here, since it has been made impossible to construct a view that doesn't
conform to VH2 by using a slightly different type to Banks' views. The type system prevents us
from writing a VH2-unhealthy view because the view type only ranges over a single instance of the
view variables and system variables. There is no "before" and "after", there is only "now", or in
other words, there's no dashed variables, only undashed variables. Trying to use dashed variables
in a view definition will result in a type error from isabelle at some point.

For completeness, we have a definition for VH2, but it's just the identity function
*)

definition VH2 where [banks_defs]: "VH2 = id"

definition VH3
  where [banks_defs]: "VH3 P = (P !\\ $vu \<longrightarrow> P)\<^sub>e"

(* VH is simply both of the healthiness conditions *)
definition VH where [banks_defs]: "VH = VH1 \<circ> VH2"

expr_constructor VH

lemma VH1_idempotent: "VH1 \<circ> VH1 = VH1"
  by (expr_simp add: VH1_def)

lemma VH_is_VH1[banks_defs]: "VH v = VH1 v"
  by (simp add: VH_def VH2_def)

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

(* TODO fix this lemma *)
(*
lemma VH3_implies_VH1: "((VH3 v) a) \<longrightarrow> ((VH1 v) a)"
  apply (expr_simp2 add: VH1_def VH3_def)
  sorry
*)

declare [[show_types]]

definition U :: "('s \<Rightarrow> bool) \<Rightarrow> ('s obligation_wrapper \<Rightarrow> bool)"
  where [banks_defs]: "U P = ((P\<up>obs) \<and> (P\<up>fog))\<^sub>e"

definition D where [banks_defs]: "D Q = (Q \\ $fog \<down> obs)\<^sub>e"

expr_constructor U D

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
  where [banks_defs]: "\<Delta> V = (V\<^sup>< \<and> V\<^sup>> )\<^sub>e"

expr_constructor \<Delta>

lemma \<Delta>_conj_refine: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((\<Delta> V) \<and> P1)\<^sub>e \<sqsubseteq> ((\<Delta> V) \<and> P2)\<^sub>e"
  apply (expr_simp2 add: \<Delta>_def)
  by (smt (verit, ccfv_SIG) ref_by_fun_def ref_preorder.eq_refl)

term "((\<Delta> V) \<and> P1)\<^sub>e"

lemma  ex_conj_refine: "(V \<and> P1)\<^sub>e \<sqsubseteq> (V \<and> P2)\<^sub>e \<longrightarrow> (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (V \<and> P1))\<^sub>e \<sqsubseteq> (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (V \<and> P2))\<^sub>e"
  apply (expr_simp2)
  by (smt (z3) prod.sel(1) prod.sel(2) ref_by_fun_def ref_preorder.order_refl)

(*option 3*)
(*change this so that the second argument is more generic: rel[s] (the later rel[des[s]])*)
definition L
  where [banks_defs]: "L V P = (\<exists> (sys\<^sup><, sys\<^sup>>, vu\<^sup><) \<Zspot> (\<Delta> V \<and> P \<up> sys\<^sup>2 ))\<^sub>e"

(*option 1*)
definition L_two_delta
  where "L_two_delta V P = (\<exists> (sys\<^sup><, sys\<^sup>>) \<Zspot> (\<Delta> V \<and> \<Delta> P))\<^sub>e"

(*option 2*)
definition L_one_alpha
  where "L_one_alpha V P = (\<exists> sys \<Zspot> (V \<and> P))\<^sub>e"

typ "(('a, 'b) viewed_system \<Rightarrow> \<bool>) \<Rightarrow> (('a, 'b) viewed_system \<Rightarrow> \<bool>) \<Rightarrow> ('a, 'b) viewed_system \<Rightarrow> \<bool>"

expr_constructor L
expr_constructor L_two_delta
expr_constructor L_one_alpha

(* Localisation is disjunctive *)
lemma l_disj: "(L v (P1 \<or> P2)\<^sub>e)\<^sub>e = ((L v P1) \<or> (L v P2))\<^sub>e"
  by (expr_simp2 add: L_def, blast)

term ex

find_theorems "(\<sqsubseteq>)"

lemma l_monotonic: "(P1 \<sqsubseteq> P2) \<longrightarrow> ((L v P1) \<sqsubseteq> (L v P2))"
  (* TODO can I speed up this proof using \<Delta>_conj_refine and ex_conj_refine*)
  by (pred_auto add: L_def)
  
definition G
  where [banks_defs]: "G v u = (\<forall> (vu\<^sup><, vu\<^sup>>) \<Zspot> ((\<Delta> v) \<longrightarrow> u))\<^sub>e"

definition IR
  where [banks_defs]: "IR V = \<Delta> (U V)"

expr_constructor G IR

(* note: delta is in this definition, which I think is correct, but it's not in Banks' definition *)
definition UI :: "_ \<Rightarrow> (_ \<Rightarrow> bool) \<Rightarrow> (_ \<Rightarrow> bool)"
  where [banks_defs]: "UI V P = (\<Delta> (U P) \<and> IR V)\<^sub>e"

definition infer
    where [banks_defs]: "infer P V \<psi> = (P \<and> (Not (G (V) (Not \<circ> \<psi>))))\<^sub>e"

expr_constructor infer
  
lemma "V is VH3 \<longrightarrow> infer P V \<psi> = (P \<and> (\<exists> (vu\<^sup><, vu\<^sup>>) \<Zspot> \<Delta> V \<and> \<psi>))\<^sub>e"
  by (expr_simp add: infer_def G_def VH3_def \<Delta>_def)
    

(* Instantiate default for views *)
instantiation viewed_system_ext :: (default, default, default) default
begin
definition default_viewed_system_ext :: "('a, 'b, 'c) viewed_system_scheme" where 
"default_viewed_system_ext =  \<lparr> sys\<^sub>v = default, vu\<^sub>v = default, \<dots> = default \<rparr>"
instance ..
end

definition pair_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a * 'a) \<Rightarrow> ('b * 'b)"
  where [banks_defs]:"pair_map f p = (f (fst p), f (snd p))"



(*
definition vdesign where
[banks_defs]: "vdesign P Q = ((vu:ok\<^sup>< \<and> P)\<^sub>e \<longrightarrow> (vu:ok\<^sup>> \<and> Q)\<^sub>e)"

syntax 
  "_vdesign"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<turnstile>\<^sub>v" 85)

translations
  "P \<turnstile>\<^sub>v Q" == "CONST vdesign P Q"
*)

(* Like with VH2, this healthiness condition is not particularly useful to us in this implementation
of Banks's work. OK does not need to do anything, since we simply ignore the variable ok\<^sub>v.
This is safe to do because there is no mechanism to inspect or assign to ok\<^sub>v. No predicate could
refer to ok\<^sub>v in an unhealthy way, because no predicate can refer to ok\<^sub>v at all.  *)
definition OK
  where [banks_defs]: "OK = id"

(* as such, VHD is also just VH *)
definition VHD
  where [banks_defs]: "VHD v = (OK (VH v))"

(* and since VH is just VH1, we can simplify this to just VH1 *)
lemma  VHD_is_VH1[banks_defs]: "VHD v = VH1 v"
  by (simp add: VHD_def OK_def VH_def VH2_def)

expr_constructor OK VHD

value "true (1::nat)"

value "(\<not> (1::nat) = 1)\<^sub>e (1::nat)"

term \<Delta>

term pre
       
term "( (\<not> ( (L V (\<not> pre')\<^sub>e))))"

term "(L V post')"


term "
(view_redesigned(
( (\<not> ( (L V (\<not> (\<Delta> pre'))\<^sub>e))))
\<turnstile>\<^sub>r
(L V post')
))
"

definition condition
  where "condition v = (\<lambda> (a, b). v a)"

term "(ok)\<^sub>e"

definition view_des_cond :: "(('a, 'b, 'c) viewed_system_scheme \<Rightarrow> \<bool>) \<Rightarrow> ('a des_vars_scheme, 'b, 'c) viewed_system_scheme \<Rightarrow> \<bool>"
  where [banks_defs]: "view_des_cond v = (\<lambda> a .
    ((ok)\<^sub>e (get\<^bsub>sys\<^esub> a)) \<and> (
    v \<lparr>
      sys\<^sub>v = get\<^bsub>\<^bold>v\<^sub>D\<^esub> (get\<^bsub>sys\<^esub> a)
      ,vu\<^sub>v = get\<^bsub>vu\<^esub> a
      ,\<dots> = get\<^bsub>more\<^sub>L\<^esub> a
    \<rparr>)
  )"

definition to_viewed_design
  where [banks_defs]: "to_viewed_design v = (\<lambda> a.
    (let b = (pair_map (\<lambda> b . \<lparr>
     ok\<^sub>v = get\<^bsub>ok\<^esub> (get\<^bsub>sys\<^esub> b)
     ,\<dots> = \<lparr>
          sys\<^sub>v = get\<^bsub>\<^bold>v\<^sub>D\<^esub> (get\<^bsub>sys\<^esub> b)
          ,vu\<^sub>v = (get\<^bsub>vu\<^esub> b)
          ,\<dots> = get\<^bsub>more\<^sub>L\<^esub> b
        \<rparr>
      \<rparr>)
      a
    )in v b)
  )"


lemma "(
    (V is VHD) \<and>
    (\<forall> a . ((sys:ok\<^sup>< \<longrightarrow> sys:ok\<^sup>>)\<^sub>e a \<longrightarrow> (\<Delta> (view_des_cond V)))\<^sub>e a)
  ) \<longrightarrow>
 ((L (view_des_cond V) ((pre' \<turnstile>\<^sub>r post'))) = (to_viewed_design (((not_pred (L V (not_pred pre'))) \<turnstile>\<^sub>r (L V post')))))"
  apply (expr_simp add: banks_defs)
  by metis

(* Conditional syntax copied from Simon's UTP Practical Session (Pr19, PROF) *)
(*
definition cond :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> bool)" where
[expr_defs]: "cond P b Q = (P \<and> b \<or> Q \<and> \<not>b)\<^sub>e"

syntax "_cond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(3_ \<lhd> _ \<rhd>/ _)" [52,0,53] 52)
translations "_cond P b Q" == "CONST cond (P)\<^sub>e (b)\<^sub>e (Q)\<^sub>e"

expr_constructor cond
*)
(* TODO if-then-else utp style syntax pull request*)

(* The Sys function takes a system that is defined without the use of viewed_system_scheme and "upgrades" it
   This lets you write system predicates with "foo" instead of "sys:foo", which is useful for when you have
   large or complex predicates *)
definition Sys where [banks_defs]: "Sys system = (system \<up> sys\<^sup>2)\<^sub>e"
definition Sys1 where [banks_defs]: "Sys1 system = (system \<up> sys)\<^sub>e"

expr_constructor Sys Sys1

(* Same as for Sys, but for Vu *)
definition Vu where [banks_defs]: "Vu bview = (bview \<up> vu\<^sup>2)\<^sub>e"
definition Vu1 where [banks_defs]: "Vu1 bview = (bview \<up> vu)\<^sub>e"

expr_constructor Vu Vu1

(* simplify with banks' definitions *)
method expr_simp_banks uses add = ((expr_simp2 add: banks_defs add)?)
method pred_auto_banks uses add = ((pred_auto add: banks_defs add)?)

end