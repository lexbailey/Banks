theory Scratch
  imports Main
begin

record vars =
  ok :: bool
  vu :: nat
  sys :: int

type_synonym vpair = "vars * vars"

value "\<lparr> ok = True, vu = 1, sys = 2 \<rparr>"

definition Ln :: "(vpair \<Rightarrow> bool) \<Rightarrow> (vpair \<Rightarrow> bool) \<Rightarrow> vpair \<Rightarrow> bool"
  where "Ln aview pred = (\<lambda> a .
    (\<exists> asys asys' avu .
      aview ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> (pred ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
    )
  )"

definition vh1 where "vh1 aview =
    (if (\<exists> avu avu' aok aok'.
      (\<forall> a .aview ((fst a)\<lparr>ok:=aok,vu:=avu\<rparr>, (snd a)\<lparr>ok:=aok',vu:=avu'\<rparr>))
    ) then aview else (\<lambda> a. True)
  )"

definition no_ok where "no_ok aview = (if (\<exists> a.
      (aview a \<noteq> aview ((fst a)\<lparr>ok:=\<not> ok (fst a)\<rparr>, (snd a)))
      \<or>
      (aview a \<noteq> aview ((fst a), (snd a)\<lparr>ok:=\<not> ok (snd a)\<rparr>))
    ) then (\<lambda> a. True) else aview)"

definition design :: "(vpair \<Rightarrow> bool) \<Rightarrow> (vpair \<Rightarrow> bool) \<Rightarrow> vpair \<Rightarrow> bool"
  where "design apre apost = (\<lambda> a . (ok (fst a)) \<and> (apre a) \<longrightarrow> (ok (snd a)) \<and> (apost a))"

definition notp where "notp p a = (\<not> (p a))"

lemma
  fixes "apre" "apost" "v"
  assumes "vh1 v = v"
  assumes "no_ok v = v"
  shows "Ln v (design apre apost) = (design (notp (Ln v (notp apre))) (Ln v apost))"
proof -
  have "Ln v (design apre apost) = (\<lambda> a .
    (\<exists> asys asys' avu .
      v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((design apre apost) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
    )
    )"
    by (simp only: Ln_def)
  then have "... = (\<lambda> a .
    (\<exists> asys asys' avu .
      v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((
       (\<lambda> b . (ok (fst b)) \<and> (apre b) \<longrightarrow> (ok (snd b)) \<and> (apost b))
      ) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
    )
    )"
    by (simp only: design_def)
  then have "... = (\<lambda> a .
    (\<exists> asys asys' avu .
      v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((
       (\<lambda> b . (\<not> ok (fst b)) \<or>  (\<not> apre b) \<or> ((ok (snd b)) \<and> (apost b)))
      ) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
    )
    )"
    by auto
  then have "... = (\<lambda> a .
      (\<exists> asys asys' avu .
        v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((
         (\<lambda> b . (\<not> ok (fst b)) \<or>  (\<not> apre b))
        ) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
      )

\<or>

      (\<exists> asys asys' avu .
        v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((
         (\<lambda> b . ((ok (snd b)) \<and> (apost b)))
        ) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
      )
    )"
    by blast
  then have "... = (\<lambda> a .
      ((\<not> (ok (fst a))) \<or> (\<exists> asys asys' avu .
        v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((
         (\<lambda> b . (\<not> (apre b)))
        ) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
      ))

\<or>

      ((ok (snd a)) \<and> (\<exists> asys asys' avu .
        v ((fst a)\<lparr>sys:=asys, vu:=avu\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>) \<and> ((
         (\<lambda> b . ((apost b)))
        ) ((fst a)\<lparr>sys:=asys\<rparr>, (snd a)\<lparr>sys:=asys'\<rparr>))
      ))
    )"
    using assms
    
    
  

end