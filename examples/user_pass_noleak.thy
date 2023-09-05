theory user_pass_noleak
  imports Main "../Banks/banks" (*NO_CI*)
  (*CI_ONLY imports Main "Banks.banks" CI_ONLY*)
begin

datatype Msg = Success | ErrBadUsernameOrPassword

alphabet login =
  db :: "string \<Rightarrow> string option"
  username :: string
  password :: string
  result :: Msg

alphabet view\<^sub>\<alpha> =
  v_username :: string
  v_password :: string
  v_result :: Msg

definition view where "view = (
  vu:v_username = sys:username \<and>
  vu:v_password = sys:password \<and>
  vu:v_result = sys:result)\<^sub>e"

definition auth where "auth adb user pass =
  (case (adb user) of
    None \<Rightarrow> ErrBadUsernameOrPassword
    | Some(p) \<Rightarrow> if p = pass then Success else ErrBadUsernameOrPassword
  )
"

definition system where "system = (
  username\<^sup>> = username\<^sup>< \<and>
  password\<^sup>> = password\<^sup>< \<and>
  db\<^sup>> = db\<^sup>< \<and>
  result\<^sup>> = (
    auth (db\<^sup><) (username\<^sup><) (password\<^sup><)
  ))\<^sub>e"

lemma "(L view system) \<down> vu\<^sup>2 = (
    \<exists> adb .
      v_username\<^sup>> = v_username\<^sup>< \<and>
      v_password\<^sup>> = v_password\<^sup>< \<and>
      v_result\<^sup>> = auth adb (v_username\<^sup><) (v_password\<^sup><)
  )\<^sub>e"
  by (pred_auto_banks add: view_def system_def)  

lemma "(infer (system \<up> sys\<^sup>2) view (vu:v_result\<^sup>> = Success)\<^sub>e) = (
    sys:username\<^sup>> = sys:username\<^sup>< \<and>
    sys:password\<^sup>> = sys:password\<^sup>< \<and>
    sys:db\<^sup>> = sys:db\<^sup>< \<and>
    sys:result\<^sup>> = Success \<and>
    (auth (sys:db\<^sup>>) (sys:username\<^sup>>) (sys:password\<^sup>>) = Success)
  )\<^sub>e"
  apply (pred_auto_banks add: view_def system_def)
  by presburger+

lemma "(infer (system \<up> sys\<^sup>2) view ((vu:v_username\<^sup>< = ''Alice'') \<and> vu:v_result\<^sup>> = ErrBadUsernameOrPassword)\<^sub>e) = (
    sys:username\<^sup>> = ''Alice'' \<and>
    sys:username\<^sup>< = ''Alice'' \<and>
    sys:password\<^sup>> = sys:password\<^sup>< \<and>
    sys:db\<^sup>> = sys:db\<^sup>< \<and>
    sys:result\<^sup>> = ErrBadUsernameOrPassword \<and>
    (auth (sys:db\<^sup>>) ''Alice'' (sys:password\<^sup>>) = ErrBadUsernameOrPassword)
  )\<^sub>e"
  apply (pred_auto_banks add: view_def system_def)
  by presburger+

end