theory user_pass_noleak
  imports Main "../Banks/banks" (*NO_CI*)
  (*CI_ONLY imports Main "Banks.banks" CI_ONLY*)
begin

datatype Result = Success | Failure

(* The alphabet of the authentication system *)
alphabet login =
  db :: "string \<Rightarrow> string option"
  username :: string
  password :: string
  result :: Result
  message :: string

definition apply_f where "apply_f a b = a b" 

(* Specification requires that the result variable accurately describes the result of the authentication, but does not specify the message at all *)
definition spec where "spec = (
  username\<^sup>> = username\<^sup>< \<and>
  password\<^sup>> = password\<^sup>< \<and>
  db\<^sup>> = db\<^sup>< \<and>
  (
    (apply_f (db\<^sup><) (username\<^sup><) = None \<and> result\<^sup>> = Failure)
    \<or>(apply_f (db\<^sup><) (username\<^sup><) = Some(password\<^sup><) \<and> result\<^sup>> = Success)
    \<or>(apply_f (db\<^sup><) (username\<^sup><) \<noteq> Some(password\<^sup><) \<and> apply_f (db\<^sup><) (username\<^sup><) \<noteq> None \<and> result\<^sup>> = Failure)
  )
  )\<^sub>e"

(* The attacker's view of the system *)
alphabet view\<^sub>\<alpha> =
  v_username :: string
  v_password :: string
  v_result :: Result
  v_message :: string

definition system where "system = (
  username\<^sup>> = username\<^sup>< \<and>
  password\<^sup>> = password\<^sup>< \<and>
  db\<^sup>> = db\<^sup>< \<and>
  (
    (apply_f (db\<^sup><) (username\<^sup><) = None \<and> result\<^sup>> = Failure)
    \<or>(apply_f (db\<^sup><) (username\<^sup><) = Some(password\<^sup><) \<and> result\<^sup>> = Success)
    \<or>(apply_f (db\<^sup><) (username\<^sup><) \<noteq> Some(password\<^sup><) \<and> apply_f (db\<^sup><) (username\<^sup><) \<noteq> None \<and> result\<^sup>> = Failure)
  ) \<and>
  (
    (apply_f (db\<^sup><) (username\<^sup><) = None \<and> message\<^sup>> = ''Authentication failed'')
    \<or>(apply_f (db\<^sup><) (username\<^sup><) = Some(password\<^sup><) \<and> message\<^sup>> = ''Success'')
    \<or>(apply_f (db\<^sup><) (username\<^sup><) \<noteq> Some(password\<^sup><) \<and> apply_f (db\<^sup><) (username\<^sup><) \<noteq> None \<and> message\<^sup>> = ''Authentication failed'')
  )
  )\<^sub>e"

(* Proof automation confirms that the spec is refined by the system *)
lemma "spec \<sqsubseteq> system"
  by (pred_auto add: spec_def system_def)

(* Attacker can provide a username and password and see the result and message *)
definition view where "view = (
  vu:v_username = sys:username \<and>
  vu:v_password = sys:password \<and>
  vu:v_result = sys:result \<and>
  vu:v_message = sys:message
)\<^sub>e"
  
lemma "(L view system) \<down> vu\<^sup>2 = (
    \<exists> db .
      v_username\<^sup>> = v_username\<^sup>< \<and>
      v_password\<^sup>> = v_password\<^sup>< \<and>
      (
        (apply_f db (v_username\<^sup><) = None \<and> v_result\<^sup>> = Failure)
        \<or>(apply_f db (v_username\<^sup><) = Some(v_password\<^sup><) \<and> v_result\<^sup>> = Success)
        \<or>(apply_f db (v_username\<^sup><) \<noteq> Some(v_password\<^sup><) \<and> apply_f db (v_username\<^sup><) \<noteq> None \<and> v_result\<^sup>> = Failure)
      ) \<and>
      (
        (apply_f db (v_username\<^sup><) = None \<and> v_message\<^sup>> = ''Authentication failed'')
        \<or>(apply_f db (v_username\<^sup><) = Some(v_password\<^sup><) \<and> v_message\<^sup>> = ''Success'')
        \<or>(apply_f db (v_username\<^sup><) \<noteq> Some(v_password\<^sup><) \<and> apply_f db (v_username\<^sup><) \<noteq> None \<and> v_message\<^sup>> = ''Authentication failed'')
      )
  )\<^sub>e"
  by (pred_auto_banks add: view_def system_def)

lemma "(infer (system \<up> sys\<^sup>2) view (vu:v_message\<^sup>> = ''Success'')\<^sub>e) \<down> sys\<^sup>2 = (
    username\<^sup>> = username\<^sup>< \<and>
    password\<^sup>> = password\<^sup>< \<and>
    db\<^sup>> = db\<^sup>< \<and>
    message\<^sup>> = ''Success'' \<and>
    result\<^sup>> = Success \<and>
    (apply_f (db\<^sup><) (username\<^sup><) = Some(password\<^sup><))
  )\<^sub>e"
  by (pred_auto_banks add: view_def system_def)

lemma "(infer (system \<up> sys\<^sup>2) view ((vu:v_username\<^sup>< = ''Alice'') \<and> vu:v_message\<^sup>> = ''Authentication failed'')\<^sub>e)  \<down> sys\<^sup>2 = (
    username\<^sup>> = ''Alice'' \<and> username\<^sup>< = ''Alice'' \<and>
    password\<^sup>> = password\<^sup>< \<and>
    db\<^sup>> = db\<^sup>< \<and>
    message\<^sup>> = ''Authentication failed'' \<and>
    result\<^sup>> = Failure \<and>
    (apply_f (db\<^sup><) ''Alice'' \<noteq> Some(password\<^sup><)) 
  )\<^sub>e"
  by (pred_auto_banks add: view_def system_def)
end