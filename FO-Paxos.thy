theory "FO-Paxos"
  imports Main "HOL-Statespace.StateSpaceSyntax"
begin

text \<open>We try to follow the Ivy proof of the isolate abs available here: @{url "https://github.com/nano-o/ivy-proofs/blob/master/paxos/paxos.ivy"}\<close>

section "Setting up the logical environment"

sledgehammer_params[timeout=3000]

statespace ('n,'r,'v) vars =
  vote :: "'n \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> bool"
  left_round :: "'n \<Rightarrow> 'r \<Rightarrow> bool"
  proposal :: "'r \<Rightarrow> 'v \<Rightarrow> bool"
  decision :: "'n \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> bool"

locale test = vars

no_notation Set.member  (\<open>'(\<in>')\<close>)
no_notation Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)
no_notation  ord_class.less_eq  (\<open>'(\<le>')\<close>)
no_notation  ord_class.less_eq  (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le> _)\<close>  [51, 51] 50)
no_notation  ord_class.less  (\<open>'(<')\<close>)
no_notation  ord_class.less  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close>  [51, 51] 50)

locale epr_paxos = vars _ _ _ _ project_HOL_bool_'v_fun_'r_fun_'n_fun + linorder less_eq less
  for project_HOL_bool_'v_fun_'r_fun_'n_fun :: "_ \<Rightarrow> 'n \<Rightarrow> 'r \<Rightarrow> 'v \<Rightarrow> bool" \<comment> \<open>boilerplate to unify type variables of vars and linorder\<close>
    and less_eq :: "'r \<Rightarrow> 'r \<Rightarrow> bool" (infix "\<le>" 50)
    and less (infix "<" 50) +
  fixes quorum_member :: "'n \<Rightarrow> 'q \<Rightarrow> bool" (infix "\<in>" 50)
  assumes "\<And> q1 q2 . \<exists> n . n \<in> q1 \<and> n \<in> q2" \<comment> \<open>quorums intersect\<close>
begin

text \<open>Not sure why we have to redo this:\<close>
no_notation Set.member  (\<open>'(\<in>')\<close>)
no_notation Set.member  (\<open>(\<open>notation=\<open>infix \<in>\<close>\<close>_/ \<in> _)\<close> [51, 51] 50)
no_notation  ord_class.less_eq  (\<open>'(\<le>')\<close>)
no_notation  ord_class.less_eq  (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le> _)\<close>  [51, 51] 50)
no_notation  ord_class.less  (\<open>'(<')\<close>)
no_notation  ord_class.less  (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close>  [51, 51] 50)

section "Specification of the algorithm"

definition init where
  "init c \<equiv> \<forall> n r v .
      \<not>(c\<cdot>vote) n r v
    \<and> \<not>(c\<cdot>left_round) n r
    \<and> \<not>(c\<cdot>proposal) r v
    \<and> \<not>(c\<cdot>decision) n r v"

definition join_round where
  "join_round c c' n r \<equiv> \<not>((c\<cdot>left_round) n r)
    \<and> c' = c<left_round := (c\<cdot>left_round)(n := (\<lambda> r' . (c\<cdot>left_round) n r' \<or> (r' < r)))>"

definition join_round_2 where
  "join_round_2 c c' n r \<equiv> \<not>((c\<cdot>left_round) n r)
    \<and> (\<exists> lrn . 
          c' = c<left_round := (c\<cdot>left_round)(n := lrn)>
        \<and> (\<forall> r' . lrn r' = (c\<cdot>left_round) n r' \<or> (r' < r)))"

definition propose where
  "propose c c' r q maxr v \<equiv>
    (\<forall> v . \<not>(c\<cdot>proposal) r v)
    \<and> (\<forall> n r' . n \<in> q \<and> r' < r \<longrightarrow> (c\<cdot>left_round) n r')
    \<and> (
        (\<forall> n r' v' . \<not>(n \<in> q \<and> r' < r \<and> (c\<cdot>vote) n r' v'))
        \<or> ( maxr < r
            \<and> (\<exists> n . n \<in> q \<and> (c\<cdot>vote) n maxr v)
            \<and> (\<forall> n r' v' . n \<in> q \<and> r' < r \<and> (c\<cdot>vote) n r' v' \<longrightarrow> r' \<le> maxr)))
    \<and> c' = c<proposal := (c\<cdot>proposal)(r := ((c\<cdot>proposal) r)(v := True))>"

definition cast_vote where
  "cast_vote c c' n r v \<equiv>
      \<not>(c\<cdot>left_round) n r
    \<and> (c\<cdot>proposal) r v
    \<and> c' = c<vote := (c\<cdot>vote)(n := ((c\<cdot>vote) n)(r := ((c\<cdot>vote) n r)(v := True)))>"

definition decide where
  "decide c c' n q r v \<equiv>
      (\<forall> n . n \<in> q \<longrightarrow> (c\<cdot>vote) n r v)
    \<and> c' = c<decision := (c\<cdot>decision)(n := ((c\<cdot>decision) n)(r := ((c\<cdot>decision) n r)(v := True)))>"

definition trans_rel where
  "trans_rel c c' q n r maxr v \<equiv>
      propose c c' r q maxr v
    \<or> join_round c c' n r
    \<or> cast_vote c c' n r v
    \<or> decide c c' n q r v"

section "Invariants"

definition inv1 where
  "inv1 c \<equiv> \<forall> v v' r . (c\<cdot>proposal) r v \<and> (c\<cdot>proposal) r v' \<longrightarrow> v = v'"
definition inv2 where
  "inv2 c \<equiv> \<forall> n r v . (c\<cdot>vote) n r v \<longrightarrow> (c\<cdot>proposal) r v"
definition inv3 where
  "inv3 c \<equiv> \<forall> n r v . (c\<cdot>decision) n r v \<longrightarrow> (\<exists> q . \<forall> n . n \<in> q \<longrightarrow> (c\<cdot>vote) n r v)"
definition inv4 where
  "inv4 c \<equiv> \<forall> r1 r2 v1 v2 q . r1 < r2 \<and> (c\<cdot>proposal) r2 v2 \<and> v1 \<noteq> v2 \<longrightarrow>
    (\<exists> n . n \<in> q \<and> (c\<cdot>left_round) n r1 \<and> \<not>(c\<cdot>vote) n r1 v1)"

section "Induction proofs"

lemma l1:
  shows "init c \<Longrightarrow> inv1 c" and "trans_rel c c' q n r maxr v \<and> inv1 c \<Longrightarrow> inv1 c'"
proof -
  show "init c \<Longrightarrow> inv1 c"
    by (simp add: init_def inv1_def)
next
  show "trans_rel c c' q n r maxr v \<and> inv1 c \<Longrightarrow> inv1 c'"
    unfolding trans_rel_def
    apply (auto; simp add: propose_def join_round_def cast_vote_def decide_def inv1_def; auto)
    done
qed

lemma l2:
  shows "init c \<Longrightarrow> inv2 c" and "trans_rel c c' q n r maxr v \<and> inv2 c \<Longrightarrow> inv2 c'"
proof -
  show "init c \<Longrightarrow> inv2 c"
    using init_def inv2_def by auto
next
  show "trans_rel c c' q n r maxr v \<and> inv2 c \<Longrightarrow> inv2 c'"
    unfolding trans_rel_def
    apply (auto; simp add: propose_def join_round_def cast_vote_def decide_def inv2_def; auto)
    done
qed

lemma l3:
  shows "init c \<Longrightarrow> inv3 c" and "trans_rel c c' q n r maxr v \<and> inv3 c \<Longrightarrow> inv3 c'"
proof -
  show "init c \<Longrightarrow> inv3 c"
    using init_def inv3_def by auto
next
  show "trans_rel c c' q n r maxr v \<and> inv3 c \<Longrightarrow> inv3 c'"
    unfolding trans_rel_def
    apply (auto; simp add: propose_def join_round_def cast_vote_def decide_def inv3_def; auto)
      apply (blast|metis)+
    done
qed

lemma l4:
  shows "init c \<Longrightarrow> inv4 c" and "trans_rel c c' q n r maxr v \<and> inv1 c \<and> inv2 c \<and> inv4 c \<Longrightarrow> inv4 c'"
proof -
  show "init c \<Longrightarrow> inv4 c"
    using init_def inv4_def by auto
next
  show "trans_rel c c' q n r maxr v \<and> inv1 c \<and> inv2 c \<and> inv4 c \<Longrightarrow> inv4 c'"
    unfolding trans_rel_def
    apply (auto; simp add: propose_def join_round_def cast_vote_def decide_def inv1_def inv2_def inv4_def)
    subgoal using epr_paxos.axioms(3) epr_paxos_axioms epr_paxos_axioms_def local.order.order_iff_strict by metis
     apply fastforce+
    done
qed

section "The invariants imply safety"

definition safety where
  "safety c \<equiv> \<forall> n1 n2 r1 r2 v1 v2 . (c\<cdot>decision) n1 r1 v1 \<and> (c\<cdot>decision) n2 r2 v2 \<longrightarrow> v1 = v2"

theorem safety:"inv1 c \<and> inv2 c \<and> inv3 c \<and> inv4 c \<Longrightarrow> safety c"
  apply (auto simp add: inv1_def inv2_def inv3_def inv4_def safety_def)
  subgoal using epr_paxos.axioms(3) epr_paxos_axioms epr_paxos_axioms_def
    apply (metis local.less_linear)
    done
  done

end

end