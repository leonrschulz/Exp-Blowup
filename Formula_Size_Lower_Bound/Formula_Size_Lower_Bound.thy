theory Formula_Size_Lower_Bound
imports
  Main
  Propositional_Proof_Systems.Formulas
  Propositional_Proof_Systems.Sema
  Propositional_Proof_Systems.CNF_Formulas     
begin

subsection \<open>Moved to Isabelle-devel\<close>

(*MDS*)
(*TODO: Delete when a new Isabelle version is released. *)
lemma card_Domain_le:
  assumes "finite A"
  shows "card (Domain A) \<le> card A"
  using assms by (metis card_image_le fst_eq_Domain)

(*MDS*)
(*TODO: Delete when a new Isabelle version is released. *)
lemma card_le_card_if_mem_imp_ex_mem:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" and \<X> :: "'a set" and \<Y> :: "'c set"
  defines "XY \<equiv> {(x, y)| x y. x \<in> \<X> \<and> f x y \<in> \<Y>}"
  assumes "finite \<X>" and "finite \<Y>" and
    f_inj: "inj_on (\<lambda>(x, y). f x y) XY" and
    ex_in_\<Y>: "\<And>x. x \<in> \<X> \<Longrightarrow> \<exists>y. f x y \<in> \<Y>"
  shows "card \<X> \<le> card \<Y>"
proof -
  have f_XY_subset: "(\<lambda>(x, y). f x y) ` XY \<subseteq> \<Y>"
    using XY_def by auto

  then have "finite ((\<lambda>(x, y). f x y) ` XY)"
    using \<open>finite \<Y>\<close> by (rule finite_subset)

  then have "finite XY"
    by (rule finite_image_iff[THEN iffD1, OF f_inj])

  moreover have "Domain XY = \<X>"
    unfolding XY_def
    using ex_in_\<Y>
    by (simp add: equalityI subsetI)

  ultimately have "card \<X> \<le> card XY"
    using card_Domain_le by iprover

  also have "\<dots> \<le> card \<Y>"
    using inj_on_iff_card_le[OF \<open>finite XY\<close> \<open>finite \<Y>\<close>]
    using f_XY_subset f_inj by blast

  finally show "card \<X> \<le> card \<Y>" .
qed


section \<open>Functions & Datatypes\<close>

fun BigAnd' :: "'a formula list \<Rightarrow> 'a formula" where
"BigAnd' [] = (\<^bold>\<not>\<bottom>)" |
"BigAnd' [F] = F" |
"BigAnd' (F # Fs) = F \<^bold>\<and> BigAnd' Fs"

lemma atoms_BigAnd'[simp]: "atoms (BigAnd' Fs) = \<Union>(atoms ` set Fs)"
  by (induction Fs rule: BigAnd'.induct) simp_all

lemma BigAnd'_semantics[simp]: "A \<Turnstile> BigAnd' Ts \<longleftrightarrow> (\<forall>f \<in> set Ts. A \<Turnstile> f)"
  by (induction Ts rule: BigAnd'.induct) simp_all

fun BigOr' :: "'a formula list \<Rightarrow> 'a formula" where
  "BigOr' Nil = \<bottom>" |
  "BigOr' [F] = F" |
  "BigOr' (F#Fs) = F \<^bold>\<or> BigOr' Fs"

lemma atoms_BigOr'[simp]: "atoms (BigOr' Fs) = \<Union>(atoms ` set Fs)"
  by (induction Fs rule: BigOr'.induct) simp_all

lemma BigOr'_semantics[simp]: "A \<Turnstile> BigOr' Ts \<longleftrightarrow> (\<exists>f \<in> set Ts. A \<Turnstile> f)"
  by (induction Ts rule: BigOr'.induct) simp_all

fun is_conj :: "'a formula \<Rightarrow> bool" where
"is_conj (And F G) = (is_lit_plus F \<and> is_conj G)" |
"is_conj F = is_lit_plus F"

fun is_dnf :: "'a formula \<Rightarrow> bool" where
"is_dnf (Or F G) = (is_dnf F \<and> is_dnf G)" |
"is_dnf H = is_conj H"

text \<open>Should only be applied to a formula for which @{const is_nnf} holds.\<close>
fun cont_pos :: "'a formula \<Rightarrow> 'a \<Rightarrow> bool" where
"cont_pos Bot l = False" |
"cont_pos (Atom v) l = (v = l)" |
"cont_pos (Not (Atom v)) l = False" |
"cont_pos (Not F) l = False" |
"cont_pos (And F G) l = (cont_pos F l \<or> cont_pos G l)" |
"cont_pos (Or F G) l = (cont_pos F l \<or> cont_pos G l)" |
"cont_pos (Imp F G) l = False"

text \<open>Should only be applied to a formula for which @{const is_nnf} holds.\<close>
fun cont_neg :: "'a formula \<Rightarrow> 'a \<Rightarrow> bool" where
"cont_neg Bot l = False" |
"cont_neg (Atom v) l = False" |
"cont_neg (Not (Atom v)) l = (v = l)" |
"cont_neg (Not F) l = False" |
"cont_neg (And F G) l = (cont_neg F l \<or> cont_neg G l)" |
"cont_neg (Or F G) l = (cont_neg F l \<or> cont_neg G l)" |
"cont_neg (Imp F G) l = False"

text \<open>Should only be applied to a formula for which @{const is_nnf} holds.\<close>
fun cont :: "'a formula \<Rightarrow> 'a \<Rightarrow> bool" where
"cont Bot l = False" |
"cont (Atom v) l = (v = l)" |
"cont (Not (Atom v)) l = (v = l)" |
"cont (Not F) l = False" |
"cont (And F G) l = (cont F l \<or> cont G l)" |
"cont (Or F G) l = (cont F l \<or> cont G l)" |
"cont (Imp F G) l = False"

datatype var = Var nat bool

fun Fn :: "nat \<Rightarrow> var formula" where
"Fn 0 = (\<^bold>\<not>\<bottom>)"|
"Fn (Suc n) = And
               (And
                (Or
                 (Atom (Var (Suc n) False))
                 (Atom (Var (Suc n) True))
                )
                (Or
                 (Not (Atom (Var (Suc n) False)))
                 (Not (Atom (Var (Suc n) True)))
                )
               )
               (Fn n)"

definition equiv :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool" where
"equiv F G = (\<forall> Val. (Val \<Turnstile> F) \<longleftrightarrow> (Val \<Turnstile> G))"

lemma equiv_symmetric[sym]: "\<And>\<phi> \<psi>. equiv \<phi> \<psi> \<Longrightarrow> equiv \<psi> \<phi>"
  unfolding equiv_def by simp

lemma equiv_transitive[trans]: "\<And>\<xi> \<phi> \<psi>. equiv \<xi> \<phi> \<Longrightarrow> equiv \<phi> \<psi> \<Longrightarrow> equiv \<xi> \<psi>"
  unfolding equiv_def by simp

text \<open>Similar to @{const size}, but ignores @{term "\<^bold>\<not>"} when calculating the size.\<close>
fun sizef :: "'a formula \<Rightarrow> nat" where
"sizef Bot = 1" |
"sizef (Atom a) = 1" |
"sizef (Not F) = sizef F" |
"sizef (And F G) = sizef F + sizef G + 1" |
"sizef (Or F G) = sizef F + sizef G + 1" |
"sizef (Imp F G) = sizef F + sizef G + 1" 

lemma Suc_0_le_sizef[simp]: "Suc 0 \<le> sizef F"
  by (induction F) simp_all


section \<open>Required Lemmata for Proposition 4\<close>

lemma size_Fn: "sizef(Fn n) = 8*n+1"
  by (induction n; auto)

lemma Fn_in_cnf: "is_cnf(Fn n)"
  by (induction n; auto)

lemma conj_is_dnf: "is_conj F \<Longrightarrow> is_dnf F"
  by (induction F; auto)

lemma is_dnf_BigOr':  "(\<forall> T \<in> set Ts. is_conj T \<and> (\<exists> Val. Val \<Turnstile> T)) \<Longrightarrow> is_dnf (BigOr' Ts)"
proof (induction Ts)
  case Nil
  then show ?case by simp
next
  case (Cons T Ts)
  then show ?case
    by (metis conj_is_dnf list.set_intros(1) BigOr'.simps(2) BigOr'.simps(3) list.set_intros(2)
        is_dnf.simps(1) neq_Nil_conv)
qed

lemma not_sat_Fn_both_false:
  fixes Val
  assumes a1:"n \<noteq> 0" and
          a2: "\<exists>i \<in> {1..n}. Val (Var i False) = False \<and> Val (Var i True) = False"
        shows "\<not> Val \<Turnstile> Fn n"
  using a1 a2
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  have "\<not> Val (Var (Suc n) False) \<and> \<not> Val (Var (Suc n) True) \<or> 
        Val (Var (Suc n) False) \<and> Val (Var (Suc n) True) \<or> \<not> Val \<Turnstile> Fn n" 
    by (metis One_nat_def Suc.IH Suc.prems(2) Suc_leI atLeastAtMost_iff le_antisym 
        le_neq_implies_less nat_le_linear)
  then show ?case 
    by simp
qed

lemma not_sat_Fn_both_true:
  fixes Val
  assumes a1:"n \<noteq> 0" and
          a2: "\<exists>i \<in> {1..n}. Val (Var i False) = True \<and> Val (Var i True) = True"
        shows "\<not> Val \<Turnstile> Fn n"
  using a1 a2
proof (induction n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  have "\<not> Val (Var (Suc n) False) \<and> \<not> Val (Var (Suc n) True) \<or> 
        Val (Var (Suc n) False) \<and> Val (Var (Suc n) True) \<or> \<not> Val \<Turnstile> Fn n" 
    by (metis One_nat_def Suc.IH Suc.prems(2) Suc_leI atLeastAtMost_iff le_antisym 
        le_neq_implies_less nat_le_linear)
  then show ?case 
    by simp
qed

lemma not_sat_conj_pos_false: 
  assumes a1: " is_conj F" and
          a2: "\<exists> v. cont_pos F v \<and> \<not>(Val v)"
        shows "\<not>(Val \<Turnstile> F)"
  using a1 a2
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by (metis cont_pos.elims(2) formula.distinct(19,21,3))
next
  case (And F1 F2)
  then show ?case 
    by (metis cont_pos.simps(9) formula_semantics.simps(2,4) is_conj.simps(1,2,4) 
        is_lit_plus.elims(2))
next
  case (Or F1 F2)
  then show ?case 
    by simp
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma not_sat_conj_neg_true: 
  assumes a1: "is_conj F" and
          a2: "\<exists> v. cont_neg F v \<and> Val v"
        shows "\<not>(Val \<Turnstile> F)"
  using a1 a2
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by (metis cont_neg.elims(2) formula.distinct(19,21) formula_semantics.simps(1,3))
next
  case (And F1 F2)
  then show ?case 
    by (metis cont_neg.simps(9) formula_semantics.simps(2,4) is_conj.simps(1,2,4) 
        is_lit_plus.elims(2))
next
  case (Or F1 F2)
  then show ?case 
    by simp
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma impl_not_cont_pos: "\<not> cont_pos F v \<Longrightarrow> cont_neg F v \<or> \<not> (cont F v)"
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by (smt (verit) cont.elims(1) cont.simps(3,4,5,6,7,8) cont_neg.simps(3))
next
  case (And F1 F2)
  then show ?case 
    by auto
next
  case (Or F1 F2)
  then show ?case 
    by auto
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma sat_conj_val_cont_ident:
  assumes a1: "Val1 \<Turnstile> F" and
          a2: "\<forall> v \<in> {v. cont F v}. Val1 v = Val2 v" and
          a3: "is_conj F" 
        shows "Val2 \<Turnstile> F"
  using a1 a2 a3
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by (metis cont.simps(3) formula_semantics.simps(1,2,3) is_conj.simps(4) is_nnf.simps(6) 
        is_nnf_NotD mem_Collect_eq)
next
  case (And F1 F2)
  then show ?case 
    by (metis cont.simps(9) formula_semantics.simps(2,4) is_conj.simps(1,2,4) 
        is_lit_plus.elims(2) mem_Collect_eq)
next
  case (Or F1 F2)
  then show ?case 
    by simp
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

(*MDS*)
lemma mem_atoms_if_cont_pos:
  assumes "cont_pos T v"
  shows "v \<in> atoms T"
  using assms by (induction T v rule: cont_pos.induct) auto

(*MDS*)
lemma card_atoms_le_sizef: "card (atoms F) \<le> sizef F"
proof (induction F)
  case (And F1 F2)
  have "card (atoms (F1 \<^bold>\<and> F2)) = card (atoms F1 \<union> atoms F2)"
    by simp
  also have "\<dots> \<le> card (atoms F1) + card (atoms F2)"
    using card_Un_le by metis
  also have "\<dots> < Suc (card (atoms F1) + card (atoms F2))"
    by presburger
  also have "\<dots> \<le> Suc (sizef F1 + sizef F2)"
    using And.IH by presburger
  also have "\<dots> = sizef (F1 \<^bold>\<and> F2)"
    by simp
  finally show ?case
    by presburger
next
  case (Or F1 F2)
  have "card (atoms (F1 \<^bold>\<or> F2)) = card (atoms F1 \<union> atoms F2)"
    by simp
  also have "\<dots> \<le> card (atoms F1) + card (atoms F2)"
    using card_Un_le by metis
  also have "\<dots> < Suc (card (atoms F1) + card (atoms F2))"
    by presburger
  also have "\<dots> \<le> Suc (sizef F1 + sizef F2)"
    using Or.IH by presburger
  also have "\<dots> = sizef (F1 \<^bold>\<or> F2)"
    by simp
  finally show ?case
    by presburger
next
  case (Imp F1 F2)
  have "card (atoms (F1 \<^bold>\<rightarrow> F2)) = card (atoms F1 \<union> atoms F2)"
    by simp
  also have "\<dots> \<le> card (atoms F1) + card (atoms F2)"
    using card_Un_le by metis
  also have "\<dots> < Suc (card (atoms F1) + card (atoms F2))"
    by presburger
  also have "\<dots> \<le> Suc (sizef F1 + sizef F2)"
    using Imp.IH by presburger
  also have "\<dots> = sizef (F1 \<^bold>\<rightarrow> F2)"
    by simp
  finally show ?case
    by presburger
qed simp_all

lemma aux_exp_size: "length Ts = n \<Longrightarrow> \<forall> T \<in> set Ts. sizef T \<ge> m \<Longrightarrow> sizef (BigOr' Ts) \<ge> n * m"
  by (induction Ts arbitrary: m n rule: BigOr'.induct; fastforce)

lemma exp_size: "n > 0 \<Longrightarrow> length Ts \<ge> 2^n \<Longrightarrow> \<forall> T \<in> set Ts. sizef T \<ge> m \<Longrightarrow> 
                 sizef (BigOr' Ts) \<ge> 2^n * m"
proof (induction Ts arbitrary: n m rule: BigOr'.induct)
  case 1
  then show ?case
    by simp
next
  case (2 F)
  then have False
    by (metis list.size(3) One_nat_def length_Cons leD one_less_power less_2_cases_iff)
  then show ?case ..
next
  case (3 T T' Ts')
  define Ts where
    "Ts = T' # Ts'"
  have "2 ^ n \<le> length Ts \<or> 2 ^ n = Suc (length Ts)" 
    unfolding Ts_def using "3.prems" by auto
  then have "2 ^ n * m \<le> Suc (sizef T + sizef (BigOr' Ts))" 
  proof (elim disjE)
    assume asm1: "2 ^ n \<le> length Ts"

    have "2 ^ n * m \<le> sizef (BigOr' (T' # Ts'))"
    proof (rule "3.IH")
      show "0 < n"
        by (metis "3.prems"(1))
    next
      show "2 ^ n \<le> length (T' # Ts')"
        using Ts_def asm1 by blast
    next
      show "(\<forall>T\<in>set (T' # Ts'). m \<le> sizef T)"
        by (simp add: "3.prems"(3) Ts_def)
    qed

    also have "\<dots> \<le> Suc (sizef T + sizef (BigOr' Ts))"
      by (simp add: Ts_def)

    finally show ?thesis .
  next
    assume "2 ^ n = Suc (length Ts)"

    then have "2 ^ n = length (T # Ts)" 
      by simp

    moreover have "\<forall> T \<in> set (T # Ts). sizef T \<ge> m"
      by (metis "3.prems"(3) Ts_def)

    ultimately show ?thesis
      using aux_exp_size by fastforce
  qed
  then show ?case
    by (simp add: Ts_def)
qed

(*MDS*)
lemma inj_on_Var[simp]: "inj_on (\<lambda>(x, y). Var x y) A" for A
  by (rule inj_onI) (simp add: case_prod_beta prod_eq_iff)


section \<open>Proposition 4\<close>

proposition proposition4:
  fixes n :: nat and Ts :: "var formula list"
  defines "F \<equiv> Fn n" and "G \<equiv> BigOr' Ts"
  assumes
    n_greater_0: "n > 0" and
    G_spec: "(\<forall>T\<in>set Ts. is_conj T \<and> (\<exists> Val. Val \<Turnstile> T))" and
    equiv_F_G: "equiv F G"
  shows "sizef G \<ge> n*2^n"
proof -
  note def_F = F_def
  note def_G = G_def G_spec
  have size_F: "sizef F = 8*n+1" 
    using def_F by (simp add: size_Fn)
  have in_cnf_F: "is_cnf F" 
    using def_F by (simp add: Fn_in_cnf)
  have in_dnf_G: "is_dnf G" 
    using def_G is_dnf_BigOr' by auto
  have occ_var_bool_diff: "\<forall> T \<in> set Ts. \<forall> i \<in> {1..n}. 
                           (cont_pos T (Var i False) \<noteq> cont_pos T (Var i True))"
  proof (rule ccontr)
    assume "\<not>(\<forall> T \<in> set Ts. \<forall> i \<in> {1..n}. 
            (cont_pos T (Var i False) \<noteq> cont_pos T (Var i True)))"
    then have "\<exists> T \<in> set Ts. \<exists> i \<in> {1..n}. 
               \<not>(cont_pos T (Var i False) \<noteq> cont_pos T (Var i True))" 
      by simp
    then have "\<exists> T \<in> set Ts. \<exists> i \<in> {1..n}. 
               (\<not>(cont_pos T (Var i False)) \<and> \<not>(cont_pos T (Var i True)) \<or> 
                 (cont_pos T (Var i False)) \<and> (cont_pos T (Var i True)))" 
      by auto
    then obtain T where "\<exists> i \<in> {1..n}. 
                         (\<not>(cont_pos T (Var i False)) \<and> \<not>(cont_pos T (Var i True)) \<or> 
                           (cont_pos T (Var i False)) \<and> (cont_pos T (Var i True)))" 
                  and "T \<in> set Ts" 
      by auto
    then obtain i where T_var: "(\<not>(cont_pos T (Var i False)) \<and> \<not>(cont_pos T (Var i True)) \<or> 
                                  (cont_pos T (Var i False)) \<and> (cont_pos T (Var i True)))" 
                  and "i \<in> {1..n}" 
      by blast
    show "False" 
      using T_var
    proof
      assume asm1: "\<not>(cont_pos T (Var i False)) \<and> \<not>(cont_pos T (Var i True))"
      then have "\<exists> Val. Val \<Turnstile> T" 
        by (simp add: \<open>T \<in> set Ts\<close> def_G)
      then obtain ValsatT where Valsat: "ValsatT \<Turnstile> T" 
        by auto
      define Val where 
        def_Val: "Val = (\<lambda> v. (if v = Var i False \<or> v = Var i True then False else ValsatT v))"
      then have "\<forall> v \<in> {v. cont_pos T v}. ValsatT v = Val v" 
        by (simp add: def_Val asm1)
      then have "Val \<Turnstile> T" 
        by (metis \<open>T \<in> set Ts\<close> def_Val not_sat_conj_neg_true def_G impl_not_cont_pos 
            mem_Collect_eq Valsat sat_conj_val_cont_ident)
      then have "\<exists> Val. Val \<Turnstile> T \<and> Val (Var i False) = False \<and> Val (Var i True) = False" 
        using def_Val by auto
      then have "\<exists> Val. Val \<Turnstile> G \<and> \<not>(Val \<Turnstile> F)" 
        using BigOr'_semantics \<open>T \<in> set Ts\<close> \<open>i \<in> {1..n}\<close> 
              def_F def_G not_sat_Fn_both_false n_greater_0 by blast
      then show False 
        using equiv_F_G equiv_def by auto
    next
      assume asm2: "(cont_pos T (Var i False)) \<and> (cont_pos T (Var i True))"
      then have "\<exists> Val. Val \<Turnstile> T" 
        by (simp add: \<open>T \<in> set Ts\<close> def_G)
      then have "\<exists> Val. Val \<Turnstile> T \<and> Val (Var i False) = True \<and> Val (Var i True) = True" 
        using \<open>T \<in> set Ts\<close> asm2 not_sat_conj_pos_false def_G by blast
      then have "\<exists> Val. Val \<Turnstile> G \<and> \<not>(Val \<Turnstile> F)" 
        using BigOr'_semantics \<open>T \<in> set Ts\<close> \<open>i \<in> {1..n}\<close> 
              def_F def_G not_sat_Fn_both_true n_greater_0 by blast
      then show False 
        using equiv_F_G equiv_def by auto
    qed
  qed
  have ex_T_cont_pos_var_eps: "\<exists> T \<in> set Ts. \<forall> i \<in> {1..n}. cont_pos T (Var i (nth eps (i-1)))" 
    if "length eps = n" for eps :: "bool list"
  proof (rule ccontr)
    assume "\<not> (\<exists> T \<in> set Ts. \<forall> i \<in> {1..n}. cont_pos T (Var i (nth eps (i-1))))"
    then have "\<forall> T \<in> set Ts. \<exists> i \<in> {1..n}. \<not>(cont_pos T (Var i (nth eps (i-1))))" 
      by simp
    then have content_T: "\<forall> T \<in> set Ts. \<exists> i \<in> {1..n}. cont_pos T (Var i (\<not>(nth eps (i-1))))" 
      using occ_var_bool_diff by (metis (full_types))
    define Val where 
      def_Val: "Val = (\<lambda>x. case x of (Var i b) \<Rightarrow> (if b = (nth eps (i-1)) then True else False))"
    have "Val \<Turnstile> Fn n" 
      using def_Val by (induction n; simp)
    then have 1: "Val \<Turnstile> F" 
      by (simp add: def_F)
    have "\<forall> i \<in> {1..n}. \<not> (Val (Var i (\<not>(nth eps (i-1)))))" 
      using def_Val by auto
    then have "\<forall> T \<in> set Ts. \<not>(Val \<Turnstile> T)" 
      by (metis not_sat_conj_pos_false def_G content_T)
    then have 2: "\<not>(Val \<Turnstile> G)" 
      using def_G by auto
    have "Val \<Turnstile> F \<and> \<not>(Val \<Turnstile> G)" 
      using 1 2 by auto
    then show False 
      using equiv_F_G equiv_def by auto
  qed

  (*MDS*)
  have n_le_card_atoms: "n \<le> card (atoms T)" if T_in: "T \<in> set Ts" for T
    using card_le_card_if_mem_imp_ex_mem[of "{1..n}" "atoms T" Var, simplified]
    using occ_var_bool_diff[rule_format, OF T_in]
    by (metis One_nat_def atLeastAtMost_iff mem_atoms_if_cont_pos)

  (*MDS*)
  have all_T_ge_n: "\<forall> T \<in> set Ts. sizef T \<ge> n"
    using n_le_card_atoms card_atoms_le_sizef
    using le_trans by blast
                                   
  (*MDS*)
  define conj_of_eps where
    "conj_of_eps = (\<lambda> eps. (SOME T. T \<in> set Ts \<and> (\<forall> i \<in> {1..(length eps)}. 
                            cont_pos T (Var i (nth eps (i-1))))))"

  (*MDS*)
  have T_of_conj_of_eps_in_Ts: "conj_of_eps eps \<in> set Ts" if "length eps = n" for eps
    unfolding conj_of_eps_def
    by (smt (verit, best) ex_T_cont_pos_var_eps that verit_sko_ex')

  (*MDS*)
  have card_eps_le_card_Ts: "card {eps :: bool list. length eps = n} \<le> card (set Ts)"
  proof (rule card_inj_on_le [of conj_of_eps])
    show inj_conj_of_eps: "inj_on conj_of_eps {eps. length eps = n}"
    proof (rule inj_onI)
      fix xs ys :: "bool list"
      assume
        x_in: "xs \<in> {eps. length eps = n}" and
        y_in: "ys \<in> {eps. length eps = n}"

      have "length xs = n"
        using x_in by simp

      moreover have "length ys = n"
        using y_in by simp

      ultimately have "length xs = length ys"
        by simp

      show "conj_of_eps xs = conj_of_eps ys \<Longrightarrow> xs = ys"
      proof (erule contrapos_pp)
        assume "xs \<noteq> ys"
        then obtain i where "i < n" and "nth xs i \<noteq> nth ys i"
          using \<open>length xs = length ys\<close>
          using \<open>length xs = n\<close> nth_equalityI by blast

        have "cont_pos (conj_of_eps xs) (Var (Suc i) (xs ! i))"
        proof -
          have "conj_of_eps xs \<in> set Ts \<and> 
                (\<forall>i\<in>{1..n}. cont_pos (conj_of_eps xs) (Var i (xs ! (i - 1))))"
            by (smt (verit, ccfv_SIG) \<open>length xs = n\<close> conj_of_eps_def 
                ex_T_cont_pos_var_eps someI_ex)
          then show ?thesis
            using \<open>i < n\<close> by force
        qed

        moreover have "cont_pos (conj_of_eps ys) (Var (Suc i) (ys ! i))"
        proof -
          have "conj_of_eps ys \<in> set Ts \<and> 
                (\<forall>i\<in>{1..n}. cont_pos (conj_of_eps ys) (Var i (ys ! (i - 1))))"
            by (smt (verit, ccfv_SIG) \<open>length ys = n\<close> conj_of_eps_def 
                ex_T_cont_pos_var_eps someI_ex)
          then show ?thesis
            using \<open>i < n\<close> by force
        qed

        ultimately have False if "conj_of_eps xs = conj_of_eps ys"
          unfolding that
          using \<open>nth xs i \<noteq> nth ys i\<close>
          using occ_var_bool_diff[rule_format, OF T_of_conj_of_eps_in_Ts[OF \<open>length ys = n\<close>], 
                                  of "Suc i"]
          using \<open>i < n\<close> by auto

        then show "conj_of_eps xs \<noteq> conj_of_eps ys"
          by satx
      qed
    qed

    show "conj_of_eps ` {eps. length eps = n} \<subseteq> set Ts"
    proof (intro subsetI, unfold image_iff, elim bexE, unfold mem_Collect_eq)
      show "\<And>x eps. length eps = n \<Longrightarrow> x = conj_of_eps eps \<Longrightarrow> x \<in> set Ts"
        using T_of_conj_of_eps_in_Ts by metis
    qed
  next
    show "finite (set Ts)"
      by simp
  qed

  moreover have "card {eps :: bool list. length eps = n} = 2^n"
    using card_lists_length_eq[of "{True, False}" n]
    by (smt (verit, best) Collect_cong UNIV_bool card_UNIV_bool def_F finite_code insert_commute 
        insert_iff subset_code(1))

  ultimately have G_cont_exp_T: "length Ts \<ge> 2^n"
    using card_length[of Ts] by presburger

  have "sizef (BigOr' Ts) \<ge> n*2^n" 
    using exp_size by (metis all_T_ge_n G_cont_exp_T mult.commute n_greater_0)
  
  then show ?thesis by (simp add: def_G)
qed

fun undnf :: "'a formula \<Rightarrow> 'a formula list" where
"undnf (Or F G) = undnf F @ undnf G" |
"undnf H = [H]"

lemma undnf_neq_Nil[simp]: "undnf \<phi> \<noteq> []"
  by (induction \<phi>) simp_all

fun count_Or :: "'a formula \<Rightarrow> nat" where
"count_Or (Or F G) = count_Or F + count_Or G + 1" |
"count_Or _ = 0"

lemma length_undnf: "length (undnf \<phi>) = count_Or \<phi> + 1"
  by (induction \<phi>) simp_all


lemma equiv_BigOr'_append: "equiv (BigOr' (xs @ ys)) (Or (BigOr' xs) (BigOr' ys))"
  by (induction xs) (simp_all add: equiv_def)

lemma transp_equiv: "transp equiv"
  by (rule transpI) (simp add: equiv_def)

lemma equiv_BigOr'_undnf_if_dnf:
  fixes \<phi> :: "'a formula"
  shows "equiv (BigOr' (undnf \<phi>)) \<phi>"
proof (induction \<phi> rule: is_dnf.induct)
  case (1 F G)
  then show ?case
    using equiv_BigOr'_append
    by (smt (verit) equiv_def formula_semantics.simps(5) undnf.simps(1))
qed (simp_all add: equiv_def)

lemma ball_undnf_is_conj:
  fixes \<phi> :: "'a formula"
  assumes dnf: "is_dnf \<phi>"
  shows "\<And>T. T \<in> set (undnf \<phi>) \<Longrightarrow> is_conj T"
  using dnf
  by (induction \<phi> rule: is_dnf.induct) auto

lemma sizef_BigOr': "xs \<noteq> [] \<Longrightarrow> sizef (BigOr' xs) + 1 = sum_list (map sizef xs) + length xs"
  by (induction xs rule: BigOr'.induct) simp_all

lemma sizef_conv_sum_list_undnf: "sizef \<phi> = sum_list (map sizef (undnf \<phi>)) + count_Or \<phi>"
  by (induction \<phi>) simp_all

lemma sizef_BigOr'_undnf:
  fixes \<phi> :: "'a formula"
  shows "sizef (BigOr' (undnf \<phi>)) = sizef \<phi>"
proof -
  have "sizef \<phi> + 1 = sum_list (map sizef (undnf \<phi>)) + count_Or \<phi> + 1"
    using sizef_conv_sum_list_undnf[of \<phi>] by presburger

  also have "\<dots> = sum_list (map sizef (undnf \<phi>)) + length (undnf \<phi>)"
    using length_undnf[of \<phi>] by presburger

  also have "\<dots> = sizef (BigOr' (undnf \<phi>)) + 1"
    using sizef_BigOr'[of "undnf \<phi>", simplified] by presburger

  finally show ?thesis
    by presburger
qed

lemma sizef_BigOr'_filter_le: "sizef (BigOr' (filter P xs)) \<le> sizef (BigOr' xs)"
proof (induction xs rule: BigOr'.induct)
  case 1
  then show ?case
    by simp
next
  case (2 F)
  then show ?case
    by simp
next
  case (3 F v va)
  then show ?case
    apply simp
    by (smt (verit, del_insts) BigOr'.elims
        add.commute add_diff_cancel_right diff_is_0_eq
        less_add_Suc1 less_or_eq_imp_le
        list.distinct(1) list.sel(1,3) plus_1_eq_Suc
        sizef.simps(5))
qed

lemma ex_equiv_disj_list_if_is_dnf:
  fixes \<phi> :: "'a formula"
  assumes dnf: "is_dnf \<phi>"
  shows "\<exists>(Ts :: 'a formula list). equiv \<phi> (BigOr' Ts) \<and>
    sizef (BigOr' Ts) \<le> sizef \<phi> \<and>
    (\<forall>T \<in> set Ts. is_conj T) \<and>
    (\<forall>T \<in> set Ts. \<exists>\<alpha>. \<alpha> \<Turnstile> T)"
proof -
  define Ts :: "'a formula list" where
    "Ts = filter (\<lambda>T. \<exists>\<alpha>. \<alpha> \<Turnstile> T) (undnf \<phi>)"

  show ?thesis
  proof (intro exI[of _ Ts] conjI ballI)
    have "equiv \<phi> (BigOr' (undnf \<phi>))"
      using equiv_BigOr'_undnf_if_dnf[symmetric] .
    then show "equiv \<phi> (BigOr' Ts)"
      unfolding Ts_def
      by (smt (verit) BigOr'_semantics equiv_def mem_Collect_eq set_filter)
  next
    have "sizef (BigOr' (undnf \<phi>)) = sizef \<phi>"
      using sizef_BigOr'_undnf .
    then show "sizef (BigOr' Ts) \<le> sizef \<phi>"
      unfolding Ts_def
      using sizef_BigOr'_filter_le[of "\<lambda>T. \<exists>\<alpha>. \<alpha> \<Turnstile> T" "undnf \<phi>"]
      by presburger
  next
    show "\<And>T. T \<in> set Ts \<Longrightarrow> is_conj T"
      using ball_undnf_is_conj[OF dnf]
      by (simp add: Ts_def)
  next
    show "\<And>T. T \<in> set Ts \<Longrightarrow> \<exists>\<alpha>. \<alpha> \<Turnstile> T"
      by (simp add: Ts_def)
  qed
qed

lemma proposition4':
  fixes n :: nat
  shows "\<exists>(F\<^sub>n :: var formula).
    is_cnf F\<^sub>n \<and>
    sizef F\<^sub>n = 8 * n + 1 \<and>
    (\<forall>(G\<^sub>n :: var formula). equiv F\<^sub>n G\<^sub>n \<longrightarrow> is_dnf G\<^sub>n \<longrightarrow> sizef G\<^sub>n \<ge> n * 2 ^ n)"
proof (cases n)
  case 0
  then show ?thesis
    using Fn_in_cnf size_Fn by fastforce
next
  case (Suc n')

  then have "0 < n"
    by presburger

  show ?thesis
  proof (intro exI conjI allI impI)
    show "is_cnf (Fn n)"
      using Fn_in_cnf .
  next
    show "sizef (Fn n) = 8 * n + 1"
      using size_Fn .
  next
    fix G\<^sub>n :: "var formula"
    assume "equiv (Fn n) G\<^sub>n"
    assume "is_dnf G\<^sub>n"

    then obtain Ts :: "var formula list" where
      "\<forall>T \<in> set Ts. is_conj T" and
      "\<forall>T \<in> set Ts. \<exists>\<alpha>. \<alpha> \<Turnstile> T" and
      "equiv G\<^sub>n (BigOr' Ts)" and
      sizef: "sizef (BigOr' Ts) \<le> sizef G\<^sub>n"
      using ex_equiv_disj_list_if_is_dnf[of G\<^sub>n] by metis

    moreover have "equiv (Fn n) (BigOr' Ts)"
      using equiv_transitive[OF \<open>equiv (Fn n) G\<^sub>n\<close> \<open>equiv G\<^sub>n (BigOr' Ts)\<close>] .

    ultimately have "n * 2 ^ n \<le> sizef (BigOr' Ts)"
      using proposition4[OF \<open>0 < n\<close>, of Ts] by metis

    then show "n * 2 ^ n \<le> sizef G\<^sub>n"
      using sizef by presburger
  qed
qed


section \<open>Additional Functions for Corollary 5\<close>

text \<open>Should only be applied to a formula for which @{const is_nnf} holds.\<close>
fun dualize :: "'a formula \<Rightarrow> 'a formula" where
"dualize Bot = Not Bot" |
"dualize (Atom v) = Not (Atom v)" |
"dualize (Not v) = v" |
"dualize (And F G) = Or (dualize F) (dualize G)" |
"dualize (Or F G) = And (dualize F) (dualize G)" |
"dualize (Imp F G) = Bot"


section \<open>Required Lemmata for Corollary 5\<close>

lemma size_dualized_Fn: "sizef (dualize (Fn n)) = 8*n+1" 
  by(induction n; auto)

lemma dualized_Fn_in_dnf: "is_dnf (dualize (Fn n))"
  by(induction n; auto)

lemma disj_is_cnf: "is_disj F \<Longrightarrow> is_cnf F"
  by (induction F; auto)

lemma is_cnf_BigAnd':  "(\<forall> C \<in> set Cs. is_disj C \<and> \<not>(\<forall> Val. Val \<Turnstile> C)) \<Longrightarrow> is_cnf (BigAnd' Cs)"
  by (induction Cs rule: BigAnd'.induct) (simp_all add: disj_is_cnf)

lemma size_ident_dualize: "is_nnf F \<Longrightarrow> sizef F = sizef (dualize F)"
  by (induction F; simp)

lemma equiv_dualize: "is_nnf F \<Longrightarrow> equiv (dualize F) (Not F)"
proof (induction F)
  case (Atom x)
  then show ?case 
    by (simp add: equiv_def)
next
  case Bot
  then show ?case 
    by (simp add: equiv_def)
next
  case (Not F)
  then show ?case 
    by (simp add: equiv_def)
next
  case (And F1 F2)
  then show ?case 
    by (simp add: equiv_def)
next
  case (Or F1 F2)
  then show ?case 
    by (simp add: equiv_def)
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma Fn_in_nnf: "is_nnf (Fn n)" 
  by(induction n; auto)

lemma cnf_in_nnf: "is_cnf F \<Longrightarrow> is_nnf F"
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by simp
next
  case (And F1 F2)
  then show ?case 
    by simp
next
  case (Or F1 F2)
  then show ?case 
    using disj_is_nnf is_cnf.simps(5) by blast
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma dualized_cnf_in_dnf: "is_cnf F \<Longrightarrow> is_dnf (dualize F)"
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  have "is_lit_plus (Not F)" 
    using Not.prems by auto
  then have "is_dnf F" 
    by (metis conj_is_dnf Not.prems cnf_in_nnf is_conj.simps(2,3) is_lit_plus.simps(1,3) 
        is_nnf_NotD)
  then show ?case 
    by simp
next
  case (And F1 F2)
  then show ?case 
    by simp
next
  case (Or F1 F2)
  then have a: "is_lit_plus F1 \<and> is_disj F2" 
    by simp
  have 1: "is_lit_plus (dualize F1)" 
    using a 
    by (metis (full_types) is_lit_plus.elims(3)[of "dualize F1"]
        is_lit_plus.simps(10,2,4,5)
        is_lit_plus.simps(6,7,8,9) dualize.elims[of F1 "dualize F1"])
  have 2: "is_conj (dualize F2)" 
    using a
    by (smt (verit) Or.IH(2) formula.distinct(3) is_cnf.simps(5) is_conj.simps(2,3,4)
        is_disj.elims(2) is_disj.simps(4) is_dnf.simps(5) is_lit_plus.elims(2)
        is_lit_plus.simps(1,11,2,3,4,9) dualize.simps(1,2,3,5))
  show ?case 
    using 1 2 by simp
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma dualized_disj_not_taut_impl_sat: "is_disj F \<Longrightarrow> \<exists>Val. \<not> Val \<Turnstile> F \<Longrightarrow> \<exists>Val. Val \<Turnstile> dualize F"
proof (induction F)
  case (Atom x)
  then show ?case 
    by auto
next
  case Bot
  then show ?case 
    by auto
next
  case (Not F)
  then show ?case 
    by auto
next
  case (And F1 F2)
  then show ?case 
    by auto
next
  case (Or F1 F2)
  have F_is_nnf: "is_nnf (F1 \<^bold>\<or> F2)" 
    using Or.prems(1) disj_is_nnf by blast
  then have equiv: "equiv (Not (F1 \<^bold>\<or> F2))(dualize (F1 \<^bold>\<or> F2))" 
    using equiv_dualize equiv_def by blast
  obtain Val where Val_def: "\<not> Val \<Turnstile> F1 \<^bold>\<or> F2" 
    using Or.prems(2) by auto
  then have "Val \<Turnstile> Not (F1 \<^bold>\<or> F2)" 
    by auto
  then have "Val \<Turnstile> dualize (F1 \<^bold>\<or> F2)" 
    using equiv by (simp add: equiv_def)
  then show ?case 
    by auto
next
  case (Imp F1 F2)
  then show ?case 
    by auto
qed

lemma dualized_conj_of_disjs_is_disj_of_conjs: 
  "(\<forall> C \<in> set Cs. is_disj C \<and> (\<exists> Val. \<not>(Val \<Turnstile> C))) \<Longrightarrow> 
   \<exists> Ts. (dualize (BigAnd' Cs)) = BigOr' Ts \<and> (\<forall>T\<in>set Ts. is_conj T \<and> (\<exists> Val. Val \<Turnstile> T))"
proof (induction Cs)
  case Nil
  then show ?case
    by (metis BigAnd'.simps(1) BigOr'.simps(1) dualize.simps(3) empty_iff list.set(1))
next
  case (Cons C Cs)
  have is_disj_C: "is_disj C" 
    using Cons.prems by simp
  have is_no_taut_C: "\<exists>\<alpha>. \<not> \<alpha> \<Turnstile> C" 
    using Cons.prems by simp
  have "\<exists>Ts. dualize (BigAnd' Cs) = BigOr' Ts \<and> (\<forall>T\<in>set Ts. is_conj T \<and> (\<exists>Val. Val \<Turnstile> T))" 
    by (simp add: Cons.IH Cons.prems)
  then obtain TsCs where 
    def_TsCs: "dualize (BigAnd' Cs) = BigOr' TsCs \<and> (\<forall>T\<in>set TsCs. is_conj T \<and> (\<exists>Val. Val \<Turnstile> T))" 
    by auto
  define Ts where 
    "Ts = [dualize C] @ TsCs"
  then have 1: "BigOr' Ts = Or (dualize C) (dualize (BigAnd' Cs))" if "Cs \<noteq> []"
    by (metis BigAnd'.simps(2,3) BigOr'.simps(1,3) Cons.prems append_Cons append_Nil def_TsCs
        dualize.simps(4) dualized_disj_not_taut_impl_sat formula.distinct(15)
        formula_semantics.simps(2) list.exhaust list.set_intros(1,2) that)
  have a2: "is_conj (dualize C)"
    using is_disj_C
    by (metis disj_is_cnf is_conj.simps(1) is_disj.simps(1) is_dnf.simps(5) 
        is_lit_plus.simps(2) dualize.simps(5) dualized_cnf_in_dnf)
  have b2: "\<forall>T\<in>set TsCs. is_conj T" 
    using def_TsCs by auto
  have 2: "(\<forall>T\<in>set Ts. is_conj T)" 
    using Ts_def a2 b2 by auto
  have a3: "\<exists>\<alpha>. \<alpha> \<Turnstile> dualize C" 
    using is_disj_C is_no_taut_C dualized_disj_not_taut_impl_sat by auto
  have b3: "\<forall>T\<in>set TsCs. (\<exists>Val. Val \<Turnstile> T)" 
    using def_TsCs by auto
  have 3: "\<forall>T\<in>set Ts. (\<exists>Val. Val \<Turnstile> T)" 
    using Ts_def a3 b3 by auto
  have 4: "\<exists>Ts. Or (dualize C) (dualize (BigAnd' Cs)) = BigOr' Ts \<and>
    (\<forall>T\<in>set Ts. is_conj T \<and> (\<exists>Val. Val \<Turnstile> T))" if "Cs \<noteq> []"
    using 1[OF that] 2 3 by metis
  show ?case
  proof (intro exI[of _ Ts] conjI ballI)
    show "dualize (BigAnd' (C # Cs)) = BigOr' Ts"
    proof (cases "Cs = []")
      case True
      then show ?thesis
        by (metis BigAnd'.simps(2) BigOr'.simps(2) def_TsCs Ts_def dualize.simps(3)
            list.set_intros(1) formula_semantics.simps(2) BigOr'.simps(3) append.right_neutral
            neq_Nil_conv BigAnd'.simps(1) formula.distinct(15))
    next
      case False
      then show ?thesis
        by (metis "1" BigAnd'.simps(3) dualize.simps(4) neq_Nil_conv)
    qed
  next
    show "\<And>T. T \<in> set Ts \<Longrightarrow> is_conj T"
      by (metis 2)
  next
    show "\<And>T. T \<in> set Ts \<Longrightarrow> \<exists>Val. Val \<Turnstile> T"
      by (metis 3)
  qed
qed


section \<open>Corollary 5\<close>

corollary corollary5:
  fixes n :: nat and Cs :: "var formula list"
  defines "Fprime \<equiv> dualize (Fn n)" and "G \<equiv> BigAnd' Cs"
  assumes
    n_greater_0: "n > 0" and
    G_spec: "(\<forall> C \<in> set Cs. is_disj C \<and> \<not>(\<forall> Val. Val \<Turnstile> C))" and
    equiv_Fprime_G: "equiv Fprime G"
  shows "sizef G \<ge> n*2^n"
proof -
  note def_Fprime = Fprime_def
  note def_G = G_def G_spec
  have size_Fprime: "sizef Fprime = 8*n+1" 
    using def_Fprime by (simp add: size_dualized_Fn)
  have Fprime_in_dnf: "is_dnf Fprime" 
    by (simp add: def_Fprime dualized_Fn_in_dnf)
  have G_in_cnf: "is_cnf G" 
    using def_G is_cnf_BigAnd' by auto
  have G_in_nnf: "is_nnf G" 
    using G_in_cnf cnf_in_nnf by auto
  show ?thesis
  proof (rule ccontr)
    assume "\<not> n*2^n \<le> sizef G"
    then have "sizef G < n*2^n" 
      by simp
    then have dualized_G_exp_size: "sizef (dualize G) < n*2^n" 
      using G_in_nnf by (simp add: size_ident_dualize)
    have "equiv (dualize G) (Fn n)"
    proof -
      have "equiv G Fprime" 
        using equiv_Fprime_G equiv_def by blast
      then have "equiv G (dualize (Fn n))" 
        by (simp add: def_Fprime)
      then have "equiv G (Not (Fn n))" 
        using Fn_in_nnf equiv_dualize equiv_def by meson
      then have "equiv (Not G) (Fn n)" 
        by (simp add: equiv_def)
      then show ?thesis 
        using G_in_nnf equiv_dualize equiv_def by meson
    qed
    then have equiv_Fn_dualized_G: "equiv (Fn n) (dualize G)" 
      by (simp add: equiv_def)
    have dualized_G_disj_of_conj: "\<exists> Ts. (dualize G) = BigOr' Ts \<and> (\<forall>T\<in>set Ts. is_conj T \<and> 
                                                                              (\<exists> Val. Val \<Turnstile> T))" 
      using def_G dualized_conj_of_disjs_is_disj_of_conjs by auto
    show False 
      using proposition4 
      using dualized_G_exp_size equiv_Fn_dualized_G dualized_G_disj_of_conj 
      by (metis le_antisym n_greater_0 nat_less_le)
  qed
qed

fun uncnf :: "'a formula \<Rightarrow> 'a formula list" where
"uncnf (And F G) = uncnf F @ uncnf G" |
"uncnf H = [H]"

lemma uncnf_neq_Nil[simp]: "uncnf \<phi> \<noteq> []"
  by (induction \<phi>) simp_all

fun count_And :: "'a formula \<Rightarrow> nat" where
"count_And (And F G) = count_And F + count_And G + 1" |
"count_And _ = 0"

lemma sizef_BigAnd': "xs \<noteq> [] \<Longrightarrow> sizef (BigAnd' xs) + 1 = sum_list (map sizef xs) + length xs"
  by (induction xs rule: BigAnd'.induct) simp_all

lemma length_uncnf: "length (uncnf \<phi>) = count_And \<phi> + 1"
  by (induction \<phi>) simp_all

lemma sizef_conv_sum_list_uncnf: "sizef \<phi> = sum_list (map sizef (uncnf \<phi>)) + count_And \<phi>"
  by (induction \<phi>) simp_all

lemma sizef_BigAnd'_uncnf:
  fixes \<phi> :: "'a formula"
  shows "sizef (BigAnd' (uncnf \<phi>)) = sizef \<phi>"
proof -
  have "sizef \<phi> + 1 = sum_list (map sizef (uncnf \<phi>)) + count_And \<phi> + 1"
    using sizef_conv_sum_list_uncnf[of \<phi>] by presburger

  also have "\<dots> = sum_list (map sizef (uncnf \<phi>)) + length (uncnf \<phi>)"
    using length_uncnf[of \<phi>] by presburger

  also have "\<dots> = sizef (BigAnd' (uncnf \<phi>)) + 1"
    using sizef_BigAnd'[of "uncnf \<phi>", simplified] by presburger

  finally show ?thesis
    by presburger
qed

lemma ball_uncnf_is_disj:
  fixes \<phi> :: "'a formula"
  assumes cnf: "is_cnf \<phi>"
  shows "\<And>C. C \<in> set (uncnf \<phi>) \<Longrightarrow> is_disj C"
  using cnf
  by (induction \<phi> rule: is_cnf.induct) auto

lemma sizef_BigAnd'_filter_le: "sizef (BigAnd' (filter P xs)) \<le> sizef (BigAnd' xs)"
proof (induction xs rule: BigAnd'.induct)
  case 1
  then show ?case
    by simp
next
  case (2 F)
  then show ?case
    by simp
next
  case (3 F v va)
  then show ?case
    by (metis BigAnd'.simps(1) BigOr'.simps(1) add_diff_cancel_right diff_is_0_eq sizef.simps(3)
        sizef_BigAnd' sizef_BigOr' sizef_BigOr'_filter_le)
qed

lemma equiv_BigAnd'_append: "equiv (BigAnd' (xs @ ys)) (And (BigAnd' xs) (BigAnd' ys))"
  by (induction xs) (simp_all add: equiv_def)

lemma equiv_BigAnd'_uncnf_if_cnf:
  fixes \<phi> :: "'a formula"
  shows "equiv (BigAnd' (uncnf \<phi>)) \<phi>"
proof (induction \<phi> rule: uncnf.induct)
  case (1 F G)
  then show ?case
    by (smt (verit) equiv_def equiv_BigAnd'_append formula_semantics.simps(4) uncnf.simps(1))
qed (simp_all add: equiv_def)

lemma ex_equiv_conj_list_if_is_cnf:
  fixes \<phi> :: "'a formula"
  assumes cnf: "is_cnf \<phi>"
  shows "\<exists>(Cs :: 'a formula list). equiv \<phi> (BigAnd' Cs) \<and>
    sizef (BigAnd' Cs) \<le> sizef \<phi> \<and>
    (\<forall>C \<in> set Cs. is_disj C) \<and>
    (\<forall>C \<in> set Cs. \<not> \<Turnstile> C)"
proof -
  define Cs :: "'a formula list" where
    "Cs = filter (\<lambda>C. \<not> \<Turnstile> C) (uncnf \<phi>)"

  show ?thesis
  proof (intro exI[of _ Cs] conjI ballI)
    have "equiv \<phi> (BigAnd' (uncnf \<phi>))"
      using equiv_BigAnd'_uncnf_if_cnf[symmetric] .
    then show "equiv \<phi> (BigAnd' Cs)"
      unfolding Cs_def
      by (smt (verit, del_insts) BigAnd'_semantics equiv_def mem_Collect_eq set_filter)
  next
    have "sizef (BigAnd' (uncnf \<phi>)) = sizef \<phi>"
      using sizef_BigAnd'_uncnf .
    then show "sizef (BigAnd' Cs) \<le> sizef \<phi>"
      unfolding Cs_def
      using sizef_BigAnd'_filter_le[of "\<lambda>C. \<not> \<Turnstile> C" "uncnf \<phi>"]
      by presburger
  next
    show "\<And>C. C \<in> set Cs \<Longrightarrow> is_disj C"
      using ball_uncnf_is_disj[OF cnf]
      by (simp add: Cs_def)
  next
    show "\<And>C. C \<in> set Cs \<Longrightarrow> \<not> \<Turnstile> C"
      by (simp add: Cs_def)
  qed
qed

lemma corollary5':
  fixes n :: nat
  shows "\<exists>(F\<^sub>n :: var formula).
    is_dnf F\<^sub>n \<and>
    sizef F\<^sub>n = 8 * n + 1 \<and>
    (\<forall>(G\<^sub>n :: var formula). equiv F\<^sub>n G\<^sub>n \<longrightarrow> is_cnf G\<^sub>n \<longrightarrow> sizef G\<^sub>n \<ge> n * 2 ^ n)"
proof (cases n)
  case 0
  then show ?thesis
    using dualized_Fn_in_dnf size_dualized_Fn
    by fastforce
next
  case (Suc n')

  then have "n > 0"
    by presburger

  show ?thesis
  proof (intro exI conjI allI impI)
    show "is_dnf (dualize (Fn n))"
      using dualized_Fn_in_dnf .
  next
    show "sizef (dualize (Fn n)) = 8 * n + 1"
      using size_dualized_Fn .
  next
    fix G\<^sub>n :: "var formula"
    assume "equiv (dualize (Fn n)) G\<^sub>n"
    assume "is_cnf G\<^sub>n"

    then obtain Cs :: "var formula list" where
      "\<forall>C \<in> set Cs. is_disj C" and
      "\<forall>C \<in> set Cs. \<not> \<Turnstile> C" and
      "equiv G\<^sub>n (BigAnd' Cs)" and
      sizef: "sizef (BigAnd' Cs) \<le> sizef G\<^sub>n"
      using ex_equiv_conj_list_if_is_cnf[of G\<^sub>n] by metis

    moreover have "equiv (dualize (Fn n)) (BigAnd' Cs)"
      using equiv_transitive[OF \<open>equiv (dualize (Fn n)) G\<^sub>n\<close> \<open>equiv G\<^sub>n (BigAnd' Cs)\<close>] .

    ultimately have "n * 2 ^ n \<le> sizef (BigAnd' Cs)"
      using corollary5[OF \<open>0 < n\<close>, of Cs] by metis

    then show "n * 2 ^ n \<le> sizef G\<^sub>n"
      using sizef by presburger
  qed
qed


section \<open>Unused Functions & Lemmata\<close>

subsection \<open>From Proposition 4\<close>

fun variables :: "'a formula \<Rightarrow> 'a set " where
"variables Bot = {}" |
"variables (Atom v) = {v}" |
"variables (Not F) = variables F" |
"variables (And F G) = variables F \<union> variables G" |
"variables (Or F G) = variables F \<union> variables G" |
"variables (F \<^bold>\<rightarrow> G) = variables F \<union> variables G"

lemma Fn_sat: "\<exists> Val. Val \<Turnstile> Fn n"
proof -
  define Val where "Val = (\<lambda>x. case x of (Var i b) \<Rightarrow> b)"
  then have "Val \<Turnstile> Fn n" 
    by (induction n; simp)
  then show ?thesis 
    by auto
qed

lemma impl_not_cont: "\<not> cont F v \<Longrightarrow> \<not> cont_pos F v \<and> \<not> cont_neg F v"
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by (smt (verit) cont.elims(1) cont_neg.simps(3,4,5,6,7,8) cont_pos.elims(1) 
        formula.distinct(11,19,21,23,3))
next
  case (And F1 F2)
  then show ?case 
    by simp
next
  case (Or F1 F2)
  then show ?case 
    by simp
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

subsection \<open>From Corollary 5\<close>

lemma dualized_conj_is_disj: "is_conj F \<Longrightarrow> is_disj (dualize F)"
proof (induction F)
  case (Atom x)
  then show ?case 
    by simp
next
  case Bot
  then show ?case 
    by simp
next
  case (Not F)
  then show ?case 
    by (metis is_conj.simps(4) is_disj.simps(2,3) is_lit_plus.simps(1,3)
        is_nnf.simps(6) is_nnf_NotD dualize.simps(3))
next
  case (And F1 F2)
  then show ?case
    by (metis is_cnf.simps(5) is_conj.simps(1) is_disj.simps(1) is_dnf.simps(5)
        dualize.simps(4,5) dualized_cnf_in_dnf)
next
  case (Or F1 F2)
  then show ?case 
    by simp
next
  case (Imp F1 F2)
  then show ?case 
    by simp
qed

lemma dualized_dnf_in_cnf: "is_dnf F \<Longrightarrow> is_cnf (dualize F)"
proof (induction F)
  case (Atom x)
  then show ?case 
    by auto
next
  case Bot
  then show ?case 
    by auto
next
  case (Not F)
  then show ?case 
    by (metis is_cnf.simps(2,3) is_conj.simps(4) is_disj.simps(2,3) is_dnf.simps(4)
        is_lit_plus.simps(1,3) is_nnf.simps(6) is_nnf_NotD dualize.simps(3))
next
  case (And F1 F2)
  have "is_conj (And F1 F2)" 
    using \<open>is_dnf (F1 \<^bold>\<and> F2)\<close> by simp
  then have "is_lit_plus F1" and "is_conj F2" 
    by auto
  have 1: "is_lit_plus (dualize F1)" 
    using \<open>is_lit_plus F1\<close> 
    by (metis is_lit_plus.elims(2) is_lit_plus.simps(1,2,3,4) dualize.simps(1,2,3))
  have 2: "is_disj (dualize F2)" 
    using \<open>is_conj F2\<close> by (simp add: dualized_conj_is_disj)
  have "is_lit_plus (dualize F1) \<and> is_disj (dualize F2)" 
    using 1 2 by simp
  then show ?case 
    by simp
next
  case (Or F1 F2)
  then show ?case 
    by auto
next
  case (Imp F1 F2)
  then show ?case 
    by auto
qed

text \<open>The definition of the lemma with F = BigOr Ts cannot be true because of the recursive 
definition of BigOr where base case is Bot. So e.g. if F = "Atom x" BigOr Ts would always include 
Bot and as a result not be equal to F but only equivalent.\<close>
lemma dnf_equiv_disj_of_conj: "is_dnf F \<Longrightarrow> \<exists> Ts. equiv F (BigOr Ts) \<and> (\<forall>T\<in>set Ts. is_conj T)"
proof (induction F)
  case (Atom x)
  have "is_conj (Atom x)" 
    using \<open>is_dnf (Atom x)\<close> by simp
  define Ts where def_Ts: "Ts = [Atom x]"
  have "equiv (Atom x) (BigOr Ts)" 
    using def_Ts equiv_def by force
  then show ?case 
    by (metis \<open>is_conj (Atom x)\<close> def_Ts ord.lexordp_eq_pref ord.lexordp_eq_simps(2) 
        set_ConsD split_list_cycles)
next
  case Bot
  then show ?case 
    by (metis BigOr.simps(1) empty_iff equiv_def set_empty2)
next
  case (Not F)
  have "is_conj (Not F)" 
    using \<open>is_dnf (Not F)\<close> by simp
  then have "is_lit_plus (Not F)" 
    by simp
  then have "F = Bot \<or> (\<exists> a. F = Atom a)" 
    using is_nnf_NotD by auto
  then show ?case
  proof
    assume asm1: "F = Bot"
    define Ts where def_Ts: "Ts = [Not Bot :: 'a formula]" 
      \<comment> \<open>Ts can here not be defined as Top here because is_lit_plus Top is false.\<close>
    then have "equiv (Not F) (BigOr Ts)" 
      using asm1 equiv_def by force
    then show ?case 
      using \<open>is_conj (Not F)\<close> by (metis asm1 def_Ts in_set_member member_rec(2) set_ConsD)
  next
    assume asm2: "\<exists> a. F = Atom a"
    then obtain a where def_a: "F = Atom a" 
      by auto
    define Ts where def_Ts: "Ts = [Not (Atom a)]"
    then have "equiv (Not (Atom a)) (BigOr Ts)" 
      by (simp add: equiv_def)
    then show ?case 
      by (metis List.insert_def \<open>is_conj (\<^bold>\<not> F)\<close> def_Ts def_a insert_Nil not_Cons_self2 set_ConsD)
  qed
next
  case (And F1 F2)
  have "is_conj (And F1 F2)" 
    using \<open>is_dnf (And F1 F2)\<close> by simp
  define Ts where def_Ts: "Ts = [And F1 F2]"
  then have "equiv (And F1 F2) (BigOr Ts)" 
    by (simp add: equiv_def)
  then show ?case 
    by (metis \<open>is_conj (F1 \<^bold>\<and> F2)\<close> def_Ts in_set_insert insert_Nil list.distinct(1) set_ConsD)
next
  case (Or F1 F2)
  have "is_dnf F1" and "is_dnf F2" 
    using \<open>is_dnf (Or F1 F2)\<close> by auto
  have "\<exists> Ts. equiv F1 (BigOr Ts) \<and> (\<forall> a \<in> set Ts. is_conj a)" 
    using \<open>is_dnf F1\<close> Or.IH(1) by blast
  then obtain TsF1 where TsF1_def: "equiv F1 (BigOr TsF1) \<and> (\<forall> a \<in> set TsF1. is_conj a)" 
    by auto
  have "\<exists> Ts. equiv F2 (BigOr Ts) \<and> (\<forall> a \<in> set Ts. is_conj a)" 
    using Or.IH(2) using \<open>is_dnf F2\<close> by blast
  then obtain TsF2 where TsF2_def: "equiv F2 (BigOr TsF2) \<and> (\<forall> a \<in> set TsF2. is_conj a)" 
    by auto
  define Ts where def_Ts: "Ts = TsF1 @ TsF2"
  have 1: "equiv (Or F1 F2) (BigOr Ts)" 
    using def_Ts TsF1_def TsF2_def unfolding equiv_def by auto
  have 2: "(\<forall> a \<in> set Ts. is_conj a)" 
    using def_Ts TsF1_def TsF2_def by auto
  show ?case 
    using 1 2 by auto
next
  case (Imp F1 F2)
  then show ?case 
    by auto
qed

end