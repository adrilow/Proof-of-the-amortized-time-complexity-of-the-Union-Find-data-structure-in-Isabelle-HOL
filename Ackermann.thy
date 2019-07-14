theory Ackermann imports Main "~~/src/HOL/ex/Primrec"  "~~/src/HOL/Library/Discrete" InverseNatNat begin

\<comment> \<open>This theory, including the structure of many proofs and the comments 
   follow closely the Coq library accompanying the paper by Charguéraud and Pottier:
   \<^url>\<open>http://gallium.inria.fr/~fpottier/dev/uf/\<close>\<close>


(*Tarjan's definition, formulated in terms of compower*)
definition Ackermann where 
  "Ackermann k \<equiv> ((\<lambda>f x. (f ^^ Suc x) x) ^^ k) Suc"

definition abase where "abase x \<equiv> Suc x"

definition astep where "astep (f::nat=>nat) x \<equiv> compow (Suc x) f x"

definition Ackermann' where "Ackermann' k \<equiv> compow k astep abase"

lemma Ackermann_alt_eq: "Ackermann = Ackermann'"
  unfolding Ackermann_def Ackermann'_def abase_def astep_def by simp

(*WTF is dis*)
lemma "compow 1 (0::nat) = 0"
  apply simp
  oops

lemma Ackermann01: "Ackermann 0 1 = 2"
  unfolding Ackermann_def
  by auto


(********************************************)
subsection{*Tarjan's characteristic equations*}
(********************************************)


lemma Ackermann_base_eq: "Ackermann 0 x = Suc x"
  unfolding Ackermann_def by simp

lemma Ackermann_step_eq: "Ackermann (Suc k) x = compow (Suc x) (Ackermann k) x"
  unfolding Ackermann_def by simp


(********************************************)
subsection{*Closed forms for @{term "Ackermann 1"} and @{term "Ackermann 2"}, from Cormen et al.*}
(********************************************)


lemma Ackermann_1_eq: "Ackermann (Suc 0) x = Suc (2 * x)"
proof -
  {
    fix x y
    have "compow x (Ackermann 0) y = x + y"
      unfolding Ackermann_def
      by (induction x) auto
  } note fact = this
  show ?thesis unfolding Ackermann_def by (simp add: Ackermann_step_eq fact)
qed

lemma Ackermann_1_eq': "Ackermann 1 x = Suc (2 * x)"
  by (simp add: Ackermann_1_eq)


lemma compow_Ackermann_1_eq_lemma: assumes "i>0" "x>0" 
  shows "Suc (2 * (2 ^ i * Suc x - 1)) = 2 ^ Suc i * Suc x - 1"
proof -
  {
    have sg1: "2 ^ Suc i * Suc x > 1"
      using assms
      by (metis One_nat_def Suc_mono less_1_mult one_less_numeral_iff power_gt1 less_num_simps(2))
  } note sg1 = this
  show ?thesis
  apply (subst Suc_eq_plus1)
  apply (subst diff_mult_distrib2) 
  apply (subst mult_1_right)
  apply (subst semigroup_mult_class.mult.assoc[symmetric])
  apply (subst power_class.power.power_Suc[symmetric])
  apply (subst Suc_eq_plus1[symmetric])
  using sg1
  by auto
qed

lemma compow_Ackermann_1_eq: "compow i (Ackermann 1) x = 2^i * (Suc x) -1"
proof (induction i arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc i)
  have sg1: "compow (Suc i) (Ackermann 1) x = Ackermann 1 ((compow i (Ackermann 1) ) x)"
    by simp
   show ?case 
     apply (subst sg1)
     apply (subst Suc)
     apply (subst Ackermann_1_eq')
     apply (cases "i>0")
     subgoal
       apply (cases "x>0")
       subgoal  using compow_Ackermann_1_eq_lemma[of i x] .
       subgoal 
         by (metis One_nat_def Suc_1 Suc_diff_Suc lessI mult.right_neutral
             not_gr_zero power_Suc power_gt1 right_diff_distrib')
       done
     apply (cases "x>0")
     by auto
qed

lemma Ackermann_2_eq: "Ackermann 2 x = 2^(Suc x) * (Suc x) - 1"
  apply (subst numeral_2_eq_2; subst One_nat_def[symmetric])
  apply (subst Ackermann_step_eq)
  apply (subst compow_Ackermann_1_eq) ..
  
(********************************************)
subsection {*Every @{term "Ackermann k"} is inflationary. 
             That is, @{term "x \<le> Ackermann k x"} holds.*}
(********************************************)

abbreviation inflationary where "inflationary f \<equiv> \<forall>x. x \<le> f x"

lemma inflationary_concrete: "inflationary f \<Longrightarrow> x \<le> f x"
  by simp

lemma inflationary_abase: "inflationary abase"
  unfolding abase_def by fastforce


lemma mono_id: "mono id" unfolding mono_def by auto

(*This is of course true for any sufficiently nice ordering (not necessarily nat), no idea how it's called*)
lemma inflationary_compow': assumes "inflationary f" shows "(x::nat) \<le> (f^^i) x"
proof (induction i)
  case 0
  then show ?case by auto 
next
  case (Suc i)
  hence "x \<le>  (f ^^ i) x" .
  also have "\<dots>\<le> f ((f ^^ i) x) " using assms by auto
  finally show ?case apply (subst Nat.funpow.simps(2)) by simp
qed

lemma inflationary_compow: assumes "inflationary (f::nat\<Rightarrow>nat)" shows "inflationary (f^^i)"
  using inflationary_compow'[OF assms] by force

lemma preserves_inflationary_astep: assumes "inflationary f" shows "inflationary (astep f)"
  unfolding astep_def using inflationary_compow[OF assms] by blast


lemma compow_infaltionary_astep: "inflationary ((astep ^^ k) abase)"
proof (induction k)
  case 0
  then show ?case using inflationary_abase by auto
next
  case (Suc k)
  show ?case using preserves_inflationary_astep[OF Suc] by simp
qed


(*In the Coq proof this induction is abstracted through iter_invariant*)
lemma Ackermann'_k_inflationary: "inflationary (Ackermann' k)"
proof (induction k)
  case 0
  then show ?case 
    unfolding Ackermann'_def
    by (auto simp add: inflationary_abase)
next
  case (Suc k)
   show ?case
    unfolding Ackermann'_def
    apply (subst Nat.funpow.simps(2)) 
    using preserves_inflationary_astep[OF Suc] unfolding Ackermann'_def by simp
qed

lemma Ackermann_k_inflationary: "inflationary (Ackermann k)"
  using Ackermann'_k_inflationary Ackermann_alt_eq by simp
  
lemma compow_Ackermann_k_inflationary: "inflationary ((Ackermann k)^^n)"
  using inflationary_compow[OF Ackermann_k_inflationary, of n k] .

lemma compow_Ackermann_k_inflationary': "x\<le> ((Ackermann k)^^n) x"
  using compow_Ackermann_k_inflationary by simp
  
  
(********************************************)
subsection {*@{term astep} is @{term inflationary}.*}
(********************************************)

lemma inflationary_astep: assumes "inflationary f" shows "f x \<le> astep f x"
proof -
  have 1:"(f::nat\<Rightarrow>nat) ^^ 1 = f" by simp
  show ?thesis
  unfolding astep_def
  apply (subst Suc_eq_plus1)
  apply (subst funpow_add[of x 1 f])
  apply (subst 1)
  using assms inflationary_compow[OF assms]
  by simp
qed


(********************************************)
subsection {*@{term Ackermann} is monotonic in its first argument. 
            The results, which are functions, are compared pointwise*}
(********************************************)


lemma mono_pow_nat: "mono (f::nat\<Rightarrow>nat) \<Longrightarrow> mono (f ^^ n)"
  by (induct n) (auto simp: mono_def)

lemma strict_mono_pow_nat: "strict_mono (f::nat\<Rightarrow>nat) \<Longrightarrow> strict_mono (f ^^ n)"
  by (induct n) (simp add: strict_mono_def)+

lemma mono_abase: "mono abase"
  unfolding abase_def mono_def by auto

lemma astep_preserves_mono: assumes "mono f" "inflationary f" shows "mono (astep f)"
proof -
  {
    fix x y
    assume xy: "(x::nat)\<le>y"
    have "astep f x \<le>  (f ^^ Suc y) y" unfolding astep_def
      using funpow_mono2[OF assms(1), of "Suc x" "Suc y" x y, OF _ xy] assms(2) xy by blast
    hence "astep f x \<le> astep f y" unfolding astep_def by simp
  }
  thus ?thesis unfolding mono_def by fast
qed

lemma mono_Ackermann': "mono (Ackermann' k)"
proof (induction k)
 case 0
  show ?case unfolding Ackermann'_def apply (subst funpow_simps_right(1))+ 
    using mono_abase  unfolding id_def mono_def by blast
next
  case (Suc k)
   show ?case 
     unfolding Ackermann'_def
     apply (subst Nat.funpow.simps(2))+
     using astep_preserves_mono[OF Suc Ackermann'_k_inflationary] unfolding Ackermann'_def by simp
qed

lemma mono_Ackermann: "mono (Ackermann k)"
  apply (subst Ackermann_alt_eq) using mono_Ackermann' .

lemma mono_Ackermann'_in_k: "mono (\<lambda>k. Ackermann' k x)"
proof -
  {
    fix k 
    have "Ackermann' k x \<le> Ackermann' (Suc k) x"
      unfolding Ackermann'_def 
      using inflationary_astep[OF compow_infaltionary_astep[of k], of x]
      by fastforce
  }
  thus ?thesis using mono_iff_le_Suc by blast
qed

lemma mono_Ackermann_in_k: "mono (\<lambda>k. Ackermann k x)"
  apply (subst Ackermann_alt_eq) using mono_Ackermann'_in_k .


(********************************************)
subsection {*Power can be expressed with @{term compow}*}
(********************************************)

lemma funpow_Suc_right_apply: "(f ^^ Suc n) x = (f ^^ n) (f x)" 
  by (metis comp_apply funpow_Suc_right)


lemma pow_compow: " x ^ y = compow y (\<lambda>a. x * a ) 1" \<comment>\<open>(( * ) x ^^ y) 1\<close>
  by (induction y) auto

\<comment>\<open> Lower bound for @{term "Ackermann 2"}: @{term "2^x \<le> Ackermann 2 x"} \<close>

lemma Ackermann_2_lower_bound': assumes "x>0" shows "2 ^ x < Ackermann 2 x"
proof -
  {
    fix x::nat
    assume "x>0"
    hence "(2::nat) ^ x < 2 * 2 ^ x" by fastforce
  } note last1 = this
  {
    fix a::nat fix b::nat fix c::nat
    assume "a<b" "c>0"
    hence "a<b+c-1" by simp
  } note last2 = this
  {
    fix x::nat
    assume 1: "x>0"
    have " 2 ^ x * (2 * x) > 0" using 1 by auto
  } note last3 = this
  show ?thesis
  apply (subst pow_compow)
  apply (subst (2) Suc_1[symmetric])
  apply (subst Ackermann_step_eq)
  apply (subst  funpow_Suc_right_apply)
  apply (subst (3) One_nat_def)
  apply (subst Ackermann_1_eq)
  apply (subst compow_Ackermann_1_eq)
  apply (simp add: pow_compow)
  apply (subst  One_nat_def[symmetric])+
  apply (subst pow_compow[symmetric])+ 
    using last2[OF  last1[OF \<open>0<x\<close>] ,of  "2 ^ x * (2 * x)", OF  last3[OF \<open>0<x\<close>]] .
qed


lemma Ackermann_2_lower_bound: "2 ^ x \<le> Ackermann 2 x"
  apply (cases "0<x")
  subgoal using Ackermann_2_lower_bound'[of x] by auto
  subgoal by (auto simp: Ackermann_2_eq)
  done
 

(********************************************)
subsection {*A slightly more powerful version of the previous lemma. It is not a
   direct consequence of the previous lemma, because @{term "2 ^ (Discrete.log n)"} is
   in general less than or equal to n*}
(********************************************)


lemma Ackermann_2_log_lower_bound: "n \<le> Ackermann 2 (Discrete.log n)"
proof -
  {
    fix m::nat
    assume mins:"m\<ge>2"
    have "Discrete.log 2 = 1" by (simp add: Discrete.log.simps)
    with mins have "(Discrete.log m + 1) \<ge> 2" using log_mono unfolding mono_def by fastforce
    hence sg1: "2 * 2 ^ Discrete.log m * (Discrete.log m + 1) - 1  \<ge> 2 * 2 ^ Discrete.log m * 2 - 1 "
      by (simp add: diff_le_mono)
    also have "\<dots> \<ge>  2 * 2 ^ Discrete.log m" using calculation by linarith
    also have "\<dots> \<ge> m" using log_exp2_ge[of m]
      using sg1 le_trans by linarith
  } note case1 = this
  {
    fix m::nat
    assume maxs:"m<2"
    have "m \<le> 2 * 2 ^ Discrete.log m * (Discrete.log m + 1) - 1" 
      apply (cases m)
      using maxs by (simp add: Discrete.log.simps)+
  } note case2 = this
  show ?thesis
    apply (subst Ackermann_2_eq)
    apply (subst power_Suc)
    apply (subst mult.commute)
    apply (subst Suc_eq_plus1)
    apply (subst mult.commute)
    apply (cases "n\<ge>2")
    subgoal using case1[of n] .
    subgoal using case2[of n] by simp
    done
qed

(********************************************)
subsection {*2 ^ (2 ^ ( ... 2)) { x + 1 times } \<le> Ackermann 3 x*}
(********************************************)


lemma compow_mono_in_f_2': assumes "mono (f::nat\<Rightarrow>nat)" "mono (g::nat\<Rightarrow>nat)" "\<forall> x y. x\<le> y \<longrightarrow> f x \<le> g y" "x\<le>y"
  shows "(f ^^ i) x \<le> (g ^^ i) y"
  using assms
proof (induction i arbitrary: x y)
  case 0
  then show ?case by simp
next
  case (Suc i)
  show ?case apply (subst funpow_Suc_right_apply)+ 
    using Suc(1)[OF Suc(2) Suc(3) Suc(4), of "f x" "g y"] Suc(5) Suc(4) by blast
qed

lemma compow_mono_in_f_2: assumes "mono (f::nat\<Rightarrow>nat)" "mono (g::nat\<Rightarrow>nat)" "\<forall> x. f x \<le> g x" "x\<le>y"
  shows "(f ^^ i) x \<le> (g ^^ i) y"
proof -
  have "\<forall> x y. x\<le> y \<longrightarrow> f x \<le> g y" using assms(3)
    using assms(2) le_trans mono_def by blast
  thus ?thesis using compow_mono_in_f_2'[OF assms(1-2) _ assms(4)]
    by presburger
qed

\<comment>\<open>This is a version of @{term funpow_mono2} for comparing two functions on the same i\<close>
lemma compow_mono_in_f: assumes "mono (f::nat\<Rightarrow>nat)" "mono (g::nat\<Rightarrow>nat)" "\<forall>x. f x \<le> g x"
  shows "(f ^^ i) x \<le> (g ^^ i) x"
  using compow_mono_in_f_2 assms by blast

\<comment>\<open>This is a version of @{term funpow_mono2} for comparing two functions instead of only
  the number of iterations\<close>
lemma compow_mono_in_f_and_i': assumes "mono (f::nat\<Rightarrow>nat)" "mono (g::nat\<Rightarrow>nat)" "inflationary g"
  "\<forall> x y. x\<le> y \<longrightarrow> f x \<le> g y" "x\<le>y" "i\<le>j"
  shows "(f ^^ i) x \<le> (g ^^ j) y"
  using assms
proof goal_cases
  case 1
  have "(f ^^ i) x \<le> (g ^^ i) y" using assms compow_mono_in_f_2' by auto
  also have "(g ^^ i) y \<le> (g ^^ j) y"  using assms funpow_mono2 by blast
  finally show ?case .
qed
thm funpow_mono2 compow_mono_in_f

lemma Ackermann_3_lower_bound:  "compow (Suc x) ((^) 2) 0 \<le> Ackermann 3 x"
proof -
  have def_3:"3 = Suc 2" by simp
  have monopow: "mono ((^) (2::nat))" unfolding mono_def by simp
  have sg1: "\<forall>x. 2 ^ x \<le> Ackermann 2 x" using Ackermann_2_lower_bound by blast
  have sg2: "\<forall> x y. x\<le> y \<longrightarrow> Ackermann 2 x \<le> Ackermann 2 y" 
    using mono_Ackermann[of 2] unfolding mono_def .
  have sg3: "\<forall> x y. x\<le> y \<longrightarrow>  2 ^ x \<le> Ackermann 2 y" using sg1 sg2 order_trans by blast
  show ?thesis
    apply (subst def_3)
    apply (subst Ackermann_step_eq)
    using Ackermann_2_lower_bound 
      compow_mono_in_f_and_i'[OF monopow mono_Ackermann[of 2] Ackermann_k_inflationary[of 2],
                              of 0 x "Suc x" "Suc x", OF sg3] by blast
qed

(********************************************)
subsection {*Every @{term "Ackermann k"} tends to infinity*}
(********************************************)

lemma Ackermann_k_tends_to_infinity:
  "filterlim (Ackermann k) at_top at_top"
  apply (subst filterlim_iff)
  apply (subst eventually_sequentially)
  apply (subst eventually_at_top_linorder)
  using Ackermann_k_inflationary[of k] 
  using order.trans by blast


(********************************************)
subsection {*Every @{term "Ackermann k"} is strictly inflationary. 
             That is, @{term "x < Ackermann k x"} holds.*}
(********************************************)

lemma Ackermann_k_strictly_inflationary:
  "x < Ackermann k x"
proof -
  have "x < Ackermann 0 x" apply (subst Ackermann_base_eq) by simp
  also have "\<dots> \<le> Ackermann k x" using mono_Ackermann_in_k unfolding mono_def by blast
  finally show ?thesis .
qed

(********************************************)
subsection {*For every n other than zero, 
             @{term "compow n (Ackermann k)"} is strictly inflationary.*}
(********************************************)

lemma compow_Ackermann_k_strictly_inflationary':
  shows "x < compow (Suc n) (Ackermann k) x"
proof - 
  have sg1: "x < Ackermann k x" using Ackermann_k_strictly_inflationary .
  also have sg2: "\<dots> \<le> (Ackermann k ^^ n) (Ackermann k x)" 
    using compow_Ackermann_k_inflationary' mono_Ackermann unfolding mono_def by blast
  finally show ?thesis apply (subst funpow_Suc_right_apply) by simp
qed

lemma compow_Ackermann_k_strictly_inflationary:
  assumes "n>0"
  shows "x < compow n (Ackermann k) x"
proof -
  obtain m where sg1: "n = Suc m" using gr0_implies_Suc[OF assms] by blast
  show ?thesis apply (subst sg1) using compow_Ackermann_k_strictly_inflationary' by simp
qed

(********************************************)
subsection {*The function  @{term "\<lambda>k. Ackermann k x"} is @{term strict_mono}.*}
(********************************************)

lemma Ackermann_strict_mono_in_k_step:
  assumes "x > 0"
  shows "Ackermann k x < Ackermann (Suc k) x"
  apply (subst Ackermann_step_eq)
  apply simp
  apply (subst funpow_swap1[of "Ackermann k" x x])
  using compow_Ackermann_k_strictly_inflationary[of x "Ackermann k x" k , OF assms] .

lemma Ackermann_strict_mono_in_k:
  assumes "x > 0"
  shows "strict_mono (\<lambda>k. Ackermann k x)"
  unfolding strict_mono_def
  apply auto
proof goal_cases
  case (1 k1 k2)
  have "Ackermann k1 x < Ackermann (Suc k1) x" 
    using Ackermann_strict_mono_in_k_step[OF assms] by simp
  also have "Ackermann (Suc k1) x \<le> Ackermann k2 x" using 1 mono_Ackermann_in_k unfolding mono_def by auto
  finally show ?case .
qed

(********************************************)
subsection {*Orbits of inflationary functions*}
(********************************************)

lemma Ackermann_k_x_tends_to_infinity_along_k:
  assumes "x > 0" shows "filterlim (\<lambda>k. Ackermann k x) at_top at_top"
  using  filterlim_subseq[OF Ackermann_strict_mono_in_k[OF assms]] .

(* The orbit of a strictly inflationary function goes to infinity. *)
 (* This lemma has nothing to do with Ackermann's function and could
     be placed in a separate file. *)

lemma compow_strictly_inflationary_tends_to_infinity:
  assumes "\<forall>x. x < f x" shows "filterlim (\<lambda>i. compow i f x) sequentially sequentially"
proof -
  {
    fix i
    have "x + i \<le> compow i f x" using assms proof (induction i)
      case (Suc i)
      have "Suc (x + i) \<le> f ((f ^^ i) x)"
        using assms Suc(1)[OF \<open> \<forall>x. x < f x\<close>] Suc_leI le_less_trans by blast
      then show ?case by (simp add: funpow_swap1 funpow_Suc_right_apply)
    qed simp
  } note bound = this
  thus ?thesis 
    apply (subst filterlim_iff)
    apply (subst eventually_sequentially)
    apply (subst eventually_at_top_linorder)
    apply auto
    by (meson order_trans trans_le_add2)
qed

lemma compow_i_Ackermann_tends_to_infinity_along_i:
  "filterlim (\<lambda>i. compow i (Ackermann k) x) at_top at_top"
  using compow_strictly_inflationary_tends_to_infinity[of "Ackermann k"] 
        Ackermann_k_strictly_inflationary[of _ k]
  by blast

(********************************************)
subsection {*Iterating i times an inflationary function f yields a monotonic function of i.*}
(********************************************)

lemma compow_inflationary_monotonic:
  assumes "inflationary (f::nat\<Rightarrow>nat)"
  shows "mono (\<lambda>i. (f ^^ i) x)"
  using assms unfolding mono_def
  apply auto
proof goal_cases
  case (1 i j)
  {
    fix y
    have "y \<le> (f ^^ (j - i)) y" using inflationary_compow'[OF assms, of y "j-i"] .
  } note gener = this
  have jlong: "j = (j - i) + i" using 1(2) by simp
  have sane: "(f ^^ (j - i) \<circ> f ^^ i) x = (f ^^ (j - i)) ((f ^^ i) x)" by simp
  show ?case 
    apply (subst jlong) 
    apply (subst funpow_add)
    apply (subst sane)
    using gener[of "(f ^^ i) x"] .
qed

(********************************************)
subsection {* @{term "(\<lambda> i. compow i (Ackermann k) x)"} is monotonic.*}
(********************************************)

lemma compow_Ackermann_mono_in_i:
  "mono (\<lambda> i. (Ackermann k ^^ i) x)"
  unfolding mono_def
  apply safe
proof goal_cases
  case (1 i j)
  show ?case using 
      funpow_mono2[OF mono_Ackermann[of k] \<open>i\<le>j\<close>, of x x] Ackermann_k_inflationary[of k] by blast
qed


(********************************************)
section {*Inverse Ackermann function, aka \<alpha>.*}
(********************************************)

definition \<alpha> where
  "\<alpha> n \<equiv> Least (\<lambda>k. Ackermann k 1 \<ge> n)"


interpretation A1nn: f_nat_nat "\<lambda>k. Ackermann k 1"
  apply standard subgoal using Ackermann_strict_mono_in_k[of 1] by simp
  subgoal using Ackermann_k_x_tends_to_infinity_along_k[of 1] by simp
  done

abbreviation \<alpha>' where
  "\<alpha>' \<equiv> A1nn.\<alpha>\<^sub>f "

lemma \<alpha>_alt_eq: "\<alpha> = \<alpha>'" unfolding \<alpha>_def A1nn.\<alpha>\<^sub>f_def by blast


lemma mono_\<alpha>: "mono \<alpha>"
  apply (subst \<alpha>_alt_eq)
  using A1nn.\<alpha>\<^sub>f_mono .


context 
  fixes x::nat
  assumes pos: "x>0"
begin
interpretation Apnn: f_nat_nat "\<lambda>k. Ackermann k x"
  apply standard subgoal using Ackermann_strict_mono_in_k[OF pos] .
  subgoal using Ackermann_k_x_tends_to_infinity_along_k[OF pos] .
  done

lemma \<beta>_x_Suc_x: 
  shows "Apnn.\<beta>\<^sub>f (x + 1) = 0"
proof -
  have "Apnn.\<beta>\<^sub>f (x + 1) < 1" 
    apply (rule Apnn.\<beta>\<^sub>f_spec_direct_contrapositive)
     apply (subst Ackermann_base_eq) apply simp
    apply (subst Ackermann_1_eq') using pos by simp
  thus ?thesis by blast
qed

(********************************************)
subsection{* @{term \<alpha>} grows very slowly. In particular, of course, it never grows by more
             than one at a time.*}
(********************************************)

\<comment>\<open>We state this lemma directly in a generalized form that will be useful when
   we later consider the function @{term alphar} introduced by Alstrup et al. \<close>

lemma \<alpha>_grows_one_by_one: "Apnn.\<alpha>\<^sub>f (Suc n) \<le> Suc (Apnn.\<alpha>\<^sub>f n)"
  apply (subst Apnn.\<alpha>\<^sub>f_spec)
  apply (subst Ackermann_step_eq)
  apply simp
proof -
  let ?alpha = "Apnn.\<alpha>\<^sub>f"
  let ?thesis = "Suc n \<le> Ackermann (?alpha n) ((Ackermann (?alpha n) ^^ x) x)"
  let ?f = "Ackermann (?alpha n)"
  have pos': "1\<le>x" using pos by fastforce
  have fact: "?f x \<le> compow x ?f x"
    using funpow_mono2[OF mono_Ackermann[of "(?alpha n)"], 
                       of 1 x x x, OF pos' order.refl] 
    Ackermann_k_inflationary[of "(?alpha n)"] by auto
  have fact2: "n \<le> Ackermann (?alpha  n) x"
    by (simp add: Apnn.f_\<alpha>\<^sub>f)
  have "Suc n \<le> Ackermann (?alpha n) n" 
    by (simp add: Ackermann_k_strictly_inflationary Suc_leI)
  also have "\<dots> \<le> Ackermann (?alpha n) (Ackermann (?alpha n) x)" using fact2
    by (simp add: monoD mono_Ackermann)
  finally show ?thesis using fact mono_Ackermann le_trans unfolding mono_def by blast
qed
end

lemma "\<alpha> (Suc n) \<le> Suc (\<alpha> n)" 
  apply (subst \<alpha>_alt_eq)+
  using \<alpha>_grows_one_by_one[OF zero_less_one] .

(********************************************)
subsection{* As soon as @{term n} is at least 4, @{term "\<alpha> n"} is greater than one. *}
(********************************************)

lemma two_le_\<alpha>: assumes "4 \<le> n" shows "2 \<le> \<alpha> n"
  apply (subst \<alpha>_alt_eq) 
proof -
  have fact: "Ackermann 1 1 < n" apply (subst Ackermann_1_eq') using assms by fastforce
  show "2 \<le> A1nn.\<alpha>\<^sub>f n"  using A1nn.\<alpha>\<^sub>f_spec_direct_contrapositive[OF fact] by simp
qed
  
(********************************************)
\<comment>\<open> @{term "\<alpha> n"} is at most @{term "Suc (\<alpha> (Discrete.log n))"}. This gives a weak sense of how
   slowly the function @{term \<alpha>} grows. In fact, the function log* would
   satisfy the same property; yet @{term \<alpha>} grows even more slowly than
   log*.

   This property also shows that @{term "\<alpha> n"} and @{term "\<alpha> (Discrete.log n)"} are
   asymptotically equivalent. This explains why Tarjan and Cormen et al. are
   content with a bound of @{term "\<alpha> n"} for the amortized complexity of union and
   find, even though they could easily obtain @{term "\<alpha> (Discrete.log n)"}. See Exercise
   21.4-6 in Cormen et al. \<close>
(********************************************)

lemma "n \<le> Ackermann (A1nn.\<alpha>\<^sub>f (Discrete.log n)) (Discrete.log n)"
  oops
lemma prove_le_log: assumes "2 ^ k \<le> n" shows "k \<le> Discrete.log n" using assms 
  using Discrete.log_le_iff by fastforce

lemma \<alpha>_n_0_\<alpha>_logn:
  assumes "16 \<le> n" shows "\<alpha> n \<le> Suc (\<alpha> (Discrete.log n))"
  apply (subst \<alpha>_alt_eq)
  apply (rule A1nn.\<alpha>\<^sub>f_spec_reciprocal)
  apply (subst Ackermann_step_eq)
  apply simp
  apply (subst One_nat_def[symmetric])
  apply (subst \<alpha>_alt_eq)+
  apply (cases "(A1nn.\<alpha>\<^sub>f (Discrete.log n)) \<ge> 2" )
  proof goal_cases
    let ?log = "Discrete.log"
    case 1
    have "n \<le> Ackermann 2 (?log n)" using Ackermann_2_log_lower_bound[of n] .
    also have "\<dots> \<le> Ackermann 2 (Ackermann (A1nn.\<alpha>\<^sub>f (?log n)) 1)" 
      using A1nn.f_\<alpha>\<^sub>f[of "?log n"] mono_Ackermann unfolding mono_def by blast
    also have "\<dots> \<le> Ackermann (A1nn.\<alpha>\<^sub>f (?log n)) (Ackermann (A1nn.\<alpha>\<^sub>f (?log n)) 1)"
      using 1(1) mono_Ackermann_in_k[of "(Ackermann (A1nn.\<alpha>\<^sub>f (?log n)) 1)"] two_le_\<alpha> 
      unfolding mono_def  
      by (simp add: \<alpha>_alt_eq)  
    finally show ?case .
  next
    case 2
    have 3: "4 \<le> Discrete.log n " using assms by (simp add: prove_le_log)
    have "2 \<le> A1nn.\<alpha>\<^sub>f (Discrete.log n)" using two_le_\<alpha>[OF 3] 
      by (subst (asm) \<alpha>_alt_eq)
    then show ?case using 2 by blast
  qed



(********************************************)
subsection {*alphar*}

\<comment>\<open> Alstrup et al. define the function @{term alphar} as follows (page 17).
   Note that their definition of @{term Ackermann} is not the same as ours -- they
   index k from 1 and up, whereas, following Tarjan, we index k
   from 0 and up -- so our definition of alphar looks different. \<close>
(********************************************)

context 
  fixes r::nat
  assumes pos: "r>0"
begin
definition alphar where
  "alphar n \<equiv> Suc (Least (\<lambda>k. Ackermann k r \<ge> Suc n))"

\<comment>\<open>abbreviation defalphar where "defalphar  \<equiv> \<lambda>k. Ackermann k r"\<close>

interpretation pnn: f_nat_nat "\<lambda>k. Ackermann k r"
  apply standard subgoal using Ackermann_strict_mono_in_k[OF pos] .
  subgoal using Ackermann_k_x_tends_to_infinity_along_k[OF pos] .
  done

definition prealphar where "prealphar n \<equiv> pnn.\<alpha>\<^sub>f (Suc n)"

definition alphar' where "alphar' n \<equiv> Suc (prealphar n)"

lemma alphar_alt_eq: "alphar = alphar'"
  unfolding alphar_def alphar'_def prealphar_def pnn.\<alpha>\<^sub>f_def by blast

subsubsection{* @{term "alphar n"} is positive.*}

lemma alphar_pos: "0 < alphar n"
  unfolding alphar_def by simp

(********************************************)
subsubsection{* @{term "alphar n"} is monotonic.*}
(********************************************)

lemma mono_alphar: "mono alphar"
  apply (subst alphar_alt_eq)
  unfolding alphar'_def prealphar_def
  using pnn.\<alpha>\<^sub>f_mono unfolding mono_def by simp

(********************************************)
subsubsection{* Like @{term \<alpha>}, @{term alphar} grows at most by one at a time. *}
(********************************************)

lemma alphar_grows_one_by_one:
  "alphar (Suc n) \<le> Suc (alphar n)"
  apply (subst alphar_alt_eq)+
  unfolding alphar'_def prealphar_def
  using \<alpha>_grows_one_by_one[OF pos] by auto

(********************************************)
\<comment>\<open> If @{term r} is 1, then @{term "alphar n"} is as follows. \<close>
(********************************************)

lemma alphar_one: assumes "r = 1" shows "alphar n  = Suc (\<alpha> (Suc n))"
  apply (subst alphar_alt_eq)
  apply (subst \<alpha>_alt_eq)
  unfolding alphar'_def prealphar_def pnn.\<alpha>\<^sub>f_def A1nn.\<alpha>\<^sub>f_def using assms by blast

(********************************************)
\<comment>\<open> @{term "alphar r"} is 1. (Exploited on page 18.) \<close>
(********************************************)

lemma alphar_r:
  "alphar r = 1"
  apply (subst alphar_alt_eq)
  unfolding alphar'_def
proof -
  have "prealphar r \<le> 0" unfolding prealphar_def 
    apply (rule  pnn.\<alpha>\<^sub>f_spec_reciprocal) 
    apply (subst Ackermann_base_eq) by simp
  thus "Suc (local.prealphar r) = 1" by force
qed

(********************************************)
\<comment>\<open> If @{term r} is less than @{term n}, then @{term "alphar n"} is at least two (page 17). \<close>
(********************************************)

lemma alphar_geq_two: assumes "r < n" shows "1 < alphar n"  
  apply (subst alphar_alt_eq)
  unfolding alphar'_def
  apply simp
  unfolding prealphar_def 
  apply (rule pnn.\<alpha>\<^sub>f_spec_direct_contrapositive)
  apply (subst Ackermann_base_eq) using assms by simp

(********************************************)
\<comment>\<open> @{term "Ackermann (prealphar n) r"} is greater than @{term n} (page 17). \<close>
(********************************************)

lemma Ackermann_prealphar_gt: "n < Ackermann (prealphar n) r"
proof -
  have "Suc n \<le> Ackermann (prealphar n) r" using pnn.f_\<alpha>\<^sub>f unfolding prealphar_def by simp
  thus ?thesis by simp
qed

end

end