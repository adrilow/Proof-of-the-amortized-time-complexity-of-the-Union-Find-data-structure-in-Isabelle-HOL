theory InverseNatNat imports Main HOL.Filter begin

locale f_nat_nat =
  fixes f :: "nat\<Rightarrow>nat"
  assumes strict_mono_f: "strict_mono f"
    and tends_to_inf: "filterlim f at_top at_top"
  
context f_nat_nat
begin

lemma tendstoinf: "\<exists>n\<^sub>0.\<forall>n\<ge>n\<^sub>0. (f n) > K" 
  using tends_to_inf 
  apply (subst (asm) filterlim_at_top[of f sequentially])
  using  eventually_at_top_linorder
  by (meson eventually_gt_at_top eventually_sequentially)

lemma mono_f: "mono f" using strict_mono_f
  by (simp add: strict_mono_mono)

lemma alphaf_existence:
  "\<exists>x. y \<le> f x" 
proof -
  obtain n\<^sub>0 where "\<forall>n\<ge>n\<^sub>0. y < f n" using tendstoinf[of y] by blast
  hence "y \<le> f n\<^sub>0" by fastforce
  thus ?thesis by blast
qed


lemma betaf_bound: "\<exists>x.\<forall>y\<^sub>0. f y\<^sub>0 \<le> y \<longrightarrow> y\<^sub>0 \<le> x"
  by (meson le_cases less_le_trans sup.strict_order_iff tendstoinf)


(* -------------------------------------------------------------------------- *)
(* Because f tends towards infinity, for every y, there exists a least
   x such that f x is at least y. We refer to it as \<alpha>\<^sub>f y. *)
(* -------------------------------------------------------------------------- *)


definition \<alpha>\<^sub>f where "\<alpha>\<^sub>f y \<equiv> Least (\<lambda>x. y \<le> f x)"

(* By definition, "\<alpha>\<^sub>f y" is the least x such that "y \<le> f x holds.
   Because f is monotonic, this property holds for all x above "\<alpha>\<^sub>f y".
   Thus, "y \<le> f x" is equivalent to "\<alpha>\<^sub>f y \<le> x". In that sense, \<alpha>\<^sub>f
   is an inverse of f. *)

lemma \<alpha>\<^sub>f_spec_direct: assumes "\<alpha>\<^sub>f y \<le> x" shows "y \<le> f x"
proof -
  have "y \<le> f (\<alpha>\<^sub>f y)" using alphaf_existence[of y] unfolding \<alpha>\<^sub>f_def using LeastI by fast
  also have  "\<dots> \<le> f x" using mono_f assms unfolding \<alpha>\<^sub>f_def mono_def by blast
  finally show ?thesis .
qed

lemma \<alpha>\<^sub>f_spec_direct_contrapositive: assumes "f x < y" shows "x < \<alpha>\<^sub>f y"
proof (rule classical)
  assume assm2: "\<not> x < \<alpha>\<^sub>f y"
  hence "\<alpha>\<^sub>f y \<le> x" by simp
  thus "x < \<alpha>\<^sub>f y" using \<alpha>\<^sub>f_spec_direct[of y x] assms by linarith
qed

lemma \<alpha>\<^sub>f_spec_reciprocal: assumes "y \<le> f x" shows "\<alpha>\<^sub>f y \<le> x"
 using alphaf_existence[of y] assms Least_le unfolding \<alpha>\<^sub>f_def by fast

lemma \<alpha>\<^sub>f_spec_reciprocal_contrapositive: assumes "x < \<alpha>\<^sub>f y" shows "f x < y"
proof (rule classical)
  assume assm2: "\<not> f x < y"
  hence "y \<le> f x" by linarith
  thus "f x < y" using \<alpha>\<^sub>f_spec_reciprocal[of y x] assms by linarith
qed

lemma \<alpha>\<^sub>f_spec: "(\<alpha>\<^sub>f y \<le> x) = (y \<le> f x)"
  using \<alpha>\<^sub>f_spec_reciprocal f_nat_nat.\<alpha>\<^sub>f_spec_direct f_nat_nat_axioms by blast

lemma f_\<alpha>\<^sub>f: "y \<le> f (\<alpha>\<^sub>f y)"
  by (simp add: \<alpha>\<^sub>f_spec_direct)

lemma \<alpha>\<^sub>f_f: "\<alpha>\<^sub>f (f x) \<le> x"
  using \<alpha>\<^sub>f_spec_reciprocal by auto

lemma \<alpha>\<^sub>f_f_exact: "\<alpha>\<^sub>f (f x) = x"
  using  strict_mono_f  f_\<alpha>\<^sub>f[of x] \<alpha>\<^sub>f_f[of x] unfolding strict_mono_def
  by (meson f_\<alpha>\<^sub>f less_le_not_le order.not_eq_order_implies_strict)

lemma \<alpha>\<^sub>f_mono: "mono \<alpha>\<^sub>f"
  using \<alpha>\<^sub>f_spec_reciprocal f_\<alpha>\<^sub>f le_trans unfolding mono_def 
  by blast

(* -------------------------------------------------------------------------- *)
(* Almost symmetrically, if "f 0 \<le> y" holds, then there exists a largest x
   such that "f x" is bounded by y. We refer to it as "\<beta>\<^sub>f y". Because
   f is monotonic, this property holds for all x below "\<beta>\<^sub>f y". Thus,
   "f x \<le> y" is equivalent to "x \<le> \<beta>\<^sub>f y". In that sense, \<beta>\<^sub>f is an
   inverse of f. *)
(* -------------------------------------------------------------------------- *)

definition \<beta>\<^sub>f where "\<beta>\<^sub>f y = Greatest (\<lambda>x. f x \<le> y)"

lemma \<beta>\<^sub>f_spec_direct: assumes "f 0 \<le> y" "x \<le> \<beta>\<^sub>f y" shows "f x \<le> y"
proof -
  have "f x \<le> f (\<beta>\<^sub>f y)" using mono_f assms unfolding mono_def \<beta>\<^sub>f_def by blast
  also have "\<dots> \<le> y" using mono_f assms  unfolding mono_def  \<beta>\<^sub>f_def
    by (metis GreatestI_ex_nat betaf_bound)
  finally show ?thesis .
qed

lemma \<beta>\<^sub>f_spec_direct_contrapositive: assumes "f 0 \<le> y" "y < f x" shows "\<beta>\<^sub>f y < x"
proof (rule classical)
  assume assm2: "\<not> \<beta>\<^sub>f y < x"
  hence "x \<le> \<beta>\<^sub>f y" by simp
  thus "\<beta>\<^sub>f y < x" using  \<beta>\<^sub>f_spec_direct[OF assms(1) \<open>x \<le> \<beta>\<^sub>f y\<close>] assms by linarith
qed

lemma \<beta>\<^sub>f_spec_direct_contrapositive_le: assumes "f 0 \<le> y" "y < f (Suc x)" shows "\<beta>\<^sub>f y \<le> x"
proof -
  have "\<beta>\<^sub>f y < Suc x" using \<beta>\<^sub>f_spec_direct_contrapositive[OF assms(1) assms(2)] .
  thus ?thesis by simp
qed

lemma \<beta>\<^sub>f_spec_reciprocal: assumes "f x \<le> y"  shows "x \<le> \<beta>\<^sub>f y"
  using assms mono_f Greatest_le_nat betaf_bound unfolding mono_def \<beta>\<^sub>f_def
  by presburger

lemma \<beta>\<^sub>f_spec_reciprocal_contrapositive: assumes "\<beta>\<^sub>f y < x" shows "y < f x"
proof (rule classical)
  assume assm2: "\<not> y < f x"
  hence "f x \<le> y" by simp
  thus "y < f x" using \<beta>\<^sub>f_spec_reciprocal[OF \<open>f x \<le> y\<close>] assms by linarith
qed

lemma \<beta>\<^sub>f_spec: assumes "f 0 \<le> y" shows "(x \<le> \<beta>\<^sub>f y) = (f x \<le> y)"
  using \<beta>\<^sub>f_spec_direct \<beta>\<^sub>f_spec_reciprocal assms by blast

lemma f_\<beta>\<^sub>f: assumes "f 0 \<le> y" shows "f (\<beta>\<^sub>f y) \<le> y"
  by (simp add: \<beta>\<^sub>f_spec_direct assms)

lemma \<beta>\<^sub>f_f: "x \<le> \<beta>\<^sub>f (f x)"
  by (simp add: \<beta>\<^sub>f_spec_reciprocal)

lemma \<beta>\<^sub>f_f_exact: "x = \<beta>\<^sub>f (f x)"
  by (meson \<beta>\<^sub>f_f f_\<beta>\<^sub>f le0 order_class.order.antisym strict_mono_f strict_mono_less_eq)

(*mono f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y)*)
lemma \<beta>\<^sub>f_mono: "\<forall>x y. (f 0 \<le> x \<and> x \<le> y) \<longrightarrow> f x \<le> f y"
  using \<beta>\<^sub>f_spec_reciprocal f_\<beta>\<^sub>f
  by (simp add: strict_mono_f strict_mono_less_eq)

(* -------------------------------------------------------------------------- *)
section{* Relationship between \<alpha>_f and \<beta>_f *}
(* -------------------------------------------------------------------------- *)

(* Because f is strictly monotonic, for a fixed y, there is at most one
   point x where "f x = y" holds. This implies that, if "\<beta>\<^sub>f y" is
   defined, then "\<beta>\<^sub>f y" is less than or equal to "\<alpha>\<^sub>f y". *)

lemma \<beta>\<^sub>f_le_\<alpha>\<^sub>f: assumes "f 0 \<le> y" shows "\<beta>\<^sub>f y \<le> \<alpha>\<^sub>f y"
  using mono_f strict_mono_f assms
  by (metis \<alpha>\<^sub>f_spec_direct \<beta>\<^sub>f_spec_direct dual_order.antisym le_cases strict_mono_eq)

lemma \<beta>\<^sub>f_le_\<alpha>\<^sub>f_equality: assumes "f x = y" shows "\<alpha>\<^sub>f y = x" "\<beta>\<^sub>f y = \<alpha>\<^sub>f y" 
  using assms 
proof -
  have 1: "\<alpha>\<^sub>f y = x" using \<alpha>\<^sub>f_f_exact assms by auto
  have 2: "\<beta>\<^sub>f y = x" using \<beta>\<^sub>f_f_exact assms by auto
  show "f x = y \<Longrightarrow> \<alpha>\<^sub>f y = x" using 1 2 by fast
  show "f x = y \<Longrightarrow> \<beta>\<^sub>f y = \<alpha>\<^sub>f y" using 1 2 by presburger
qed

lemma \<beta>\<^sub>f_le_\<alpha>\<^sub>f_equality_converse: assumes "f 0 \<le> y" "\<beta>\<^sub>f y = \<alpha>\<^sub>f y" "\<alpha>\<^sub>f y = x" shows "f x = y"
  using assms dual_order.antisym f_\<alpha>\<^sub>f f_\<beta>\<^sub>f by fastforce

lemma \<beta>\<^sub>f_\<alpha>\<^sub>f_differ_by_at_most_one:
  "\<alpha>\<^sub>f y \<le> Suc (\<beta>\<^sub>f y)"
  using Suc_n_not_le_n \<alpha>\<^sub>f_spec \<beta>\<^sub>f_spec_reciprocal nat_le_linear  by blast

lemma \<alpha>\<^sub>f_lt_\<beta>\<^sub>f: assumes "f 0 \<le> y" "y < z" shows "\<beta>\<^sub>f y < \<alpha>\<^sub>f z" 
  using \<beta>\<^sub>f_spec_direct_contrapositive assms f_\<alpha>\<^sub>f less_le_trans by blast

lemma \<beta>\<^sub>f_tends_to_infinity: 
  "filterlim \<beta>\<^sub>f at_top at_top"
  apply (subst filterlim_iff)
  apply (subst eventually_sequentially)
  using \<beta>\<^sub>f_spec_reciprocal eventually_sequentially by fast

lemma \<alpha>\<^sub>f_tends_to_infinity:
  "filterlim \<alpha>\<^sub>f at_top at_top"
proof -
  have sg1: "\<And>x y. \<lbrakk>True; True; x \<le> y\<rbrakk> \<Longrightarrow> \<alpha>\<^sub>f x \<le> \<alpha>\<^sub>f y" using \<alpha>\<^sub>f_mono unfolding mono_def by blast
  show ?thesis 
    using filterlim_at_top_at_top
      [where f = "\<alpha>\<^sub>f" , where g = "f", where P ="(\<lambda>x. f 0 \<le> x)", where Q = "(\<lambda>x. True)", OF sg1]
 \<beta>\<^sub>f_le_\<alpha>\<^sub>f eventually_ge_at_top[of "f 0"]  \<alpha>\<^sub>f_f_exact by simp
qed
  


end
end

