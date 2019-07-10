theory Union_Find_Time_alpha_verification
  imports Union_Find_Time_alpha_abstract_analysis Union_Find_Time_alpha_fix
begin

subsubsection{*uf_init_lemmas*}

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al rkl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl 
    * \<up>(ufa_invar l \<and> ufa_\<alpha> l = R \<and> length rkl = length l \<and> invar_rank l rkl)
    * $(\<Phi> l rkl)"



lemma of_list_rule':
    "<$ (1 + n)> Array.of_list [0..<n] <\<lambda>r. r \<mapsto>\<^sub>a [0..<n]>"
  using of_list_rule[of "[0..<n]"] by auto 


lemma uf_init_rank_simp: "{(x, y). x < length [0..<n] \<and> y < length [0..<n] \<and> [0..<n] ! x = y} 
  = {(x,y). x < length [0..<n] \<and> y = x}"
  using nth_upt_zero by blast

  
lemma ufa_\<beta>_init_simp: "ufa_\<beta> [0..<n] = {(x, y). x < length [0..<n] \<and> y = x}\<^sup>+"
  unfolding ufa_\<beta>_def ufa_\<beta>_start_def 
  apply (subst uf_init_rank_simp)
  by blast

lemma ufa_\<beta>_init_simp': "trans  {(x, y). x < length [0..<n] \<and> y = x}"
   apply rule
  apply auto
  done

lemma ufa_\<beta>_init_simp'':"{(x, y). x < length [0..<n] \<and> y = x} = {(x, y). x < length [0..<n] \<and> y = x}\<^sup>+"
  using Transitive_Closure.trancl_id[OF ufa_\<beta>_init_simp', of n, symmetric ] .

lemma ufa_init_invar': "invar_rank [0..<n] (replicate n 0)"
  unfolding invar_rank_def apply auto 
  proof goal_cases
  case (1 i)
  have setsimp: "i<n \<Longrightarrow> {j. i = j \<and> j <n} = {i}" by blast
   show ?case unfolding descendants_def 
    apply (subst ufa_\<beta>_init_simp)
     apply (subst ufa_\<beta>_init_simp''[symmetric])
     apply auto
     apply (subst setsimp)
     subgoal using 1 .
     apply (subst Groups_Big.card_eq_sum)
     by simp
 qed

lemma zero_is_min_of_nat_set:
  assumes"finite S" "(0::nat)\<in>S" shows "Min S = 0"
proof -
  have sg1: "S \<noteq> {}" using assms(2) by auto
  have sg2: "\<forall>a\<in>S. 0\<le>a" by blast
  show ?thesis 
    using  Lattices_Big.linorder_class.eq_Min_iff[OF assms(1) sg1, of 0, symmetric] sg2 assms(2) 
    by argo
qed

lemma \<Phi>_init_value: "\<Phi> [0..<n] (replicate n 0) = 2*n"
proof -
  {
    fix i
    have "i<n \<Longrightarrow> rep_of [0..<n] i = i" 
      using nth_upt_zero[of i n] rep_of_refl[of "[0..<n]" i] upt_zero_length[of n]
    by auto
  }
  note rep_of_simp = this
  hence if_branch: "\<forall>x\<in>{0..<n}. rep_of [0..<n] x = x" by auto
  {
    fix x
    assume assms:"x<n"
    have 1: "(replicate n 0) ! x = 0" using assms by simp
    have 2: "0 \<in> {k. k \<le> Suc 0 \<and> Suc (Suc 0) \<le> Ackermann k (Suc 0)}"
      using Ackermann01 by auto
    hence 3: "0 = Min {k. k \<le> Suc 0 \<and> Suc (Suc 0) \<le> Ackermann k (Suc 0)}" 
      by (simp add: zero_is_min_of_nat_set)
    have " \<alpha>\<^sub>r (rankr (replicate n 0) x) = \<rho>"
      unfolding rankr_def
      apply (subst 1)
      unfolding alphar_def \<rho>_def
      apply auto
      using 3[symmetric] .
  }
  note alphar_simp = this
  show ?thesis
    apply simp
    unfolding \<phi>_def
    apply (simp add: if_branch)
    apply (simp add: alphar_simp)
    unfolding \<rho>_def
    by simp 
qed

definition uf_init_time :: "nat \<Rightarrow> nat" where "uf_init_time n == (2*n+3+2*n)"

lemma uf_init_bound[asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n. n)" 
  unfolding uf_init_time_def by auto2

lemma Array_new_rule'[sep_heap_rules]: "<$ (n + 1) * true> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>\<^sub>t"
  by sep_auto

lemmas \<Phi>_simp[simp del]
lemma uf_init_rule: 
  "<$(uf_init_time n)> uf_init n <is_uf {(i,i) |i. i<n}  >\<^sub>t"
  unfolding uf_init_time_def uf_init_def is_uf_def[abs_def]
  apply (vcg)
   apply (vcg heap: of_list_rule')
  apply (vcg)
  apply clarsimp
  apply (sep_auto (nopre) (nopost) simp: ufa_init_invar)
  apply clarsimp
  apply (vcg)
  apply clarsimp
proof goal_cases
  case (1 x xa)
  have " x \<mapsto>\<^sub>a [0..<n] * xa \<mapsto>\<^sub>a replicate n 0 * $ (n * 2) \<Longrightarrow>\<^sub>A
       x \<mapsto>\<^sub>a [0..<n] * xa \<mapsto>\<^sub>a replicate n 0 * true * $ (\<Phi> [0..<n] (replicate n 0)) *
       \<up> (ufa_invar [0..<n] \<and> ufa_\<alpha> [0..<n] = {(i, i) |i. i < n}
       \<and> length (replicate n 0) = length [0..<n] \<and> invar_rank [0..<n] (replicate n 0))"
    apply (auto simp add: ufa_init_invar ufa_init_correct ufa_init_invar' \<Phi>_init_value)
    apply sep_auto
    done
  then show ?case by sep_auto
qed
 

subsubsection{*uf_rep_of lemmas*}

(*TODO: decouple height_of*)
lemma uf_rep_of_rule: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(height_of l i + 2)> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>\<^sub>t"
  apply (induct rule: rep_of_induct)
  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_refl)
  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_step height_of_step)
  done



subsubsection{*uf_compress lemmas*}

lemma compress_invar:
  assumes "invar l szl"
    "ufa_invar l" "i<length l"
  shows "invar (l[i := rep_of l i]) szl"
  using assms unfolding invar_def
  apply safe
  subgoal by simp
  subgoal apply simp  
    by (smt nth_list_update_eq nth_list_update_neq rep_of_iff rep_of_min sum.ivl_cong)  
  subgoal for i
    apply(rule order.trans)
    apply(rule power_increasing[where N="h_of l i"])
    subgoal apply(rule h_of_compress) by auto
     apply simp
    apply simp  
    by (metis nth_list_update_eq nth_list_update_neq rep_of_min)
  done


lemma uf_compress_rule: "\<lbrakk> ufa_invar l; i<length l; ci=rep_of l i; invar l szl \<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al *  $(1+height_of l i*3)> uf_compress i ci p 
  <\<lambda>_. (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' * \<up>(invar l' szl \<and> ufa_invar l' \<and> length l' = length l 
     \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)))>\<^sub>t"
proof (induction rule: rep_of_induct)
  case (base i) thus ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: rep_of_refl)
    done
next
  case (step i)
  note SS = `ufa_invar l` `i<length l` `l!i\<noteq>i` `ci = rep_of l i` `invar l szl`

   
  have IH': 
    "<p \<mapsto>\<^sub>a l * $ (1 + height_of l (l ! i) *3)> 
       uf_compress (l ! i) (rep_of l i) p
     <\<lambda>_.  (\<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * 
        \<up> (invar l' szl \<and>ufa_invar l' \<and> length l' = length l 
           \<and> (\<forall>i<length l'. rep_of l i = rep_of l' i)))
     >\<^sub>t"   
    apply(rule pre_rule[OF _ post_rule[OF step.IH[simplified SS rep_of_idx] ]] ) 
    by (sep_auto simp add: rep_of_idx SS)+  

  show ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: SS height_of_step heap: )
    apply(sep_auto heap: IH') 
 
    using SS apply (sep_auto  ) 
    subgoal using compress_invar by simp
    subgoal using ufa_compress_invar by fastforce
    subgoal by simp
    subgoal using ufa_compress_aux(2) by fastforce
    done
qed


subsubsection{*uf_rep_of_c lemmas*}

lemma uf_rep_of_c_rule: "\<lbrakk>ufa_invar l; i<length l; invar l szl\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4+height_of l i*4)> uf_rep_of_c p i <\<lambda>r.  (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l' \<and> invar l' szl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)))>\<^sub>t"
  unfolding uf_rep_of_c_def
  by (sep_auto heap: uf_compress_rule uf_rep_of_rule) 

thm height_of_ub

definition height_ub :: "nat \<Rightarrow> nat" where "height_ub n = nat (ceiling (log 2 n))"


lemma height_ub_bound[asym_bound]: "height_ub \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding height_ub_def using abcd_lnx[of 0 1 1 0] by auto

lemma height_ub:
  assumes "invar l sl" "ufa_invar l" "i<length l"
  shows "height_of l i \<le> height_ub (length l)"
proof -
  from height_of_ub[OF assms] have "2 ^ height_of l i \<le> length l" .
  from le_log2_of_power[OF this]
    show ?thesis unfolding height_ub_def by linarith
  qed



lemma uf_rep_of_c_rule_ub: 
  assumes "ufa_invar l"  "i<length l" "invar l szl"
  shows "<p\<mapsto>\<^sub>al * $(4+ height_ub (length l)*4)> uf_rep_of_c p i <\<lambda>r. (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l' \<and> invar l' szl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))) >\<^sub>t"
proof -
  from assms height_ub have "height_of l i \<le> height_ub (length l)" by auto
  then obtain x where p: "height_ub (length l) = height_of l i + x"  
    using le_Suc_ex by blast  
  show ?thesis unfolding p
    using assms by(sep_auto heap: uf_rep_of_c_rule)
qed


subsubsection{*uf_cmp lemmas*}



lemma cnv_to_ufa_\<alpha>_eq: 
  "\<lbrakk>(\<forall>i<length l. rep_of l' i = rep_of l i); length l = length l'\<rbrakk> 
  \<Longrightarrow> (ufa_\<alpha> l = ufa_\<alpha> l')"
  unfolding ufa_\<alpha>_def by auto

lemma "  card (Domain (ufa_\<alpha> l)) = length l"
  by simp

definition uf_cmp_time :: "nat \<Rightarrow> nat" where "uf_cmp_time n = 10+ height_ub n*8"

lemma uf_cmp_time_bound[asym_bound]: 
  "uf_cmp_time \<in> \<Theta>(\<lambda>n. ln n)" unfolding uf_cmp_time_def by auto2 

lemma uf_cmp_rule:
  "<is_uf R u * $(uf_cmp_time (card (Domain R)))> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>\<^sub>t" 
  sorry
  

subsubsection{*uf_union_lemmas*}


lemma uf_rep_of_rule_ub: assumes "ufa_invar l" "i<length l"  "invar l szl"
  shows "<p\<mapsto>\<^sub>al * $(height_ub (length l) + 2)> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>\<^sub>t"
proof -
  from assms height_ub have "height_of l i \<le> height_ub (length l)" by auto
  then obtain x where p: "height_ub (length l) = height_of l i + x"  
    using le_Suc_ex by blast  
  show ?thesis unfolding p
    using assms by(sep_auto heap: uf_rep_of_rule)
qed


definition "uf_union_time n = 11+ height_ub n*2"

lemma uf_union_time_bound[asym_bound]: "uf_union_time \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding uf_union_time_def by auto2

lemma uf_union_rule: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u * $(uf_union_time (card (Domain R)))> uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  sorry



(*************************)
lemma uf_union_rule_alpha: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u> uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  sorry

(*************************)

interpretation UnionFind_Impl is_uf uf_init uf_init_time uf_cmp uf_cmp_time uf_union uf_union_time
proof (unfold_locales, goal_cases)
case (1 t x' x)
  show ?case
    unfolding PR_CONST_def mop_per_init_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_init_rule, where Cost_lb="uf_init_time x"])
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    using 1 by simp
next
  case (2 t R' R a' a b' b)
   show ?case 
    unfolding PR_CONST_def mop_per_compare_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_cmp_rule, where Cost_lb="(uf_cmp_time (card (Domain R')))"])
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    using 2 by simp
next
  case (3  t R' R a' a b' b)
   show ?case 
    unfolding PR_CONST_def mop_per_union_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_union_rule, where Cost_lb="(uf_union_time (card (Domain R')))"])
        apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    subgoal using 3 by simp
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    subgoal using 3 by simp
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def invalid_assn_def)+
    using 3 by simp
qed

end
