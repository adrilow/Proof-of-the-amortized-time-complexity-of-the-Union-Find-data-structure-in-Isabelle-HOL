theory Union_Find_Time_alpha_verification
  imports Union_Find_Time_alpha_abstract_analysis Union_Find_Time_alpha_fix
begin

subsubsection{*uf_init_lemmas*}

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al rkl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl 
    * \<up>(ufa_\<alpha> l = R \<and> length rkl = length l \<and> invar_rank l rkl)
    * $(\<Phi> l rkl)"


lemma of_list_rule':
    "<$ (1 + n)> Array.of_list [0..<n] <\<lambda>r. r \<mapsto>\<^sub>a [0..<n]>"
  using of_list_rule[of "[0..<n]"] by auto 


lemma uf_init_rank_simp': "{(x, y). x < length [0..<n] \<and> y < length [0..<n] \<and> x \<noteq> y \<and> [0..<n] ! x = y} 
  = {(x,y). x < length [0..<n] \<and> y = x \<and> x\<noteq>y}"
  using nth_upt_zero by blast

lemma uf_init_rank_simp: "{(x, y). x < length [0..<n] \<and> y < length [0..<n] \<and> x \<noteq> y \<and> [0..<n] ! x = y} = {}"
  using uf_init_rank_simp' by blast
  
lemma ufa_\<beta>_init_simp: "ufa_\<beta> [0..<n] = {}"
  unfolding ufa_\<beta>_def ufa_\<beta>_start_def 
  apply (subst uf_init_rank_simp)
  by simp

lemma ufa_\<beta>_init_simp': "trans  {(x, y). x < length [0..<n] \<and> y = x}"
   apply rule
  apply auto
  done

lemma ufa_\<beta>_init_simp'':"{(x, y). x < length [0..<n] \<and> y = x} = {(x, y). x < length [0..<n] \<and> y = x}\<^sup>+"
  using Transitive_Closure.trancl_id[OF ufa_\<beta>_init_simp', of n, symmetric ] .

lemma ufa_\<beta>_init_desc: "i<n \<Longrightarrow> descendants [0..<n] i = {i}" 
  unfolding descendants_def ufa_\<beta>_start_def 
  by auto (metis (no_types, lifting) case_prodE mem_Collect_eq nth_upt_zero rtrancl.cases upt_zero_length)


lemma ufa_init_invar': "invar_rank [0..<n] (replicate n 0)"
  unfolding invar_rank_def apply auto 
  proof goal_cases
    case 1
    then show ?case unfolding ufa_invar_def
      by (simp add: ufa_init_invar ufa_invarD(1))
  next
    case (2 i)
    then show ?case using ufa_\<beta>_init_desc[OF 2] by auto
 qed

lemma zero_is_least_of_nat:
  assumes "P (0::nat)" shows "Least P = 0"
  using Least_eq_0 assms by simp

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
    hence 3: "0 = Least (\<lambda>k. k \<le> Suc 0 \<and> Suc (Suc 0) \<le> Ackermann k (Suc 0))"  by simp
    have " \<alpha>\<^sub>r (rankr (replicate n 0) x) = \<rho>"
      unfolding rankr_def
      apply (subst 1)
      unfolding alphar_def alphar_def[OF \<rho>_gt_0]
      apply auto
      using 3[symmetric] by (simp add: Ackermann_base_eq \<rho>_def)
  }
  note alphar_simp = this
  {
    fix i assume assms: "i<n"
    have 1: "(replicate n 0) ! i = 0" using assms by simp
    hence "rankr (replicate n 0) i = \<rho>" unfolding rankr_def by simp
  } note rankr_simp = this 
  show ?thesis
    apply simp
    unfolding \<phi>_def
    apply (simp add: if_branch)
    apply (simp add: alphar_simp)
     using rankr_simp unfolding \<rho>_def 
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

lemma height_of_ipc_equiv:
  assumes "bw_ipc l x d l'"  "ufa_invar l" "x<length l" 
  shows "d = height_of l x"
  using assms proof (induction rule: bw_ipc.induct)
  case (BWIPCBase x l)
  then show ?case 
    using h_rep rep_of_iff by fastforce 
next
  case (BWIPCStep x y l i l')
  then show ?case unfolding ufa_\<beta>_start_def 
    using height_of_step by auto
qed

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

lemma compress_invar_rank:
  assumes "invar_rank l rkl" "i<length l"
  shows "invar_rank (l[i := rep_of l i]) rkl"
  
  by (metis assms(1) assms(2) compress_evolution invar_rank'_def invar_rank_def invar_rank_evolution list_update_id rep_of_refl)


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


lemma uf_compress_rule': assumes "invar_rank l rkl" "i<length l" "ci=rep_of l i" 
  shows "  <p\<mapsto>\<^sub>al *  $(1+(height_of l i)*3)> uf_compress i ci p 
  <\<lambda>_. (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' * \<up>(invar_rank l' rkl \<and> length l' = length l 
     \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)) )>\<^sub>t"
proof -

  have "ufa_invar l" using invar_rank_ufa_invarI[OF assms(1)] .
  
  show ?thesis using \<open>ufa_invar l\<close> assms(2,3,1) 
  proof (induction rule: rep_of_induct)
    case (base i) thus ?case
      apply (subst uf_compress.simps)
      apply (sep_auto simp: rep_of_refl)
      done
  next
    case (step i)
    note SS = `ufa_invar l` `i<length l` `l!i\<noteq>i` `ci = rep_of l i` `invar_rank l rkl`


    have IH': 
      "<p \<mapsto>\<^sub>a l * $ (1 + height_of l (l ! i) *3)> 
       uf_compress (l ! i) (rep_of l i) p
     <\<lambda>_.  (\<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * 
        \<up> (invar_rank l' rkl \<and> length l' = length l 
           \<and> (\<forall>i<length l'. rep_of l i = rep_of l' i)))
     >\<^sub>t"   
      apply(rule pre_rule[OF _ post_rule[OF step.IH[simplified SS rep_of_idx] ]] ) 
      by (sep_auto simp add: rep_of_idx SS)+  

    show ?case
      apply (subst uf_compress.simps)
      apply (sep_auto simp: SS height_of_step heap: )
       apply(sep_auto heap: IH') 

      using SS apply (sep_auto  ) 
      subgoal using compress_invar_rank by simp
      subgoal using ufa_compress_invar by fastforce
      subgoal using ufa_compress_aux(2) by (auto dest!: invar_rank_ufa_invarI)
      done
  qed
qed


subsubsection{*uf_rep_of_c lemmas*}


lemma uf_rep_of_c_rule: "\<lbrakk>ufa_invar l; i<length l; invar l szl\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4+height_of l i*4)> uf_rep_of_c p i <\<lambda>r.  (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l' \<and> invar l' szl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)))>\<^sub>t"
  unfolding uf_rep_of_c_def
  by (sep_auto (nopost) heap: uf_rep_of_rule uf_compress_rule)
find_theorems "_ \<le> _""_ \<Longrightarrow>\<^sub>A _"
find_theorems "<_> _ <_>" "_ \<Longrightarrow>\<^sub>A _ "
thm pre_rule''[OF _ gc_time]
lemma uf_rep_of_c_rule'': "\<lbrakk>invar_rank l rkl; i<length l; bw_ipc l i d l'\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4+d*4)> uf_rep_of_c p i <\<lambda>r.  (\<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> invar_rank l' rkl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)))>\<^sub>t"
proof goal_cases
  case 1
  hence d_def:"d = height_of l i" using height_of_ipc_equiv invar_rank_ufa_invarI by blast
  from 1 show ?case unfolding d_def 
  unfolding uf_rep_of_c_def apply -
  apply (frule invar_rank_ufa_invarI)
  by (sep_auto  heap: uf_rep_of_rule uf_compress_rule')
qed

lemma uf_rep_of_c_rule': "\<lbrakk>invar_rank l rkl; i<length l; bw_ipc l i d l'\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4+d*4)> uf_rep_of_c p i <\<lambda>r.  p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> invar_rank l' rkl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t"sorry


definition uf_rep_of_c_time where "uf_rep_of_c_time n = 2 * \<alpha>\<^sub>r (n + (\<rho> - 1)) + 4"

lemma frame_credits: "\<lbrakk> t'\<le>t; <P * $t'> f <Q> \<rbrakk> \<Longrightarrow> <P * $t> f <Q>" sorry



lemma uf_rep_of_c_rule''': "\<lbrakk>invar_rank l rkl; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4*(\<Phi> l rkl + uf_rep_of_c_time (length l)) )> uf_rep_of_c p i <\<lambda>r.\<exists>\<^sub>A l'. p\<mapsto>\<^sub>al' 
    *$(4* \<Phi> l' rkl) * \<up>(r=rep_of l i \<and> invar_rank l' rkl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t"
proof goal_cases
  case 1
  obtain d l' where bw: " bw_ipc l i d l'" " \<Phi> l' rkl + d < \<Phi> l rkl + 2 * \<alpha>\<^sub>r (length l + (\<rho> - 1))" using
      amortized_cost_of_iterated_path_compression_global[OF 1(1,2)] by blast
  hence potentialjump: "4*(\<Phi> l rkl + uf_rep_of_c_time (length l)) \<ge> 4*\<Phi> l' rkl + d*4 + 4" 
    unfolding uf_rep_of_c_time_def by fastforce
  show ?case apply (rule frame_credits) apply (rule potentialjump) using 1 bw(1)
    by (sep_auto heap: uf_rep_of_c_rule'[where d=d]) 
  qed
      
definition is_uf2 :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf2 R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al rkl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl 
    * \<up>(ufa_\<alpha> l = R \<and> length rkl = length l \<and> invar_rank l rkl)
    * $(\<Phi> l rkl * 10)"

thm ufa_\<alpha>_dom_card

subsubsection{*uf_cmp lemmas*}

definition uf_cmp_time where "uf_cmp_time n \<equiv> 2 * uf_rep_of_c_time n + 10"

lemma uf_cmp_rule: "\<lbrakk>invar_rank l rkl\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4*(\<Phi> l rkl + uf_cmp_time (length l)) )> 
  uf_cmp (s,p) i j 
  <\<lambda>r.\<exists>\<^sub>A l'. p\<mapsto>\<^sub>al' 
    *$(4* \<Phi> l' rkl) * \<up>((r\<longleftrightarrow>(rep_of l i = rep_of l j)) \<and> invar_rank l' rkl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t"
proof goal_cases
  case 1
  have sum1: "4 * \<Phi> l rkl +
        (8 * uf_rep_of_c_time (length l) + 40) = 4 * \<Phi> l rkl +
        (8 * uf_rep_of_c_time (length l) + 39) + 1" by algebra
  from 1 show ?case
unfolding uf_cmp_time_def uf_cmp_def
  apply vcg
  apply simp
  apply (subst sum1) apply (subst time_credit_add[of "(4 * \<Phi> l rkl +
        (8 * uf_rep_of_c_time (length l) + 39))" 1])
  apply (sep_auto heap: length_rule)
  apply safe proof goal_cases
  case (1 x)
  then show ?case 
  proof (cases "x \<le> i \<or> x \<le> j")
    case True
    then show ?thesis using 1 apply vcg 
    proof goal_cases
      case (1 x')
      hence " p \<mapsto>\<^sub>a l *
    $ (\<Phi> l rkl * 4 + uf_rep_of_c_time (length l) * 8 + 38) *
    \<up> (\<not> x') \<Longrightarrow>\<^sub>A p \<mapsto>\<^sub>a l * true * $ (4 * \<Phi> l rkl) *
       \<up> (x' = (rep_of l i = rep_of l j) \<and>
          invar_rank l rkl \<and>
          length l = length l \<and>
          (\<forall>i<length l. rep_of l i = rep_of l i))"  sorry
      then show ?case  using ent_ex_postI by fast
    qed
next
  case False
  have sum2: "\<Phi> l rkl * 4 + uf_rep_of_c_time (length l) * 8 + 39 
            = \<Phi> l rkl * 4 + uf_rep_of_c_time (length l) * 4 + uf_rep_of_c_time (length l) * 4 + 39" 
    by algebra
  have sep2: "$(\<Phi> l rkl * 4 + uf_rep_of_c_time (length l) * 4 +
            uf_rep_of_c_time (length l) * 4 +
            39)  =   $ (\<Phi> l rkl * 4 + uf_rep_of_c_time (length l) * 4) * 
            $ (uf_rep_of_c_time (length l) * 4 + 39)"
    using time_credit_add add.assoc[of "\<Phi> l rkl * 4 + uf_rep_of_c_time (length l) * 4" 
          "uf_rep_of_c_time (length l) * 4" 39] by presburger

  also have sep3: "\<dots> =    $ (4* (\<Phi> l rkl + uf_rep_of_c_time (length l))) * 
            $ (uf_rep_of_c_time (length l) * 4 + 39)" 
    by (simp add: mult.commute)
  have sep4: "p \<mapsto>\<^sub>a l *
         ($ (4 * (\<Phi> l rkl + uf_rep_of_c_time (length l))) *
          $ (uf_rep_of_c_time (length l) * 4 + 39)) = p \<mapsto>\<^sub>a l *
   $ (4 * (\<Phi> l rkl + uf_rep_of_c_time (length l))) *
   $ (uf_rep_of_c_time (length l) * 4 + 39 )" by simp
  have "i<x" "j<x" using False by auto
  with \<open>invar_rank l rkl\<close> show ?thesis apply auto apply vcg 
    apply (subst sum2)
     apply (subst sep2)
     apply (subst sep3)
     apply (subst sep4)
    apply (rule frame_rule[of "p \<mapsto>\<^sub>a l * $ (4 * (\<Phi> l rkl + uf_rep_of_c_time (length l)))" "uf_rep_of_c p i"
                   _ "$ (uf_rep_of_c_time (length l) * 4 + 39)" ] )
     apply (vcg heap: uf_rep_of_c_rule''' )
    apply vcg apply auto proof goal_cases
    case (1 x')
    then show ?case apply (vcg (ss)) apply (vcg (ss)) 
    proof goal_cases
      case (1 l')
      hence inv:"invar_rank l' rkl" by blast
      from 1 have ll': "length l = length l'" by argo
      have sum3: "4 * \<Phi> l' rkl + (uf_rep_of_c_time (length l) * 4 + 39) = 4 * (\<Phi> l' rkl +
        (uf_rep_of_c_time (length l))) + 39" by algebra
      have sep5: "p \<mapsto>\<^sub>a l' * true * $ (4 * (\<Phi> l' rkl + uf_rep_of_c_time (length l')) + 39) 
                = p \<mapsto>\<^sub>a l' *        $ (4 * (\<Phi> l' rkl + uf_rep_of_c_time (length l'))) * ($(39) * true)"        
        by (simp add: time_credit_add)
      from 1 ll' inv show ?case apply (subst sum3) apply (subst (asm) ll')+ apply (subst ll')+
        apply vcg apply (subst sep5)
        apply (rule frame_rule[of "p \<mapsto>\<^sub>a l' * $ (4 * (\<Phi> l' rkl + uf_rep_of_c_time (length l')))"
             "uf_rep_of_c p j" _ " ($ 39 * true)"])
         apply (vcg heap: uf_rep_of_c_rule''' )
        apply vcg
        apply auto
        apply vcg
        apply auto proof goal_cases
        case (1 l'')
        have "p \<mapsto>\<^sub>a l'' * true * $ (\<Phi> l'' rkl * 4 + 38) \<Longrightarrow>\<^sub>A
  p \<mapsto>\<^sub>a l'' * true * $ (4 * \<Phi> l'' rkl) *
  \<up> (invar_rank l'' rkl \<and>
     length l'' = length l' \<and>
     (\<forall>i<length l'. rep_of l'' i = rep_of l i))" using 1 apply sep_auto
          by (smt assn_times_assoc gc_time le_add1 match_first merge_true_star mult.commute)
        then  show ?case using ent_ex_postI by fast 
      qed
    qed
  qed   
qed
qed
qed


lemma cnv_to_ufa_\<alpha>_eq: 
  "\<lbrakk>(\<forall>i<length l. rep_of l' i = rep_of l i); length l = length l'\<rbrakk> 
  \<Longrightarrow> (ufa_\<alpha> l = ufa_\<alpha> l')"
  unfolding ufa_\<alpha>_def by auto

lemma "  card (Domain (ufa_\<alpha> l)) = length l"
  by simp


lemma uf_cmp_rule: "\<lbrakk>invar_rank l rkl\<rbrakk> \<Longrightarrow>
  <is_uf R u * $(uf_cmp_time (card (Domain R)))> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>\<^sub>t" 
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
