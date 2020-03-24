theory Union_Find_Time_alpha_verification
  imports Union_Find_Time_alpha_abstract_analysis Union_Find_Time_alpha_fix
begin


subsubsection\<open>uf_init_lemmas\<close>

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al rkl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl 
    * \<up>(ufa_\<alpha> l = R \<and> length rkl = length l \<and> invar_rank l rkl)
    * $(\<Phi> l rkl * 4)"

lemma of_list_rule':
    "<$ (1 + n)> Array_Time.of_list [0..<n] <\<lambda>r. r \<mapsto>\<^sub>a [0..<n]>"
  by (sep_auto heap: of_list_rule[of "[0..<n]", simplified])

lemma \<Phi>_init_value: "\<Phi> [0..<n] (replicate n 0) = 2*n"  
    by (simp add: \<phi>_def rankr_def \<rho>_def alphar_r)  

definition uf_init_time :: "nat \<Rightarrow> nat" where "uf_init_time n \<equiv> 4*(2*n+3+2*n)"

lemma uf_init_bound[asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n. n)" 
  unfolding uf_init_time_def by auto2

lemmas \<Phi>_simp[simp del]  
lemma uf_init_rule':
    "<$(uf_init_time n)> uf_init n <is_uf {(i,i) |i. i<n}  >\<^sub>t" 
  unfolding uf_init_time_def uf_init_def is_uf_def 
  apply (sep_auto heap: of_list_rule' eintros del: exI) 
  apply(rule exI[where x="[0..<n]"])  
  apply(rule exI[where x="replicate n 0"]) 
  by (sep_auto simp add: ufa_init_correct ufa_init_invar_rank \<Phi>_init_value)

subsubsection\<open>uf_rep_of lemmas\<close>

lemma uf_rep_of_rule: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(height_of l i + 2)> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>\<^sub>t"
  by (induct rule: rep_of_induct)
     (sep_auto simp: uf_rep_of.simps rep_of_step rep_of_refl height_of_step)+

subsubsection\<open>uf_compress lemmas\<close>

lemma compress_invar_rank':
  assumes "invar_rank l rkl" "i<length l" "u=rep_of l i"
  shows "invar_rank (l[i := u]) rkl"
  by (metis assms(1,2,3) compress_evolution invar_rank_evolution list_update_id rep_of_refl)

lemma uf_compress_rule_explicit:
  assumes "invar_rank l rkl" "i<length l" "ci=rep_of l i" "bw_ipc l i d l'"
  shows "<p\<mapsto>\<^sub>al * $(1+d*3)>
           uf_compress i ci p 
        <\<lambda>_. (p\<mapsto>\<^sub>al' * \<up>(invar_rank l' rkl \<and> length l' = length l 
                        \<and> (\<forall>i<length l. rep_of l' i = rep_of l i)) )>\<^sub>t"
  using assms(4,1-3)
proof (induct rule: bw_ipc.induct)
  case (BWIPCBase x l)
  hence "x = rep_of l x" using rep_of_refl by auto
  with BWIPCBase show ?case by (sep_auto simp: uf_compress.simps)
next
  case (BWIPCStep x y l i l')
  hence "y<length l" unfolding ufa_\<beta>_start_def by fast
  have "ufa_invar l" using invar_rank_ufa_invarI[OF BWIPCStep(4)] .
  hence "ci<length l" using BWIPCStep rep_of_bound by auto
  have "(x,y)\<in> (ufa_\<beta>_start l)\<^sup>*" using BWIPCStep by blast
  have "y = l!x" using BWIPCStep(1) unfolding ufa_\<beta>_start_def by blast
  have "rep_of l y = ci" 
    using rep_of_invar_along_path[OF \<open>ufa_invar l\<close> \<open>ci<length l\<close> \<open>y<length l\<close> \<open>x<length l\<close> 
        \<open>ci=rep_of l x\<close> \<open>(x,y)\<in> (ufa_\<beta>_start l)\<^sup>*\<close>] by blast
  have ipcx: "bw_ipc l x (Suc i) (l'[x := rep_of l x])" using  bw_ipc.intros(2)[OF BWIPCStep(1,2)] .
  have IH: "<p \<mapsto>\<^sub>a l * $ (1 + i * 3)>
              uf_compress (l!x) (rep_of l x) p
           <\<lambda>r. p \<mapsto>\<^sub>a l' * \<up> (invar_rank l' rkl \<and> length l' = length l
                               \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t" 
    using BWIPCStep(3)[OF \<open>invar_rank l rkl\<close> \<open>y<length l\<close>  \<open>rep_of l y = ci\<close>[symmetric]]
           \<open>ci = rep_of l x\<close> \<open>y = l!x\<close> by blast
  show ?case 
  proof (cases "x = ci")
    case True
    hence "x = l!x"
      using \<open>ci = rep_of l x\<close> BWIPCStep.prems(2) \<open>ufa_invar l\<close> rep_of_min by fastforce
    then have "bw_ipc l x 0 l" by (rule bw_ipc.intros)
    hence " Suc i = 0" 
      using bw_ipc_root_unique  \<open>x = l!x\<close> \<open>bw_ipc l x (Suc i) (l'[x := rep_of l x])\<close>   by auto
    then show ?thesis by simp
  next
    case False 
    thus ?thesis 
      apply (subst uf_compress.simps)   
      by (sep_auto heap: IH intro: compress_invar_rank' dest: invar_rank_ufa_invarI
          simp: \<open>x<length l\<close> \<open>ci = rep_of l x\<close> ufa_compress_rep_of )
  qed
qed


subsubsection\<open>uf_rep_of_c lemmas\<close>

lemma uf_rep_of_c_rule_explicit:
  assumes "invar_rank l rkl" "i<length l" "bw_ipc l i d l'"
  shows"<p\<mapsto>\<^sub>al * $(4+d*4)>
             uf_rep_of_c p i 
        <\<lambda>r. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> invar_rank l' rkl
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t"
proof -
  have "ufa_invar l" using invar_rank_ufa_invarI[OF assms(1)] .
  show ?thesis unfolding uf_rep_of_c_def 
    apply (subst height_of_ipc_equiv[OF assms(3) \<open>ufa_invar l\<close> assms(2)])
    using assms \<open>ufa_invar l\<close>
    apply (sep_auto heap: uf_rep_of_rule) 
     apply (subst height_of_ipc_equiv[OF assms(3) \<open>ufa_invar l\<close> assms(2), symmetric])
     apply (sep_auto heap: uf_compress_rule_explicit[where d = d])
    by sep_auto
qed

definition uf_rep_of_c_time where "uf_rep_of_c_time n = 8 * \<alpha>\<^sub>r (n + (\<rho> - 1))"

lemma uf_rep_of_c_rule: "\<lbrakk>invar_rank l rkl; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al * $(4* \<Phi> l rkl + uf_rep_of_c_time (length l))> uf_rep_of_c p i <\<lambda>r.\<exists>\<^sub>A l'. p\<mapsto>\<^sub>al' 
    *$(4* \<Phi> l' rkl) * \<up>(r=rep_of l i \<and> invar_rank l' rkl
       \<and> length l = length l'  \<and> ufa_\<alpha> l = ufa_\<alpha> l'
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t"
proof goal_cases
  case 1
  obtain d l' where bw: "bw_ipc l i d l'" " \<Phi> l' rkl + d < \<Phi> l rkl + 2 * \<alpha>\<^sub>r (length l + (\<rho> - 1))"
    using amortized_cost_of_iterated_path_compression_global[OF 1(1,2)] by blast
  hence potentialjump: "4*\<Phi> l rkl + uf_rep_of_c_time (length l) \<ge> 4*\<Phi> l' rkl + d*4 + 4" 
    unfolding uf_rep_of_c_time_def by fastforce
  have sep: "4 * \<Phi> l rkl + uf_rep_of_c_time (length l) =
           4 * \<Phi> l' rkl + d * 4 + 4 + (4 * \<Phi> l rkl + uf_rep_of_c_time (length l)
           - (4 * \<Phi> l' rkl + d * 4 + 4))" 
    using add_diff_inverse potentialjump by simp
  show ?case
    apply (subst sep) 
    using 1 bw by (sep_auto heap: uf_rep_of_c_rule_explicit[where d=d] intro!: ufa_\<alpha>I)
qed

\<comment>\<open>lemma "(\<lambda>n. \<alpha> (n+1)) \<in> \<Theta>(\<lambda>n. \<alpha> n)" 

lemma "(\<lambda>x. 20  + 8 * real (\<alpha> (x + 1)))
  \<in> \<Theta>(\<lambda>x. real (\<alpha> x))" unfolding \<rho>_def apply auto2

lemma uf_rep_of_c_time2_asym: "uf_rep_of_c_time2 \<in> \<Theta>(\<lambda>n. \<alpha> n)"
  unfolding uf_rep_of_c_time2_def using alphar_one[OF \<rho>_gt_0 ] \<rho>_def apply simp
  apply auto2 \<close>

subsubsection\<open>uf_cmp lemmas\<close>

definition uf_cmp_time where "uf_cmp_time n \<equiv> 2 * uf_rep_of_c_time n + 2"

lemma uf_cmp_rule: assumes "invar_rank l rkl" "i<length l" "j<length l"
  shows "<p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl* $(\<Phi> l rkl * 4 + uf_cmp_time (length l) )> 
          uf_cmp (s,p) i j 
        <\<lambda>r.\<exists>\<^sub>A l'. p\<mapsto>\<^sub>al' * s\<mapsto>\<^sub>arkl * $(\<Phi> l' rkl * 4)
             * \<up>((r\<longleftrightarrow>(rep_of l i = rep_of l j)) \<and> invar_rank l' rkl
                  \<and> length l' = length l  \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>\<^sub>t"
    using assms
    by (sep_auto simp: uf_cmp_time_def uf_cmp_def 
                 heap: uf_rep_of_c_rule[where rkl=rkl])

lemma ufa_\<alpha>_out_of_bounds: "i \<ge> length l \<or> j \<ge> length l \<Longrightarrow> (i, j) \<in> ufa_\<alpha> l = False" 
      using leD ufa_\<alpha>_lenD by force 

lemma uf_cmp_rule_out_of_bounds: assumes "invar_rank l rkl" "i \<ge> length l \<or> j \<ge> length l"
  shows "<p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl* $(\<Phi> l rkl * 4 + uf_cmp_time (length l) )> 
    uf_cmp (s,p) i j 
  <\<lambda>r. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>arkl * $(\<Phi> l rkl * 4) * \<up>((\<not> r) \<and> invar_rank l rkl)>\<^sub>t"
  using assms by (sep_auto simp: uf_cmp_def uf_cmp_time_def)

lemma uf_cmp_rule_abstract:
  "<is_uf R u * $(uf_cmp_time (card (Domain R)))> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>\<^sub>t" 
  apply (sep_auto split: prod.splits simp: is_uf_def)
  subgoal for s p l rkl
    apply (cases "i< length l \<and> j < length l") 
    subgoal by (sep_auto heap: uf_cmp_rule simp: ufa_\<alpha>_def)
    subgoal by (sep_auto heap: uf_cmp_rule_out_of_bounds simp: ufa_\<alpha>_out_of_bounds)
    done
  done

subsubsection\<open>uf_union_lemmas\<close>


definition "uf_union_time n = 13 + uf_rep_of_c_time n * 2"

definition uf_union_snd :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>  nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union_snd r p ci cj i j \<equiv> do {
    if (ci=cj) then return (r,p) 
    else do {
      ri \<leftarrow> Array_Time.nth r ci;
      rj \<leftarrow> Array_Time.nth r cj;
      if ri<rj then do {
        Array_Time.upd ci cj p;
         return (r,p)
      } else do { 
        Array_Time.upd cj ci p;
        if (ri=rj) then do {
            Array_Time.upd ci (ri+1) r;
            return (r,p)
        } else return (r,p)
      }
    }
  }"

lemma uf_union_parts: "uf_union u i j \<equiv> do {
    let (r,p)=u;
    ci \<leftarrow> uf_rep_of_c p i;
    cj \<leftarrow> uf_rep_of_c p j;
    uf_union_snd r p ci cj i j
  }" unfolding uf_union_def uf_union_snd_def by simp

lemma ufa_union_rep_of: assumes "ufa_invar l" "i<length l" "j<length l"
  shows "ufa_union l i j = ufa_union l (rep_of l i) (rep_of l j)"
proof -
  have sub1: "rep_of l (rep_of l i) = rep_of l i" using assms using rep_of_idem by blast
  have sub2: "rep_of l (rep_of l j) = rep_of l j" using assms using rep_of_idem by blast
  show ?thesis apply (subst sub1) apply (subst sub2) ..
qed

lemma per_union_same :
  "i < length l'' \<Longrightarrow> j < length l''
     \<Longrightarrow> rep_of l'' i = rep_of l'' j  \<Longrightarrow> invar_rank l'' rkl
     \<Longrightarrow>  (aa, bb) \<in> per_union (ufa_\<alpha> l'') i j \<Longrightarrow> (aa, bb) \<in> ufa_\<alpha> l''"
  by (metis invar_rank_ufa_invarI list_update_id rep_of_bound rep_of_path_iff ufa_union_correct)  
 
lemma EvUnion':
  assumes "x<length l" "y<length l" "x=l!x" "y=l!y" "x\<noteq>y"
    "newl = (union_by_rank_l l rkl x y)" "newrkl = (union_by_rank_rkl rkl x y)"
  shows "evolution l rkl newl newrkl"
  unfolding assms(6,7) apply(rule EvUnion) by fact+ 

lemma per_union_union_by_rank_l: 
  assumes "ufa_invar l" "i < length l" "j < length l"
  shows "ufa_\<alpha> (union_by_rank_l l rkl (rep_of l i) (rep_of l j))
        = per_union (ufa_\<alpha> l) i j"
  using assms
  unfolding union_by_rank_l_def 
  by (auto simp: ufa_union_rep_of[symmetric] ufa_union_correct intro: rep_of_bound)



lemma 
  fixes l rkl i j
  defines "rkl' \<equiv> union_by_rank_rkl rkl (rep_of l i) (rep_of l j)" and
    "l' \<equiv> union_by_rank_l l rkl (rep_of l i) (rep_of l j)"  
  assumes
    "length rkl = length l" "invar_rank l rkl"
    "i < length l" "j < length l"
    "rep_of l i \<noteq> rep_of l j"
  shows uf_union_snd_over_aprox:
    "p \<mapsto>\<^sub>a l' * r \<mapsto>\<^sub>a rkl' * true * $ (\<Phi> l rkl * 4 + 8)
       \<Longrightarrow>\<^sub>A p \<mapsto>\<^sub>a l' * r \<mapsto>\<^sub>a rkl' * true * $ (\<Phi> l' rkl' * 4)"
proof -
  have "ufa_invar l" using invar_rank_ufa_invarI assms by auto

  have ineq: "\<Phi> l' rkl'\<le> \<Phi> l rkl + 2"
    unfolding rkl'_def l'_def
    apply(rule potential_increase_during_link) 
    using assms
    by (auto intro: invar_rank_ufa_invarI rep_of_bound rep_of_min[symmetric])
  then have ineq: "\<Phi> l' rkl' * 4 \<le> \<Phi> l rkl * 4 + 8" 
    by linarith 
  from le_Suc_ex[OF ineq] obtain R where
    R: "\<Phi> l rkl * 4 + 8 = \<Phi> l' rkl' * 4 + R"
    by blast
  show ?thesis   
    apply(subst R) unfolding l'_def rkl'_def by(sep_auto)
qed

lemma uf_union_snd_rule:
  fixes l rkl i j
  defines "rkl' \<equiv> (if rep_of l i = rep_of l j then rkl else union_by_rank_rkl rkl (rep_of l i) (rep_of l j))"
    and   "l' \<equiv> (if rep_of l i = rep_of l j then l else union_by_rank_l l rkl (rep_of l i) (rep_of l j))"
  assumes "length rkl = length l" "invar_rank l rkl " "i<length l" "j<length l"
        "rep_of l i = ci" "rep_of l j = cj"
  shows "<p \<mapsto>\<^sub>a l * r \<mapsto>\<^sub>a rkl * $(\<Phi> l rkl * 4 + 13)> 
      uf_union_snd r p ci cj i j
     <\<lambda>(r',p'). p' \<mapsto>\<^sub>a l' * r' \<mapsto>\<^sub>a rkl' * $ (\<Phi> l' rkl' * 4)
          * \<up> (ufa_\<alpha> l' = per_union (ufa_\<alpha> l) i j \<and> length rkl = length l' \<and> invar_rank l' rkl')>\<^sub>t"
  unfolding uf_union_snd_def uf_union_time_def  
  using assms
  apply sep_auto
  subgoal
    by (simp add: union_by_rank_l_def per_union_impl)
  subgoal for l' la h
    by (auto simp: per_union_same) 
  subgoal by sep_auto
  subgoal 
    apply(cases "rkl ! rep_of l i" "rkl ! rep_of l j" rule: linorder_cases)
    subgoal (* rank of i's representant < rank of j's representant *)
      apply(sep_auto intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal  apply(subst per_union_union_by_rank_l[symmetric]) 
        by (auto  intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal  apply(subst per_union_union_by_rank_l) 
        by (auto  intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal
        apply(rule invar_rank_evolution)
         apply simp
        apply(rule EvUnion'[where x="rep_of l i" and y="rep_of l j"])
        by (auto intro: invar_rank_ufa_invarI rep_of_bound rep_of_min[symmetric]
            simp: union_by_rank_l_def union_by_rank_rkl_def
            ufa_union_rep_of  )
      subgoal
        apply(rule ent_trans[where Q="p \<mapsto>\<^sub>a union_by_rank_l l rkl (rep_of l i) (rep_of l j)
                                     * r \<mapsto>\<^sub>a union_by_rank_rkl rkl (rep_of l i) (rep_of l j) 
                                     * true * $ (\<Phi> l rkl * 4 + 8)"] )
        subgoal apply (sep_auto simp: union_by_rank_rkl_def union_by_rank_l_def intro: invar_rank_ufa_invarI )
          apply(subst ufa_union_rep_of[symmetric])
             apply (auto intro: invar_rank_ufa_invarI)
          by (sep_auto)
        subgoal by (rule uf_union_snd_over_aprox)    
        done
      subgoal by sep_auto
      done
    subgoal (* rank of i's representant = rank of j's representant *)
      apply(sep_auto intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal  apply(subst per_union_union_by_rank_l[symmetric]) 
        by (auto  intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal  apply(subst per_union_union_by_rank_l) 
        by (auto  intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal
        apply(rule invar_rank_evolution)
         apply simp
        apply(rule EvUnion'[where x="rep_of l i" and y="rep_of l j"])
        by (auto intro: invar_rank_ufa_invarI rep_of_bound rep_of_min[symmetric]
            simp: union_by_rank_l_def union_by_rank_rkl_def
            ufa_union_rep_of  )
      subgoal
        apply(rule ent_trans[where Q="p \<mapsto>\<^sub>a union_by_rank_l l rkl (rep_of l i) (rep_of l j)
                                     * r \<mapsto>\<^sub>a union_by_rank_rkl rkl (rep_of l i) (rep_of l j) 
                                     * true * $ (\<Phi> l rkl * 4 + 8)"] )
        subgoal apply (sep_auto simp: union_by_rank_rkl_def union_by_rank_l_def )
          apply(subst ufa_union_rep_of[symmetric])
             apply (auto intro: invar_rank_ufa_invarI)
          by (sep_auto)
        subgoal by (rule uf_union_snd_over_aprox)    
        done
      subgoal by sep_auto
      subgoal by sep_auto
      done
    subgoal (* rank of i's representant > rank of j's representant *)
      apply(sep_auto intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal  apply(subst per_union_union_by_rank_l[symmetric]) 
        by (auto  intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal  apply(subst per_union_union_by_rank_l) 
        by (auto  intro: rep_of_bound invar_rank_ufa_invarI)
      subgoal
        apply(rule invar_rank_evolution)
         apply simp
        apply(rule EvUnion'[where x="rep_of l i" and y="rep_of l j"])
        by (auto intro: invar_rank_ufa_invarI rep_of_bound rep_of_min[symmetric]
            simp: union_by_rank_l_def union_by_rank_rkl_def
            ufa_union_rep_of  )
      subgoal      
        apply(rule ent_trans[where Q="p \<mapsto>\<^sub>a union_by_rank_l l rkl (rep_of l i) (rep_of l j)
                                     * r \<mapsto>\<^sub>a union_by_rank_rkl rkl (rep_of l i) (rep_of l j) 
                                     * true * $ (\<Phi> l rkl * 4 + 8)"] )
        subgoal apply (sep_auto simp: union_by_rank_rkl_def union_by_rank_l_def )
          apply(subst ufa_union_rep_of[symmetric])
             apply (auto intro: invar_rank_ufa_invarI)
          by (sep_auto)
        subgoal by (rule uf_union_snd_over_aprox)    
        done
      done
    done
  done

lemma uf_union_rule: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u * $(uf_union_time (card (Domain R)))>
         uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  unfolding uf_union_time_def is_uf_def
  apply (sep_auto split: prod.splits)
  subgoal for r p _ _ l rkl
    apply(drule ufa_\<alpha>_lenD(1))
    apply(drule ufa_\<alpha>_lenD(1))
    by (sep_auto simp: uf_union_parts heap: uf_rep_of_c_rule[where rkl=rkl] uf_union_snd_rule )
  done 


interpretation UnionFind_Impl is_uf uf_init uf_init_time uf_cmp uf_cmp_time uf_union uf_union_time
proof (unfold_locales, goal_cases)
case (1 t x' x)
  show ?case
    unfolding PR_CONST_def mop_per_init_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_init_rule', where Cost_lb="uf_init_time x"])
      apply (sep_auto simp: per_init'_def hn_ctxt_def pure_def)+
    using 1 by simp
next
  case (2 t R' R a' a b' b)
   show ?case 
    unfolding PR_CONST_def mop_per_compare_def apply simp
    apply(rule extract_cost_otherway'[OF _ uf_cmp_rule_abstract, where Cost_lb="(uf_cmp_time (card (Domain R')))"])
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

thy_deps(Partial_Equivalence_Relation|Sepref|Asymptotics_1D|InverseNatNat)
unused_thms
end
