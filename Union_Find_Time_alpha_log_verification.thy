theory Union_Find_Time_alpha_log_verification
  imports Union_Find_Time_alpha_abstract_analysis Union_Find_Time_alpha
  UnionFind_Intf
begin

subsubsection{*uf_init_lemmas*}

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al szl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>aszl 
    * \<up>(ufa_invar l \<and> ufa_\<alpha> l = R \<and> length szl = length l \<and> invar l szl)"


lemma of_list_rule':
    "<$ (1 + n)> Array_Time.of_list [0..<n] <\<lambda>r. r \<mapsto>\<^sub>a [0..<n]>"
  using of_list_rule[of "[0..<n]"] by auto 

lemma height_of_init: "j<n \<Longrightarrow> height_of [0..<n] j = 0"
  by (simp add: height_of.psimps ufa_init_invar ufa_invarD(1))

lemma h_of_init: "i < n \<Longrightarrow> h_of [0..<n] i = 0"
  unfolding h_of_def apply auto
  apply(rule antisym) 
  subgoal apply(rule Max.boundedI)
     apply simp
    using ufa_init_invar apply auto apply(rule exI[where x=i]) apply simp
    subgoal  
      by (simp add: rep_of_refl)  
    apply(rule height_of_init) by simp
  by simp 

lemma ufa_init_invar': "invar [0..<n] (replicate n (Suc 0))"
  unfolding invar_def apply auto using h_of_init by auto

definition uf_init_time :: "nat \<Rightarrow> nat" where "uf_init_time n == (2*n+3)"

lemma uf_init_bound[asym_bound]: "uf_init_time \<in> \<Theta>(\<lambda>n. n)" 
  unfolding uf_init_time_def by auto2

lemma uf_init_rule: 
  "<$(uf_init_time n)> uf_init n <is_uf {(i,i) |i. i<n}>\<^sub>t"
  unfolding uf_init_time_def uf_init_def is_uf_def[abs_def]
  by (sep_auto simp: ufa_init_correct ufa_init_invar ufa_init_invar' zero_time heap: of_list_rule')
 

subsubsection{*uf_rep_of lemmas*}

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

thm uf_rep_of_c_rule_ub
lemma uf_cmp_rule:
  "<is_uf R u * $(uf_cmp_time (card (Domain R)))> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>\<^sub>t" 
  unfolding uf_cmp_def is_uf_def uf_cmp_time_def
  apply (sep_auto heap: uf_rep_of_c_rule_ub length_rule dest: ufa_\<alpha>_lenD simp: not_le split: prod.split)
   apply(rule fi_rule[OF uf_rep_of_c_rule_ub]) defer defer defer
      apply(simp only: mult.assoc)
  apply(rule match_first)      
      apply simp 
      apply(time_frame_inference)
     defer apply simp apply simp apply simp
  apply(sep_auto) 
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (subst ufa_find_correct)
  by (auto simp add: ) 
  

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




lemma 12:
  assumes "i < length l " "j < length l" 
       "ufa_invar l " "(i, j) \<notin> ufa_\<alpha> l "
     and size:  "szl ! rep_of l i < szl ! rep_of l j  "
  and i:  "invar l szl "
      shows "invar (ufa_union l i j) (szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j])"
proof - 
  let ?upd = "ufa_union l i j"

  from i have [simp]: "length szl = length l" unfolding invar_def by auto

  { fix a b and f :: "'a\<Rightarrow>nat" have r: "a\<noteq>b \<Longrightarrow> sum f {a,b}   = f a + f b" by simp     }
  note ff=this

  have *: "{0..<length l} = ({0..<length l}-{rep_of l j}) \<union> {rep_of l j}" 
    using assms rep_of_bound by auto  
  have **:"{0..<length l} = ({0..<length l}-{rep_of l i,rep_of l j}) \<union> {rep_of l i,rep_of l j}" 
    using assms rep_of_bound by auto  

  have ss: "(({0..<length l} - {rep_of l j}) \<inter> {ia. ?upd ! ia = ia})
        = ({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia}" using assms by (auto simp: nth_list_update') 


  have "(\<Sum>ia = 0..<length l. if ?upd ! ia = ia then szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0)
     = sum (\<lambda>ia. if ?upd ! ia = ia then szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0) ({0..<length l}-{rep_of l j})
            + (szl ! rep_of l i + szl ! rep_of l j)" (is "?A = _")
    apply(subst *)  apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply safe 
    subgoal using assms rep_of_bound  
      using invar_def by fastforce  
    subgoal using assms  
      by (simp add: rep_of_min ufa_find_correct)  
    subgoal using assms  
      by (simp add: rep_of_min ufa_find_correct) 
    done 
  also have "\<dots> = sum (\<lambda>i. if l ! i = i then szl ! i else 0)
                         ({0..<length l}-{rep_of l i,rep_of l j})
               + (szl ! rep_of l i + szl ! rep_of l j)" (is "?L + _ = ?R + _")
  proof -
    have "?L = sum (\<lambda>ia. szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l j})\<inter>{ia. ?upd ! ia = ia})"
      apply(subst sum.inter_restrict) by simp_all
    also have "\<dots> = sum (\<lambda>ia. szl[rep_of l j := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia})"
      unfolding ss by simp
    also have "\<dots> = ?R"
      apply(subst sum.inter_restrict) apply simp apply auto apply(rule sum.cong) apply simp using assms by auto  
    finally have "?L = ?R" .
    then show ?thesis by simp
  qed  
  also have "\<dots> = (\<Sum>i = 0..<length l. if l ! i = i then szl ! i else 0)"
    apply(subst (2) **) apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply(subst ff) using assms apply (auto simp: rep_of_min) 
    done
  also from i have "\<dots> = length l" unfolding invar_def by auto
  finally have A: "?A = length l" .
    
  have max_distrib: "\<And>a b :: nat. (2::nat) ^ max a b = max (2 ^ a) (2 ^ b)" 
    by (simp add: max_def)  
  { 
    assume a: "rep_of l j < length szl" "?upd ! rep_of l j = rep_of l j"  
    
    from i have g: "\<And>i. i<length l \<Longrightarrow> l ! i = i \<Longrightarrow> 2 ^ h_of l i \<le> szl ! i" unfolding invar_def by metis
    
    have "(2::nat) ^ (max (h_of l (rep_of l j)) (Suc (h_of l (rep_of l i))))
          \<le> max ( (szl ! (rep_of l j))) (2 * (szl ! (rep_of l i)))"
      apply(subst max_distrib) 
      apply(rule max.mono)
      subgoal apply(rule g) using assms a by (auto simp: rep_of_min)    
      subgoal apply(simp only: power.power_Suc) apply(rule mult_left_mono)
        apply(rule g) using assms a by (auto simp: rep_of_refl rep_of_min rep_of_bound)    
      done
    also have "\<dots> \<le> szl ! rep_of l i + szl ! rep_of l j"
      using size by auto
    finally
    have "2 ^ max (h_of l (rep_of l j)) (Suc (h_of l (rep_of l i))) \<le> szl ! rep_of l i + szl ! rep_of l j"
      .
  } note absch = this

  show ?thesis unfolding invar_def
    apply safe
    subgoal using i[unfolded invar_def] by simp
    subgoal apply simp using A by simp
    subgoal for i apply(cases "i=rep_of l j")
      subgoal apply simp
        apply(rule order.trans)
         apply(rule power_increasing[OF h_of_uf_union_touched])
                prefer 9
        subgoal using absch by simp
        using assms by (auto simp: rep_of_idem) 
      subgoal 
        apply simp apply(subst h_of_uf_union_untouched) 
               prefer 8 subgoal
          using i unfolding invar_def 
          by (metis nth_list_update')            
        using assms apply (auto simp: rep_of_idem )  
        by (metis nth_list_update')  
      done
    done
qed

lemma 21:
  assumes "i < length l "" j < length l ""
       ufa_invar l "
       "(i, j) \<notin> ufa_\<alpha> l "
   and size: "\<not> szl ! rep_of l i < szl ! rep_of l j  "
  and i: "invar l szl "
      shows "invar (ufa_union l j i) (szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j])"
proof - 
  let ?upd = "ufa_union l j i"

  from i have [simp]: "length szl = length l" unfolding invar_def by auto

  { fix a b and f :: "'a\<Rightarrow>nat" have r: "a\<noteq>b \<Longrightarrow> sum f {a,b}   = f a + f b" by simp     }
  note ff=this

  have *: "{0..<length l} = ({0..<length l}-{rep_of l i}) \<union> {rep_of l i}" 
    using assms rep_of_bound by auto  
  have **:"{0..<length l} = ({0..<length l}-{rep_of l i,rep_of l j}) \<union> {rep_of l i,rep_of l j}" 
    using assms rep_of_bound by auto  

  have ss: "(({0..<length l} - {rep_of l i}) \<inter> {ia. ?upd ! ia = ia})
        = ({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia}" using assms by (auto simp: nth_list_update') 


  have "(\<Sum>ia = 0..<length l. if ?upd ! ia = ia then szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0)
     = sum (\<lambda>ia. if ?upd ! ia = ia then szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia else 0) ({0..<length l}-{rep_of l i})
            + (szl ! rep_of l i + szl ! rep_of l j)" (is "?A = _")
    apply(subst *)  apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply safe 
    subgoal using assms rep_of_bound  
      using invar_def by fastforce  
    subgoal using assms   
      using rep_of_min ufa_find_correct by fastforce  
    subgoal using assms  
      using rep_of_min ufa_find_correct by fastforce   
    done 
  also have "\<dots> = sum (\<lambda>i. if l ! i = i then szl ! i else 0)
                         ({0..<length l}-{rep_of l i,rep_of l j})
               + (szl ! rep_of l i + szl ! rep_of l j)" (is "?L + _ = ?R + _")
  proof -
    have "?L = sum (\<lambda>ia. szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l i})\<inter>{ia. ?upd ! ia = ia})"
      apply(subst sum.inter_restrict) by simp_all
    also have "\<dots> = sum (\<lambda>ia. szl[rep_of l i := szl ! rep_of l i + szl ! rep_of l j] ! ia)
                 (({0..<length l}-{rep_of l i,rep_of l j}) \<inter> {ia. l ! ia = ia})"
      unfolding ss by simp
    also have "\<dots> = ?R"
      apply(subst sum.inter_restrict) apply simp apply auto apply(rule sum.cong) apply simp using assms by auto  
    finally have "?L = ?R" .
    then show ?thesis by simp
  qed  
  also have "\<dots> = (\<Sum>i = 0..<length l. if l ! i = i then szl ! i else 0)"
    apply(subst (2) **) apply(subst sum_Un_nat) apply simp apply simp apply simp
    apply(subst ff) using assms apply (auto simp: rep_of_min) 
    using ufa_find_correct by blast
  also from i have "\<dots> = length l" unfolding invar_def by auto
  finally have A: "?A = length l" .
    
  have max_distrib: "\<And>a b :: nat. (2::nat) ^ max a b = max (2 ^ a) (2 ^ b)" 
    by (simp add: max_def)  
  { 
    assume a: "rep_of l i < length szl" "?upd ! rep_of l i = rep_of l i"  
    
    from i have g: "\<And>i. i<length l \<Longrightarrow> l ! i = i \<Longrightarrow> 2 ^ h_of l i \<le> szl ! i" unfolding invar_def by metis
    
    have "(2::nat) ^ (max (h_of l (rep_of l i)) (Suc (h_of l (rep_of l j))))
          \<le> max ( (szl ! (rep_of l i))) (2 * (szl ! (rep_of l j)))"
      apply(subst max_distrib) 
      apply(rule max.mono)
      subgoal apply(rule g) using assms a by (auto simp: rep_of_min)    
      subgoal apply(simp only: power.power_Suc) apply(rule mult_left_mono)
        apply(rule g) using assms a by (auto simp: rep_of_refl rep_of_min rep_of_bound)    
      done
    also have "\<dots> \<le> szl ! rep_of l i + szl ! rep_of l j"
      using size by auto
    finally
    have "2 ^ max (h_of l (rep_of l i)) (Suc (h_of l (rep_of l j))) \<le> szl ! rep_of l i + szl ! rep_of l j"
      .
  } note absch = this

  show ?thesis unfolding invar_def
    apply safe
    subgoal using i[unfolded invar_def] by simp
    subgoal apply simp using A by simp
    subgoal for e apply(cases "e=rep_of l i")
      subgoal apply simp
        apply(rule order.trans)
         apply(rule power_increasing[OF h_of_uf_union_touched])
                prefer 9
        subgoal using absch by simp
        using assms by (auto simp: rep_of_idem ufa_find_correct)   
      subgoal 
        apply simp apply(subst h_of_uf_union_untouched) 
               prefer 8 subgoal
          using i unfolding invar_def 
          by (metis nth_list_update')            
        using assms apply (auto simp: rep_of_idem )  
        by (metis nth_list_update')  
      done
    done
qed

 

lemma uf_union_rule': "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u * $(11+ height_ub (card (Domain R))*2)> uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  unfolding uf_union_def
  apply (cases u)
  apply (simp add: is_uf_def[abs_def])
  apply(sep_auto heap: uf_rep_of_rule_ub)
    apply(simp add: ufa_\<alpha>_lenD)
  apply simp
  apply(sep_auto heap: uf_rep_of_rule_ub)
    apply(simp add: ufa_\<alpha>_lenD)
   apply simp
  apply (sep_auto
    simp: per_union_cmp ufa_\<alpha>_lenD ufa_find_correct
    rep_of_bound
    ufa_union_invar
    ufa_union_correct
  )
  subgoal apply(drule ufa_\<alpha>_lenD) apply(drule ufa_\<alpha>_lenD) using 12[of i _ j] sorry(*by blast*)
  apply (sep_auto
    simp: per_union_cmp ufa_\<alpha>_lenD ufa_find_correct
    rep_of_bound
    ufa_union_invar
    ufa_union_correct
  )
  subgoal apply(drule ufa_\<alpha>_lenD) apply(drule ufa_\<alpha>_lenD) using 21 sorry (*by blast *)
  sorry


definition "uf_union_time n = 11+ height_ub n*2"

lemma uf_union_time_bound[asym_bound]: "uf_union_time \<in> \<Theta>(\<lambda>n. ln n)"
  unfolding uf_union_time_def by auto2

lemma uf_union_rule: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u * $(uf_union_time (card (Domain R)))> uf_union u i j <is_uf (per_union R i j)>\<^sub>t"
  unfolding uf_union_time_def using uf_union_rule' by auto


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