theory Union_Find_Time_alpha_abstract_analysis

imports 
  "../../SepLog_Automatic" 
  "../../Refine_Imperative_HOL/Sepref_Additional" 
  Collections.Partial_Equivalence_Relation
  "HOL-Library.Code_Target_Numeral"
  \<comment>\<open>"SepLogicTime_RBTreeBasic.Asymptotics_1D"\<close>
  UnionFind_Impl
  Ackermann
begin

notation timeCredit_assn  ("$") 

text {*
  We implement a simple union-find data-structure based on an array.
  It uses path compression and a size-based union heuristics.
*}

subsection {* Abstract Union-Find on Lists *}
text {*
  We first formulate union-find structures on lists, and later implement 
  them using Imperative/HOL. This is a separation of proof concerns
  between proving the algorithmic idea correct and generating the verification
  conditions.
*}

subsubsection {* Representatives *}
text {*
  We define a function that searches for the representative of an element.
  This function is only partially defined, as it does not terminate on all
  lists. We use the domain of this function to characterize valid union-find 
  lists. 
*}
function (domintros) rep_of 
  where "rep_of l i = (if l!i = i then i else rep_of l (l!i))"
  by pat_completeness auto

text {* A valid union-find structure only contains valid indexes, and
  the @{text "rep_of"} function terminates for all indexes. *}
definition 
  "ufa_invar l \<equiv> \<forall>i<length l. rep_of_dom (l,i) \<and> l!i<length l"

lemma ufa_invarD: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of_dom (l,i)" 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> l!i<length l" 
  unfolding ufa_invar_def by auto

text {* We derive the following equations for the @{text "rep-of"} function. *}
lemma rep_of_refl: "l!i=i \<Longrightarrow> rep_of l i = i"
  apply (subst rep_of.psimps)
  apply (rule rep_of.domintros)
  apply (auto)
  done

lemma rep_of_step: 
  "\<lbrakk>ufa_invar l; i<length l; l!i\<noteq>i\<rbrakk> \<Longrightarrow> rep_of l i = rep_of l (l!i)"
  apply (subst rep_of.psimps)
  apply (auto dest: ufa_invarD)
  done

lemmas rep_of_simps = rep_of_refl rep_of_step

lemma rep_of_iff: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> 
  \<Longrightarrow> rep_of l i = (if l!i=i then i else rep_of l (l!i))"
  by (simp add: rep_of_simps)

text {* We derive a custom induction rule, that is more suited to
  our purposes. *}
lemma rep_of_induct[case_names base step, consumes 2]:
  assumes I: "ufa_invar l" 
  assumes L: "i<length l"
  assumes BASE: "\<And>i. \<lbrakk> ufa_invar l; i<length l; l!i=i \<rbrakk> \<Longrightarrow> P l i"
  assumes STEP: "\<And>i. \<lbrakk> ufa_invar l; i<length l; l!i\<noteq>i; P l (l!i) \<rbrakk> 
    \<Longrightarrow> P l i"
  shows "P l i"
proof -
  from ufa_invarD[OF I L] have "ufa_invar l \<and> i<length l \<longrightarrow> P l i"
    apply (induct l\<equiv>l i rule: rep_of.pinduct)
    apply (auto intro: STEP BASE dest: ufa_invarD)
    done
  thus ?thesis using I L by simp
qed

text {* In the following, we define various properties of @{text "rep_of"}. *}
lemma rep_of_min: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
proof -
  have "\<lbrakk>rep_of_dom (l,i) \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
    apply (induct arbitrary:  rule: rep_of.pinduct)
    apply (subst rep_of.psimps, assumption)
    apply (subst (2) rep_of.psimps, assumption)
    apply auto
    done 
  thus "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
    by (metis ufa_invarD(1))
qed

lemma rep_of_bound: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> rep_of l i < length l"
  apply (induct rule: rep_of_induct)
  apply (auto simp: rep_of_iff)
  done

lemma rep_of_idem: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> rep_of l (rep_of l i) = rep_of l i"
  by (auto simp: rep_of_min rep_of_refl)

lemma rep_of_min_upd: "\<lbrakk> ufa_invar l; x<length l; i<length l \<rbrakk> \<Longrightarrow> 
  rep_of (l[rep_of l x := rep_of l x]) i = rep_of l i"
  by (metis list_update_id rep_of_min)   

lemma rep_of_idx: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of l (l!i) = rep_of l i"
  by (metis rep_of_step)

subsubsection {* Abstraction to Partial Equivalence Relation *}
definition ufa_\<alpha> :: "nat list \<Rightarrow> (nat\<times>nat) set" 
  where "ufa_\<alpha> l 
    \<equiv> {(x,y). x<length l \<and> y<length l \<and> rep_of l x = rep_of l y}"

lemma ufa_\<alpha>_equiv[simp, intro!]: "part_equiv (ufa_\<alpha> l)"
  apply rule
  unfolding ufa_\<alpha>_def
  apply (rule symI)
  apply auto
  apply (rule transI)
  apply auto
  done

lemma ufa_\<alpha>_lenD: 
  "(x,y)\<in>ufa_\<alpha> l \<Longrightarrow> x<length l"
  "(x,y)\<in>ufa_\<alpha> l \<Longrightarrow> y<length l"
  unfolding ufa_\<alpha>_def by auto

lemma ufa_\<alpha>_dom[simp]: "Domain (ufa_\<alpha> l) = {0..<length l}"
  unfolding ufa_\<alpha>_def by auto

lemma ufa_\<alpha>_dom_card: "card (Domain (ufa_\<alpha> l)) = length l"
  by simp

lemma ufa_\<alpha>_refl[simp]: "(i,i)\<in>ufa_\<alpha> l \<longleftrightarrow> i<length l"
  unfolding ufa_\<alpha>_def
  by simp

lemma ufa_\<alpha>_len_eq: 
  assumes "ufa_\<alpha> l = ufa_\<alpha> l'"  
  shows "length l = length l'"
  by (metis assms le_antisym less_not_refl linorder_le_less_linear ufa_\<alpha>_refl)

subsubsection {* Operations *}
lemma ufa_init_invar: "ufa_invar [0..<n]"
  unfolding ufa_invar_def
  by (auto intro: rep_of.domintros)

lemma ufa_init_correct: "ufa_\<alpha> [0..<n] = {(x,x) | x. x<n}"
  unfolding ufa_\<alpha>_def
  using ufa_init_invar[of n]
  apply (auto simp: rep_of_refl)
  done

lemma ufa_find_correct: "\<lbrakk>ufa_invar l; x<length l; y<length l\<rbrakk> 
  \<Longrightarrow> rep_of l x = rep_of l y \<longleftrightarrow> (x,y)\<in>ufa_\<alpha> l"
  unfolding ufa_\<alpha>_def
  by auto

abbreviation "ufa_union l x y \<equiv> l[rep_of l x := rep_of l y]"

lemma ufa_union_invar:
  assumes I: "ufa_invar l"
  assumes L: "x<length l" "y<length l"
  shows "ufa_invar (ufa_union l x y)"
  unfolding ufa_invar_def
proof (intro allI impI, simp only: length_list_update)
  fix i
  assume A: "i<length l"
  with I have "rep_of_dom (l,i)" by (auto dest: ufa_invarD)

  have "ufa_union l x y ! i < length l" using I L A
    apply (cases "i=rep_of l x")
    apply (auto simp: rep_of_bound dest: ufa_invarD)
    done
  moreover have "rep_of_dom (ufa_union l x y, i)" using I A L
  proof (induct rule: rep_of_induct)
    case (base i)
    thus ?case
      apply -
      apply (rule rep_of.domintros)
      apply (cases "i=rep_of l x")
      apply auto
      apply (rule rep_of.domintros)
      apply (auto simp: rep_of_min)
      done
  next
    case (step i)

    from step.prems `ufa_invar l` `i<length l` `l!i\<noteq>i` 
    have [simp]: "ufa_union l x y ! i = l!i"
      apply (auto simp: rep_of_min rep_of_bound nth_list_update)
      done

    from step show ?case
      apply -
      apply (rule rep_of.domintros)
      apply simp
      done
  qed
  ultimately show 
    "rep_of_dom (ufa_union l x y, i) \<and> ufa_union l x y ! i < length l"
    by blast

qed

lemma ufa_union_aux:
  assumes I: "ufa_invar l"
  assumes L: "x<length l" "y<length l" 
  assumes IL: "i<length l"
  shows "rep_of (ufa_union l x y) i = 
    (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
  using I IL
proof (induct rule: rep_of_induct)
  case (base i)
  have [simp]: "rep_of l i = i" using `l!i=i` by (simp add: rep_of_refl)
  note [simp] = `ufa_invar l` `i<length l`
  show ?case proof (cases)
    assume A[simp]: "rep_of l x = i"
    have [simp]: "l[i := rep_of l y] ! i = rep_of l y" 
      by (auto simp: rep_of_bound)

    show ?thesis proof (cases)
      assume [simp]: "rep_of l y = i" 
      show ?thesis by (simp add: rep_of_refl)
    next
      assume A: "rep_of l y \<noteq> i"
      have [simp]: "rep_of (l[i := rep_of l y]) i = rep_of l y"
        apply (subst rep_of_step[OF ufa_union_invar[OF I L], simplified])
        using A apply simp_all
        apply (subst rep_of_refl[where i="rep_of l y"])
        using I L
        apply (simp_all add: rep_of_min)
        done
      show ?thesis by (simp add: rep_of_refl)
    qed
  next
    assume A: "rep_of l x \<noteq> i"
    hence "ufa_union l x y ! i = l!i" by (auto)
    also note `l!i=i`
    finally have "rep_of (ufa_union l x y) i = i" by (simp add: rep_of_refl)
    thus ?thesis using A by auto
  qed
next    
  case (step i)

  note [simp] = I L `i<length l`

  have "rep_of l x \<noteq> i" by (metis I L(1) rep_of_min `l!i\<noteq>i`)
  hence [simp]: "ufa_union l x y ! i = l!i"
    by (auto simp add: nth_list_update rep_of_bound `l!i\<noteq>i`) []

  have "rep_of (ufa_union l x y) i = rep_of (ufa_union l x y) (l!i)" 
    by (auto simp add: rep_of_iff[OF ufa_union_invar[OF I L]])
  also note step.hyps(4)
  finally show ?case
    by (auto simp: rep_of_idx)
qed
  
lemma ufa_union_correct: "\<lbrakk> ufa_invar l; x<length l; y<length l \<rbrakk> 
  \<Longrightarrow> ufa_\<alpha> (ufa_union l x y) = per_union (ufa_\<alpha> l) x y"
  unfolding ufa_\<alpha>_def per_union_def
  by (auto simp: ufa_union_aux
    split: if_split_asm
  )

lemma ufa_compress_aux:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_invar (l[x := rep_of l x])" 
  and "\<forall>i<length l. rep_of (l[x := rep_of l x]) i = rep_of l i"
proof -
  {
    fix i
    assume "i<length (l[x := rep_of l x])"
    hence IL: "i<length l" by simp

    have G1: "l[x := rep_of l x] ! i < length (l[x := rep_of l x])"
      using I IL 
      by (auto dest: ufa_invarD[OF I] simp: nth_list_update rep_of_bound)
    from I IL have G2: "rep_of (l[x := rep_of l x]) i = rep_of l i 
      \<and> rep_of_dom (l[x := rep_of l x], i)"
    proof (induct rule: rep_of_induct)
      case (base i)
      thus ?case
        apply (cases "x=i")
        apply (auto intro: rep_of.domintros simp: rep_of_refl)
        done
    next
      case (step i) 
      hence D: "rep_of_dom (l[x := rep_of l x], i)"
        apply -
        apply (rule rep_of.domintros)
        apply (cases "x=i")
        apply (auto intro: rep_of.domintros simp: rep_of_min)
        done
      
      thus ?case apply simp using step
        apply -
        apply (subst rep_of.psimps[OF D])
        apply (cases "x=i")
        apply (auto simp: rep_of_min rep_of_idx)
        apply (subst rep_of.psimps[where i="rep_of l i"])
        apply (auto intro: rep_of.domintros simp: rep_of_min)
        done
    qed
    note G1 G2
  } note G=this

  thus "\<forall>i<length l. rep_of (l[x := rep_of l x]) i = rep_of l i"
    by auto

  from G show "ufa_invar (l[x := rep_of l x])" 
    by (auto simp: ufa_invar_def)
qed

lemma ufa_compress_invar:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_invar (l[x := rep_of l x])" 
  using assms by (rule ufa_compress_aux)

lemma ufa_compress_correct:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_\<alpha> (l[x := rep_of l x]) = ufa_\<alpha> l"
  by (auto simp: ufa_\<alpha>_def ufa_compress_aux[OF I])



subsubsection \<open>stuff about the height (by Max Haslbeck)\<close>


function (domintros) height_of 
  where "height_of l i = (if l!i = i then 0::nat else 1 + height_of l (l!i))"
  by pat_completeness auto
print_theorems 

lemma height_of_dom_rep_of_dom[simp]: "height_of_dom (l, i) = rep_of_dom (l, i)"
  apply(rule)
  subgoal 
    apply (induct arbitrary:  rule: height_of.pinduct) 
    apply (rule rep_of.domintros) by simp
  subgoal 
    apply (induct arbitrary:  rule: rep_of.pinduct)
    apply (rule height_of.domintros) by simp
  done

lemma height_of_step: "ufa_invar l \<Longrightarrow>
         i < length l \<Longrightarrow>
         l ! i \<noteq> i \<Longrightarrow>
          height_of l i = Suc (height_of l (l ! i))"  
  by (simp add: height_of.psimps ufa_invarD(1)) 


 

definition "h_of l i = Max {height_of l j|j. j<length l \<and> rep_of l j = i}"

(*TODO: invariant about the rank*)
definition invar where
  "invar l sl = (length l = length sl 
              \<and> sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l} = length l
              \<and> (\<forall>i<length l. l!i=i \<longrightarrow> (2::nat) ^ h_of l i \<le> sl ! i))"

lemma invar_sli_le_l:
  assumes "invar l sl" "ufa_invar l" "i<length l"
  shows "sl ! (rep_of l i) \<le> length l"
proof -
  from assms(1) have a: "sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l} = length l"
      and len: "length sl = length l" by(auto simp: invar_def)

  let ?r = "(rep_of l i)"
  from assms have "?r<length l" by(auto simp: rep_of_bound)    
  then have f: "{0..<length l} = {?r} \<union> ({0..<length l}-{?r})" by auto
  have "sl ! (?r) \<le> sum (\<lambda>i. if l!i=i then sl !i else 0) ({0..<length l}-{?r}) + (if l!?r=?r then sl !?r else 0)"
    using assms by (auto simp: rep_of_min) 
  also have "\<dots> = sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l}"
    apply(subst (2) f) apply(subst sum_Un_nat) by simp_all
  also have "\<dots> = length l" using a by simp
  finally show "sl ! (rep_of l i) \<le> length l" .
qed



lemma h_rep: "ufa_invar l \<Longrightarrow> y<length l\<Longrightarrow> height_of l (rep_of l y) = 0"
  apply (subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar )   
  by (simp add: rep_of_min) 




lemma ufa_compress_compresses:
  "\<lbrakk>ufa_invar l; i<length l; j<length l\<rbrakk> \<Longrightarrow>
      height_of (l[j:=rep_of l j]) i \<le> height_of l i"
  proof (induct rule: rep_of_induct)
    case (base i)
    then show ?case
      apply(subst height_of.psimps)  subgoal apply simp apply(rule ufa_invarD(1)) by(auto simp add: ufa_compress_invar)
      apply (auto simp add: rep_of_refl) 
      by (metis nth_list_update' rep_of_iff) 
  next
    case (step i)
    show ?case 
      apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_compress_invar )
      apply auto 
      apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_compress_invar )
      using step(1-3) apply auto
      apply(cases "i=j")
      subgoal apply simp apply(subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_compress_invar ufa_invarD(1))   
      using rep_of_min by auto  
    subgoal apply simp apply(rule step(4)) using step by auto
    done
  qed                                                                                  

lemma ufa_union_on_path_only_increases_by_one:
  "\<lbrakk>ufa_invar l; i<length l; x<length l; y<length l; rep_of l i = rep_of l x\<rbrakk> \<Longrightarrow> 
      height_of (ufa_union l x y) i \<le> Suc (height_of l i)"
proof (induct rule: rep_of_induct)
  case (base i)
  then show ?case
    apply(cases "i=rep_of l x")
    subgoal
      apply(subst height_of.psimps)  subgoal by (simp add: ufa_invarD(1) ufa_union_invar )  
      apply simp
      apply (auto simp add:   )[]
       apply(subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar)  
      apply (auto simp: h_rep)[] by(simp add: rep_of_min)
    subgoal 
      apply(subst height_of.psimps)  subgoal apply simp  
        by (simp add: ufa_invarD(1) ufa_union_invar)  
      by simp 
    done
next
  case (step i)
  then have not: "i\<noteq>rep_of l x" 
    using rep_of_min by blast 

  show ?case
    apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_union_invar ) 
    using not apply simp
    apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar ) 
    apply simp apply safe
     apply(rule step(4)) using step 
    by (auto simp add: rep_of_idx) 
qed

lemma ufa_union_not_on_path_stays:
  "\<lbrakk>ufa_invar l; i<length l; x<length l; y<length l; rep_of l i \<noteq> rep_of l x\<rbrakk> \<Longrightarrow> 
      height_of (ufa_union l x y) i = height_of l i"
proof (induct rule: rep_of_induct)
  case (base i)
  then show ?case
    apply(cases "i=rep_of l x")
    subgoal
      by (auto simp add:  h_rep  rep_of_iff)  
    subgoal 
      apply(subst height_of.psimps)  subgoal apply simp  
        by (simp add: ufa_invarD(1) ufa_union_invar) 
      apply auto
      apply(subst height_of.psimps)  subgoal apply simp  
        by (simp add: ufa_invarD(1) ufa_union_invar)  
      by simp 
    done
next
  case (step i)
  then have not: "i\<noteq>rep_of l x" 
    using rep_of_min by blast 

  show ?case
    apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_union_invar ) 
    using not step(1-3) apply auto
    apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar ) 
    apply simp 
     apply(rule step(4)) using step 
    by (auto simp add: rep_of_idx) 
qed


lemma ufa_union_on_path:
"\<lbrakk>ufa_invar l; i<length l; x<length l; y<length l\<rbrakk> \<Longrightarrow> 
      height_of (ufa_union l x y) i \<le> Suc (height_of l i)"
  proof (induct rule: rep_of_induct)
    case (base i)
    then show ?case
      apply(cases "i=rep_of l x")
      subgoal
      apply(subst height_of.psimps)  subgoal by (simp add: ufa_invarD(1) ufa_union_invar )  
      apply (auto simp add:   )[]
        apply(subst height_of.psimps) subgoal by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar)  
        apply auto[] by(simp add: rep_of_min)
      subgoal 
        apply(subst height_of.psimps)  subgoal apply simp  
          by (simp add: ufa_invarD(1) ufa_union_invar)  
        by simp 
      done
  next
    case (step i)
    then have not: "i\<noteq>rep_of l x" 
      using rep_of_min by blast 

    show ?case
      apply(subst height_of.psimps)  subgoal using step by (simp add: ufa_invarD(1) ufa_union_invar ) 
      using not apply simp
      apply(subst (2) height_of.psimps)  subgoal using step by (simp add: rep_of_bound ufa_invarD(1) ufa_union_invar ) 
      apply simp apply safe
      apply(rule step(4)) using step by auto
  qed


lemma hel: "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> finite A  \<Longrightarrow> MAXIMUM A f \<le> MAXIMUM A g"  
  by (smt Max_ge_iff Max_in finite_imageI imageE image_eqI image_is_empty order_refl)  
lemma MAXIMUM_mono: "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> finite A  \<Longrightarrow> A = B \<Longrightarrow> MAXIMUM A f \<le> MAXIMUM B g"  
  using hel by blast 
lemma MAXIMUM_eq: "(\<And>x. x\<in>A \<Longrightarrow> f x = g x) \<Longrightarrow> finite A  \<Longrightarrow> A = B \<Longrightarrow> MAXIMUM A f = MAXIMUM B g"  
  apply(rule antisym) by  (auto intro: MAXIMUM_mono)





lemma h_of_alt: "h_of l i = MAXIMUM {j|j. j<length l \<and> rep_of l j = i} (height_of l)"
  unfolding h_of_def 
  by (simp add: setcompr_eq_image) 
 

lemma h_of_compress: "ufa_invar l \<Longrightarrow> j < length l \<Longrightarrow> h_of (l[j:=rep_of l j]) i \<le>  h_of l i"
  unfolding h_of_alt 
  apply(rule MAXIMUM_mono)
  subgoal apply(rule ufa_compress_compresses) by auto
  by (auto simp add: ufa_compress_aux(2))   


lemma h_of_uf_union_untouched:
  "ufa_invar l \<Longrightarrow> x < length l \<Longrightarrow> y < length l \<Longrightarrow> i < length l \<Longrightarrow> l!i = i 
    \<Longrightarrow> i \<noteq> rep_of l x \<Longrightarrow> i \<noteq> rep_of l y   \<Longrightarrow> h_of (ufa_union l x y) i = h_of l i"
  unfolding h_of_alt 
  apply(rule MAXIMUM_eq)
  subgoal apply(rule ufa_union_not_on_path_stays)  
    using ufa_union_aux by auto  
  using ufa_union_aux by auto
 

lemma Suc_h_of: assumes
  a:  "i < length l " "rep_of l i = i"
  shows 
  "Suc (h_of l i) = MAXIMUM {j|j. j<length l \<and> rep_of l j = i} (\<lambda>j. Suc (height_of l j))"
  unfolding h_of_alt  
  apply(subst  mono_Max_commute[where f=Suc]) 
  subgoal by (simp add: mono_Suc)
  subgoal by simp
  subgoal using a by auto  
  by (simp add: image_image) 

lemma MAXIMUM_Un: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {} 
  \<Longrightarrow> MAXIMUM (A \<union> B) f = max (MAXIMUM A f) (MAXIMUM B f)"
  apply(simp add: image_Un)
  apply(subst Max_Un) by auto


lemma fixes A::nat 
  shows "A\<le>A' \<Longrightarrow> B\<le>B' \<Longrightarrow> max A B \<le> max A' B'"    
  by auto  
 


lemma h_of_uf_union_id:
  assumes "ufa_invar l "" x < length l "" y < length l "" i < length l "
    " rep_of l i = i" "i = rep_of l y" and neq: "rep_of l y = rep_of l x"
  shows "h_of (ufa_union l x y) i = h_of l i"
  using neq apply simp using assms  
  by (metis list_update_id rep_of_min)  


lemma h_of_uf_union_touched:
  assumes "ufa_invar l "" x < length l "" y < length l "" i < length l "
    " rep_of l i = i" "i = rep_of l y" and neq: "rep_of l y \<noteq> rep_of l x"
  shows "h_of (ufa_union l x y) i \<le> max (h_of l (rep_of l y)) (Suc (h_of l (rep_of l x)))"
proof -
  have *: "{j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i}
      = {j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i \<and> rep_of l j = rep_of l y}
          \<union> {j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i \<and> rep_of l j = rep_of l x}" (is "_ = ?A \<union> ?B")
    apply auto using assms  
    by (simp add: ufa_union_aux)  

  have A: "?A = {j |j. j < length l \<and> rep_of l j = rep_of l y}"
    using ufa_union_aux assms by auto
  have B: "?B = {j |j. j < length l \<and> rep_of l j = rep_of l x}"
    using ufa_union_aux assms by auto

  have "h_of (ufa_union l x y) i = MAXIMUM {j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i} (height_of (ufa_union l x y))"
    unfolding h_of_alt by simp
  also have "\<dots> = MAXIMUM (?A \<union> ?B) (height_of (ufa_union l x y))"
    unfolding * by simp
  also have "\<dots> = max (MAXIMUM ?A (height_of (ufa_union l x y))) (MAXIMUM ?B (height_of (ufa_union l x y)))"
    apply(subst MAXIMUM_Un) apply simp_all
    subgoal  apply(rule exI[where x=y]) using assms by (simp add: ufa_union_aux)  
    subgoal  apply(rule exI[where x=x]) using assms by (simp add: ufa_union_aux)  
    done
  also have "\<dots> \<le> max (MAXIMUM ?A (height_of l)) (MAXIMUM ?B (\<lambda>j. Suc (height_of l j)))"
    apply(rule max.mono)
    subgoal apply(rule MAXIMUM_mono)
      subgoal apply(rule order_eq_refl) apply(rule ufa_union_not_on_path_stays) using assms by auto  
      by simp_all 
    subgoal apply(rule MAXIMUM_mono)
      subgoal apply(rule ufa_union_on_path)  using assms by auto
       apply simp by simp
    done
  also have "\<dots> \<le> max  (h_of l (rep_of l y)) (Suc (h_of l (rep_of l x)))"
    apply(rule max.mono)
    subgoal unfolding h_of_alt A by simp
    subgoal apply(subst Suc_h_of)
      subgoal using assms by (auto simp: rep_of_min rep_of_bound rep_of_refl)
      subgoal using assms by (auto simp: rep_of_min rep_of_bound rep_of_refl)  
      unfolding B by simp
    done
  finally show ?thesis .
qed 

lemma height_of_le_h_of: "i < length l \<Longrightarrow> height_of l i \<le> h_of l (rep_of l i)"
    unfolding h_of_def apply(rule Max.coboundedI) apply simp
    apply(subst setcompr_eq_image) apply(rule imageI)
    by auto




lemma height_of_ub: assumes "invar l sl" "ufa_invar l" "i<length l"
  shows "2 ^ (height_of l i) \<le> length l"
proof -
  from assms(1) have "length l = length sl "
            and 2:  "sum (\<lambda>i. if l!i=i then sl !i else 0) {0..<length l} = length l"
            and 3:  "\<And>i. i<length l \<Longrightarrow>  l!i=i \<Longrightarrow> (2::nat) ^ h_of l i \<le> sl ! i"
    unfolding invar_def  by auto

  have *: "height_of l i \<le> h_of l (rep_of l i)"     
    using assms by (auto intro: height_of_le_h_of)

  have "(2::nat) ^ (height_of l i) \<le> 2 ^ (h_of l (rep_of l i))"
    apply(rule power_increasing) apply(rule *) by simp
  also have "\<dots> \<le> sl ! (rep_of l i)"
   using 3 assms by(auto simp add: rep_of_bound rep_of_min )   
  also have "\<dots> \<le> length l" using assms 
    by (auto simp: rep_of_bound intro: invar_sli_le_l) 
  finally show ?thesis .
qed

section{*Stuff about the rank (TODO) (by Adrián Löwenberg)*}

subsection{*Definitions*}

definition \<rho> where "\<rho> \<equiv> 1::nat "

\<comment>\<open>@{term \<rho>} is arbitray but the following must be true\<close>
lemma \<rho>_geq_1: "1 \<le> \<rho>" unfolding \<rho>_def ..

lemma \<rho>_gt_0: "0<\<rho>" using \<rho>_geq_1 by simp

abbreviation \<alpha>\<^sub>r where "\<alpha>\<^sub>r n \<equiv> alphar \<rho> n"
                                
definition rankr where "rankr rkl i \<equiv> (rkl ! i) + \<rho>"

(*This relation points towards rep_of, so (i,rep_of l i) \<in> ufa_\<beta> l*)
definition ufa_\<beta>_start :: "nat list \<Rightarrow> (nat\<times>nat) set" 
  where "ufa_\<beta>_start l 
    \<equiv> {(x,y). x<length l \<and> y<length l \<and> x\<noteq>y \<and> l!x = y}"

definition ufa_\<beta> :: "nat list \<Rightarrow> (nat\<times>nat) set"
  where "ufa_\<beta> l \<equiv> trancl (ufa_\<beta>_start l)"


lemma ufa_\<beta>_dom: " Domain (ufa_\<beta> l) \<subseteq> {0..<length l}" 
  unfolding ufa_\<beta>_def ufa_\<beta>_start_def 
  apply (subst trancl_domain) by fastforce 

lemma rep_of_ufa_\<beta>_refl: 
  assumes "ufa_invar l" "i <length l" 
  shows "(i,rep_of l i) \<in> (ufa_\<beta>_start l)\<^sup>* " 
  unfolding ufa_\<beta>_def  
proof (induction rule: rep_of_induct[OF assms(1,2)])
  case (1 i)
  then show ?case using rep_of_refl[OF 1(3)] by simp
next
  case (2 i)
  have "(i, l ! i) \<in> ufa_\<beta>_start l"
      unfolding ufa_\<beta>_start_def using 2 assms(1) ufa_invarD(2) by force
  then show ?case using 2 rep_of_idx[OF assms(1) \<open>i < length l\<close>]
      converse_rtrancl_into_rtrancl[of i _ "ufa_\<beta>_start l" "rep_of l i"] by auto
qed
    
lemma rep_of_ufa_\<beta>:
  assumes "ufa_invar l" "i <length l" "i\<noteq>rep_of l i" 
  shows "(i,rep_of l i) \<in> ufa_\<beta> l" 
  unfolding ufa_\<beta>_def using rep_of_ufa_\<beta>_refl[OF assms(1,2)] assms(3)
  by (simp add: rtrancl_eq_or_trancl)

\<comment>\<open> I presume it is also antisymmetric, however that is not needed \<close>
lemma ufa_\<beta>_order[simp, intro!]: 
  assumes "ufa_invar l"
  shows  "trans (ufa_\<beta> l)"
   apply rule
proof goal_cases
  case 1
  then show ?case unfolding ufa_\<beta>_def by (simp add: trans_rtrancl)
qed


subsubsection{*Closures with distances*}

inductive kpath 
  for r :: "('a \<times> 'a) set"
  where
    kpath_refl [intro!, Pure.intro!, simp]: "kpath r x x 0"
  | kpath_into_rtrancl [Pure.intro]: 
      "(x, y) \<in> r \<Longrightarrow> kpath r y z k \<Longrightarrow> kpath r x z (Suc k)"


lemma kpath_rtclosure: assumes "kpath r x y k" shows "(x,y) \<in> r\<^sup>*"
  using assms by (induction rule: kpath.induct) auto

lemma rtclosure_kpath: assumes "(x,y) \<in> r\<^sup>*" shows "\<exists>k. kpath r x y k"
  using assms proof (induction rule: rtrancl_induct)
  case base
  then show ?case using kpath_refl by blast
next
  case (step y z)
  obtain k where path: "kpath r x y k" using step by blast
  thus ?case using step(2) 
  proof (induction rule: kpath.induct) 
    case (kpath_refl x)
    then show ?case using  kpath.kpath_refl kpath_into_rtrancl by fast
  next
    case (kpath_into_rtrancl x y' z' k)
    then show ?case using kpath.kpath_into_rtrancl by fast
  qed
qed

lemma tclosure_kpath: assumes "(x,y) \<in> r\<^sup>+" shows "\<exists>k>0. kpath r x y k"
  using assms proof (induction rule: trancl_induct)
  case (base y)
  then show ?case using kpath_into_rtrancl by fast
next
  case (step y z)
  obtain k where path: "k>0" "kpath r x y k" using step by blast
  show ?case using path(2) step(2)
  proof (induction rule: kpath.induct)
    case (kpath_refl x)
    then show ?case using kpath_into_rtrancl by fast
  next
    case (kpath_into_rtrancl x y z' k)
    then show ?case using kpath.kpath_into_rtrancl by force
  qed 
qed


definition descendants where 
  "descendants l i = {j. (j,i)\<in> ufa_\<beta> l}"

definition ancestors where
  "ancestors l i = {j. (i,j)\<in> ufa_\<beta> l}"

definition invar_rank where "invar_rank l rkl \<equiv> (ufa_invar l \<and> length l = length rkl 
                            \<and> (\<forall>i j. i< length l \<and> j< length l \<and> l!i=j \<and>  i\<noteq>j \<longrightarrow> rkl ! i < rkl ! j) 
                            \<comment> \<open>if j is on the path from i to rep_of l i, then rank of j is bigger than rank of i\<close>
                            \<and> sum (\<lambda>i. if l!i=i then rkl!i else 0) {0..<length l} \<le> length l
                            \<and> (\<forall>i<length l. l!i=i \<longrightarrow> (2::nat) ^ rkl!i \<le> card (descendants l i)) )"
                            \<comment>\<open>rank i \<le> log (card (Domain (ufa_\<alpha> l)))\<close>

definition invar_rank' where "invar_rank' l rkl \<equiv> ufa_invar l \<and> invar_rank l rkl"

subsection{*Lemmas About the rank from UnionFind11Rank, UnionFind21Parent and UnionFind41Potential*}

lemma parent_has_nonzero_rank: assumes "invar_rank l rkl" "l!i = j" "i < length l" "j < length l" "i\<noteq>j"
   shows "0<rkl!j"
proof -
  have "rkl!i < rkl!j" using assms unfolding invar_rank_def by blast
  thus ?thesis by linarith
qed


\<comment>\<open>Because rank increases along edges, if there is a path of length k from i to j, 
  then @{term "rkl!i + k \<le> rkl!j"} holds\<close>

lemma rank_bounds_height_precise: 
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "kpath (ufa_\<beta>_start l) i j k" 
  shows "rkl!i + k \<le> rkl!j" using assms(5) 
proof (induction rule: kpath.induct)
  case (kpath_into_rtrancl x y z k)
  have "rkl!x < rkl!y" using assms(1) kpath_into_rtrancl(1) 
    unfolding invar_rank_def ufa_\<beta>_start_def by blast
  then show ?case using kpath_into_rtrancl by simp
qed simp


\<comment>\<open> The rank of a vertex is an upper bound on its height in the forest. That is,
   a path that leads to a vertex y has length at most @{term "rkl!y"}. In the absence
   of path compression, we could actually require an equality. \<close>

lemma rank_bounds_height:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "kpath (ufa_\<beta>_start l) i j k"
  shows "k \<le> rkl!j"
  using rank_bounds_height_precise[OF assms] by linarith


lemma rank_increases_along_path_refl:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "rkl!i \<le> rkl!j"
proof -
  obtain "k" where kstuff: "kpath (ufa_\<beta>_start l) i j k" 
    using assms(5) rtclosure_kpath[of i j "ufa_\<beta>_start l" ] by blast
  then show ?thesis using rank_bounds_height_precise[OF assms(1-4) kstuff] by simp
qed

\<comment>\<open>Rank increases strictly along a nontrivial path.\<close>
lemma rank_increases_strictly_along_path:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> ufa_\<beta> l"
  shows "rkl!i < rkl!j"
proof -
  obtain "k" where kstuff: "k>0" "kpath (ufa_\<beta>_start l) i j k" 
    using assms(5) tclosure_kpath[of i j "ufa_\<beta>_start l" ] unfolding ufa_\<beta>_def by blast
  then show ?thesis using rank_bounds_height_precise[OF assms(1-4) kstuff(2)] by simp
qed

lemma ancestor_has_greater_rank:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "j \<in> ancestors l i"
  shows "rkl!i \<le> rkl!j"
  using assms(4) unfolding ancestors_def 
  using rank_increases_strictly_along_path[OF assms(1-3)] by fastforce


\<comment>\<open>Remember @{thm ufa_\<alpha>_dom}, 
  @{term "i < length l"} is equivalent to @{term "i \<in> Domain (ufa_\<alpha> l)"}\<close>

lemma rank_is_logarithmic:
  assumes "invar_rank l rkl" "i < length l"
  shows "rkl!i \<le> Discrete.log (length l)"
proof -
  { \<comment>\<open>First we prove this for roots\<close>
    fix i
    assume "i < length l" and is_root:"l!i=i"
    have crad: "{j. (j, i) \<in> ufa_\<beta> l} \<subseteq> {0..<length l}" using ufa_\<beta>_dom by blast
    have sg1: "card (descendants l i) \<le> length l" unfolding descendants_def using ufa_\<beta>_dom
      using crad subset_eq_atLeast0_lessThan_card by blast
    have "rkl!i \<le> Discrete.log (length l)"
      apply (rule prove_le_log) using assms sg1 \<open>i < length l\<close> is_root unfolding invar_rank_def
      by force
  } note root = this
  thus ?thesis proof (cases "l!i=i")
    case False
    obtain j where j_def:"j = rep_of l i" by simp
    have "l!j = j" using rep_of_min[of l i] j_def assms unfolding invar_rank_def by argo
    have "i \<noteq> rep_of l i" using False rep_of_iff[OF _ assms(2)] assms(1) \<open>l ! j = j\<close> j_def 
      unfolding invar_rank_def by force 
    have sg1: "(i,j) \<in> ufa_\<beta> l" using j_def rep_of_ufa_\<beta>[OF _ assms(2) \<open>i\<noteq>rep_of l i\<close>]  assms(1) 
      unfolding invar_rank_def by fastforce
    hence "j < length l" using assms unfolding ufa_\<beta>_def ufa_\<beta>_start_def invar_rank_def
      using j_def rep_of_bound by blast 
    have "rkl!i < rkl!j" using rank_increases_strictly_along_path[OF assms \<open>j < length l\<close> _ sg1] 
         \<open>i\<noteq>rep_of l i\<close> j_def by blast
    then show ?thesis using root[OF \<open>j<length l\<close> \<open>l!j=j\<close>] by linarith
  qed (simp add: root assms(2))
qed

\<comment>\<open>Really equivalent to @{thm height_of_ub}\<close>

lemma height_is_logarithmic:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "kpath (ufa_\<beta>_start l) i j k" 
  shows "k \<le> Discrete.log (length l)"
proof -
  have "k \<le> rkl!j" using rank_bounds_height[OF assms] .
  also have "\<dots> \<le> Discrete.log (length l)" using rank_is_logarithmic[OF assms(1,3)] .
  finally show ?thesis .
qed


lemma log_lt_n: "0 < n \<Longrightarrow> Discrete.log n < n"
  by (induction rule: Discrete.log_induct) simp+


lemma rank_is_linear: assumes "invar_rank l rkl" "i < length l" 
  shows "rkl ! i < length l"
proof -
  have "0 < length l" using \<open>i < length l\<close> by simp
  have "rkl ! i \<le> Discrete.log (length l)" using rank_is_logarithmic[OF assms] .
  also have "\<dots> < length l" using log_lt_n[OF \<open>0<length l\<close>] .
  finally show ?thesis .
qed


lemma \<rho>_leq_rankr: "\<rho> \<le> rankr rkl x"
  unfolding rankr_def by simp

lemma rankr_positive: "0 < rankr rkl x"
  unfolding rankr_def using \<rho>_geq_1 by fastforce

lemma rankr_increases_along_path_refl:
 assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
 shows "rankr rkl i \<le> rankr rkl j"
  unfolding rankr_def using rank_increases_along_path_refl[OF assms] by auto

lemma rankr_increases_strictly_along_path:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> ufa_\<beta> l"
  shows "rankr rkl i < rankr rkl j"
  unfolding rankr_def using rank_increases_strictly_along_path[OF assms] by auto


lemma \<alpha>\<^sub>r_rankr_grows_along_a_path:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> ufa_\<beta> l"
  shows "\<alpha>\<^sub>r (rankr rkl i) \<le> \<alpha>\<^sub>r (rankr rkl j)"
  using mono_alphar[of \<rho>] using \<rho>_geq_1 rankr_increases_strictly_along_path[OF assms] 
  unfolding mono_def by fastforce


lemma rep_of_invar_along_path':
  assumes "ufa_invar l" "i < length l" "i' < length l"  "j < length l" 
          "i = rep_of l j" "(j,i) \<in> (ufa_\<beta>_start l)\<^sup>*"  "(j,i') \<in> (ufa_\<beta>_start l)\<^sup>*"
        shows "i = rep_of l i'"
  using assms(7)
proof (induction rule: rtrancl_induct)
  case base
  then show ?case using assms(5) .
next
  case (step y z)
  then show ?case unfolding ufa_\<beta>_start_def 
    using assms(1) invar_rank_def rep_of_idx by fastforce
qed

lemma rep_of_invar_along_path:
  assumes "ufa_invar l" "i < length l" "i' < length l"  "j < length l" 
          "i = rep_of l j"  "(j,i') \<in> (ufa_\<beta>_start l)\<^sup>*"
        shows "i = rep_of l i'"
proof -
  have sg1: "(j,i) \<in> (ufa_\<beta>_start l)\<^sup>*" proof (cases "j \<noteq> rep_of l j")
    case True
    then show ?thesis using rep_of_ufa_\<beta>[of l j] \<open>i=rep_of l j\<close> assms 
      unfolding invar_rank_def ufa_\<beta>_def by auto      
  next
    case False
    then show ?thesis unfolding ufa_\<beta>_start_def
      using assms(5) by auto
  qed
  show ?thesis using rep_of_invar_along_path'[OF assms(1-5) sg1 assms(6)] .
qed


lemma rep_of_path_iff:
  assumes "ufa_invar l" "i < length l" "j < length l"
  shows "(rep_of l j = i) \<longleftrightarrow> ((j,i) \<in> (ufa_\<beta>_start l)\<^sup>* \<and> l!i=i)"
proof -
  show ?thesis apply(subst rep_of_iff) 
    subgoal using assms(1) unfolding invar_rank_def by simp 
    subgoal using assms(3) .
    subgoal apply safe proof goal_cases
      case 1
      then show ?case apply (subst rep_of_iff[symmetric]) 
        subgoal using assms unfolding invar_rank_def by blast
        subgoal using assms(3) .
        apply (cases "j = rep_of l j") proof goal_cases
        case 2
        show ?case using rep_of_ufa_\<beta>[OF _ assms(3) 2(2)] assms(1) 
          unfolding ufa_\<beta>_def invar_rank_def by simp
      qed simp
    next
      case 2
      then show ?case using rep_of_min rep_of_iff  assms unfolding invar_rank_def by force
    next
      case 3
      hence "i = rep_of l i" by (simp add: rep_of_refl)
      then show ?case using 3 assms(2,3) unfolding ufa_\<beta>_start_def apply (cases "i=j")
      proof goal_cases
        case 2
        then show ?case apply (cases "l!j \<noteq> j") proof goal_cases
          case 1
          obtain i' where i'rep: "i' = rep_of l j" by blast
          hence ji'path: "(j,i') \<in> (ufa_\<beta>_start l)\<^sup>*" using rep_of_ufa_\<beta>[OF \<open>ufa_invar l\<close> assms(3) ] 1(7) 
            unfolding ufa_\<beta>_def by fastforce
          have "l!i'=i'" using i'rep by (simp add: \<open>ufa_invar l\<close> assms(3) rep_of_min)
          hence i'rep': "i' = rep_of l i'" by (simp add: rep_of_refl)
          hence lengthi': "i' < length l" by (simp add: \<open>ufa_invar l\<close> assms(3) i'rep rep_of_bound) 
          have "i' = rep_of l i" 
            using rep_of_invar_along_path[OF assms(1) \<open>i'<length l\<close> \<open>i<length l\<close> \<open>j<length l\<close> i'rep] 
                ji'path 1(2) unfolding ufa_\<beta>_start_def by blast
          hence "i = i'" using \<open>i = rep_of l i\<close> \<open>i' = rep_of l i'\<close> by blast
          then show ?case using i'rep 
            by (simp add: "1"(7) \<open>ufa_invar l\<close> assms(3) rep_of_step)
        next
          case 2
          hence "l!j=j" by blast
          with 2 (1-6) have "i=j" using converse_rtranclE' by force
          then show ?case using 2(1-6) \<open>l!j=j\<close> by simp
        qed
      qed simp
    qed
    done
qed


\<comment>\<open>Two vertices connected by a path must be equivalent. (UnionFind01Data)\<close>
lemma path_is_equiv:
  assumes "ufa_invar l" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> ufa_\<beta> l"
  shows "(i,j) \<in> ufa_\<alpha> l"
proof -
  obtain r where "r = rep_of l j" by blast
  have "r = l!r"
    using \<open>r = rep_of l j\<close> assms(1) assms(3) invar_rank_def rep_of_min by auto
  have "ufa_invar l" using assms(1) unfolding invar_rank_def by blast
  have "r<length l"
    using \<open>r = rep_of l j\<close> assms(1) assms(3) invar_rank_def rep_of_bound by blast
  have "(i,r) \<in> ufa_\<beta> l" using \<open>(i,j) \<in> ufa_\<beta> l\<close> rep_of_path_iff[OF assms(1) \<open>r<length l\<close> \<open>j<length l\<close>]
    using ufa_\<beta>_order \<open>r = rep_of l j\<close> unfolding ufa_\<beta>_def by auto
  hence "r = rep_of l i" using rep_of_path_iff[OF assms(1) \<open>r<length l\<close> \<open>i<length l\<close>] \<open>r = l!r\<close> 
    unfolding ufa_\<beta>_def by fastforce
  thus ?thesis using \<open>r = rep_of l j\<close>  assms(2,3) unfolding ufa_\<alpha>_def by blast  
qed

lemma path_to_parent:
  assumes "ufa_invar l" "i < length l" "l!i\<noteq>i"
  shows "(i,l!i) \<in> ufa_\<beta> l"
  using assms ufa_invarD(2) unfolding ufa_\<beta>_def ufa_\<beta>_start_def invar_rank_def
  by fastforce

\<comment>\<open>is_equiv_parent (UnionFind21Parent)\<close>
lemma rep_of_parent_is_same:
  assumes "ufa_invar l" "i < length l" "l!i\<noteq>i"
  shows "(i,l!i) \<in> ufa_\<alpha> l"
  using path_is_equiv[OF assms(1,2) _ assms(3)[symmetric] path_to_parent[OF assms]] ufa_invarD(2)  assms 
  unfolding invar_rank_def by blast

\<comment>\<open>@{thm rep_of_idx} is equivalent to is_repr_parent (UnionFind21Parent)\<close>

lemma path_from_parent_to_rep_of:
  assumes "ufa_invar l" "i < length l" "j = rep_of l i"
  shows "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
  using assms rep_of_idx[OF assms(1,2)] rep_of_bound[OF assms(1,2)] rep_of_path_iff by blast


lemma parent_has_greater_rank:
  assumes "invar_rank l rkl" "i < length l" "l!i\<noteq>i"
  shows "rkl!i < rkl!(l!i)"
  using assms unfolding invar_rank_def ufa_invar_def by auto


lemma parent_has_greater_rankr:
  assumes "invar_rank l rkl" "i < length l" "l!i\<noteq>i"
  shows "rankr rkl i < rankr rkl (l!i)"
  unfolding rankr_def using parent_has_greater_rank assms unfolding \<rho>_def by simp

lemma \<alpha>\<^sub>r_rankr_grows_along_edges:
  assumes "invar_rank l rkl" "i < length l" "l!i\<noteq>i"
  shows "\<alpha>\<^sub>r (rankr rkl i) \<le> \<alpha>\<^sub>r (rankr rkl (l!i))"
  using mono_alphar[OF \<rho>_gt_0] parent_has_greater_rankr[OF assms] unfolding mono_def by simp

lemma \<alpha>\<^sub>r_rankr_grows_along_edges_corollary:
  assumes "invar_rank l rkl" "i < length l" "l!i\<noteq>i" "\<alpha>\<^sub>r (rankr rkl i) \<noteq> \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "\<alpha>\<^sub>r (rankr rkl i) < \<alpha>\<^sub>r (rankr rkl (l!i))"
  using \<alpha>\<^sub>r_rankr_grows_along_edges[OF assms(1-3)] assms(4) by linarith


section{*Level: Definition and Lemmas*}
\<comment>\<open>The level of @{term i} is defined as one plus the @{term "Greatest k"} such that
   @{term "Ackermann k (rankr rkl i)"} is less than or equal to @{term "rankr rkl (l!i)"}.\<close>


context \<comment>\<open>NonRoot\<close>
  fixes l::"nat list" and rkl::"nat list" and i::nat
  assumes contextasm: "invar_rank l rkl" "i<length l" "l!i\<noteq>i"
begin

definition defk where "defk k \<equiv> Ackermann k (rankr rkl i)"

interpretation lnn: f_nat_nat "defk"
  apply standard subgoal using Ackermann_strict_mono_in_k rankr_positive unfolding defk_def by blast
  subgoal using Ackermann_k_x_tends_to_infinity_along_k rankr_positive unfolding defk_def by blast
  done

definition prek where "prek \<equiv> lnn.\<beta>\<^sub>f (rankr rkl (l!i))"

definition level where "level \<equiv> Suc prek"

definition level' where "level' l' rkl' i' \<equiv> Suc (Greatest (\<lambda>k. rankr rkl' (l'!i') 
                                              \<ge> (Ackermann k (rankr rkl' i'))))"

lemma level_alt_eq: "level = level' l rkl i" 
  unfolding level_def level'_def prek_def lnn.\<beta>\<^sub>f_def defk_def by blast


\<comment>\<open>The following lemma proves that @{term level} is well-defined.\<close>
lemma level_exists:
  "Ackermann 0 (rankr rkl i) \<le> rankr rkl (l!i)"
  apply (subst Ackermann_base_eq) using parent_has_greater_rankr[OF contextasm] by simp

\<comment>\<open> The level of @{term i} seems to be a measure of the distance of the rank
   of @{term i} and the rank of its parent. In the case where these ranks
   are closest, @{term "rankr rkl (l!i)"} is @{term "Suc (rankr rkl i)"}, so level is 1. \<close>

lemma level_is_one:
  assumes "(rkl!(l!i)) = Suc (rkl!i)"
  shows "level = 1"
  unfolding level_def prek_def 
proof -
  have f: "rankr rkl (l!i) = Suc (rankr rkl i)" using assms unfolding rankr_def by simp
  show "Suc (lnn.\<beta>\<^sub>f (rankr rkl (l ! i))) = 1" apply (subst f)
    using \<beta>_x_Suc_x[OF rankr_positive[of rkl i]] unfolding defk_def by simp
qed

\<comment>\<open> In the case where these ranks are furthest away, @{term "rankr rkl i"} is r and
   @{term "rankr rkl (l!i)"} is, well, whatever it is. We find that the level is
   less than @{term "\<alpha>\<^sub>r (rankr rkl (l!i))"}. (Page 18.) \<close>

lemma level_lt_\<alpha>\<^sub>r:  "level < \<alpha>\<^sub>r (rankr rkl (l!i))"
  apply (subst alphar_alt_eq)
  subgoal using \<rho>_gt_0 .
  apply (subst alphar'_def)
  subgoal using \<rho>_gt_0 .
  unfolding level_def
  apply simp
  unfolding prek_def
  apply (rule lnn.\<beta>\<^sub>f_spec_direct_contrapositive) unfolding defk_def
  subgoal by (simp add: level_exists)
  apply (rule order.strict_trans2) 
   apply (subst Ackermann_prealphar_gt[of \<rho> "rankr rkl (l!i)" , OF \<rho>_gt_0])
  subgoal ..
  using \<rho>_leq_rankr[of rkl i] mono_Ackermann unfolding mono_def by blast


\<comment>\<open>Another connection between @{term rankr} at @{term i} and at @{term "l!i"}\<close>

lemma rankr_parent_i_lt: "rankr rkl (l!i) < Ackermann level (rankr rkl i)"
  unfolding level_def 
  apply (subst defk_def[symmetric])
  apply (rule lnn.\<beta>\<^sub>f_spec_reciprocal_contrapositive[of "rankr rkl (l ! i)" "Suc prek"] )
  unfolding prek_def by blast


section{*Index: Definition and Lemmas*}

\<comment>\<open> The index of @{term i} is defined as the largest @{term j} such that @{term j} 
  iterations of @{term "Ackermann prek"} take us from @{term "rankr rkl i"} 
  to at most @{term "rankr rkl (l!i)"}. \<close>

interpretation inn: f_nat_nat "\<lambda>j. compow j (Ackermann prek) (rankr rkl i)"
proof (standard, goal_cases)
  case 1
  { fix x::nat and y::nat assume lt:"x<y"
    have "compow x (Ackermann prek) (rankr rkl i) < compow ((y-x) + x) (Ackermann prek) (rankr rkl i)"
      apply (subst funpow_add) apply simp
      apply (rule compow_Ackermann_k_strictly_inflationary
            [of "(y - x)"  "(Ackermann local.prek ^^ x) (rankr rkl i)" "local.prek"])
      using lt by fastforce
  } thus ?case unfolding strict_mono_def by auto
next
  case 2
  then show ?case using compow_i_Ackermann_tends_to_infinity_along_i[of prek "(rankr rkl i)"] .
qed 

definition index where "index \<equiv> inn.\<beta>\<^sub>f (rankr rkl (l!i))"
\<comment>\<open>If that sounds crazy, it is\<close>

definition index' where "index' l' rkl' i' \<equiv> Greatest (\<lambda>j. rankr rkl' (l'!i')
                        \<ge> compow j (Ackermann (level - 1)) (rankr rkl' i'))"
lemma index_alt_eq: 
  shows "index = index' l rkl i"
  unfolding index_def index'_def inn.\<beta>\<^sub>f_def level_def by simp


\<comment>\<open>The following lemmas justify that index is well defined\<close>

lemma index_exists: 
  "compow 0 (Ackermann prek) (rankr rkl i) \<le> rankr rkl (l!i)"
  using parent_has_greater_rank[OF contextasm] unfolding rankr_def by auto

\<comment>\<open>@{term index} is at least one\<close>

lemma index_ge_1: "1\<le>index"
  unfolding index_def
  \<comment>\<open> By definition of @{term index}, we must show that applying @{term "Ackermann prek"} once
     to @{term "rankr rkl i"} takes us below or at @{term "rankr rkl (l!i)"}.\<close>
  apply (rule inn.\<beta>\<^sub>f_spec_reciprocal[of 1 "(rankr rkl (l ! i))"])
  apply simp
  apply (subst defk_def[symmetric])
  apply (rule lnn.\<beta>\<^sub>f_spec_direct[of "rankr rkl (l ! i)" prek])
  unfolding defk_def prek_def by (auto simp: level_exists)

\<comment>\<open>@{term index}  is at most @{term "rankr rkl i"}.\<close>

lemma index_le_rank: "index \<le> rankr rkl i"
  unfolding index_def
  apply (rule inn.\<beta>\<^sub>f_spec_direct_contrapositive_le[of "(rankr rkl (l ! i))" "rankr rkl i"])
  subgoal apply simp using parent_has_greater_rank[OF contextasm] unfolding rankr_def by fastforce
  subgoal apply (rule order.strict_trans2) apply (subst rankr_parent_i_lt)
  subgoal ..
  unfolding level_def apply (subst Ackermann_step_eq) by simp
  done

end


section{*Potential function \<Phi> of the whole Union Find data structure*}

definition \<phi> where "\<phi> l rkl i \<equiv> if  l!i = i
                    then \<alpha>\<^sub>r (rankr rkl i) * Suc (rankr rkl i)
                    else (if \<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i)) 
                        then (\<alpha>\<^sub>r (rankr rkl i) - level l rkl i) * (rankr rkl i) - index l rkl i + 1
                        else 0)"

definition \<Phi> where "\<Phi> l rkl \<equiv> Finite_Set.fold (\<lambda> i a.  (\<phi> l rkl i) + a) (0::nat) (Domain (ufa_\<alpha> l))"

lemma \<Phi>_simp[simp]: "\<Phi> l rkl = sum (\<lambda> i. \<phi> l rkl i) {0..<length l}"
proof -
  have 1: "(\<lambda>i. (+) (\<phi> l rkl i)) = (((+) \<circ>\<circ>\<circ> \<phi>) l rkl)" by auto
  show ?thesis
    unfolding \<Phi>_def
    apply simp
    apply (subst 1)
    using  Groups_Big.comm_monoid_add_class.sum.eq_fold[of "\<lambda>i. \<phi> l rkl i" "{0..<length l}", symmetric] .
qed

\<comment>\<open>The following lemmas repeat the cases of the definition of \<phi>\<close>

lemma \<phi>_case_1:
  assumes "l!i=i"
  shows "\<phi> l rkl i = \<alpha>\<^sub>r (rankr rkl i) * Suc (rankr rkl i)"
  unfolding \<phi>_def using assms by (simp cong: if_cong)

lemma \<phi>_case_2:
  assumes "l!i\<noteq>i" "\<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "\<phi> l rkl i = (\<alpha>\<^sub>r (rankr rkl i) - level l rkl i) * (rankr rkl i) - index l rkl i + 1"
  unfolding \<phi>_def using assms by (simp cong: if_cong)

lemma \<phi>_case_3:
  assumes "l!i\<noteq>i" "\<alpha>\<^sub>r (rankr rkl i) \<noteq> \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "\<phi> l rkl i = 0"
  unfolding \<phi>_def using assms by (simp cong: if_cong)

\<comment>\<open>This lemma unifies the last two cases above.\<close>

lemma \<phi>_case_2_or_3:
  assumes "l!i\<noteq>i"
  shows "\<phi> l rkl i \<le> (\<alpha>\<^sub>r (rankr rkl i) - level l rkl i) * (rankr rkl i) - index l rkl i + 1"
  apply (cases "\<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i))")
  subgoal using assms by (simp add: \<phi>_case_2)
  subgoal using assms by (simp add: \<phi>_case_3)
  done

\<comment>\<open> In case 2 above, the subtractions are safe: they cannot produce a
   negative number. The first subtraction always produces at least 1,
   while the second subtraction always produces at least 0. \<close>

lemma \<phi>_case_2_safe_level:
  assumes "invar_rank l rkl" "i<length l" "l!i\<noteq>i"  "\<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "level l rkl i < \<alpha>\<^sub>r (rankr rkl i)"
  using assms level_lt_\<alpha>\<^sub>r[OF assms(1-3)] by argo

\<comment>\<open> We note that the equality hypothesis on the ranks is required.
   Indeed, in case 3, we could have @{term "level l rkl i = \<alpha>\<^sub>r (rankr rkl i)"}. \<close>

lemma \<phi>_case_2_safe_index:
  assumes "invar_rank l rkl" "i<length l" "l!i\<noteq>i"  "\<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "index l rkl i \<le> (\<alpha>\<^sub>r (rankr rkl i) - level l rkl i) * (rankr rkl i)"
  apply (rule order.trans[OF index_le_rank[OF assms(1-3)]])
  apply simp using rankr_positive[of rkl i] using \<phi>_case_2_safe_level[OF assms] by linarith

\<comment>\<open> In case 1 above, [phi x] is at least 1. (Page 18.) \<close>
\<comment>\<open> This property seems unused, so we do not name it. \<close>

lemma assumes "l!i=i" shows "1 \<le> \<phi> l rkl i"
proof -
  { fix z::nat have "1\<le>z \<longleftrightarrow> 0<z" by fastforce } note alt = this
  show ?thesis
    apply (subst \<phi>_case_1[OF assms])
    apply (subst alt)
    apply (rule mult_pos_pos)
     apply (simp add: alphar_pos[OF \<rho>_gt_0]) 
    by simp
qed


\<comment>\<open> In case 2 above, @{term "\<phi> l rkl i"} is at least 1. (Page 18) \<close>

lemma \<phi>_case_2_lower_bound:
  assumes "invar_rank l rkl" "i<length l" "l!i\<noteq>i"  "\<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "1 \<le> \<phi> l rkl i"
  apply (subst \<phi>_case_2[OF assms(3,4)])
  using \<phi>_case_2_safe_index[OF assms]
  by presburger

\<comment>\<open> Alstrup et al. write, on page, 18, "if x is a nonroot leaf, then rankr (x) = \<rho>".
   This appears to be false: in the presence of path compression, a nonroot leaf
   can have nonzero rank. (Imagine it used to be a root with nonzero rank and (as
   per the numerous family condition) many descendants; but these descendants were
   removed by path compression.) Thus, we are unable to conclude that phi x = 0.
   This does not seem to be a problem: this remark in not exploited anywhere. \<close>

\<comment>\<open> An upper bound on @{term "\<phi> l rkl i"}. In any case, @{term "\<phi> l rkl i"}
   is at most the formula that appears in case 1. \<close>

lemma \<phi>_upper_bound:
 "\<phi> l rkl i \<le> \<alpha>\<^sub>r (rankr rkl i) * Suc (rankr rkl i)"
  unfolding \<phi>_def
  apply (simp cong: if_cong) apply safe proof goal_cases
  case 1
  let ?n = "\<alpha>\<^sub>r (rankr rkl i)"
  have "0 < ?n" by (simp add: \<rho>_gt_0 alphar_pos)
  have gener: "Suc ((?n - level l rkl i) * rankr rkl i) \<le> ?n + ?n * rankr rkl i"  
    using \<open>0 < ?n\<close> by (auto simp: algebra_simps)
  have "rankr rkl i - index l rkl i \<le> rankr rkl i" by simp
  with gener 1 show ?case by fastforce
qed


section{*Lemmas about \<Phi>, i.e. about the whole Union Find data structure*}

lemma \<Phi>_empty:
  "\<Phi> [] [] = 0"
  by simp

\<comment>\<open> If @{term i} is a root and has zero rank, then @{term "\<phi> l rkl i = \<rho> + 1"}\<close>

lemma \<phi>_root_zero_rank:
  assumes "invar_rank l rkl" "i < length l" "l!i=i" "rkl!i=0"
  shows "\<phi> l rkl i = Suc \<rho>"
proof -
  have f: "rankr rkl i = \<rho>" unfolding rankr_def using \<open>rkl!i=0\<close> by simp
  show ?thesis  
    apply (subst \<phi>_case_1[OF \<open>l!i=i\<close>])
    apply (subst f)+
    apply (subst alphar_r[OF \<rho>_gt_0]) by simp
qed

\<comment>\<open>The next lemma in Coq (\<Phi>_extend) doesn't apply to our model with a fixed domain\<close>



lemma invar_rank_sli_le_l:
  assumes "invar_rank l rkl" "ufa_invar l" "i<length l"
  shows "rkl ! (rep_of l i) \<le> length l"
proof -
  from assms(1) have a: "sum (\<lambda>i. if l!i=i then rkl !i else 0) {0..<length l} \<le> length l"
      and len: "length rkl = length l" by(auto simp: invar_rank_def)
  let ?r = "(rep_of l i)"
  from assms have "?r<length l" by(auto simp: rep_of_bound)    
  then have f: "{0..<length l} = {?r} \<union> ({0..<length l}-{?r})" by auto
  have "rkl ! (?r) \<le> sum (\<lambda>i. if l!i=i then rkl !i else 0) ({0..<length l}-{?r}) + (if l!?r=?r then rkl !?r else 0)"
    using assms by (auto simp: rep_of_min) 
  also have "\<dots> = sum (\<lambda>i. if l!i=i then rkl !i else 0) {0..<length l}"
    apply(subst (2) f) apply(subst sum_Un_nat) by simp_all
  also have "\<dots> \<le> length l" using a by simp
  finally show "rkl ! (rep_of l i) \<le> length l" .
qed


lemma amortized_cost_compress:
  assumes "ufa_invar l"
  shows "\<Phi> l rkl + 2* (\<alpha>\<^sub>r (card (Domain (ufa_\<alpha> l)))) + 4 \<ge> \<Phi> (l[x := rep_of l x]) rkl + d + 1"
  apply (subst ufa_\<alpha>_dom_card)
  sorry

end