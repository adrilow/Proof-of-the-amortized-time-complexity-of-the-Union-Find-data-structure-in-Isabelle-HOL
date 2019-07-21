theory Union_Find_Time_alpha_abstract_analysis

imports 
  "../../SepLog_Automatic" 
  "../../Refine_Imperative_HOL/Refine_Automation" 
  Collections.Partial_Equivalence_Relation
  "HOL-Library.Code_Target_Numeral"
  \<comment>\<open>"SepLogicTime_RBTreeBasic.Asymptotics_1D"\<close>
 (* UnionFind_Impl *)
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

lemma ufa_\<beta>_start_functional:
  assumes "ufa_invar l" "i< length l" "j < length l" "i'<length l"
          "(i,j)\<in> ufa_\<beta>_start l" "(i,i')\<in> ufa_\<beta>_start l"
        shows "j = i'" 
  using assms unfolding ufa_\<beta>_start_def by fast

\<comment>\<open>If we are in a cycle and make one step, then we are still in a cycle.\<close>

lemma one_step_in_a_cycle:
  assumes "ufa_invar l" "i <length l" "j<length l" "i'<length l" "(i,j) \<in> ufa_\<beta> l" "i = j" "(i,i') \<in> ufa_\<beta>_start l"
  shows "(i',i') \<in> ufa_\<beta> l"
  using assms(5,1,2,3,4,6,7) unfolding ufa_\<beta>_def  
proof (induction arbitrary: i'  rule: trancl_induct)
  case (base y)
  hence "y = i'" using ufa_\<beta>_start_functional by fast
  then show ?case using base by blast
next
  case (step y z)
  have "(y,i) \<in> ufa_\<beta>_start l" using step by argo
  have "(y, y) \<in> (ufa_\<beta>_start l)\<^sup>+" using step(1) \<open>(y, i) \<in> ufa_\<beta>_start l\<close> by auto
  have "(i',y) \<in> (ufa_\<beta>_start l)\<^sup>+ \<or> i'=y" using step(1) step(9) apply safe unfolding ufa_\<beta>_start_def 
    using converse_tranclE  by force
  thus ?case using step \<open>(y, y) \<in> (ufa_\<beta>_start l)\<^sup>+\<close> by fastforce 
qed

\<comment>\<open>Thus, a path cannot leave a cycle.\<close>

lemma cannot_escape_a_cycle:
  assumes "ufa_invar l" "i <length l" "j<length l" "(i,i) \<in> ufa_\<beta> l" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "(j,j) \<in> ufa_\<beta> l"
  using assms(5,1-4) unfolding ufa_\<beta>_def thm converse_trancl_induct[of i i] 
proof (induction arbitrary: i rule: rtrancl_induct)
  case base
  then show ?case using assms  unfolding ufa_\<beta>_def by blast
next
  case (step y z)
  hence "y<length l" unfolding ufa_\<beta>_start_def by blast
  show ?case using one_step_in_a_cycle 
      step(3)[OF \<open>ufa_invar l\<close> \<open>i<length l\<close> \<open>y<length l\<close> \<open>(i, i) \<in> (ufa_\<beta>_start l)\<^sup>+\<close>] 
      step(1,2) step(4-7) unfolding ufa_\<beta>_def ufa_\<beta>_start_def by blast
qed

\<comment>\<open>Thus, the fact every vertex has a representative contradicts the
   existence of a cycle.\<close>

lemma aciclicity:
  assumes "ufa_invar l" "i<length l" "(i,i) \<in> ufa_\<beta> l"
  shows "False"
proof -
  let ?z = "rep_of l i"
  have sg0: "(i,?z)\<in> (ufa_\<beta>_start l)\<^sup>*" using rep_of_ufa_\<beta>_refl[OF assms(1,2)] .
  have sg1: "?z=l!?z" by (simp add: assms(1,2) rep_of_min)
  have sg1': "?z<length l" by (simp add: assms(1,2) rep_of_bound)
  have sgz: "(?z,?z) \<in> ufa_\<beta> l" using cannot_escape_a_cycle sg1 sg1' sg0 assms by blast
  thus ?thesis using sg0 sg1 sg1' sgz assms unfolding ufa_\<beta>_def ufa_\<beta>_start_def
    using tranclD by fast
qed
  
\<comment>\<open>If there is a non-empty path from i to j, then i and j must be distinct.\<close>

lemma paths_have_distinct_endpoints:
  assumes "ufa_invar l" "i<length l" "j<length l" "(i,j) \<in> ufa_\<beta> l"
  shows "i \<noteq> j"
proof (rule ccontr)
  assume "\<not>i\<noteq>j" hence "i = j" by simp
  thus "False" using aciclicity assms by fast
qed

\<comment>\<open>If there is an edge from i to j, then i and j must be distinct.\<close>

lemma edges_have_distinct_endpoints:
  assumes "ufa_invar l" "i<length l" "j<length l" "(i,j) \<in> ufa_\<beta>_start l"
  shows "i\<noteq>j"
  using assms unfolding ufa_\<beta>_start_def by blast

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
  "descendants l i = {j. (j,i)\<in> (ufa_\<beta>_start l)\<^sup>*}"

definition ancestors where
  "ancestors l i = {j. (i,j)\<in> (ufa_\<beta>_start l)\<^sup>*}"

lemma ancestors_in_domain:
  assumes "i<length l" 
  shows "ancestors l i \<subseteq> {0..<length l}"
  unfolding ancestors_def 
  apply auto 
  proof goal_cases
  case (1 x)
  then show ?case using assms proof (induction rule: rtrancl_induct)
    case (step y z)
    then show ?case unfolding ufa_\<beta>_start_def by simp
  qed simp
qed



definition invar_rank where "invar_rank l rkl \<equiv> (ufa_invar l \<and> length l = length rkl 
                            \<and> (\<forall>i j. i< length l \<and> j< length l \<and> l!i=j \<and>  i\<noteq>j \<longrightarrow> rkl ! i < rkl ! j) 
                            \<comment> \<open>if j is on the path from i to rep_of l i, then rank of j is bigger than rank of i\<close>
                            \<and> sum (\<lambda>i. if l!i=i then rkl!i else 0) {0..<length l} \<le> length l
                            \<and> (\<forall>i<length l. l!i=i \<longrightarrow> (2::nat) ^ rkl!i \<le> card (descendants l i)) )"
                            \<comment>\<open>rank i \<le> log (card (Domain (ufa_\<alpha> l)))\<close>

definition invar_rank' where "invar_rank' l rkl \<equiv> ufa_invar l \<and> invar_rank l rkl"

subsection{*Lemmas About the rank from UnionFind11Rank, UnionFind21Parent and UnionFind41Potential*}

lemma invar_rank_ufa_invarI: "invar_rank l rkl \<Longrightarrow> ufa_invar l" unfolding invar_rank_def by blast


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
  using rank_increases_along_path_refl[OF assms(1-3)] by fastforce


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



lemma descendant_of_root:
  assumes "ufa_invar l" "r<length l"  "x<length l" "r=l!r" 
  shows "x \<in> descendants l r \<longleftrightarrow> r = rep_of l x"
  using rep_of_path_iff[OF \<open>ufa_invar l\<close> \<open>r<length l\<close> \<open>x<length l\<close>] 
  unfolding descendants_def ufa_\<beta>_start_def using assms(4) by auto

lemma descendants_subset_domain:
  assumes "ufa_invar l" "x < length l"
  shows "descendants l x \<subseteq> {0..<length l}"
  using assms unfolding descendants_def proof (auto,goal_cases)
  case (1 y)
    then show ?case unfolding ufa_\<beta>_start_def using converse_rtranclE by force
  qed


lemma disjoint_descendants:
  assumes "ufa_invar l" "x<length l" "y<length l" "x = l!x" "y = l!y" "x\<noteq>y"
  shows "(descendants l x)\<inter>(descendants l y) = {}"
proof (auto,goal_cases)
  case (1 z)
  have "z<length l" using 1(1) using descendants_subset_domain[OF assms(1,2)] by auto
  have sg1: "x = rep_of l z" using 1 
      descendant_of_root[OF \<open>ufa_invar l\<close> \<open>x<length l\<close> \<open>z<length l\<close> \<open>x=l!x\<close>] by blast
  have sg2: "y = rep_of l z" using 1 
      descendant_of_root[OF \<open>ufa_invar l\<close> \<open>y<length l\<close> \<open>z<length l\<close> \<open>y=l!y\<close>] by blast
  show ?case using sg1 sg2 \<open>x\<noteq>y\<close> by blast
qed



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
    have sg1: "card (descendants l i) \<le> length l" 
      using descendants_subset_domain[OF _ \<open>i<length l\<close>] assms(1) unfolding invar_rank_def 
      by (simp add: subset_eq_atLeast0_lessThan_card)
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

lemma lnn_f_nat_nat: "f_nat_nat defk"
  apply standard subgoal using Ackermann_strict_mono_in_k rankr_positive unfolding defk_def by blast
  subgoal using Ackermann_k_x_tends_to_infinity_along_k rankr_positive unfolding defk_def by blast
  done


interpretation lnn: f_nat_nat "defk" using lnn_f_nat_nat .
  
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

lemma inn_f_nat_nat: "f_nat_nat (\<lambda>j. compow j (Ackermann prek) (rankr rkl i))"
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

interpretation inn: f_nat_nat "\<lambda>j. compow j (Ackermann prek) (rankr rkl i)" 
  using inn_f_nat_nat .

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


section{*Lemmas about parents during ufa_union and compression (UnionFind22ParentEvolution)*}

\<comment>\<open>During a union, a vertex v which already has a parent keeps this parent.\<close>

lemma ufa_union_preserves_parent:
  assumes "ufa_invar l" "x<length l" "y<length l" "v<length l" "x=l!x" "v\<noteq>l!v"
  shows "l!v = (ufa_union l x y)!v"
proof (cases "v\<noteq>x")
  case True
    then show ?thesis using assms by (simp add: rep_of_refl)
  next
  case False
    then show ?thesis using assms by fast
  qed


\<comment>\<open>After a link, the parent of x is y. Yes, but we don't have the link operation, only union\<close>

lemma ufa_union_sets_parent:
  assumes "ufa_invar l" "x<length l" "y<length l" "x=l!x"
  shows "(ufa_union l x y)!x = rep_of l y"
proof -
  have "rep_of l x = x" using assms using rep_of_refl by auto
  hence "rep_of (ufa_union l x y) x = rep_of l y" using  assms(1-3) rep_of_refl ufa_union_aux by fastforce
  thus ?thesis using assms  \<open>rep_of l x = x\<close> by auto
qed

section {*Lemmas about paths and inavriants under compression (UnionFind04Compress)*}

context 
  fixes x::nat and y::nat and l::"nat list"
  assumes x_edge_y: "(x,y)\<in> (ufa_\<beta>_start l)"
begin \<comment>\<open>x_edge_y\<close>

lemma compress_preserves_other_edges:
  assumes "(v,w)\<in> (ufa_\<beta>_start l)" "v\<noteq>x"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))"
  using assms unfolding ufa_\<beta>_start_def by auto

lemma compress_preserves_roots:
  assumes "r = l!r"
  shows "r = l[x:=rep_of l x] ! r"
  using assms apply (cases "r = x") apply auto using rep_of_refl list_update_id by metis

context
  assumes inv: "ufa_invar l" and
          pathyz: "(y, rep_of l x) \<in> (ufa_\<beta>_start l)\<^sup>*"
begin \<comment>\<open>invar\<close>

lemma compress_preserves_paths_out_of_y:
  assumes "(v,w)\<in>(ufa_\<beta>_start l)\<^sup>*" "(y,v)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))\<^sup>*"
  sorry

lemma compress_preserves_paths_out_of_z:
  assumes "(v,w)\<in>(ufa_\<beta>_start l)\<^sup>*" "(rep_of l x,v)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))\<^sup>*"
  using compress_preserves_paths_out_of_y[OF assms(1)] pathyz assms(2) rtrancl_trans by fast


lemma compress_preserves_paths_to_roots:
  assumes "(v,r)\<in>(ufa_\<beta>_start l)\<^sup>*" "r=l!r"
  shows "(v,r)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))\<^sup>*"
  using assms pathyz x_edge_y inv
proof (induction)
case base
then show ?case by blast
next
  case (step y z)
  then show ?case proof (cases "x = v")
    case True
    from step True show ?thesis 
      by (smt case_prodD length_list_update mem_Collect_eq rep_of_bound rep_of_idx 
          rep_of_invar_along_path rep_of_path_iff rep_of_refl ufa_\<beta>_start_def ufa_compress_aux(2) 
          ufa_compress_invar)
  next
    case False
    show ?thesis apply (rule converse_rtrancl_into_rtrancl)
      using compress_preserves_other_edges[OF _ False[symmetric], of y] step 
      sorry
  qed
qed

lemma compress_preserves_rep_of_direct:
  assumes "r = rep_of l x"
  shows "r = rep_of (l[x := rep_of l x]) x"
  using assms inv ufa_\<beta>_start_def ufa_compress_aux(2) x_edge_y by auto


end \<comment>\<open>invar\<close>
end \<comment>\<open>x_edge_y\<close>


section {*Lemmas about \<Phi> under compression (UnionFind42PotentialCompress)*}

\<comment>\<open>During a compression, the level function is unchanged at ancestors of y\<close>

\<comment>\<open>This would be compress_preserves_k_above_y, again this does not apply as we compress differently\<close>


\<comment>\<open> Assume x and y are non-roots. (This is required for their level and index
   to be defined.) Assume that there is a non-trivial path from x to y.
   Finally, assume that x and y have the same level, i.e., @{term "level l rkl x = level l rkl y"}.
   Then, @{term "compow (Suc (index l rkl x)) (Ackermann (prek l rkl x)) (rankr rkl x) \<le> rankr rkl (l!y)"}. 
   This is part of the proof of Lemma 4.10 in Alstrup et al.'s paper. \<close>

lemma levelx_levely:
  assumes "invar_rank l rkl" "x<length l" "y<length l" "x\<noteq>l!x" "y\<noteq>l!y" "(l!x,y) \<in> (ufa_\<beta>_start l)\<^sup>*" "level l rkl x = level l rkl y"
  shows "compow (Suc (index l rkl x)) (Ackermann (prek l rkl x)) (rankr rkl x) \<le> rankr rkl (l!y)"
proof -
  have pp: "prek l rkl x = prek l rkl y" using level_def assms by simp
  \<comment>\<open> Because there is a path from the parent of x to y, the rank of y
     is at least the rank of the parent of x. \<close>
  have "l!x<length l" using assms(1,2) unfolding invar_rank_def ufa_invar_def by blast
  hence hxy: "rankr rkl (l!x) \<le> rankr rkl y"
    using  assms rankr_increases_along_path_refl by blast
  \<comment>\<open> By definition of @{term "index l rkl"}, iterating @{term "index l rkl x"} times 
    @{term "Ackermann (prek l rkl x)"}, starting from @{term "rankr rkl x"}, takes us at most to c
     @{term "rankr rkl (l!x)"}. \<close>
  have hx: "compow (index l rkl x) (Ackermann (prek l rkl x)) (rankr rkl x) \<le> rankr rkl (l!x)"
    unfolding index_def[OF assms(1,2) assms(4)[symmetric]] 
    apply (rule f_nat_nat.f_\<beta>\<^sub>f[OF inn_f_nat_nat, OF assms(1) assms(2) assms(4)[symmetric], of "rankr rkl (l ! x)"])
    apply simp
    using assms(1,2) parent_has_greater_rankr by fastforce
  (* By definition of [prek], applying [A (prek x)] to [rankr y] takes us
     at least to [rankr (p y)]. *)
  have hy': "Ackermann 0 (rankr rkl y) \<le> rankr rkl (l ! y)" apply (subst Ackermann_base_eq) unfolding rankr_def 
    using assms(1,3,5) parent_has_greater_rank by fastforce
  have hy: "Ackermann (prek l rkl x) (rankr rkl y) \<le> rankr rkl (l!y)"
    apply (subst pp)
    using f_nat_nat.\<beta>\<^sub>f_spec_direct[OF lnn_f_nat_nat, OF assms(1) assms(3) assms(5)[symmetric], of "rankr rkl (l ! y)" "(prek l rkl y)"] unfolding defk_def[OF assms(1) assms(3) assms(5)[symmetric]] sorry
  show ?thesis apply simp using hx hxy hy sorry
qed


\<comment>\<open>Under the same assumptions as the previous lemma, if one preforms path compression on x then
  either @{term "rankr rkl x"} changes (which means it increases, really, but we have not proved 
  that), or @{term "index l rkl x"} increases\<close>

lemma levelx_levely_compress:
  assumes "invar_rank l rkl" "x<length l" "y<length l" "x\<noteq>l!x" "y\<noteq>l!y" "(l!x,y) \<in> (ufa_\<beta>_start l)\<^sup>*" "level l rkl x = level l rkl y"
          "z = rep_of l x" "level l rkl x = level (l[x:= rep_of l x]) rkl x"
  shows "Suc (index l rkl x) \<le> index (l[x:= rep_of l x]) rkl x"
proof -
  have pyz: "z = rep_of l (l!y)" using assms
    by (metis (no_types, hide_lams) invar_rank_def rep_of_bound rep_of_idx rep_of_invar_along_path ufa_invarD(2))
  have rpyz: "rankr rkl (l!y) \<le> rankr rkl z"
    by (metis (no_types, lifting) assms(1) assms(3) eq_iff invar_rank_def pyz rankr_increases_along_path_refl rep_of_bound rep_of_ufa_\<beta>_refl ufa_invarD(2))
  note f = levelx_levely[OF assms(1-7)]
  have rpyz': "(Ackermann (prek l rkl x) ^^ Suc (index l rkl x)) (rankr rkl x) \<le> rankr rkl z" using rpyz f by linarith
  have prehkk: "prek l rkl x = prek (l[x:= rep_of l x]) rkl x" using assms(9) using level_def assms sorry
  show ?thesis sorry
qed



section{*Notion of state evolution over time (UnionFind13RankLink, UnionFind23Evolution)*}


subsubsection{*UnionFind13RankLink*}
definition union_by_rank_l where "union_by_rank_l l rkl x y \<equiv> if (rkl!x < rkl!y) 
                                  then (ufa_union l x y) else (ufa_union l y x)"

definition union_by_rank_rkl where "union_by_rank_rkl rkl x y \<equiv> if (rkl!x = rkl!y) 
                                    then rkl[x := Suc (rkl!x)] else rkl"

lemma link_cannot_decrease_rank:
  "rkl!v \<le> (union_by_rank_rkl rkl x y)!v"
  unfolding union_by_rank_rkl_def 
  apply (cases "rkl!x=rkl!y")
  apply (simp cong: if_cong) 
   apply (metis eq_iff lessI less_imp_le_nat nth_list_update_eq nth_list_update_neq nth_update_invalid)
  by (simp cong: if_cong)

lemma link_preserves_rank_of_non_roots:
  assumes "x<length l" "y<length l" "v<length l" "x=l!x" "v\<noteq>l!v"
  shows "rkl!v = (union_by_rank_rkl rkl x y)!v"
proof -
  have "x\<noteq>v" using assms by blast
  thus ?thesis unfolding union_by_rank_rkl_def 
    using assms nth_list_update_neq[OF \<open>x \<noteq>v\<close>, of  rkl "Suc (rkl!x)"]
    by (auto cong: if_cong)  
qed

lemma invar_rank_link:
  assumes "invar_rank l rkl" "x < length l" "y < length l" "x=l!x" "y=l!y" "x\<noteq>y"
  shows "invar_rank (union_by_rank_l l rkl x y) (union_by_rank_rkl rkl x y)"
  sorry

lemma invar_rank_compress:
  assumes "invar_rank l rkl"  "(x,y)\<in>(ufa_\<beta>_start l)"
  shows "invar_rank (l[x:= rep_of l y]) rkl"
  unfolding invar_rank_def using assms proof (safe,goal_cases)
  case 1
  then show ?case unfolding ufa_\<beta>_start_def
    using invar_rank_ufa_invarI rep_of_idx ufa_compress_invar by auto
next
  case 2
  then show ?case unfolding invar_rank_def by auto
next
  case (3 i j)
  then show ?case unfolding ufa_\<beta>_start_def
    by (smt case_prodD invar_rank_ufa_invarI length_list_update mem_Collect_eq 
        nth_list_update' parent_has_greater_rank rank_increases_strictly_along_path 
        rep_of_iff rep_of_ufa_\<beta>)
next
  case 4
  then show ?case unfolding invar_rank_def  unfolding ufa_\<beta>_start_def apply auto
    by (smt case_prodD mem_Collect_eq nth_list_update_eq nth_list_update_neq rep_of_path_iff sum_ivl_cong)
next
  case (5 i)
  then show ?case unfolding invar_rank_def apply auto sorry
qed


\<comment>\<open>This is only an application of @{thm ufa_union_correct}\<close>
lemma dsf_per_add_edge_by_rank: "False" oops 

\<comment>\<open>The second part of UnionFind13RankLink seems to specific to be needed, but maybe it
is useful to have some explicit lemmas about rep_of under union_by_rank\<close>


subsection{*UnionFind23Evolution*}

inductive evolution
for l::"nat list" and rkl::"nat list"
  where 
  EvUnion: "x<length l \<Longrightarrow> y<length l \<Longrightarrow> x=l!x \<Longrightarrow> y=l!y \<Longrightarrow> x\<noteq>y 
          \<Longrightarrow> evolution l rkl (union_by_rank_l l rkl x y) (union_by_rank_rkl rkl x y)"
| EvCompress: "(x,y)\<in>(ufa_\<beta>_start l) \<Longrightarrow>  evolution l rkl (l[x:= rep_of l y]) rkl"


lemma compress_evolution:
  assumes "invar_rank l rkl" "x<length l" "x\<noteq>l!x" 
  shows "evolution l rkl (l[x:= rep_of l x]) rkl"
proof -
  have pxz: "rep_of l (l!x) = rep_of l x" using assms unfolding invar_rank_def
    using rep_of_idx by blast
  have "l!x < length l" using assms unfolding invar_rank_def ufa_invar_def by blast
  hence "(x,l!x)\<in> (ufa_\<beta>_start l)" using assms unfolding ufa_\<beta>_start_def by blast
  with assms pxz EvCompress show ?thesis by fastforce
qed

context \<comment>\<open>StudyOfEvolution\<close>
  fixes l::"nat list" and rkl::"nat list" and l'::"nat list" and rkl'::"nat list"
  assumes contextasm: "invar_rank l rkl" "evolution l rkl l' rkl'"
begin

lemma invar_rank_evolution: "invar_rank l' rkl'"
  using contextasm(2,1) invar_rank_link invar_rank_compress 
  by (induction rule: evolution.induct) blast+
  

lemma rank_grows: "rkl!v \<le> rkl'!v"
  using contextasm(2,1) link_cannot_decrease_rank 
  by (induction rule: evolution.induct) blast+

lemma non_root_has_constant_rank:
  assumes "v<length l" "v\<noteq>l!v"
  shows "rkl!v = rkl'!v"
  using contextasm(2,1) assms link_preserves_rank_of_non_roots 
  by (induction rule: evolution.induct) blast+


lemma non_root_forever:
  assumes "v\<noteq>l!v"
  shows "v\<noteq>l'!v"
  using contextasm(2,1) proof (induction rule: evolution.induct)
  case (EvUnion x y)
  then show ?case unfolding union_by_rank_l_def using assms rep_of_refl
    apply (simp cong: if_cong) by (metis nth_list_update_neq)
next
  case (EvCompress x y)
  have "ufa_invar l" using invar_rank_ufa_invarI[OF contextasm(1)] .
  then show ?case using assms unfolding invar_rank_def
    by (metis (no_types, lifting) case_prodD local.EvCompress(1) mem_Collect_eq 
        nth_list_update_eq nth_list_update_neq rep_of_min ufa_\<beta>_start_def)
qed

\<comment>\<open>The quantity @{term "rkl!(l!v)"} grows with time, either because the rank of the parent of v
  changes (during a union), or because the parent of v changes (during compression).\<close>

lemma rank_parent_grows:
  assumes "v\<noteq>l!v"
  shows "rkl!(l!v) \<le> rkl'!(l'!v)"
  sorry

end  \<comment>\<open>StudyOfEvolution\<close>



section{*Evolution of level, index and potential over time (UnionFind43PotentialAnalysis)*}

context \<comment>\<open>StudyOfEvolution\<close>
  fixes l::"nat list" and rkl::"nat list" and l'::"nat list" and rkl'::"nat list"
  assumes contextasm: "invar_rank l rkl" "evolution l rkl l' rkl'"
begin


context \<comment>\<open>NonRoot\<close>
  fixes v::nat
  assumes vinDom: "v<length l" and
    v_has_a_parent: "v\<noteq>l!v"
begin

lemma non_root_has_constant_rankr:
  "rankr rkl v = rankr rkl' v"
  using \<rho>_gt_0 non_root_has_constant_rank[OF contextasm vinDom v_has_a_parent] unfolding rankr_def by simp

lemma rankr_parent_grows:
  "rankr rkl (l!v) \<le> rankr rkl' (l'!v)"
  using \<rho>_gt_0 rank_parent_grows[OF contextasm v_has_a_parent]  unfolding rankr_def by simp


\<comment>\<open>Because @{term "rankr rkl v"} is constant while @{term "rankr rkl (l!v)"} may grow, 
  @{term "level l rkl v"} can only grow\<close>

lemma level_v_grows:
  "level l rkl v \<le> level l' rkl' v"
  sorry

\<comment>\<open>As long as  @{term "level l rkl v"} remains constant, @{term "index l rkl v"} can only grow.\<close>

lemma index_v_grows_if_level_v_constant:
  assumes "level l rkl v = level l' rkl' v"
  shows "index l rkl v \<le> index l' rkl' v"
  sorry

\<comment>\<open>The potential @{term "\<phi> l rkl v"} cannot increase. (Lemma 4.5 on pages 18-19)\<close>

lemma \<phi>_cannot_increase_nonroot:
  "\<phi> l' rkl' v \<le> \<phi> l rkl v"
  sorry


end \<comment>\<open>NonRoot\<close>


\<comment>\<open>Let v be an arbitrary vertex (possibly a root). If its rank is preserved,
   then its potential cannot increase.\<close>


lemma \<phi>_v_cannot_increase:
  assumes "v<length l" "rankr rkl v = rankr rkl' v"
  shows "\<phi> l' rkl' v \<le> \<phi> l rkl v"
proof (cases "v\<noteq>l!v")
  case True
  show ?thesis using \<phi>_cannot_increase_nonroot[OF assms(1) True] .
next
  case False
  hence is_root: "l!v = v" by presburger
  show ?thesis
    apply (subst \<phi>_case_1[OF is_root, of rkl]) 
    apply(rule  \<phi>_upper_bound[of l' rkl' v] order.trans[OF \<phi>_upper_bound[of l' rkl' v], 
                of "\<alpha>\<^sub>r (rankr rkl v) * Suc (rankr rkl v)"])
    apply (subst assms)+
    by blast
qed

end  \<comment>\<open>StudyOfEvolution\<close>


\<comment>\<open>The increase of the potential \<Phi> during a link is at most 2. This is
   Lemma 4.7 on page 19. The formal proof follows roughly the paper proof,
   except we find it necessary to make certain case analyses explicit.\<close>

lemma potential_increase_during_link_preliminary:
  assumes "invar_rank l rkl" "x\<noteq>y" "x<length l" "y<length l" "x=l!x" "y=l!y" 
  "(rkl!x < rkl!y \<and> rkl' = rkl) \<or> (rkl!x = rkl!y \<and> rkl'= rkl[y:= Suc (rkl!y)])"
  "evolution l rkl (ufa_union l x y) rkl'"
shows "\<Phi> (ufa_union l x y) rkl' \<le> \<Phi> l rkl + 2 "
  sorry \<comment>\<open>:-)\<close>


lemma potential_increase_during_link:
  assumes "invar_rank l rkl" "x\<noteq>y" "x<length l" "y<length l" "x=l!x" "y=l!y"
  "l' = union_by_rank_l l rkl x y" "rkl' = union_by_rank_rkl rkl x y"
shows "\<Phi> l' rkl' \<le> \<Phi> l rkl + 2"
proof -
  have sg0: "evolution l rkl l' rkl'" using assms by (auto intro: evolution.intros)
  show ?thesis 
    apply (subst assms(7)) apply (subst assms(8))
    unfolding union_by_rank_l_def union_by_rank_rkl_def
    using potential_increase_during_link_preliminary[OF assms(1-6), of rkl' ] sg0 
    apply (subst (asm) assms(7)) unfolding union_by_rank_l_def union_by_rank_rkl_def
    by (smt assms(1,3,4,5,6,8) not_less_iff_gr_or_eq potential_increase_during_link_preliminary
        union_by_rank_l_def union_by_rank_rkl_def)
qed

section{*Abstract definition of iterated path compression (UnionFind05IteratedCompression)*}

\<comment>\<open> We now define an inductive predicate that encodes the process of performing
   path compression iteratively along a path, up to the root. ipc stands for
   "iterative path compression". The predicate @{term "ipc l x i l'"} means that in
   the initial state l, performing path compression along the path that
   begins at x leads in i steps to the final state l'. \<close>

\<comment>\<open> We define backward and forward variants of this predicate, bw_ipc and
   fw_ipc.

   The forward variant corresponds intuitively to a two-pass algorithm, where
   the first pass finds the representative z, and the second pass performs
   iterated path compression. This formulation is clearly the sequential
   composition of several path compression steps. For this reason, this
   formulation is more amenable to a simple proof of several lemmas (e.g.
   amortized_cost_fw_ipc_preliminary and invar_rank_fw_ipc.

   The backward variant corresponds intuitively to the one-pass, recursive
   formulation of path compression, where path compression is performed as the
   stack is unwound. This formulation is *not* clearly the sequential
   composition of several path compression steps, because it is not obvious
   a priori that the representative of x before compression is the
   representative of x after compression.

   Naturally, the two predicates are in fact equivalent. \<close>

inductive bw_ipc
  where
  BWIPCBase: "x=l!x \<Longrightarrow> bw_ipc l x 0 l"
| BWIPCStep: "(x,y)\<in>(ufa_\<beta>_start l) \<Longrightarrow> bw_ipc l y i l' \<Longrightarrow> bw_ipc l x (Suc i) (l'[x:= rep_of l' x])"

inductive fw_ipc
  where
  FWIPCBase: "x=l!x \<Longrightarrow> fw_ipc l x 0 l"
| FWIPCStep: "(x,y)\<in>(ufa_\<beta>_start l) \<Longrightarrow> fw_ipc (l[x:= rep_of l y]) y i l' \<Longrightarrow> fw_ipc l x (Suc i) l'"


lemma bw_ipc_root_unique:
  assumes "x = l!x" "bw_ipc l x i l'"
  shows "i = 0 \<and> l' = l"
  using assms(2,1) proof (induction rule: bw_ipc.induct)
  case (BWIPCBase x l)
  then show ?case by blast
next
  case (BWIPCStep x y l i l')
  then show ?case unfolding ufa_\<beta>_start_def by blast
qed

lemma ipc_defined:
  assumes "ufa_invar l"
  shows "\<exists> i l'. bw_ipc l x i l'"
  sorry

lemma bw_ipc_fw_ipc:
  assumes "ufa_invar l" "bw_ipc l x i l'" 
  shows "fw_ipc l x i l'"
  sorry

lemma fw_ipc_bw_ipc:
  assumes "ufa_invar l" "fw_ipc l x i l'"
  shows "bw_ipc l x i l'" 
  sorry

\<comment>\<open>One probably needs the lemmas of this file (equivalence of the two, properties about
  single step compressions and the predicates) to proceed. But without developing the proofs,
  the concrete required formulation is not yet clear.\<close>



section{*Lemmas about pleasantness (UnionFind24Pleasant)*}

\<comment>\<open> This section defines the notion of ``pleasantness'' -- the property of having
   a proper non-root ancestor with the same level -- and establishes several
   lemmas which establish an upper bound on the number of unpleasant vertices. \<close>

\<comment>\<open> This reasoning is usually not explicitly carried out on paper, yet it is
   quite lenghty and painful here. \<close>

\<comment>\<open> We parameterize these definitions and lemmas over a predicate ok and a
   level function, so that they work both for Tarjan's original proof and
   for Alstrup et al.'s proof. \<close>

locale Pleasant = \<comment>\<open>Pleasant\<close>
  fixes ok::"nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
    and level::"nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" 
begin


context \<comment>\<open>FK\<close>
  fixes l::"nat list"  and rkl::"nat list"
assumes contextasm: "invar_rank l rkl" 
begin

\<comment>\<open> A non-root vertex @{term x} is pleasant if it is OK and if it has a proper non-root
   ancestor @{term y} such that @{term x} and @{term y} have the same level, 
   i.e., @{term "level l rkl x = level l rkl y"}. \<close>

definition pleasant where "pleasant x \<equiv> ok l rkl x \<and> x\<noteq>l!x 
    \<and> (\<exists>y. y\<noteq>l!y \<and> ((l!x),y) \<in> (ufa_\<beta>_start l)\<^sup>* \<and> (level l rkl x = level l rkl y) )"

lemma pleasant_non_root:
  assumes "pleasant x" shows "x\<noteq>l!x"
  using assms unfolding pleasant_def by fast

definition unpleasant_ancestors where "unpleasant_ancestors x \<equiv> 
                                       (ancestors l x) \<inter> {y. (\<not>pleasant y) \<and> y\<noteq>l!y}"

definition displeasure where "displeasure x \<equiv> card (unpleasant_ancestors x)"

lemma ancestors_of_parent:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)"
  shows "ancestors l x = ancestors l y \<union> {x}"
  unfolding ancestors_def proof( auto, goal_cases)
  case (1 z)
  then show ?case using assms unfolding ufa_\<beta>_start_def
    using converse_rtranclE by force
next
  case (2 z)
  then show ?case using assms unfolding ufa_\<beta>_start_def 
    by (meson converse_rtrancl_into_rtrancl)
qed

lemma ancestors_of_root:
  assumes "x=l!x"
  shows "ancestors l x = {x}"
  unfolding ancestors_def ufa_\<beta>_start_def using assms apply auto
  using converse_rtranclE by force


lemma displeasure_of_root:
  assumes "x=l!x"
  shows "displeasure x = 0"
  unfolding displeasure_def unpleasant_ancestors_def 
  apply (subst ancestors_of_root[OF assms])
  using assms by auto
  

lemma displeasure_parent_if_pleasant:
  assumes "(x,y) \<in> ufa_\<beta>_start l" "pleasant x"
  shows "displeasure x = displeasure y"
  unfolding displeasure_def unpleasant_ancestors_def
  apply (subst ancestors_of_parent[OF assms(1)]) using assms
  by auto

lemma displeasure_parent_if_unpleasant:
  assumes "(x,y) \<in> ufa_\<beta>_start l" "\<not>pleasant x"
  shows "displeasure x = Suc (displeasure y)"
  unfolding displeasure_def unpleasant_ancestors_def
  apply (subst ancestors_of_parent[OF assms(1)]) using assms 
proof goal_cases
  case 1
  have x1: "x\<notin> ancestors l y" using assms unfolding ancestors_def 
    by (metis (no_types, lifting) aciclicity case_prodD contextasm invar_rank_def
        mem_Collect_eq trancl.intros(1) trancl_rtrancl_trancl ufa_\<beta>_def ufa_\<beta>_start_def)
  hence x1': "{x} \<inter> (ancestors l y \<inter> {y. \<not> pleasant y \<and> y \<noteq> l ! y}) = {}" by fast
  have x2: "x\<in>{y. \<not> pleasant y \<and> y \<noteq> l ! y}" using assms unfolding ufa_\<beta>_start_def by fast
  have sg: "(ancestors l y \<union> {x}) \<inter> {y. \<not> pleasant y \<and> y \<noteq> l ! y} 
        = {x} \<union> (ancestors l y \<inter> {y. \<not> pleasant y \<and> y \<noteq> l ! y})" using x1 x2 by fast
  have fx: "finite {x}" by blast
  have fr'': "y < length l" using assms(1) unfolding ufa_\<beta>_start_def by fast
  have fr': "finite (ancestors l y)" using ancestors_in_domain[OF \<open>y<length l\<close>]
    using rev_finite_subset finite_atLeastZeroLessThan_int by blast
  hence fr: " finite (ancestors l y \<inter> {y. \<not> pleasant y \<and> y \<noteq> l ! y})" by blast
  show ?case using x1'  unfolding ufa_\<beta>_start_def 
    apply (subst sg) using card_Un_disjoint[OF fx fr x1'] by simp
qed
  

lemma displeasure_parent:
  assumes "(x,y) \<in> ufa_\<beta>_start l"
  shows "displeasure x \<le> Suc (displeasure y)"
proof (cases "pleasant x")
  case True
  then show ?thesis using displeasure_parent_if_pleasant assms by simp
next
  case False
  then show ?thesis using displeasure_parent_if_unpleasant assms by simp
qed


context  \<comment>\<open>Actually, the assumptions about ok and level are only needed for this context\<close>
  fixes bound::nat
  assumes  ok_hereditary: "ok l rkl x \<Longrightarrow> (x,y) \<in> (ufa_\<beta>_start l) \<Longrightarrow> ok l rkl y"
    and level_bounded: "ok l rkl x \<Longrightarrow> x\<noteq>l!x \<Longrightarrow> (level l rkl x) < bound "

begin


\<comment>\<open>Let us write levels for the cardinal of the image under @{term "level l rkl"} of the set
   of the non-root ancestors of x. That is, levels is the number of distinct levels of the
   non-root ancestors of x.\<close>

definition levels where "levels x = card (level l rkl `(ancestors l x \<inter> {y. y\<noteq>l!y}))"

\<comment>\<open>If the image of the function @{term "level l rkl"} is included in @{term "{0..<n}"},
   then @{term "levels x"} is at most n.\<close>

lemma hereditary_property: 
  assumes "\<And>x y. P x \<Longrightarrow> (x,y)\<in>(ufa_\<beta>_start l) \<Longrightarrow> P y" "P x" "y\<in> ancestors l x"
  shows "P y"
proof -
  have sg: "(x,y)\<in> (ufa_\<beta>_start l)\<^sup>*" using assms unfolding ancestors_def by fast
   show ?thesis using sg assms unfolding ancestors_def
     by (induction rule: rtrancl_induct) blast+
 qed

lemma bounded_levels:
  assumes "ok l rkl x"
  shows "levels x \<le> bound"
  apply (rule order.trans[of "levels x" "card {0..<bound}" bound])
   prefer 2 apply auto[1]
  unfolding levels_def
  apply (rule card_mono)
   apply auto[1]
  apply (subst subset_iff)
  apply auto
proof goal_cases
  case (1 xa)
  show ?case
    apply (rule level_bounded[OF _ 1(2)])
    using 1 assms hereditary_property[OF ok_hereditary] by fast
qed
  

lemma levels_parent_if_pleasant:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)"
  shows "levels y \<le> levels x"
  sorry

lemma levels_parent_if_unpleasant:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)" "\<not>pleasant x" "ok l rkl x"
  shows "Suc (levels y) \<le> levels x"
  sorry

lemma bounded_displeasure_preliminary_1:
  assumes "(x,z)\<in> (ufa_\<beta>_start l)" "z=l!z" "ok l rkl z" 
  shows "displeasure x \<le> levels x"
  sorry

lemma bounded_displeasure_preliminary_2:
  assumes "ok l rkl x"
  shows "displeasure x \<le> bound"
  sorry

\<comment>\<open> As an ad hoc corollary, if every non-root non-OK vertex has an OK parent,
   then we obtain the following bound. This is useful in the special case
   where OK is defined as "non-zero-rank". \<close>

lemma bounded_displeasure:
  \<comment>\<open>TODO: rewrite this in a sensible way\<close>
  assumes "\<forall>x y. l!x\<noteq>x \<longrightarrow> \<not>ok l rkl x \<longrightarrow> (x,y)\<in> (ufa_\<beta>_start l) \<longrightarrow> ok l rkl y" 
  shows "displeasure x \<le> Suc bound"
  sorry

end \<comment>\<open>Until here the assumtions about ok and level\<close>

end \<comment>\<open>FK\<close>

context \<comment>\<open>Preservation\<close>
  assumes compress_preserves_level_above_y:
    "\<lbrakk>(x,y)\<in> (ufa_\<beta>_start l); (y,v)\<in> (ufa_\<beta>_start l)\<^sup>*; v\<noteq>l!v\<rbrakk> \<Longrightarrow> level (l[x:= rep_of l y]) rkl v = level l rkl v"
 and compress_preserves_ok_above_y:
    "\<lbrakk>(x,y)\<in> (ufa_\<beta>_start l); (y,v)\<in> (ufa_\<beta>_start l)\<^sup>*; v\<noteq>l!v; ok l rkl v \<rbrakk> \<Longrightarrow> ok (l[x:= rep_of l y]) rkl v"
begin

lemma compress_preserves_pleasant_above_y:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)" "(y,v)\<in> (ufa_\<beta>_start l)\<^sup>*" "pleasant l rkl v"
  shows "pleasant (l[x:= rep_of l y]) rkl v"
  sorry

lemma compress_preserves_displeasure_of_y:
  assumes "(x,y) \<in> (ufa_\<beta>_start l)" 
  shows "displeasure (l[x:= rep_of l y]) rkl y \<le> displeasure l rkl y "
  sorry

end \<comment>\<open>Preservation\<close>

end \<comment>\<open>Pleasant\<close>



\<comment>\<open>The predicate top_part corresponds to the "top part of the path"
   mentioned in the proof of Lemma 4.11.\<close>
definition top_part where "top_part l rkl x \<equiv> \<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (rep_of l x))"

context \<comment>\<open>invar_rank\<close>
  fixes l::"nat list" and rkl::"nat list"
  assumes contextasm: "invar_rank l rkl"
begin




lemma top_part_hereditary:
  assumes  "top_part l rkl x" "(x,y)\<in>(ufa_\<beta>_start l)"
  shows "top_part l rkl y"
    \<comment>\<open>rep_of l x = rep_of l y and 1(1) together with rank increasing along edges should suffice\<close>
proof -
  have "ufa_invar l" using contextasm unfolding invar_rank_def by blast
  have "x<length l" using assms(2) unfolding ufa_\<beta>_start_def by blast
  have h3: "(y, rep_of l x) \<in> (ufa_\<beta>_start l)\<^sup>*" using rep_of_ufa_\<beta>_refl[OF \<open>ufa_invar l\<close> \<open>x<length l\<close>] assms(2) 
    by (smt \<open>ufa_invar l\<close> case_prodD mem_Collect_eq rep_of_bound rep_of_idx rep_of_path_iff ufa_\<beta>_start_def)
  have h4: "rep_of l x = rep_of l y" using assms \<open>ufa_invar l\<close> rep_of_idx 
      unfolding ufa_\<beta>_start_def by force
    thus ?thesis unfolding top_part_def 
      sorry
  qed
  


lemma compress_preserves_top_part_above_y:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)" "top_part l rkl v"
  shows "top_part (l[x:=rep_of l x]) rkl v"
proof -
  have sg1: "(y, rep_of l x) \<in> (ufa_\<beta>_start l)\<^sup>*" using assms(1)
    by (smt case_prodD contextasm invar_rank_ufa_invarI mem_Collect_eq rep_of_bound
        rep_of_idx rep_of_path_iff ufa_\<beta>_start_def)
  show ?thesis using assms(2)
  unfolding top_part_def 
  sorry 
qed

end \<comment>\<open>invar_rank\<close>

interpretation pl: Pleasant top_part level .


context \<comment>\<open>invar_rank\<close>
  fixes l::"nat list" and rkl::"nat list"
  assumes contextasm: "invar_rank l rkl"
begin


\<comment>\<open>The proof of Lemma 4.11 says this is a strict inequality. This is
   true. Here, we do not exploit the fact that a level is at least 1,
   which is why we end up establishing a large inequality.\<close>

lemma bounded_displeasure_alstrup:
  assumes "top_part l rkl x" 
  shows "pl.displeasure l rkl x \<le> \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
  sorry

\<comment>\<open>During a path compression step at x, the vertex x is the only one whose
   potential changes. So, if the potential of x decreases, then the total
   potential \<Phi> decreases as well.\<close>

lemma from_\<phi>_to_\<Phi>:
  assumes "x\<noteq>l!x" "\<phi> (l[x:= rep_of l x]) rkl x < \<phi> l rkl x"
  shows "\<Phi> (l[x:= rep_of l x]) rkl < \<Phi> l rkl "
proof -
  {fix a::nat and b::nat and c::nat and d::nat
    assume la: "a \<le> c" "b<d"
    have "a+b < c+d" using la by simp
  } note rt=this
  have "x<length l" using assms(2) nat_neq_iff by force
  have "sum (\<phi> (l[x := rep_of l x]) rkl) ({0..<length l} - {x} \<union> {x}) =
        sum (\<phi> (l[x := rep_of l x]) rkl) ({0..<length l} - {x}) + 
        sum (\<phi> (l[x := rep_of l x]) rkl) {x} - 
        sum (\<phi> (l[x := rep_of l x]) rkl)  (({0..<length l} - {x})\<inter>{x})"
    apply (rule sum_Un_nat[of "({0..<length l} - {x})" "{x}" ])
    by blast+
  hence "sum (\<phi> (l[x := rep_of l x]) rkl) ({0..<length l}) =
         sum (\<phi> (l[x := rep_of l x]) rkl) ({0..<length l} - {x}) 
       + sum (\<phi> (l[x := rep_of l x]) rkl) {x}"
    by (smt Diff_disjoint Un_Diff_cancel Un_commute \<open>x < length l\<close> atLeastLessThan_iff 
        finite.intros(1,2) finite_Diff finite_atLeastLessThan inf_commute insert_absorb 
        insert_is_Un sum.union_disjoint zero_order(1))
  hence sub1: "sum (\<phi> (l[x := rep_of l x]) rkl) ({0..<length l}) =
        sum (\<phi> (l[x := rep_of l x]) rkl) ({0..<length l} - {x}) + \<phi> (l[x := rep_of l x]) rkl x"
    by simp
  have sub2: "sum (\<phi> l rkl) {0..<length l} = sum (\<phi> l rkl) ({0..<length l} - {x}) + \<phi> l rkl x"
    by (simp add: \<open>x < length l\<close> add.commute sum.remove)
  { fix i::nat
    assume "i\<in>({0..<length l} - {x})"
    have "(\<phi> (l[x := rep_of l x]) rkl i) \<le> (\<phi> l rkl i)" 
      using compress_evolution \<open>x < length l\<close> \<phi>_v_cannot_increase assms(1) contextasm
      using \<open>i \<in> {0..<length l} - {x}\<close> by force
    } note conteq=this
  show ?thesis apply simp apply (subst sub1) apply (subst sub2)
    apply (rule rt)
     defer subgoal using assms(2) .
    using conteq using sum_mono by blast
qed
    
   

lemma pleasant_\<phi>:
  assumes "pl.pleasant l rkl x"
  shows "\<phi> (l[x:= rep_of l x]) rkl x < \<phi> l rkl x"
  sorry


lemma arbitrary_\<Phi>:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)"
  shows "\<Phi> (l[x:= rep_of l x]) rkl \<le> \<Phi> l rkl"
  apply simp using \<phi>_v_cannot_increase[OF contextasm]
  by (metis atLeastLessThan_iff compress_evolution contextasm eq_iff list_update_beyond 
      list_update_id not_le_imp_less rep_of_refl sum_mono)

end  \<comment>\<open>invar_rank\<close>

context \<comment>\<open>invar_rank\<close>
  fixes l::"nat list" and rkl::"nat list"
  assumes contextasm: "invar_rank l rkl"
begin

\<comment>\<open>We now evaluate the amortized cost of path compression in the "top part" of the path. \<close>


lemma amortized_cost_fw_ipc_top_part_inductive:
  assumes "fw_ipc l x i l'" "top_part l rkl x"
  shows "\<Phi> l' rkl + i \<le> \<Phi> l rkl + pl.displeasure l rkl x"
  unfolding pl.displeasure_def[OF contextasm]
  using assms contextasm
proof (induction)
  case (FWIPCBase x l)
  then show ?case by linarith
next
  case step: (FWIPCStep x y l i l')
  have "x<length l" "y<length l"  
    using step  unfolding ufa_\<beta>_start_def by auto 
  have "invar_rank (l[x := rep_of l y]) rkl" 
    using  invar_rank_evolution[OF \<open>invar_rank l rkl\<close>  EvCompress[OF step(1), of rkl]] .
  have "rep_of l x < length l" using 
      rep_of_bound[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] \<open>x<length l\<close>] .
  have eq: "rep_of l y = rep_of l x"  
    apply (subst rep_of_path_iff[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] 
                                 \<open>rep_of l x<length l\<close> \<open>y<length l\<close>])
    apply safe
    using step(1) rep_of_ufa_\<beta>_refl[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] \<open>x<length l\<close>]
     apply (metis \<open>rep_of l x < length l\<close> \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI 
            r_into_rtrancl rep_of_invar_along_path rep_of_path_iff step.prems(2))
    using \<open>x < length l\<close> invar_rank_ufa_invarI rep_of_min step.prems by blast

  have step': " (x, y) \<in> ufa_\<beta>_start l" "fw_ipc (l[x := rep_of l x]) y i l'"
            "\<lbrakk>top_part (l[x := rep_of l x]) rkl y; invar_rank (l[x := rep_of l x]) rkl\<rbrakk>
             \<Longrightarrow> \<Phi> l' rkl + i \<le> \<Phi> (l[x := rep_of l x]) rkl +
                                 card (pl.unpleasant_ancestors (l[x := rep_of l x]) rkl y)" 
                "top_part l rkl x" "invar_rank l rkl" using step by (auto simp add: eq)

  have dpleq: "pl.displeasure (l[x := rep_of l y]) rkl y
      \<le> pl.displeasure l rkl y" 
    apply (rule pl.compress_preserves_displeasure_of_y[of x y l rkl, OF _ _ step'(1)])
  proof goal_cases
    case (1 x y l v rkl)
    then show ?case sorry
  next
    case (2 x' y' l' v rkl)
    then show ?case unfolding top_part_def sorry
  qed

  have ir':"invar_rank (l[x := rep_of l x]) rkl" using
        invar_rank_evolution[OF \<open>invar_rank l rkl\<close> EvCompress[OF step'(1), of rkl]] eq by argo
  have sub1: "rep_of (l[x := rep_of l x]) y = rep_of l x" using \<open>rep_of l y = rep_of l x\<close>
        using \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI step.prems ufa_compress_aux(2) by auto
  have tpy: "top_part (l[x := rep_of l x]) rkl y" 
        using top_part_hereditary[OF \<open>invar_rank l rkl\<close> step'(4) step'(1)] 
        unfolding top_part_def 
        apply (subst sub1) apply(subst eq[symmetric]) .  
  note IH' = step'(3)[OF tpy ir']

  then show ?case proof (cases "pl.pleasant l rkl x")
    case True
    have "x \<noteq> l!x" using step'(1) unfolding ufa_\<beta>_start_def by blast
    show ?thesis apply (subst pl.displeasure_def[OF \<open>invar_rank l rkl\<close>, symmetric])
      using pl.displeasure_parent_if_pleasant[OF \<open>invar_rank l rkl\<close> step'(1) True]
      from_\<phi>_to_\<Phi>[OF \<open>invar_rank l rkl\<close> \<open>x\<noteq>l!x\<close>  pleasant_\<phi>[OF \<open>invar_rank l rkl\<close> True]]
      IH' True dpleq 
      apply (subst (asm) pl.displeasure_def[OF \<open>invar_rank (l[x := rep_of l x]) rkl\<close>, symmetric])
      apply (subst (asm) eq[symmetric])+
      by linarith
  next
    case False
    show ?thesis apply (subst pl.displeasure_def[OF \<open>invar_rank l rkl\<close>, symmetric])
      using pl.displeasure_parent_if_unpleasant[OF \<open>invar_rank l rkl\<close> step'(1) False]
        arbitrary_\<Phi>[OF \<open>invar_rank l rkl\<close> step'(1)] IH' False dpleq
      apply (subst (asm) pl.displeasure_def[OF \<open>invar_rank (l[x := rep_of l x]) rkl\<close>, symmetric])
      apply (subst (asm) eq[symmetric])+
      by linarith
  qed
qed


lemma amortized_cost_fw_ipc_top_part:
  assumes "fw_ipc l x i l'" "top_part l rkl x"
  shows "\<Phi> l' rkl + i \<le> \<Phi> l rkl + \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
  using amortized_cost_fw_ipc_top_part_inductive[OF assms] bounded_displeasure_alstrup[OF assms(2)] 
  by linarith

\<comment>\<open>Say x is "easy" if @{term "alphar \<circ> (rankr rkl)"} is NOT constant all the way from x
   to its root z, but maps x and its parent to the same value. In this case,
   a path compression step at x causes the potential of x to decrease. This
   is Lemma 4.9 in Alstrup et al.'s paper.\<close>



lemma easy_\<phi>:
  assumes "x\<noteq>l!x" "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (l!x))" 
  "\<alpha>\<^sub>r (rankr rkl (l!x)) < \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
shows "\<phi> (l[x:= rep_of l x]) rkl x < \<phi> l rkl x"
  sorry

end \<comment>\<open>invar_rank\<close>
  \<comment>\<open>Change of context in order to use the above lemmas for arbitrary l\<close>
context \<comment>\<open>invar_rank\<close>
  fixes l::"nat list" and rkl::"nat list"
  assumes contextasm: "invar_rank l rkl"
begin


\<comment>\<open>The following result covers the so-called "bottom part" of the path.
   It combines Lemma 4.8 and the "bottom part" of Lemma 4.10, and calls
   the previous result @{thm amortized_cost_fw_ipc_top_part} when it reaches
   the "top part" of the path.\<close>

lemma amortized_cost_fw_ipc_bottom_part:
  assumes "fw_ipc l x i l'"
  shows "\<Phi> l' rkl + i \<le> \<Phi> l rkl + 2 * \<alpha>\<^sub>r (rankr rkl (rep_of l x)) - \<alpha>\<^sub>r (rankr rkl x)"
  using assms contextasm
proof (induction)
  case (FWIPCBase x l)
  have sub: "rep_of l x = x" using rep_of_refl[OF FWIPCBase(1)[symmetric]] by argo
  show ?case apply (subst sub) by linarith
next
  case step: (FWIPCStep x y l i l')
  have "x<length l" "y<length l"  
    using step  unfolding ufa_\<beta>_start_def by auto 
  have "invar_rank (l[x := rep_of l y]) rkl" 
    using  invar_rank_evolution[OF \<open>invar_rank l rkl\<close>  EvCompress[OF step(1), of rkl]] .
  have "rep_of l x < length l" using 
      rep_of_bound[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] \<open>x<length l\<close>] .
  have eq: "rep_of l y = rep_of l x"  
    apply (subst rep_of_path_iff[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] 
                                 \<open>rep_of l x<length l\<close> \<open>y<length l\<close>])
    apply safe
    using step(1) rep_of_ufa_\<beta>_refl[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] \<open>x<length l\<close>]
     apply (metis \<open>rep_of l x < length l\<close> \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI 
            r_into_rtrancl rep_of_invar_along_path rep_of_path_iff step.prems)
    using \<open>x < length l\<close> invar_rank_ufa_invarI rep_of_min step.prems by blast

  have step': "(x, y) \<in> ufa_\<beta>_start l" "fw_ipc (l[x := rep_of l x]) y i l'"
              "invar_rank (l[x := rep_of l x]) rkl \<Longrightarrow>
                \<Phi> l' rkl + i \<le> \<Phi> (l[x := rep_of l x]) rkl +
                2 * \<alpha>\<^sub>r (rankr rkl (rep_of (l[x := rep_of l x]) y)) - \<alpha>\<^sub>r (rankr rkl y)"
              "invar_rank l rkl" using step by (auto simp add: eq)

  have aleq:"\<alpha>\<^sub>r (rankr rkl x) \<le> \<alpha>\<^sub>r (rankr rkl (rep_of l x))" 
    using \<alpha>\<^sub>r_rankr_grows_along_a_path[OF \<open>invar_rank l rkl\<close> \<open>x<length l\<close> \<open>rep_of l x < length l\<close>]
  proof (cases "x = rep_of l x")
    case True
    then show ?thesis by simp
  next
    case False
    have "(x,rep_of l x)\<in>(ufa_\<beta>_start l)\<^sup>*" 
      using \<open>x < length l\<close> invar_rank_ufa_invarI rep_of_ufa_\<beta>_refl step.prems by blast
    with False have a: "(x,rep_of l x)\<in>ufa_\<beta> l" 
      unfolding ufa_\<beta>_def by (simp add: rtrancl_eq_or_trancl)
    show ?thesis using \<alpha>\<^sub>r_rankr_grows_along_a_path[OF \<open>invar_rank l rkl\<close> \<open>x<length l\<close> 
                                                  \<open>rep_of l x < length l\<close> False a] .
  qed

  with step' show ?case proof (cases " \<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (rep_of l x))")
    case True
    hence "top_part l rkl x" unfolding top_part_def .
    show ?thesis using amortized_cost_fw_ipc_top_part[OF \<open>invar_rank l rkl\<close> 
                       FWIPCStep[OF step(1) step(2)] \<open>top_part l rkl x\<close>] True by linarith
  next
    case False
    have ir':"invar_rank (l[x := rep_of l x]) rkl" using  
        invar_rank_evolution[OF \<open>invar_rank l rkl\<close> EvCompress[OF step'(1), of rkl]] eq by argo
    note IH' = step'(3)[OF ir']

    then show ?thesis proof (cases "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (l!x))")
      case True 
      have "x\<noteq>l!x" using step(1) unfolding ufa_\<beta>_start_def by blast
      have "y = l!x" using step'(1) unfolding ufa_\<beta>_start_def by blast
      have ineq: "\<alpha>\<^sub>r (rankr rkl (l ! x)) < \<alpha>\<^sub>r (rankr rkl (rep_of l x))" using False 
        apply (subst (asm) True) using True aleq by linarith
      note \<Phi>ineq = from_\<phi>_to_\<Phi>[OF \<open>invar_rank l rkl\<close> \<open>x\<noteq>l!x\<close> 
                          easy_\<phi>[OF \<open>invar_rank l rkl\<close> \<open>x\<noteq>l!x\<close> True ineq]] 
      have sub1: "rep_of (l[x := rep_of l x]) y = rep_of l x" using \<open>rep_of l y = rep_of l x\<close>
        using \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI step.prems ufa_compress_aux(2) by auto
      show ?thesis 
        using \<Phi>ineq step'(1) aleq IH' True False 
        apply (subst (asm)  \<open>y = l!x\<close>[symmetric])
        apply (subst (asm) sub1)
        by linarith
    next
      case false': False
      have "y = l!x" using step'(1) unfolding ufa_\<beta>_start_def by blast
      note \<Phi>leq = arbitrary_\<Phi>[OF \<open>invar_rank l rkl\<close> step'(1)]
      have sub1: "rep_of (l[x := rep_of l x]) y = rep_of l x" using \<open>rep_of l y = rep_of l x\<close>
        using \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI step.prems ufa_compress_aux(2) by auto
      have "\<alpha>\<^sub>r (rankr rkl x) \<le> \<alpha>\<^sub>r (rankr rkl y)" using false' step'(1)
        apply (subst (asm)  \<open>y = l!x\<close>[symmetric])
        using \<alpha>\<^sub>r_rankr_grows_along_edges \<open>x < length l\<close> \<open>y = l ! x\<close> step.prems by fastforce
      then show ?thesis using False false' IH' aleq \<Phi>leq
        apply (subst (asm)  \<open>y = l!x\<close>[symmetric]) 
        apply (subst (asm) sub1)
        by linarith
    qed
  qed
qed

lemma amortized_cost_fw_ipc:
  assumes "fw_ipc l x i l'" 
  shows "\<Phi> l' rkl + i < \<Phi> l rkl + 2 * \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
proof -
  have sg1: "\<alpha>\<^sub>r (rankr rkl x) > 0" using alphar_pos[OF \<rho>_gt_0] by fast
  have sg2: "\<alpha>\<^sub>r (rankr rkl (rep_of l x)) > 0" using alphar_pos[OF \<rho>_gt_0] by fast
  show ?thesis using sg1 sg2 amortized_cost_fw_ipc_bottom_part[OF assms] by fastforce
qed


\<comment>\<open>This corollary combines @{thm ipc_defined}, @{thm amortized_cost_fw_ipc}, and
   @{thm bw_ipc_fw_ipc}, so as to obtain the amortized cost of iterated path
   compression, in a variant based on bw_ipc, and in a form where the ipc
   predicate appears as part of the conclusion (not as a hypothesis).\<close>

lemma amortized_cost_of_iterated_path_compression_local:
  assumes "x < length l" 
  shows "\<exists> i l'. bw_ipc l x i l' \<and> \<Phi> l' rkl + i < \<Phi> l rkl + 2 * \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
proof -
  obtain i l' where h1: "bw_ipc l x i l'" using \<open>invar_rank l rkl\<close> unfolding invar_rank_def 
    using ipc_defined by presburger
  thus ?thesis using assms \<open>invar_rank l rkl\<close> amortized_cost_fw_ipc bw_ipc_fw_ipc 
    unfolding invar_rank_def by fast
qed

\<comment>\<open> A simplified version, where we bound the rankr of @{term "rep_of l x"} by the length of l,
   plus @{term "\<rho> - 1"}. \<close>

lemma amortized_cost_of_iterated_path_compression_global:
  assumes "x<length l" 
  shows "\<exists> i l'. bw_ipc l x i l' \<and> \<Phi> l' rkl + i < \<Phi> l rkl + 2 * \<alpha>\<^sub>r (length l + (\<rho> - 1))"
proof -
  obtain i l' where local: "bw_ipc l x i l'" 
                           "\<Phi> l' rkl + i < \<Phi> l rkl + 2 * \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
    using amortized_cost_of_iterated_path_compression_local[OF assms] by blast
  have "rkl! rep_of l x \<le> Discrete.log (length l)"  using 
      rank_is_logarithmic[OF contextasm rep_of_bound[OF invar_rank_ufa_invarI[OF contextasm]assms]].
  have "0<length l" using assms by simp
  have "rkl!rep_of l x < length l" 
    using log_lt_n[OF \<open>0<length l\<close>] \<open>rkl! rep_of l x \<le> Discrete.log (length l)\<close> by linarith
  hence "rankr rkl (rep_of l x) \<le> length l + (\<rho>-1)" unfolding rankr_def using \<rho>_gt_0 by linarith
  hence "\<alpha>\<^sub>r (rankr rkl (rep_of l x)) \<le> \<alpha>\<^sub>r (length l + (\<rho>-1))" 
    using mono_alphar[OF \<rho>_gt_0] unfolding mono_def by presburger
  thus ?thesis using local by fastforce
qed

end \<comment>\<open>invar_rank\<close>




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