theory Union_Find_Time_alpha_abstract_analysis

imports 
  "SepAuto_Time.SepLog_Automatic" 
  Collections.Partial_Equivalence_Relation
  "HOL-Library.Code_Target_Numeral"
  Imperative_HOL_Time.Asymptotics_1D
  Ackermann
begin

notation timeCredit_assn  ("$") 
no_notation Ref_Time.update ("_ := _" 62)

text \<open>
  We implement a simple union-find data-structure based on an array.
  It uses path compression and a size-based union heuristics.
\<close>

subsection \<open> Abstract Union-Find on Lists \<close>
text \<open>
  We first formulate union-find structures on lists, and later implement 
  them using Imperative/HOL. This is a separation of proof concerns
  between proving the algorithmic idea correct and generating the verification
  conditions.
\<close>

subsubsection \<open> Representatives \<close>
text \<open>
  We define a function that searches for the representative of an element.
  This function is only partially defined, as it does not terminate on all
  lists. We use the domain of this function to characterize valid union-find 
  lists. 
\<close>
function (domintros) rep_of 
  where "rep_of l i = (if l!i = i then i else rep_of l (l!i))"
  by pat_completeness auto

inductive is_repr where
  root: "l!i = i \<Longrightarrow> is_repr l i i"  
| child: "is_repr l (l!i) j \<Longrightarrow> is_repr l i j"


text \<open> A valid union-find structure only contains valid indexes, and
  the @{text "rep_of"} function terminates for all indexes. \<close>
definition 
  "ufa_invar l \<equiv> \<forall>i<length l. rep_of_dom (l,i) \<and> l!i<length l"

lemma ufa_invarD: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of_dom (l,i)" 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> l!i<length l" 
  unfolding ufa_invar_def by auto

text \<open> We derive the following equations for the @{text "rep-of"} function. \<close>
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

text \<open> We derive a custom induction rule, that is more suited to
  our purposes. \<close>
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

text \<open>In the following, we define various properties of @{text "rep_of"}. \<close>
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

lemma rep_of_dom_inverse_intro:
  assumes "rep_of_dom (l,i)" "l!i\<noteq>i"
  shows "rep_of_dom (l,l!i)"
  using assms 
proof (induction rule: rep_of.pinduct)
  case (1 l i)
  then show ?case apply (cases "l ! (l ! i) \<noteq> l ! i") 
    by (auto intro: rep_of.domintros simp: rep_of.psimps)
qed

lemma rep_of_is_repr:
  "is_repr l i j = (rep_of_dom (l,i) \<and> (rep_of l i = j))"
proof (safe, goal_cases)
  case 1
  then show ?case by induction (auto intro: rep_of.domintros)
next
  case 2
  have "rep_of_dom (l, i)" using 2 by induction (auto intro: rep_of.domintros)
  with 2 show ?case
  proof induction
    case (root l i)
    then show ?case by (auto simp: rep_of.psimps)
  next
    case (child l i j)
    hence "rep_of_dom (l, l ! i)" using rep_of.psimps[OF child(3)]
      apply (cases "i=l!i") using rep_of_dom_inverse_intro by auto
    with child show ?case by (auto simp add: rep_of.psimps)
  qed
next
  case 3
  then show ?case proof (induction rule: rep_of.pinduct)
    case (1 l i)
    then show ?case apply (cases "l ! i \<noteq> i") proof ( auto,goal_cases)
      case 1
      hence "rep_of l i = rep_of l (l ! i)" by (auto simp add: rep_of.psimps)
      with 1 show ?case by (auto intro: is_repr.intros)
    next
      case 2
      hence "i=rep_of l i" by (auto simp add: rep_of.psimps)
      with 2 show ?case by (auto intro: is_repr.intros)
    qed
  qed
qed


subsubsection \<open> Abstraction to Partial Equivalence Relation \<close>
definition ufa_\<alpha> :: "nat list \<Rightarrow> (nat\<times>nat) set" 
  where "ufa_\<alpha> l 
    \<equiv> {(x,y). x<length l \<and> y<length l \<and> rep_of l x = rep_of l y}"

lemma ufa_\<alpha>_equiv[simp, intro!]: "part_equiv (ufa_\<alpha> l)" 
  by rule (auto simp: ufa_\<alpha>_def intro: symI transI)

lemma ufa_\<alpha>I: "(\<forall>i<length l. rep_of l' i = rep_of l i) \<Longrightarrow> (length l = length l') \<Longrightarrow> (ufa_\<alpha> l' = ufa_\<alpha> l)"
  unfolding ufa_\<alpha>_def by auto

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

subsubsection \<open> Operations (by Peter Lammich)\<close>
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

lemma ufa_compress_rep_of:
  assumes "ufa_invar l" "x<length l" "u=rep_of l x"
  shows "\<And>i. i<length l \<Longrightarrow> rep_of (l[x := u]) i = rep_of l i"
  using ufa_compress_aux assms 
  by auto

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


lemma MAXIMUM_mono_aux: assumes "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x)" "finite A"
  shows "Max (f ` A) \<le> Max (g ` A)" 
proof (cases "A\<noteq>{}")
  case True
  have "Max (f`A) \<in> (f`A)" using Max_in assms True by auto
  then obtain a where aA: "a\<in>A" and fa: "f a = Max (f ` A)" by auto
  have "Max (f ` A) = f a" using fa ..
  also have "\<dots> \<le> g a" using aA assms(1) by auto
  also have "\<dots> \<le> Max (g ` A)" using Max.coboundedI aA assms by simp
  finally show ?thesis .
next
  case False
  thus ?thesis using assms by auto
qed

lemma MAXIMUM_mono: "(\<And>x. x\<in>A \<Longrightarrow> f x \<le> g x) \<Longrightarrow> finite A  \<Longrightarrow> A = B \<Longrightarrow> Max (f ` A) \<le> Max (g ` B)"  
  using MAXIMUM_mono_aux by blast 

lemma MAXIMUM_eq: "(\<And>x. x\<in>A \<Longrightarrow> f x = g x) \<Longrightarrow> finite A  \<Longrightarrow> A = B \<Longrightarrow> Max (f ` A) =  Max (g ` B)"
  apply(rule antisym) by  (auto intro: MAXIMUM_mono)






lemma h_of_alt: "h_of l i = Max ((height_of l) ` {j|j. j<length l \<and> rep_of l j = i})"
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
  "Suc (h_of l i) = Max ((\<lambda>j. Suc (height_of l j)) ` {j|j. j<length l \<and> rep_of l j = i}) "
  unfolding h_of_alt  
  apply(subst  mono_Max_commute[where f=Suc]) 
  subgoal by (simp add: mono_Suc)
  subgoal by simp
  subgoal using a by auto  
  by (simp add: image_image) 

lemma MAXIMUM_Un: "finite A \<Longrightarrow> finite B \<Longrightarrow> A \<noteq> {} \<Longrightarrow> B \<noteq> {} 
  \<Longrightarrow> Max (f` (A \<union> B) ) = max (Max (f`A)) (Max (f`B) )"
  apply(simp add: image_Un)
  apply(subst Max_Un) by auto

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

  have "h_of (ufa_union l x y) i = Max ( (height_of (ufa_union l x y)) `{j|j. j<length (ufa_union l x y) \<and> rep_of (ufa_union l x y) j = i})"
    unfolding h_of_alt by simp
  also have "\<dots> = Max ((height_of (ufa_union l x y))` (?A \<union> ?B) )"
    unfolding * by simp
  also have "\<dots> = max (Max ( (height_of (ufa_union l x y))`?A)) (Max ( (height_of (ufa_union l x y))`?B))"
    apply(subst MAXIMUM_Un) apply simp_all
    subgoal  apply(rule exI[where x=y]) using assms by (simp add: ufa_union_aux)  
    subgoal  apply(rule exI[where x=x]) using assms by (simp add: ufa_union_aux)  
    done
  also have "\<dots> \<le> max (Max ( (height_of l) ` ?A)) (Max ( (\<lambda>j. Suc (height_of l j)) `?B))"
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

section\<open>Stuff about the rank (by Adrián Löwenberg)\<close>

subsection\<open>Definitions\<close>

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
  "trans (ufa_\<beta> l)"
  by (auto simp add: ufa_\<beta>_def trans_rtrancl) 

lemma ufa_\<beta>_start_functional:
  assumes "ufa_invar l" "i< length l" "j < length l" "i'<length l"
          "(i,j)\<in> ufa_\<beta>_start l" "(i,i')\<in> ufa_\<beta>_start l"
        shows "j = i'" 
  using assms unfolding ufa_\<beta>_start_def by fast

\<comment>\<open>If we are in a cycle and make one step, then we are still in a cycle.\<close>

lemma one_step_in_a_cycle:
  assumes "ufa_invar l" "i <length l" "j<length l" "i'<length l"
      and "(i,j) \<in> ufa_\<beta> l" "i = j" "(i,i') \<in> ufa_\<beta>_start l"
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
  have "(i',y) \<in> (ufa_\<beta>_start l)\<^sup>+ \<or> i'=y"
    using step(1) step(9) apply safe
    unfolding ufa_\<beta>_start_def 
    using converse_tranclE  by force
  thus ?case using step \<open>(y, y) \<in> (ufa_\<beta>_start l)\<^sup>+\<close> by fastforce 
qed

\<comment>\<open>Thus, a path cannot leave a cycle.\<close>

lemma cannot_escape_a_cycle:
  assumes "ufa_invar l" "i <length l" "j<length l" "(i,i) \<in> ufa_\<beta> l" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "(j,j) \<in> ufa_\<beta> l"
  using assms(5,1-4) unfolding ufa_\<beta>_def 
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

lemma acyclicity:
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
  thus "False" using acyclicity assms by fast
qed


\<comment>\<open>If there is an edge from i to j, then i and j must be distinct.\<close>

lemma edges_have_distinct_endpoints:
  assumes "ufa_invar l" "i<length l" "j<length l" "(i,j) \<in> ufa_\<beta>_start l"
  shows "i\<noteq>j"
  using assms unfolding ufa_\<beta>_start_def by blast

subsubsection\<open>Closures with distances\<close>

inductive kpath 
  for r :: "('a \<times> 'a) set"
  where
    kpath_refl [intro!, Pure.intro!, simp]: "kpath r x x 0"
  | kpath_into_rtrancl [Pure.intro]: 
      "(x, y) \<in> r \<Longrightarrow> kpath r y z k \<Longrightarrow> kpath r x z (Suc k)"


lemma kpath_rtclosure: assumes "kpath r x y k" shows "(x,y) \<in> r\<^sup>*"
  using assms by (induction rule: kpath.induct) auto

lemma rtclosure_kpath: assumes "(x,y) \<in> r\<^sup>*" shows "\<exists>k. kpath r x y k"
  using assms
proof (induction rule: rtrancl_induct)
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

lemma tclosure_kpath:
  assumes "(x,y) \<in> r\<^sup>+" shows "\<exists>k>0. kpath r x y k"
  using assms
proof (induction rule: trancl_induct)
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
proof (safe)
  fix x 
  assume "(i, x) \<in> (ufa_\<beta>_start l)\<^sup>*"
  then show "x \<in> {0..<length l}"
    using assms
  proof (induction rule: rtrancl_induct)
    case (step y z)
    then show ?case unfolding ufa_\<beta>_start_def by simp
  qed simp
qed

lemma ancestors_of_parent_inclusion:
  assumes "(x,y)\<in>(ufa_\<beta>_start l)"
  shows "ancestors l y \<subseteq> ancestors l x"
  unfolding ancestors_def using assms
  by auto


lemma ufa_\<beta>_init_desc: "i<n \<Longrightarrow> descendants [0..<n] i = {i}" 
  unfolding descendants_def ufa_\<beta>_start_def 
  by auto (metis (no_types, lifting) case_prodE mem_Collect_eq
                nth_upt_zero rtrancl.cases upt_zero_length)
 

definition invar_rank where
  "invar_rank l rkl \<equiv> (ufa_invar l \<and> length l = length rkl 
                      \<and> (\<forall>i j. i< length l \<and> j< length l \<and> l!i=j \<and>  i\<noteq>j \<longrightarrow> rkl ! i < rkl ! j) 
                      \<comment> \<open>if j is on the path from i to rep_of l i,
                             then rank of j is bigger than rank of i\<close>
                      \<and> (\<forall>i<length l. l!i=i \<longrightarrow> (2::nat) ^ rkl!i \<le> card (descendants l i)) )"
                      \<comment>\<open>rank i \<le> log (card (Domain (ufa_\<alpha> l)))\<close>

definition invar_rank' where "invar_rank' l rkl \<equiv> ufa_invar l \<and> invar_rank l rkl"

subsection\<open>Lemmas About the rank from UnionFind11Rank, UnionFind21Parent and UnionFind41Potential\<close>

lemma invar_rank_ufa_invarI: "invar_rank l rkl \<Longrightarrow> ufa_invar l" unfolding invar_rank_def by blast

lemma ufa_init_invar_rank: "invar_rank [0..<n] (replicate n 0)"
  by(auto simp: invar_rank_def ufa_init_invar ufa_\<beta>_init_desc)

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
  assumes "invar_rank l rkl" "i < length l" "j < length l" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "rkl!i \<le> rkl!j"
proof (cases "i=j")
  case True
  then show ?thesis by simp
next
  case False
   obtain "k" where kstuff: "kpath (ufa_\<beta>_start l) i j k" 
    using assms(4) rtclosure_kpath[of i j "ufa_\<beta>_start l" ] by blast
  then show ?thesis using rank_bounds_height_precise[OF assms(1-3) False kstuff] by simp
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
 assumes "invar_rank l rkl" "i < length l" "j < length l" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
 shows "rankr rkl i \<le> rankr rkl j"
  unfolding rankr_def using rank_increases_along_path_refl[OF assms] by auto

lemma rankr_increases_strictly_along_path:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> ufa_\<beta> l"
  shows "rankr rkl i < rankr rkl j"
  unfolding rankr_def using rank_increases_strictly_along_path[OF assms] by auto


lemma \<alpha>\<^sub>r_rankr_grows_along_a_path:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "i\<noteq>j" "(i,j) \<in> ufa_\<beta> l"
  shows "\<alpha>\<^sub>r (rankr rkl i) \<le> \<alpha>\<^sub>r (rankr rkl j)"
  using mono_alphar[OF \<rho>_gt_0] rankr_increases_strictly_along_path[OF assms] 
  unfolding mono_def by fastforce

lemma \<alpha>\<^sub>r_rankr_grows_along_a_path_refl:
  assumes "invar_rank l rkl" "i < length l" "j < length l" "(i,j) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "\<alpha>\<^sub>r (rankr rkl i) \<le> \<alpha>\<^sub>r (rankr rkl j)"
  using mono_alphar[OF \<rho>_gt_0] rankr_increases_along_path_refl[OF assms]
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
  show ?thesis
    apply rule
    subgoal (* \<Rightarrow> *)
      apply safe
      subgoal
        using assms
        apply (cases "j = rep_of l j") 
        subgoal by simp
        subgoal apply(rule trancl_into_rtrancl[OF rep_of_ufa_\<beta>[unfolded ufa_\<beta>_def]])
          by auto
        done
      subgoal using rep_of_min rep_of_iff  assms unfolding invar_rank_def by force
      done 
    subgoal (* \<Leftarrow> *)
      apply safe
    proof (goal_cases)
      case 3: 1
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

lemma is_repr_pathI:
  assumes "(x,z)\<in>(ufa_\<beta>_start l)\<^sup>*" "z=l!z"
  shows "is_repr l x z"
  using assms proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by (auto intro: is_repr.intros)
next
  case (step y z)
  then show ?case unfolding ufa_\<beta>_start_def by (auto intro: is_repr.intros)
qed


lemma descendant_of_root:
  assumes "ufa_invar l" "r<length l"  "x<length l" "r=l!r" 
  shows "x \<in> descendants l r \<longleftrightarrow> r = rep_of l x"
  using rep_of_path_iff[OF \<open>ufa_invar l\<close> \<open>r<length l\<close> \<open>x<length l\<close>] 
  unfolding descendants_def ufa_\<beta>_start_def using assms(4) by auto

lemma descendants_subset_domain:
  assumes "ufa_invar l" "x < length l"
  shows "descendants l x \<subseteq> {0..<length l}"
  using assms converse_rtranclE by (force simp: descendants_def ufa_\<beta>_start_def)

lemma finite_descendants:
  assumes "ufa_invar l" "x < length l"
  shows "finite (descendants l x)"
  using subset_eq_atLeast0_lessThan_finite[OF  descendants_subset_domain[OF assms]] .


lemma disjoint_descendants:
  assumes "ufa_invar l" "x<length l" "y<length l" "x = l!x" "y = l!y" "x\<noteq>y"
  shows "(descendants l x)\<inter>(descendants l y) = {}"
proof (safe, goal_cases)
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
  thus ?thesis
  proof (cases "l!i=i")
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
  using path_is_equiv[OF assms(1,2) _ assms(3)[symmetric] path_to_parent[OF assms]]
        ufa_invarD(2) assms
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


section\<open>Level: Definition and Lemmas\<close>
\<comment>\<open>The level of @{term i} is defined as one plus the @{term "Greatest k"} such that
   @{term "Ackermann k (rankr rkl i)"} is less than or equal to @{term "rankr rkl (l!i)"}.\<close>


context \<comment>\<open>NonRoot\<close>
  fixes l::"nat list" and rkl::"nat list" and i::nat
begin

definition defk where "defk k \<equiv> Ackermann k (rankr rkl i)"

lemma lnn_f_nat_nat: "f_nat_nat defk"
  apply standard
  subgoal using Ackermann_strict_mono_in_k rankr_positive unfolding defk_def by blast
  subgoal using Ackermann_k_x_tends_to_infinity_along_k rankr_positive unfolding defk_def by blast
  done


interpretation lnn: f_nat_nat "defk" using lnn_f_nat_nat .
  
definition prek where "prek \<equiv> lnn.\<beta>\<^sub>f (rankr rkl (l!i))"

definition level where "level \<equiv> Suc prek"

definition level' where "level' l' rkl' i' \<equiv> Suc (Greatest (\<lambda>k. rankr rkl' (l'!i') 
                                              \<ge> (Ackermann k (rankr rkl' i'))))"

lemma level_alt_eq: "level = level' l rkl i" 
  unfolding level_def level'_def prek_def lnn.\<beta>\<^sub>f_def defk_def by blast


context \<comment>\<open>NonRoot\<close>
  assumes contextasm: "invar_rank l rkl" "i<length l" "l!i\<noteq>i"
begin


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
proof -
  have "rankr rkl (l ! i) < Ackermann (prealphar \<rho> (rankr rkl (l ! i))) \<rho>"
    by (rule Ackermann_prealphar_gt[OF \<rho>_gt_0])
  also have "\<dots> \<le> Ackermann (prealphar \<rho> (rankr rkl (l ! i))) (rankr rkl i)"
    using \<rho>_leq_rankr[of rkl i] mono_Ackermann unfolding mono_def by blast
  finally have *: "rankr rkl (l ! i) < Ackermann (prealphar \<rho> (rankr rkl (l ! i))) (rankr rkl i)" .

  have "level = Suc local.prek" unfolding level_def by simp
  also have "local.prek < (prealphar \<rho> (rankr rkl (l ! i)))"
    unfolding prek_def
    apply (rule lnn.\<beta>\<^sub>f_spec_direct_contrapositive) 
    unfolding defk_def
    subgoal by (simp add: level_exists)
    subgoal by (rule *)
    done 
  also have "Suc (prealphar \<rho> (rankr rkl (l ! i))) = alphar' \<rho> (rankr rkl (l ! i))"
    using \<rho>_gt_0 by(simp add: alphar'_def)
  also have "\<dots> = \<alpha>\<^sub>r (rankr rkl (l!i))"
    using \<rho>_gt_0 by(simp add:alphar_alt_eq)
  finally show ?thesis by simp
qed 



\<comment>\<open>Another connection between @{term rankr} at @{term i} and at @{term "l!i"}\<close>

lemma rankr_parent_i_lt: "rankr rkl (l!i) < Ackermann level (rankr rkl i)"
  unfolding level_def 
  apply (subst defk_def[symmetric])
  apply (rule lnn.\<beta>\<^sub>f_spec_reciprocal_contrapositive[of "rankr rkl (l ! i)" "Suc prek"] )
  unfolding prek_def by blast


section\<open>Index: Definition and Lemmas\<close>

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
  subgoal using parent_has_greater_rank[OF contextasm] unfolding rankr_def by fastforce
  subgoal apply (rule order.strict_trans2) apply (subst rankr_parent_i_lt)
  subgoal ..
  unfolding level_def apply (subst Ackermann_step_eq) by simp
  done

end
end


section\<open>Potential function \<Phi> of the whole Union Find data structure\<close>

definition \<phi> where "\<phi> l rkl i \<equiv> if  l!i = i
                    then \<alpha>\<^sub>r (rankr rkl i) * Suc (rankr rkl i)
                    else (if \<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i)) 
                        then (\<alpha>\<^sub>r (rankr rkl i) - level l rkl i) * (rankr rkl i) - index l rkl i + 1
                        else 0)"

definition \<Phi> where "\<Phi> l rkl \<equiv> Finite_Set.fold (\<lambda> i a.  (\<phi> l rkl i) + a) (0::nat) (Domain (ufa_\<alpha> l))"

lemma \<Phi>_simp[simp]: "\<Phi> l rkl = sum (\<lambda> i. \<phi> l rkl i) {0..<length l}"
proof -
  have 1: "(\<lambda>i. (+) (\<phi> l rkl i)) = (((+) \<circ>\<circ>\<circ> \<phi>) l rkl)" by auto
  then show ?thesis
    by (simp add: \<Phi>_def sum.eq_fold)
qed

\<comment>\<open>The following lemmas repeat the cases of the definition of \<phi>\<close>

lemma \<phi>_case_1:
  assumes "l!i=i"
  shows "\<phi> l rkl i = \<alpha>\<^sub>r (rankr rkl i) * Suc (rankr rkl i)"
  unfolding \<phi>_def using assms by simp

lemma \<phi>_case_2:
  assumes "l!i\<noteq>i" "\<alpha>\<^sub>r (rankr rkl i) = \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "\<phi> l rkl i = (\<alpha>\<^sub>r (rankr rkl i) - level l rkl i) * (rankr rkl i) - index l rkl i + 1"
  unfolding \<phi>_def using assms by simp

lemma \<phi>_case_3:
  assumes "l!i\<noteq>i" "\<alpha>\<^sub>r (rankr rkl i) \<noteq> \<alpha>\<^sub>r (rankr rkl (l!i))"
  shows "\<phi> l rkl i = 0"
  unfolding \<phi>_def using assms by simp

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
proof -
  let ?n = "\<alpha>\<^sub>r (rankr rkl i)"
  have "0 < ?n" by (simp add: \<rho>_gt_0 alphar_pos)
  have gener: "Suc ((?n - level l rkl i) * rankr rkl i) \<le> ?n + ?n * rankr rkl i"  
    using \<open>0 < ?n\<close> by (auto simp: algebra_simps)
  have "rankr rkl i - index l rkl i \<le> rankr rkl i" by simp
  with gener show ?thesis    
    by (fastforce simp: \<phi>_def)
qed


section\<open>Lemmas about \<Phi>, i.e. about the whole Union Find data structure\<close>

lemma \<Phi>_empty:
  "\<Phi> [] [] = 0"
  by simp

\<comment>\<open> If @{term i} is a root and has zero rank, then @{term "\<phi> l rkl i = \<rho> + 1"}\<close>

lemma \<phi>_root_zero_rank:
  assumes "invar_rank l rkl" "i < length l" "l!i=i" "rkl!i=0"
  shows "\<phi> l rkl i = Suc \<rho>"
proof -
  have *: "rankr rkl i = \<rho>" unfolding rankr_def using \<open>rkl!i=0\<close> by simp
  show ?thesis  
    by (simp add: \<phi>_case_1[OF \<open>l!i=i\<close>] * alphar_r[OF \<rho>_gt_0])
qed

\<comment>\<open>The next lemma in Coq (\<Phi>_extend) doesn't apply to our model with a fixed domain\<close>


section\<open>Lemmas about parents during ufa_union and compression (UnionFind22ParentEvolution)\<close>

\<comment>\<open>During a union, a vertex v which already has a parent keeps this parent.\<close>

lemma ufa_union_preserves_parent:
  assumes "ufa_invar l" "x<length l" "y<length l" "v<length l" "x=l!x" "v\<noteq>l!v"
  shows "l!v = (ufa_union l x y)!v"
using assms by (cases "v\<noteq>x"; simp add: rep_of_refl)


\<comment>\<open>After a link, the parent of x is y. Yes, but we don't have the link operation, only union\<close>

lemma ufa_union_sets_parent:
  assumes "ufa_invar l" "x<length l" "y<length l" "x=l!x"
  shows "(ufa_union l x y)!x = rep_of l y"
proof -
  have "rep_of l x = x" using assms using rep_of_refl by auto
  hence "rep_of (ufa_union l x y) x = rep_of l y"
    using  assms(1-3) rep_of_refl ufa_union_aux by fastforce
  thus ?thesis using assms  \<open>rep_of l x = x\<close> by auto
qed

section \<open>Lemmas about paths and inavriants under compression (UnionFind04Compress)\<close>


lemma compress_preserves_other_edges:
  assumes "(v,w)\<in> (ufa_\<beta>_start l)" "v\<noteq>x"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= z]))"
  using assms unfolding ufa_\<beta>_start_def by auto

lemma compress_preserves_other_edges_converse:
  assumes "(v,w)\<in>(ufa_\<beta>_start (l[x:= z]))" "v\<noteq>x"
  shows "(v,w)\<in> (ufa_\<beta>_start l)"
  using assms unfolding ufa_\<beta>_start_def by auto

lemma rep_of_compress: "x = l ! x \<Longrightarrow> x = l[x := rep_of l x] ! x"
  using rep_of_refl list_update_id by metis

lemma compress_preserves_roots:
  assumes "r = l!r"
  shows "r = l[x:=rep_of l x] ! r"
  using assms apply (cases "r = x") by (auto simp: rep_of_compress) 

lemma ancestors_step:
  assumes "ufa_invar l" "i<length l" 
  shows  "ancestors l i = {i} \<union> ancestors l (l!i)"
  unfolding ancestors_def
  apply safe 
  subgoal using converse_rtranclE' ufa_\<beta>_start_def by force
  subgoal by (metis assms path_to_parent trancl_into_rtrancl trancl_rtrancl_trancl ufa_\<beta>_def)
  done
  
lemma path_from_child_is_path_from_parent:
  assumes "ufa_invar l" "i<length l" "(i,x)\<in>(ufa_\<beta>_start l)\<^sup>*" "i\<noteq>x"
  shows "(l!i,x)\<in>(ufa_\<beta>_start l)\<^sup>*"
  apply (cases "l!i = x")
  subgoal by auto
  subgoal 
    apply (cases "i=l!i")
    subgoal using assms by argo
    subgoal
    proof (rule ccontr, goal_cases)
      case 1
      have sg0: "(i,l!i)\<in> (ufa_\<beta>_start l)" unfolding ufa_\<beta>_start_def using assms 1
          ufa_invarD(2)[OF assms(1,2)] by auto
      have sg1: "x\<notin>ancestors l (l!i)" using 1 unfolding ancestors_def by blast
      then have "x\<notin> ancestors l i" apply (subst ancestors_step[OF assms(1,2)])
        using sg0 assms(3,4) 1(3) sg1 by blast
      then have "(i,x)\<notin> (ufa_\<beta>_start l)\<^sup>*" using 1 ancestors_step[OF assms(1,2)] 
        unfolding ancestors_def by blast
      then show ?case using assms by blast
    qed
    done
  done


context 
  fixes x::nat and y::nat and l::"nat list"
  assumes x_edge_y: "(x,y)\<in> (ufa_\<beta>_start l)"
begin \<comment>\<open>x_edge_y\<close>
lemma compress_preserves_paths_out_of_y':
  assumes "ufa_invar l" "(v,w)\<in>(ufa_\<beta>_start l)\<^sup>*"
          "(y,v)\<in>(ufa_\<beta>_start l)\<^sup>*" "(y, z) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= z]))\<^sup>*"
  using assms(2,3)  x_edge_y
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step y0 z)
  have "y0\<noteq>x" using paths_have_distinct_endpoints using step 
    by (metis (no_types, lifting) acyclicity assms(1) mem_Collect_eq prod.simps(2) 
        rtrancl_into_trancl2 ufa_\<beta>_def ufa_\<beta>_start_def)
  hence sg1: "(y0, z) \<in> ufa_\<beta>_start (l[x := z])" 
    using step compress_preserves_other_edges by blast
  have "(y, z) \<in> (ufa_\<beta>_start l)\<^sup>*" using step by auto
  then show ?case using step sg1 
    by (meson \<open>y0 \<noteq> x\<close> compress_preserves_other_edges converse_rtrancl_into_rtrancl)
qed
end

  
lemma ufa_compress_generalized:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l" "z<length l"
  assumes A: "(x,z)\<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "ufa_invar (l[x := z])" 
proof -
  {
    fix i
    assume C: "x\<noteq>z"
    assume "i<length (l[x := z])"
    hence IL: "i<length l" by simp
    
    have S: "rep_of_dom (l,z)" using I L unfolding ufa_invar_def by blast
    have S1: "rep_of_dom (l,i)" using I IL unfolding ufa_invar_def by blast
    have G1: "l[x := z] ! i < length (l[x := z])"
      using I IL 
      by (auto dest: ufa_invarD[OF I] simp: nth_list_update rep_of_bound)
    have S': "is_repr l i (rep_of l i)" using rep_of_is_repr S1 by blast
    
    have G2: "rep_of l i = rep_of (l[x:=z]) i \<and>rep_of_dom (l[x := z], i)"
    proof (cases "(i,x)\<in>(ufa_\<beta>_start l)\<^sup>*")
      case True
      have "is_repr (l[x := z]) i (rep_of l i)" using S' A  True I L IL C proof induction
        case (root l i)
        hence "i = z" unfolding ufa_\<beta>_start_def 
          by (smt Domain.intros Domain_Collect_case_prod mem_Collect_eq rtranclD trancl_domain)
        from root have "i = x" unfolding ufa_\<beta>_start_def 
          by (smt Domain.intros Domain_Collect_case_prod mem_Collect_eq rtranclD trancl_domain)
        from root \<open>i=z\<close> \<open>i=x\<close> have "l[x:=z]!i=i" by (simp add: \<open>i = z\<close> nth_list_update')
        then show ?case by (auto intro: is_repr.intros) 
      next
        case (child l i j)
        then show ?case proof (cases "i=x")
          case True
          show ?thesis proof (cases "i=z")
            case True
            then show ?thesis using child(9) \<open>i=x\<close> by blast
          next
            case False
            show ?thesis proof (rule is_repr_pathI, goal_cases)
            case 1
            have sg2: "(z,j) \<in> (ufa_\<beta>_start l)\<^sup>*" 
              by (metis (no_types, hide_lams) True child.hyps child.prems(1,3,5,6) 
                  rep_of_bound rep_of_idx rep_of_invar_along_path rep_of_is_repr rep_of_ufa_\<beta>_refl)
             have sg3: "(z,j) \<in> (ufa_\<beta>_start (l[i:=z]))\<^sup>*" 
               by (metis False True 
                   Union_Find_Time_alpha_abstract_analysis.compress_preserves_paths_out_of_y' 
                   child.prems(1,3) converse_rtranclE sg2)
             show ?case apply (subst True[symmetric]) 
               apply (rule  converse_rtrancl_into_rtrancl[OF _ sg3]) 
               by (simp add: False child.prems(5) child.prems(6) ufa_\<beta>_start_def)
          next
            case 2
            then show ?case 
              by (metis acyclicity child.hyps child.prems(1,3,5,6) nth_list_update' rep_of_idx 
                  rep_of_invar_along_path rep_of_is_repr rep_of_min rep_of_ufa_\<beta>_refl rtranclD 
                  transitive_closure_trans(9) ufa_\<beta>_def)
          qed
          qed
        next
          case False
          hence sg1: " (l ! i, x) \<in> (ufa_\<beta>_start l)\<^sup>*" using child 
              path_from_child_is_path_from_parent by presburger
          have sg2: "l[x := z]!i = l!i" using False child by fastforce
          show ?thesis using child(2)[OF child(3) sg1 child(5-7) ufa_invarD(2)[OF child(5,8)]] sg2 C
            by (auto intro: is_repr.intros)           
        qed
      qed
      thus ?thesis using rep_of_is_repr by simp
    next
      case False
      have "is_repr (l[x := z]) i (rep_of l i)" using S' A  False I L IL C proof induction
        case (root l i)
        then show ?case
          by (metis is_repr.root nth_list_update_neq rtrancl.simps)
      next
        case (child l i j)
        then show ?case
          by (metis is_repr.child nth_list_update_neq path_to_parent rtrancl.simps 
              trancl_into_rtrancl transitive_closure_trans(9) ufa_\<beta>_def ufa_invarD(2))
      qed 
      thus ?thesis using rep_of_is_repr by simp
    qed
    note IL G1 G2
  } note G = this

  {
    fix i
    assume "i<length (l[x := x])"
    hence IL: "i<length l" by simp
    
    have S: "rep_of_dom (l,z)" using I L unfolding ufa_invar_def by blast
    have S1: "rep_of_dom (l,i)" using I IL unfolding ufa_invar_def by blast

    have G1: "l[x := x] ! i < length (l[x := x])"
      using I IL 
      by (auto dest: ufa_invarD[OF I] simp: nth_list_update rep_of_bound)

    have S': "is_repr l i (rep_of l i)" using rep_of_is_repr S1 by blast
    have G2: "rep_of (l[x:=x]) i = rep_of (l[x:=x]) i \<and>rep_of_dom (l[x := x], i)"
    proof (cases "(i,x)\<in>(ufa_\<beta>_start l)\<^sup>*")
      case True
      have "is_repr (l[x := x]) i (rep_of (l[x := x]) i)" using S' A  True I L IL  proof induction
        case (root l i)
        then show ?case
          by (metis is_repr.root nth_list_update' nth_list_update_eq rep_of_is_repr)
      next
        case (child l i j)
        then show ?case 
          by (metis nth_list_update_eq nth_list_update_neq path_from_child_is_path_from_parent 
              rep_of.domintros rep_of_is_repr ufa_invarD(2))
      qed
      then show ?thesis using rep_of_is_repr by blast
    next
      case False
      have "is_repr (l[x := x]) i (rep_of (l[x := x]) i)" using S' A  False I L IL  proof induction
        case (root l i)
        then show ?case 
          by (metis is_repr.root nth_list_update' nth_list_update_eq rep_of_is_repr) 
      next
        case (child l i j)
        then show ?case 
          by (metis (no_types, lifting) nth_list_update_neq path_to_parent rep_of.domintros 
              rep_of_is_repr rtrancl.simps trancl_into_rtrancl transitive_closure_trans(9) 
              ufa_\<beta>_def ufa_invarD(2)) 
      qed
      then show ?thesis  using rep_of_is_repr by blast
    qed

    note IL G1 G2
  }note H = this
  show ?thesis using G H unfolding ufa_invar_def by blast
qed



context 
  fixes x::nat and y::nat and l::"nat list"
  assumes x_edge_y: "(x,y)\<in> (ufa_\<beta>_start l)"
begin \<comment>\<open>x_edge_y\<close>

lemma compress_preserves_paths_to_roots':
  assumes "ufa_invar l" "(v,r)\<in>(ufa_\<beta>_start l)\<^sup>*" "r = l!r" "(y,z)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(v,r)\<in>(ufa_\<beta>_start (l[x:=z]))\<^sup>*"
  using assms(2,1,3)
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step v w)
  have sg1: "(v,r)\<in>(ufa_\<beta>_start l)\<^sup>*"  using step by fastforce
  have sg2: "v<length l" "w<length l" using step(1) unfolding ufa_\<beta>_start_def by auto
  have sg3: "r<length l" using step(2) sg2(2) unfolding ufa_\<beta>_start_def by induction auto
  have sg4: "x<length l" "y<length l" using x_edge_y unfolding ufa_\<beta>_start_def by auto
  have sg5: "z<length l" using assms(4) sg4(2) unfolding ufa_\<beta>_start_def by induction auto
  from step show ?case
  proof (cases "x=v")
    case True
    have "r = rep_of l v" using sg1 step(5) 
        rep_of_path_iff[OF \<open>ufa_invar l\<close> \<open>r<length l\<close> \<open>v<length l\<close>] by presburger
    hence h2: "r = rep_of l x" using True by argo
    hence h3: "r = rep_of l z" using x_edge_y assms(4) 
      using rep_of_path_iff[OF assms(1) \<open>r<length l\<close> \<open>z<length l\<close>]
            rep_of_path_iff[OF \<open>ufa_invar l\<close> \<open>r<length l\<close> \<open>x<length l\<close>]
            assms(3) sg1 True 
      by (metis rep_of_bound rep_of_invar_along_path sg2(2) sg4(1) sg4(2) sg5 step.hyps(1,2)
                step.prems(1) ufa_\<beta>_start_functional)
    
    show ?thesis 
      apply (rule converse_rtrancl_into_rtrancl[where b = z]) 
       apply (subst True[symmetric])+ 
      subgoal unfolding ufa_\<beta>_start_def apply (subst length_list_update)+
        using \<open>x<length l\<close> \<open>z<length l\<close> 
        by (smt acyclicity assms(4) case_prodI mem_Collect_eq nth_list_update_eq 
            rtrancl_into_trancl2 sg2(1) step.prems(1) ufa_\<beta>_def ufa_\<beta>_start_def x_edge_y)
      using h3 rep_of_path_iff[OF assms(1) \<open>r<length l\<close> \<open>z<length l\<close>] 
            assms(4) compress_preserves_paths_out_of_y'[OF x_edge_y] step.prems(1) by blast
  next
    case False
    then show ?thesis 
      by (metis compress_preserves_other_edges converse_rtrancl_into_rtrancl 
          step.IH step.hyps(1) step.prems(1,2))
  qed
qed


lemma compress_preserves_rep_of_direct':
  assumes "ufa_invar l" "r = rep_of l x" "(y,z)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "r = rep_of (l[x := z]) x"
  using x_edge_y \<open>ufa_invar l\<close> assms(2)
proof -
  have sg0: "x<length l" "y<length l" using x_edge_y unfolding ufa_\<beta>_start_def by auto
  have sg00: "z<length l" using assms(3) sg0(2) unfolding ufa_\<beta>_start_def by induction auto
  have sg1: "rep_of l x = rep_of l y" using x_edge_y \<open>ufa_invar l\<close> 
    using rep_of_idx ufa_\<beta>_start_def by auto
  have sg2: "rep_of l y = rep_of l z" using assms(3) 
    by (metis (no_types, lifting) sg1 assms(2) case_prodD assms(1) mem_Collect_eq 
        rep_of_bound rep_of_invar_along_path rtrancl.simps ufa_\<beta>_start_def x_edge_y)
  have sg3': "(x,z)\<in>(ufa_\<beta>_start l)\<^sup>*" using x_edge_y assms(3) by simp
  have sg3: "rep_of (l[x := z]) x = rep_of (l[x := z]) z" 
    by (metis (no_types, lifting) assms(3) case_prodD assms(1) length_list_update mem_Collect_eq 
        nth_list_update_eq rep_of_idx rtrancl.simps ufa_\<beta>_start_def 
        ufa_compress_generalized[OF _ _ _ sg3'] x_edge_y)
  have sg4': "(z, rep_of l z) \<in> (ufa_\<beta>_start l)\<^sup>*""l ! rep_of l z = rep_of l z"
    using rep_of_path_iff[OF assms(1) rep_of_bound[OF assms(1) sg00] sg00] by auto
  have sg4: "rep_of (l[x := z]) z = rep_of l z" 
    apply (cases "x = z")
    subgoal using x_edge_y assms(3) 
      by (metis acyclicity assms(1) list_update_beyond not_le_imp_less rtrancl_into_trancl2 ufa_\<beta>_def) 
    using compress_preserves_paths_to_roots'[OF assms(1) sg4'(1) sg4'(2)[symmetric] assms(3)]
          sg4' 
    by (metis acyclicity assms(1) length_list_update nth_list_update_neq rep_of_bound 
        rep_of_path_iff rep_of_ufa_\<beta>_refl rtrancl_into_trancl1 sg0 sg00 sg2 ufa_\<beta>_def 
        ufa_compress_generalized[OF _ _ _ sg3'] x_edge_y)
  thus ?thesis using sg1 sg2 sg3 sg4 assms by argo
qed


context
  assumes inv: "ufa_invar l" and
          pathyz: "(y, rep_of l x) \<in> (ufa_\<beta>_start l)\<^sup>*"
begin \<comment>\<open>invar\<close>

lemma compress_preserves_paths_out_of_y:
  assumes "(v,w)\<in>(ufa_\<beta>_start l)\<^sup>*" "(y,v)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))\<^sup>*"
  using assms(1,2)  x_edge_y
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step y0 z)
  have "y0\<noteq>x" using paths_have_distinct_endpoints using step 
    by (metis (no_types, lifting) acyclicity inv mem_Collect_eq prod.simps(2) 
        rtrancl_into_trancl2 ufa_\<beta>_def ufa_\<beta>_start_def)
  hence sg1: "(y0, z) \<in> ufa_\<beta>_start (l[x := rep_of l x])" 
    using step compress_preserves_other_edges by blast
  have "(y, z) \<in> (ufa_\<beta>_start l)\<^sup>*" using step by auto
  then show ?case using step sg1 by fastforce
qed

lemma compress_preserves_paths_out_of_z:
  assumes "(v,w)\<in>(ufa_\<beta>_start l)\<^sup>*" "(rep_of l x,v)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(v,w)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))\<^sup>*"
  using compress_preserves_paths_out_of_y[OF assms(1)] pathyz assms(2) rtrancl_trans by fast

lemma compress_preserves_paths_to_roots:
  assumes "(v,r)\<in>(ufa_\<beta>_start l)\<^sup>*" "r=l!r"
  shows "(v,r)\<in>(ufa_\<beta>_start (l[x:= rep_of l x]))\<^sup>*"
  using assms pathyz x_edge_y inv
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step y0 z)
  have sg1:  "(y, rep_of l x) \<in> (ufa_\<beta>_start l)\<^sup>*" using x_edge_y using pathyz by blast
  then show ?case  proof (cases "y0=x")
    case True
    have "x<length l" using x_edge_y unfolding ufa_\<beta>_start_def by blast
    have "r<length l" using step(1,2)
      by (metis (no_types, lifting) True case_prodD mem_Collect_eq rtrancl.simps ufa_\<beta>_start_def) 
    have "(x,r)\<in> (ufa_\<beta>_start l)\<^sup>*" using step(1,2) True by simp
    hence "r = rep_of l x" using step(1,2,4) True 
        rep_of_path_iff[OF \<open>ufa_invar l\<close> \<open>r<length l\<close> \<open>x<length l\<close>] by presburger
    hence "r = rep_of (l[x:= rep_of l x]) x" using rep_of.psimps 
      by (simp add: \<open>x < length l\<close> inv ufa_compress_aux(2))
    show ?thesis using step
      by (simp add: True \<open>r = rep_of (l[x := rep_of l x]) x\<close> \<open>x < length l\<close> 
          rep_of_ufa_\<beta>_refl ufa_compress_invar)
  next
    case False
    have "(y0, z) \<in> ufa_\<beta>_start (l[x := rep_of l x])"
      using step False compress_preserves_other_edges by blast
    then show ?thesis  using step by fastforce
  qed
qed





lemma compress_preserves_rep_of_direct:
  assumes "r = rep_of l x"
  shows "r = rep_of (l[x := rep_of l x]) x"
  using assms inv ufa_\<beta>_start_def ufa_compress_aux(2) x_edge_y by auto


end \<comment>\<open>invar\<close>
end \<comment>\<open>x_edge_y\<close>




section\<open>Notion of state evolution over time (UnionFind13RankLink, UnionFind23Evolution)\<close>


subsubsection\<open>UnionFind13RankLink\<close>
definition union_by_rank_l where "union_by_rank_l l rkl x y \<equiv> if (rkl!x < rkl!y) 
                                  then (ufa_union l x y) else (ufa_union l y x)"

definition union_by_rank_rkl where "union_by_rank_rkl rkl x y \<equiv> if (rkl!x = rkl!y) 
                                    then rkl[x := Suc (rkl!x)] else rkl"

lemma union_by_rank_l_length[simp]:
      "length (union_by_rank_l l rkl i j) = length l"
  by (auto simp: union_by_rank_l_def)

lemma union_by_rank_rkl_length[simp]:
      "length (union_by_rank_rkl rkl i j) = length rkl"
  by (auto simp: union_by_rank_rkl_def)

lemma link_cannot_decrease_rank:
  "rkl!v \<le> (union_by_rank_rkl rkl x y)!v"
  apply(simp add: union_by_rank_rkl_def)
  by (metis eq_iff lessI less_imp_le_nat nth_list_update_eq nth_list_update_neq nth_update_invalid)


lemma link_preserves_rank_of_non_roots:
  assumes "x<length l" "y<length l" "v<length l" "x=l!x" "v\<noteq>l!v"
  shows "rkl!v = (union_by_rank_rkl rkl x y)!v"
proof -
  have "x\<noteq>v" using assms by blast
  thus ?thesis unfolding union_by_rank_rkl_def 
    using assms nth_list_update_neq[OF \<open>x \<noteq>v\<close>, of  rkl "Suc (rkl!x)"]
    by (auto cong: if_cong)  
qed


lemma path_link_1:
  assumes "ufa_invar l" "x=l!x" "y=l!y" "x<length l" "y<length l" "(w,x)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(w,y)\<in> (ufa_\<beta>_start (ufa_union l x y))\<^sup>*"
  using assms(6,1-5)
proof (induction rule: converse_rtrancl_induct)
  case base
  show ?case 
    using assms
    by (cases "x=y") (auto simp add: rep_of_refl ufa_\<beta>_start_def) 
next
  case (step w z)
  have "w\<noteq>x" "w\<noteq>y" using step(1,5,6) unfolding ufa_\<beta>_start_def by auto
  with step have "(w,z)\<in> (ufa_\<beta>_start (ufa_union l x y))\<^sup>*" 
    by (metis (no_types, lifting) case_prodD case_prodI length_list_update mem_Collect_eq 
        nth_list_update_neq r_into_rtrancl rep_of_simps(1) ufa_\<beta>_start_def)
  then show ?case using step by fastforce
qed

lemma path_link_2:
  assumes "ufa_invar l" "x=l!x" "y=l!y" "x<length l" "y<length l" "(w,z)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "(w,z)\<in> (ufa_\<beta>_start (ufa_union l x y))\<^sup>*"
  using assms (6,1-5)
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step v w)
  have "v\<noteq>x" "v\<noteq>y" using step(1,5,6) unfolding ufa_\<beta>_start_def by auto
  with step have "(v,w) \<in> (ufa_\<beta>_start (ufa_union l x y))\<^sup>*" 
    by (metis (no_types, lifting) case_prodD case_prodI length_list_update mem_Collect_eq 
        nth_list_update_neq rep_of_simps(1) rtrancl.simps ufa_\<beta>_start_def)
  then show ?case using step by fastforce
qed

lemma path_link_1_converse:
  assumes "ufa_invar l" "x=l!x" "y=l!y" "x<length l" "y<length l" 
          "(w,y)\<in>(ufa_\<beta>_start (ufa_union l x y))\<^sup>*"
  shows "(w,x)\<in>(ufa_\<beta>_start l)\<^sup>* \<or> (w,y)\<in>(ufa_\<beta>_start l)\<^sup>*"
  using assms(6,1-5)
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step w z)
  then show ?case
    by (smt case_prodD length_list_update mem_Collect_eq nth_list_update_neq rep_of_idx 
        rep_of_path_iff rep_of_simps(1) ufa_\<beta>_start_def)
qed

lemma path_link_2_converse:
  assumes "ufa_invar l" "x=l!x" "y=l!y" "x<length l" "y<length l" 
          "(w,z)\<in>(ufa_\<beta>_start (ufa_union l x y))\<^sup>*" "z\<noteq>y"
  shows "(w,z)\<in>(ufa_\<beta>_start l)\<^sup>*"
  using assms(6,1-5,7)
proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case (step w v)
  have "(w,v)\<in>(ufa_\<beta>_start l)\<^sup>*" using step apply (cases "w = rep_of l x")
    unfolding ufa_\<beta>_start_def
    apply (smt case_prodD converse_rtranclE' mem_Collect_eq nth_list_update_eq rep_of_refl)
    unfolding ufa_\<beta>_start_def by auto
  then show ?case using step by fastforce
qed

lemma descendants_link_2_incl:
  assumes "ufa_invar l" "x=l!x" "y=l!y" "x<length l" "y<length l"
  shows "e \<in> descendants l z \<Longrightarrow> e \<in> descendants (ufa_union l x y) z"
  unfolding descendants_def using assms path_link_2 by blast

lemma card_descendants_link_2_le:
  assumes "ufa_invar l" "x=l!x" "y=l!y" "x<length l" "y<length l" "z<length l"
  shows "card (descendants l z) \<le> card (descendants (ufa_union l x y) z)"
  using assms 
  by(auto intro!: card_mono descendants_link_2_incl finite_descendants ufa_union_invar)

lemma descendants_link_1:
  assumes "ufa_invar l"  "x=l!x" "y=l!y" "x<length l" "y<length l"
  shows "descendants (ufa_union l x y) y = descendants l x \<union> descendants l y"
  unfolding descendants_def
proof (safe, goal_cases)
  case (1 z)
  then show ?case using path_link_1_converse[OF assms 1(1)] by blast
next
  case (2 z)
  show ?case using path_link_1[OF assms 2] .
next
  case (3 z)
  show ?case using path_link_2[OF assms 3] .
qed

lemma descendants_link_2:
  assumes "ufa_invar l"  "x=l!x" "y=l!y" "x<length l" "y<length l" "z<length l" "z\<noteq>y"
  shows "descendants (ufa_union l x y) z = descendants l z"
  unfolding descendants_def
proof (safe,goal_cases)
  case (1 x)
  show ?case using path_link_2_converse[OF assms(1-5) 1 \<open>z\<noteq>y\<close>] .
next
  case (2 x)
  show ?case using path_link_2[OF assms(1-5) 2] .
qed

lemma invar_rank_ineqI:
"invar_rank l rkl \<Longrightarrow> i<length l \<Longrightarrow> l ! i = i \<Longrightarrow> 2 ^ rkl ! i \<le> card (descendants l i)"
  by(auto simp: invar_rank_def)


lemma invar_rankI:
  assumes "ufa_invar l" "length l = length rkl" 
    "\<And>i j. i< length l \<Longrightarrow> j< length l \<Longrightarrow> l!i=j \<Longrightarrow> i\<noteq>j \<Longrightarrow> rkl ! i < rkl ! j" 
    "\<And>i. i<length l \<Longrightarrow>  l!i=i \<Longrightarrow> (2::nat) ^ rkl!i \<le> card (descendants l i)"
  shows  "invar_rank l rkl" 
  using assms unfolding invar_rank_def by auto


lemma invar_rankD:
  assumes "invar_rank l rkl" 
  shows "ufa_invar l" "length l = length rkl" 
    "\<And>i j. i< length l \<Longrightarrow> j< length l \<Longrightarrow> l!i=j \<Longrightarrow> i\<noteq>j \<Longrightarrow> rkl ! i < rkl ! j" 
    "\<And>i. i<length l \<Longrightarrow>  l!i=i \<Longrightarrow> (2::nat) ^ rkl!i \<le> card (descendants l i)" 
  using assms unfolding invar_rank_def by auto


lemma invar_rank_link_ufa_invar:
  assumes "invar_rank l rkl" "x < length l" "y < length l"
  shows "ufa_invar (union_by_rank_l l rkl x y)"
 using assms by (auto simp: union_by_rank_l_def intro: invar_rank_ufa_invarI ufa_union_invar)

lemma invar_rank_link_rank_on_path:
  assumes "invar_rank l rkl" "x < length l" "y < length l" "x=l!x" "y=l!y" "x\<noteq>y"
    "i < length l" "j < length l"
    "union_by_rank_l l rkl x y ! i = j" "i \<noteq> j"
  shows     " union_by_rank_rkl rkl x y ! i < union_by_rank_rkl rkl x y ! j"
  using assms 
  unfolding union_by_rank_l_def union_by_rank_rkl_def invar_rank_def
  by (smt Suc_lessD Suc_less_eq Suc_n_not_le_n le_eq_less_or_eq length_list_update 
      not_le_imp_less nth_list_update_eq nth_list_update_neq order_less_irrefl rep_of_iff)

lemma invar_rank_link_rank_ub:
  assumes "invar_rank l rkl" "x < length l" "y < length l" "x=l!x" "y=l!y" "x\<noteq>y"
    "i < length l" "union_by_rank_l l rkl x y ! i = i"
  shows      " 2 ^ union_by_rank_rkl rkl x y ! i \<le> card (descendants (union_by_rank_l l rkl x y) i)"
proof -
  have eq: "rkl[i := Suc (rkl ! y)] ! i = Suc (rkl!y)" 
    using \<open>i < length l\<close> assms(1) invar_rank_def by force
  show ?thesis  
  proof (cases "rkl!x=rkl!y")  
    case 1: True 
    have "i=l!i" using 1 assms assms unfolding union_by_rank_l_def apply (auto cong: if_cong)
      by (metis nth_list_update_neq rep_of_refl)
    have hd: "2^rkl!i \<le> card (descendants l i)"
             "2^rkl!y \<le> card (descendants l y)"
      using assms(1) \<open>y<length l\<close> \<open>i<length l\<close> \<open>i=l!i\<close> \<open>y=l!y\<close> 
      unfolding invar_rank_def by auto
    show ?thesis 
    proof (cases "x=i")
      case True
      have "2 ^ union_by_rank_rkl rkl x y ! i \<le> card (descendants l y \<union> descendants l x)"
        using assms 1 True hd
        apply(subst card_Un_disjoint[OF _ _ disjoint_descendants])
        by (auto simp: eq union_by_rank_rkl_def union_by_rank_l_def 
                intro: finite_descendants invar_rank_ufa_invarI)
      also have "\<dots> = card (descendants (union_by_rank_l l rkl x y) i)"
        using 1 assms
        by (auto simp: union_by_rank_l_def True descendants_link_1 dest: invar_rank_ufa_invarI)    
      finally show ?thesis .
    next
      case False \<comment>\<open>x \<noteq> i\<close>
      then show ?thesis  
        using 1 assms \<open>i=l!i\<close>   
        by (auto simp: union_by_rank_rkl_def union_by_rank_l_def descendants_link_2 invar_rank_def)
    qed
  next
    case False \<comment>\<open>rkl ! x \<noteq> rkl ! y\<close>
    have i: "i=l!i" using False assms
      by (smt nth_list_update_neq rep_of_refl union_by_rank_l_def)
    have "2 ^ union_by_rank_rkl rkl x y ! i \<le> card (descendants l i)"
      using False assms i
      by (auto simp: union_by_rank_rkl_def union_by_rank_l_def split: if_splits 
              intro: invar_rank_ineqI)
    also have "\<dots> \<le> card (descendants (union_by_rank_l l rkl x y) i)"
      using assms  
      by (auto simp: union_by_rank_l_def intro: card_descendants_link_2_le invar_rank_ufa_invarI)
    finally show ?thesis .
  qed
qed

lemma invar_rank_link:
  assumes "invar_rank l rkl" "x < length l" "y < length l" "x=l!x" "y=l!y" "x\<noteq>y"
  shows "invar_rank (union_by_rank_l l rkl x y) (union_by_rank_rkl rkl x y)"
  apply(rule invar_rankI)
  using assms
  by (auto intro: invar_rank_link_rank_ub invar_rank_link_ufa_invar
                invar_rank_link_rank_on_path
          elim: invar_rankD )
  

lemma invar_rank_compress_invar: 
  assumes "invar_rank l rkl"  "(x,y)\<in>(ufa_\<beta>_start l)"
  shows "ufa_invar (l[x:= rep_of l y])"
  using assms
  unfolding ufa_\<beta>_start_def
    using invar_rank_ufa_invarI rep_of_idx ufa_compress_invar by auto

lemma invar_rank_compress_rank_on_path: 
  assumes "invar_rank l rkl"  "(x,y)\<in>(ufa_\<beta>_start l)"
    "i < length l" "j < length l"
    "l[x := rep_of l y] ! i = j" "i \<noteq> j"
  shows "rkl ! i < rkl ! j"
  using assms unfolding ufa_\<beta>_start_def
    by (smt case_prodD invar_rank_ufa_invarI length_list_update mem_Collect_eq 
        nth_list_update' parent_has_greater_rank rank_increases_strictly_along_path 
        rep_of_iff rep_of_ufa_\<beta>)
  
lemma invar_rank_compress_rank_ub: 
  assumes "invar_rank l rkl"  "(x,y)\<in>(ufa_\<beta>_start l)" "i < length l"
      "l[x := rep_of l y] ! i = i"
    shows "2 ^ rkl ! i \<le> card (descendants (l[x := rep_of l y]) i) "
proof -
  have xidom: "i<length l" "x<length l" "y<length l" using assms unfolding ufa_\<beta>_start_def by auto
  have deq: "descendants l i = descendants (l[x := rep_of l y]) i" 
    unfolding descendants_def
  proof (safe)
    fix x'
    assume "(x', i) \<in> (ufa_\<beta>_start l)\<^sup>*"
    then show "(x', i) \<in> (ufa_\<beta>_start (l[x := rep_of l y]))\<^sup>*"
    proof (cases "x'=x")
      case True
      then show ?thesis using compress_preserves_paths_to_roots[OF \<open>(x, y) \<in> ufa_\<beta>_start l\<close> 
           invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] _ \<open>(x', i) \<in> (ufa_\<beta>_start l)\<^sup>*\<close> ]
        by (smt assms case_prodD invar_rank_ufa_invarI mem_Collect_eq nth_list_update' 
            rep_of_idx rep_of_ufa_\<beta>_refl rtrancl.rtrancl_refl ufa_\<beta>_start_def)
    next
      case False
      then show ?thesis using compress_preserves_paths_to_roots[OF \<open>(x, y) \<in> ufa_\<beta>_start l\<close> 
           invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] _ \<open>(x', i) \<in> (ufa_\<beta>_start l)\<^sup>*\<close> ]
        by (smt assms case_prodD invar_rank_ufa_invarI mem_Collect_eq 
            nth_list_update' nth_list_update_eq rep_of_idx rep_of_min rep_of_ufa_\<beta>_refl 
            ufa_\<beta>_start_def xidom(1,2))
    qed 
  next
    fix x'
    assume i: "(x', i) \<in> (ufa_\<beta>_start (l[x := rep_of l y]))\<^sup>*"
    show "(x', i) \<in> (ufa_\<beta>_start l)\<^sup>*"  
    proof (cases "x'=x")
      case True
      with i assms show ?thesis
        using compress_preserves_rep_of_direct invar_rank_ufa_invarI
            length_list_update r_into_rtrancl rep_of_bound rep_of_invar_along_path rep_of_path_iff 
            ufa_compress_invar xidom(2) xidom(3)  
        by metis
    next
      case False
      have sg: "(x, y) \<in> (ufa_\<beta>_start l)\<^sup>*" using assms by fast
      with i assms(1,3) False show ?thesis using 
          compress_preserves_rep_of_direct[OF assms(2) invar_rank_ufa_invarI[OF assms(1)] _]
        apply (induction rule: converse_rtrancl_induct) by blast
          (smt assms Pair_inject case_prodD converse_rtrancl_into_rtrancl invar_rank_ufa_invarI 
            length_list_update mem_Collect_eq rep_of_bound rep_of_idx rep_of_invar_along_path  
            rep_of_refl rep_of_ufa_\<beta>_refl ufa_\<beta>_start_def ufa_compress_aux(2) ufa_compress_invar xidom(1,2))
    qed 
  qed
  have "i<length l" using assms by fastforce
  thus ?thesis apply (subst deq[symmetric]) using assms deq unfolding invar_rank_def
    by (metis nth_list_update rep_of_min xidom(2) xidom(3))
qed

lemma invar_rank_compress:
  assumes "invar_rank l rkl"  "(x,y)\<in>(ufa_\<beta>_start l)"
  shows "invar_rank (l[x:= rep_of l y]) rkl"
  apply(rule invar_rankI)
  using assms
  by (auto intro: invar_rank_compress_rank_on_path invar_rank_compress_invar
                invar_rank_compress_rank_ub
         dest: invar_rankD(2))
 


\<comment>\<open>The second part of UnionFind13RankLink seems too specific to be needed, but maybe it
is useful to have some explicit lemmas about rep_of under union_by_rank\<close>


subsection\<open>UnionFind23Evolution\<close>

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


lemma evolution_lengths:
  assumes "evolution l rkl l' rkl'"
  shows "length l = length l'" "length rkl = length rkl'"
  using assms by (induction) (auto simp: union_by_rank_l_def union_by_rank_rkl_def)
  

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
  using contextasm(2,1)
proof (induction rule: evolution.induct)
  case (EvUnion x y)
  then show ?case unfolding union_by_rank_l_def using assms rep_of_refl
    using nth_list_update_neq by (metis (full_types)) 
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
  using assms
proof (cases "l!v = l'!v")   
  case True
  then show ?thesis using rank_grows by presburger
next
  case False
  show ?thesis using contextasm(2) False assms
  proof induction
     case (EvUnion x y)
     then show ?case unfolding union_by_rank_l_def 
       by (smt contextasm(1) invar_rank_ufa_invarI nth_update_invalid ufa_union_preserves_parent)
   next
     case (EvCompress x y)
     hence hz1: "l[x := rep_of l y]!v = rep_of l y" by (metis nth_list_update')
     with EvCompress have hz2: "v = x"  by (metis nth_list_update')
     with EvCompress have unique: "l!v = y" unfolding ufa_\<beta>_start_def by fast
     from EvCompress show ?case apply (subst hz1) apply (subst unique) 
       by (metis contextasm(1) hz1 invar_rank_ufa_invarI less_imp_le_nat 
           nth_update_invalid rank_increases_strictly_along_path 
           rep_of_bound rep_of_ufa_\<beta> ufa_invarD(2) unique)
   qed
qed

end  \<comment>\<open>StudyOfEvolution\<close>

section \<open>Lemmas about \<Phi> under compression (UnionFind42PotentialCompress)\<close>

\<comment>\<open>During a compression, the level function is unchanged at ancestors of y\<close>

\<comment>\<open>This would be compress_preserves_k_above_y, again this does not apply as we compress differently\<close>


lemma compress_preserves_level_above_y:
  assumes "invar_rank l rkl" "(x,y)\<in>(ufa_\<beta>_start l)" 
          "(y,z)\<in> (ufa_\<beta>_start l)\<^sup>*"  "(y,v)\<in> (ufa_\<beta>_start l)\<^sup>*" "v\<noteq>l!v"
        shows "level (l[x:=z]) rkl v = level l rkl v"
proof -
  have "x<length l" using assms(2) unfolding ufa_\<beta>_start_def by blast
  have "y<length l" using assms(2) unfolding ufa_\<beta>_start_def by blast
  hence "v<length l" using assms(4) unfolding ufa_\<beta>_start_def using rtranclE by force
  hence "v<length (l[x:=z])" by auto
  have "l[x := z] ! v \<noteq> v" using assms 
    by (metis \<open>v < length (l[x := z])\<close> acyclicity invar_rank_ufa_invarI length_list_update 
        nth_list_update_neq rtrancl_into_trancl2 ufa_\<beta>_def)
  have "x\<noteq>v" 
    using paths_have_distinct_endpoints
          [OF invar_rank_ufa_invarI[OF assms(1)] \<open>x<length l\<close> \<open>v<length l\<close>] assms 
    by (metis trancl.intros(1) trancl_rtrancl_trancl ufa_\<beta>_def)
  hence eq: "(l[x := z] ! v) = l!v" by simp
  show ?thesis unfolding level_def prek_def by (subst eq) (rule refl)
qed



\<comment>\<open> Assume x and y are non-roots. (This is required for their level and index
   to be defined.) Assume that there is a non-trivial path from x to y.
   Finally, assume that x and y have the same level, i.e., @{term "level l rkl x = level l rkl y"}.
   Then, @{term "compow (Suc (index l rkl x)) (Ackermann (prek l rkl x)) (rankr rkl x) \<le> rankr rkl (l!y)"}. 
   This is part of the proof of Lemma 4.10 in Alstrup et al.'s paper. \<close>

lemma levelx_levely:
  assumes "invar_rank l rkl" "x<length l" "y<length l" "x\<noteq>l!x" "y\<noteq>l!y" "(l!x,y) \<in> (ufa_\<beta>_start l)\<^sup>*" 
          "level l rkl x = level l rkl y"
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
    apply (rule f_nat_nat.f_\<beta>\<^sub>f[OF inn_f_nat_nat, OF assms(1) assms(2) assms(4)[symmetric], 
                              of "rankr rkl (l ! x)"])
    apply simp
    using assms(1,2) parent_has_greater_rankr by fastforce
    \<comment>\<open>By definition of [prek], applying [A (prek x)] to [rankr y] takes us
     at least to [rankr (p y)].\<close>
  have hy': "Ackermann 0 (rankr rkl y) \<le> rankr rkl (l ! y)" 
    apply (subst Ackermann_base_eq) unfolding rankr_def 
    using assms(1,3,5) parent_has_greater_rank by fastforce
  have hy: "Ackermann (prek l rkl x) (rankr rkl y) \<le> rankr rkl (l!y)"
    apply (subst pp)
    using f_nat_nat.\<beta>\<^sub>f_spec_direct[OF lnn_f_nat_nat ] unfolding prek_def defk_def using hy' by fast
  have sg1: "Ackermann (prek l rkl x) (rankr rkl y)  \<le> rankr rkl (l ! y)" using hy by simp
  have sg0: "Ackermann (prek l rkl x) (rankr rkl (l ! x))  \<le> rankr rkl (l ! y)" using hxy sg1
      mono_Ackermann[of "prek l rkl x"] unfolding mono_def by fastforce

  have "Ackermann (prek l rkl x) ((Ackermann (prek l rkl x) ^^ index l rkl x) (rankr rkl x))
           \<le> Ackermann (prek l rkl x) (rankr rkl (l ! x))"
    by (rule monoD[OF mono_Ackermann]) (rule hx)
  also have "\<dots> \<le> rankr rkl (l ! y)" 
    by (rule sg0) 
  finally show ?thesis by simp
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
    by (metis (no_types, hide_lams) invar_rank_def rep_of_bound rep_of_idx 
        rep_of_invar_along_path ufa_invarD(2))
  have rpyz: "rankr rkl (l!y) \<le> rankr rkl z"
    by (metis (no_types, lifting) assms(1) assms(3) invar_rank_def pyz 
        rankr_increases_along_path_refl rep_of_bound rep_of_ufa_\<beta>_refl ufa_invarD(2))
  note f = levelx_levely[OF assms(1-7)]
  have rpyz': "(Ackermann (prek l rkl x) ^^ Suc (index l rkl x)) (rankr rkl x) \<le> rankr rkl z" 
    using rpyz f by linarith
  have sg0: "x < length (l[x := rep_of l x])" using assms(2) by simp
  have prehkk: "prek l rkl x = prek (l[x:= rep_of l x]) rkl x" 
    using assms(9) level_def  
        sg0 non_root_forever[OF assms(1) compress_evolution[OF assms(1,2,4)] assms(4), symmetric]
    by auto
  have f': "(Ackermann (prek (l[x := rep_of l x]) rkl x) ^^ Suc (index l rkl x)) (rankr rkl x)
    \<le> rankr rkl z" using rpyz' apply (subst (asm) prehkk) .
  have sg1: "l[x := rep_of l x] ! x = rep_of l x" by (simp add: assms(2))
  show ?thesis unfolding index_def[OF invar_rank_evolution[OF assms(1) compress_evolution[OF assms(1,2,4)]] 
        sg0 non_root_forever[OF assms(1) compress_evolution[OF assms(1,2,4)] assms(4), symmetric]]
    apply (rule f_nat_nat.\<beta>\<^sub>f_spec_reciprocal)
    subgoal 
      using inn_f_nat_nat[OF invar_rank_evolution[OF assms(1) compress_evolution[OF assms(1,2,4)]] sg0
          non_root_forever[OF assms(1) compress_evolution[OF assms(1,2,4)] assms(4), symmetric]] .
    subgoal using f' apply (subst (asm) \<open>z=rep_of l x\<close>) apply (subst sg1) .
    done
qed


section\<open>Evolution of level, index and potential over time (UnionFind43PotentialAnalysis)\<close>

lemma lexpo_well_defined:
  assumes "(k::nat) < a" "i\<le>r"
  shows "i \<le> (a-k)*r" 
proof -
  have sg1: "a-k = (1+ (a-k-1))" using assms by auto
  show ?thesis apply (subst sg1) apply (subst ring_distribs) using assms by fastforce
qed

lemma lexpo_cannot_increase_if_ak_decreases:
  assumes "(i::nat) \<le> r" "ak' < ak"
  shows "ak' * r - i' \<le> ak * r - i"
proof -
  have h: "ak' \<le> ak - 1" using assms by force
  hence "ak' * r  \<le> (ak - 1) * r " by fastforce
  hence  h2: "ak' * r  - i'\<le> (ak - 1) * r -i'" by linarith
  have "(ak - 1) * r - i' \<le> ak*r - i" apply (subst diff_mult_distrib) using assms by force
  thus ?thesis using h2 by force
qed

lemma lexpo_decreases_if_ak_decreases:
  assumes "(i::nat)\<le>r" "1\<le>i'" "0<ak'" "ak'<ak" "0<r"
  shows "ak'*r - i' < ak*r - i"
proof -
  have "0 < ak'*r" using assms(3,5) by auto
  hence "ak' * r - 0 \<le> ak * r - r" 
    using lexpo_cannot_increase_if_ak_decreases[OF _ assms(4)] assms by blast
  hence "ak' * r - 1 < ak * r - r" using \<open>0<ak'*r\<close> by linarith
  thus ?thesis using assms(1,2) by linarith
qed

lemma lexpo_cannot_increase:
  assumes "(i::nat)\<le>r" "k\<le>k'" "k'<a" "k=k' \<longrightarrow> i\<le>i'"
  shows "(a-k)*r - i \<ge> (a-k')*r-i'"
  using assms proof (cases "k=k'")
  case True
  have "(a - k') * r - i' \<le> (a - k) * r - i'" using True by blast
  then show ?thesis using assms(4) True by force
next
  case False
  have "k<k'" using assms False by linarith
  note assms' = assms(1,3) \<open>k<k'\<close> 
  then show ?thesis
  proof (cases "i\<le>i'")
    case True
    have "(a - k') * r - i' \<le> (a - k') * r - i" using True by auto
    moreover have "(a - k') * r \<le> (a - k) * r " using assms' by fastforce
    ultimately show ?thesis by linarith
  next
    case False
    hence False': "i>i'" by fastforce
    have sg1: "a - k' < a - k" using assms' by fastforce
    show ?thesis using lexpo_cannot_increase_if_ak_decreases[OF \<open>i\<le>r\<close> sg1] .
  qed
qed

lemma lexpo_cannot_increase_and_decreases_if:
  assumes "(i::nat)\<le>r" "1\<le>(i'::nat)" "i'\<le>r" "k\<le>k'" "k'<a" "k=k' \<longrightarrow> i\<le>i'"
  shows              "(a-k') * r  - i' \<le> (a-k) * r - i" 
    "(k<k' \<or> i<i') \<longrightarrow>(a-k') * r  - i' < (a-k) * r - i"
  using assms 
proof goal_cases
  case 1
  then show ?case using lexpo_cannot_increase[OF assms(1,4,5,6)] .
next
  case 2
  then show ?case
  proof (cases "k=k'")
    case True
    have h6: "i' \<le> (a - k) * r" using lexpo_well_defined[of k a, OF _ assms(3)] assms(4,5) 
      by fastforce
    show ?thesis using True diff_less_mono2[of i i'] h6 by auto
  next
    case False
    then show ?thesis using lexpo_decreases_if_ak_decreases assms by simp
  qed
qed

lemma lexpo_cannot_increase_and_decreases_if':
  assumes "(i::nat)\<le>r" "1\<le>(i'::nat)" "i'\<le>r" "k\<le>k'" "k'<a" "k=k' \<longrightarrow> i\<le>i'" "(k<k' \<or> i<i')"
  shows "(a-k') * r  - i' < (a-k) * r - i"
  using lexpo_cannot_increase_and_decreases_if(2)[OF assms(1-6)] using assms(7) by blast

lemma prove_lexpo_decreases:
  assumes "(k::nat)\<le>k'" "k = k' \<longrightarrow> 1 + (i::nat) \<le> i'"
  shows "k<k' \<or> i<i'"
  using assms by linarith

context \<comment>\<open>StudyOfEvolution\<close>
  fixes l::"nat list" and rkl::"nat list" and l'::"nat list" and rkl'::"nat list"
  assumes contextasm: "invar_rank l rkl" "evolution l rkl l' rkl'"
begin


context \<comment>\<open>NonRoot\<close>
  fixes v::nat
  assumes vinDom: "v<length l" and
    v_has_a_parent: "v\<noteq>l!v"
begin

lemma evoasms: "invar_rank l' rkl'"  "v<length l'" "l'!v\<noteq>v" 
  using vinDom non_root_forever[OF contextasm v_has_a_parent] invar_rank_evolution[OF contextasm]
    evolution_lengths[OF contextasm(2)] by auto

lemma non_root_has_constant_rankr:
  "rankr rkl v = rankr rkl' v"
  using \<rho>_gt_0 non_root_has_constant_rank[OF contextasm vinDom v_has_a_parent]
  unfolding rankr_def by simp

lemma rankr_parent_grows:
  "rankr rkl (l!v) \<le> rankr rkl' (l'!v)"
  using \<rho>_gt_0 rank_parent_grows[OF contextasm v_has_a_parent]
  unfolding rankr_def by simp


\<comment>\<open>Because @{term "rankr rkl v"} is constant while @{term "rankr rkl (l!v)"} may grow, 
  @{term "level l rkl v"} can only grow\<close>

lemma defk_f_nat_nat: "f_nat_nat (\<lambda>k. Ackermann k (rankr rkl v))" 
  using lnn_f_nat_nat unfolding defk_def . 

lemma level_v_grows:
  "level l rkl v \<le> level l' rkl' v"
  unfolding level_def prek_def defk_def
  apply (subst Suc_le_mono)
  apply (subst non_root_has_constant_rankr[symmetric])
  using rankr_parent_grows f_nat_nat.\<beta>\<^sub>f_mono[OF defk_f_nat_nat] 
    contextasm(1) level_exists v_has_a_parent vinDom by auto


\<comment>\<open>As long as  @{term "level l rkl v"} remains constant, @{term "index l rkl v"} can only grow.\<close>
    

lemma index_v_grows_if_level_v_constant:
  assumes "level l rkl v = level l' rkl' v"
  shows "index l rkl v \<le> index l' rkl' v"
proof -
  have h': "prek l rkl v = prek l' rkl' v" using assms 
    unfolding level_def by blast
  show ?thesis 
    unfolding index_def[OF contextasm(1) vinDom v_has_a_parent[symmetric]] index_def[OF evoasms]
    apply (subst h'[symmetric])
    apply (subst non_root_has_constant_rankr[symmetric])
    using rankr_parent_grows contextasm(1) index_exists v_has_a_parent vinDom
      f_nat_nat.\<beta>\<^sub>f_mono[OF inn_f_nat_nat[OF contextasm(1) vinDom v_has_a_parent[symmetric]]]
    by presburger
qed


\<comment>\<open>The potential @{term "\<phi> l rkl v"} cannot increase. (Lemma 4.5 on pages 18-19)\<close>

lemma \<phi>_cannot_increase_nonroot:
  "\<phi> l' rkl' v \<le> \<phi> l rkl v"
proof -
  have hK: "rankr rkl v = rankr rkl' v" 
    using non_root_has_constant_rank[OF contextasm vinDom v_has_a_parent]
    unfolding rankr_def by simp
  have hR: "v\<noteq>l'!v" using non_root_forever[OF contextasm v_has_a_parent] .
  show ?thesis
  proof (cases "\<alpha>\<^sub>r (rankr rkl v) = \<alpha>\<^sub>r (rankr rkl (l!v))")
    case True
    note h\<phi> =  \<phi>_case_2[OF v_has_a_parent[symmetric] True]
    show ?thesis apply (subst h\<phi>) 
      apply (cases "\<alpha>\<^sub>r (rankr rkl' v) = \<alpha>\<^sub>r (rankr rkl' (l'!v))") proof goal_cases
      case 1 \<comment>\<open>True\<close>
      note h\<phi>' = \<phi>_case_2[OF evoasms(3) 1]
      show ?case 
        apply (subst h\<phi>') 
        apply (subst Suc_eq_plus1[symmetric])+ 
        apply (subst Suc_le_mono)
        apply (subst hK[symmetric])+
        apply (rule lexpo_cannot_increase)
           apply (rule index_le_rank[OF contextasm(1) vinDom v_has_a_parent[symmetric]])
          apply (rule level_v_grows)
         apply (subst hK) apply (subst 1) apply (rule level_lt_\<alpha>\<^sub>r[OF evoasms])
        using index_v_grows_if_level_v_constant by blast
    next
      case 2 \<comment>\<open>False\<close>
      show ?case using \<phi>_case_3[OF evoasms(3) 2] by fastforce
    qed
  next
    case False
    note h\<phi> = \<phi>_case_3[OF v_has_a_parent[symmetric] False]
    note H = \<alpha>\<^sub>r_rankr_grows_along_edges_corollary[OF contextasm(1) vinDom 
        v_has_a_parent[symmetric] False]
    have h0: "\<alpha>\<^sub>r (rankr rkl' v) < \<alpha>\<^sub>r (rankr rkl' (l'!v))"
      apply (subst hK[symmetric]) 
      apply (rule order.strict_trans2) 
       apply (rule H) using rankr_parent_grows mono_alphar[OF \<rho>_gt_0] unfolding mono_def by blast
    show ?thesis apply (subst h\<phi>) using h0 \<phi>_case_3[OF evoasms(3), of rkl'] by fastforce
  qed
qed

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
    apply(rule order.trans[OF \<phi>_upper_bound[of l' rkl' v], 
                of "\<alpha>\<^sub>r (rankr rkl v) * Suc (rankr rkl v)"])
    apply (subst assms)+
    by blast
qed

end  \<comment>\<open>StudyOfEvolution\<close>

lemma aux_arithmetic_lemma_00:
  assumes "(c::nat)\<le>b" "a + b + d \<le> e + c"
  shows "a + (b - c + d) \<le> e"
  using assms by auto

lemma aux_arithmetic_lemma_000:
  assumes "(a::nat)\<le>b" "c \<le> d + a"
  shows "c \<le> d + b" using assms by linarith


lemma random_arithmetic_lemma_01:
  assumes "(1::nat)\<le>kx" "(1::nat)\<le>ix" "kx<ary" "ix \<le> (ary - kx)*ry"
  shows  
    "ary * (ry + 1 + 1) + ((ary - kx) * ry - ix + 1) \<le> ary * (ry + 1) + ary * (ry + 1) + slack"
proof -
  have aryeq: "ary = (ary - kx) + kx" using assms by auto
    obtain arykx where arykx_eq: "arykx = (ary - kx)" by blast
  show ?thesis apply (subst arykx_eq[symmetric])
      apply (subst aryeq) apply (subst(2) aryeq) apply (subst(3) aryeq)
    apply (rule aux_arithmetic_lemma_00)
    subgoal using assms(4) arykx_eq by blast
    apply (rule aux_arithmetic_lemma_000[OF assms(2)])
     apply (subst arykx_eq) using assms
    by (simp add: algebra_simps)
qed
    
lemma aux_arithmetic_lemma_001:
  assumes "(a::nat)\<le>b" "b*c \<le> d"
  shows "a*c \<le>d"
  using assms 
  by (meson dual_order.refl mult_le_mono order_trans)

lemma aux_arithmetic_lemma_02:
  assumes "(1::nat)\<le>ary"
  shows "(ary + 1) * (ry + 1 + 1) + 0 \<le> ary * (ry + 1) + ary * (ry + 1) + 2"
  using assms by (simp add: algebra_simps)

\<comment>\<open>The increase of the potential \<Phi> during a link is at most 2. This is
   Lemma 4.7 on page 19. The formal proof follows roughly the paper proof,
   except we find it necessary to make certain case analyses explicit.\<close>
 

lemma potential_increase_during_link_preliminary:
  assumes "invar_rank l rkl" "x\<noteq>y" "x<length l" "y<length l" "x=l!x" "y=l!y" 
    "(rkl!x < rkl!y \<and> rkl' = rkl) \<or> (rkl!x = rkl!y \<and> rkl'= rkl[y:= Suc (rkl!y)])"
    "evolution l rkl (ufa_union l x y) rkl'"
  shows "\<Phi> (ufa_union l x y) rkl' \<le> \<Phi> l rkl + 2 "
proof (cases "rkl!y = rkl'!y")
  case True
  hence True': "rankr rkl y = rankr rkl' y" unfolding rankr_def by presburger
  have leq: "length (ufa_union l x y) = length l" by simp 
  show ?thesis apply (subst \<Phi>_simp)+ 
    apply (rule trans_le_add1)
    apply (subst leq)
    apply (rule sum_mono)
  proof (goal_cases)
    case (1 i)
    hence "i<length l" by simp
    have rankeq: "rankr rkl i = rankr rkl' i" apply (cases "i=y") apply (simp add: True') 
      by (metis True assms(7) list_update_id list_update_overwrite)
    show ?case using  \<phi>_v_cannot_increase[OF assms(1,8) \<open>i<length l\<close> rankeq] .
  qed
next
  case False
  have leq: "length (ufa_union l x y) = length l" by simp 
  have assm': "rkl!x = rkl!y" "rkl'= rkl[y:= Suc (rkl!y)]" using assms(7) False by auto
  have hKx: "rankr rkl x = rankr rkl y" using assm'(1) unfolding rankr_def by presburger
  have hK'y: "rankr rkl' y = Suc (rankr rkl y)" 
    unfolding rankr_def apply (subst add_Suc[symmetric]) 
    using assm'(2)  assms(1,4) unfolding invar_rank_def by auto

  have hF: "ufa_union l x y = union_by_rank_l l rkl y x"
    unfolding union_by_rank_l_def by (simp add: assm'(1))
  have hK: "rkl' = union_by_rank_rkl rkl y x"
    unfolding union_by_rank_rkl_def by (simp add: assm')
  have h8: "invar_rank (ufa_union l x y) rkl'" 
    apply (subst hF) apply (subst hK)
    using invar_rank_link[OF assms(1,4,3,6,5) assms(2)[symmetric]] .

  have part1: "sum (\<phi> (ufa_union l x y) rkl') ({0..<length l} - {x, y}) 
              \<le> sum (\<phi> l rkl) ({0..<length l} - {x, y})"
  proof (rule sum_mono)
    fix i assume 1: "i \<in> {0..<length l} - {x, y}"
    hence "i<length l" by simp
    have rankeq: "rankr rkl i = rankr rkl' i" using 1 by (simp add: assm'(2) rankr_def)
    show "\<phi> (ufa_union l x y) rkl' i \<le> \<phi> l rkl i "
      using  \<phi>_v_cannot_increase[OF assms(1,8) \<open>i<length l\<close> rankeq] .
  qed

  have hK'x: "rankr rkl x = rankr rkl' x" using assm'(2) assms(2) unfolding rankr_def by auto
  have hpx: " ufa_union l x y ! x = y" 
    using ufa_union_sets_parent[OF invar_rank_ufa_invarI[OF assms(1)] assms(3,4,5)] assms(4,6) 
          rep_of_refl by simp
  have hkx: "1 \<le> level (ufa_union l x y) rkl' x" using level_def leq assms(2,3) hpx by simp
  have hix: "1 \<le> index (ufa_union l x y) rkl' x" using index_ge_1[OF h8, of x] leq assms(2,3) hpx
    by presburger

  have is_root_y:"ufa_union l x y ! y = y" using assms(4,6) by(metis assms(2,5) hpx nth_list_update')
  note hy = \<phi>_case_1[OF assms(6)[symmetric], of rkl]
  note hy2 = \<phi>_case_1[OF is_root_y, of rkl']
  note hx =  \<phi>_case_1[OF assms(5)[symmetric], of rkl]
  have is_not_root_x: "ufa_union l x y ! x \<noteq> x" using hpx assms(2) by argo
  
  have partxy: "\<phi> (ufa_union l x y) rkl' x + \<phi> (ufa_union l x y) rkl' y \<le> \<phi> l rkl x +  \<phi> l rkl y + 2" 
    apply (subst hy) apply (subst hy2) apply (subst hx)
    apply (cases "\<alpha>\<^sub>r (rankr rkl' x) = \<alpha>\<^sub>r (rankr rkl' y)")
  proof goal_cases
    case 1 \<comment>\<open>True\<close>
    have hx2: "\<phi> (ufa_union l x y) rkl' x =
              (\<alpha>\<^sub>r (rankr rkl' x) - level (ufa_union l x y) rkl' x) *
              rankr rkl' x - index (ufa_union l x y) rkl' x + 1"
      using \<phi>_case_2[OF is_not_root_x, of rkl'] 1 hpx by argo

    have h9: "level (ufa_union l x y) rkl' x < \<alpha>\<^sub>r (rankr rkl' x)" using
          \<phi>_case_2_safe_level[OF h8, of x] leq assms(3) is_not_root_x 1 hpx by argo
    have h10: "index (ufa_union l x y) rkl' x
      \<le> (\<alpha>\<^sub>r (rankr rkl' x) -  level (ufa_union l x y) rkl' x) * rankr rkl' x" 
      using \<phi>_case_2_safe_index[OF h8, of x] leq assms(3) is_not_root_x 1 hpx by argo
    have hranks: "\<alpha>\<^sub>r (rankr rkl y) = \<alpha>\<^sub>r (Suc (rankr rkl y))" using 1 hK'x hKx hK'y by argo

    obtain ix where ixeq: "ix = index (ufa_union l x y) rkl' x" by blast
    obtain kx where kxeq: "kx = level (ufa_union l x y) rkl' x" by blast
    obtain ary where aryeq: "ary = \<alpha>\<^sub>r (rankr rkl y)" by blast
    obtain rx where rxeq: "rx = rankr rkl y" by blast

    show ?case apply (subst hx2) apply (subst hK'x[symmetric])+ apply (subst hKx)+ apply (subst hK'y)+
      apply (subst hranks[symmetric]) 
      apply (subst ixeq[symmetric])+  apply (subst kxeq[symmetric])+
      apply (subst aryeq[symmetric])+ apply (subst rxeq[symmetric])+
      apply (subst Suc_eq_plus1)+
      apply (subst add.commute[of _ " ary * (rx + 1 + 1)"])
      apply (rule random_arithmetic_lemma_01[of kx ix ary rx 2])
      subgoal using kxeq hkx by blast
      subgoal using ixeq hix by blast
      subgoal using kxeq aryeq h9 1 hK'x hKx by argo
      subgoal using ixeq aryeq kxeq rxeq h10 hK'x hKx by argo
      done
  next
    case 2 \<comment>\<open>False\<close>
    have h: "\<phi> (ufa_union l x y) rkl' x = 0" 
      using  \<phi>_case_3[OF is_not_root_x , of rkl'] 2 hpx by argo
    show ?case apply (subst h) apply (subst hKx)+ apply (subst hK'y)+
      apply (subst add_0)
      apply (rule aux_arithmetic_lemma_001[OF alphar_grows_one_by_one[OF \<rho>_gt_0, of "rankr rkl y"]])
      apply (subst Suc_eq_plus1)+
      apply (subst add_0_right[symmetric, of "(\<alpha>\<^sub>r (rankr rkl y) + 1) * (rankr rkl y + 1 + 1)"])
      apply (rule aux_arithmetic_lemma_02)
      unfolding alphar_def[OF \<rho>_gt_0] by simp
  qed

  have f1: "finite ({0..<length l} - {x,y})" by blast
  have f2: "finite {x,y}" by blast
  have disj: "({0..<length l} - {x, y}) \<inter> {x, y} = {}" by blast
  have sep: "{0..<length l} = ({0..<length l} - {x,y}) \<union> {x,y}" using assms(3,4) by fastforce
  { fix f::"nat\<Rightarrow>nat" have  "(sum f {x, y}) = (f x) + (f y)" using assms(2) by auto}note split=this
  show ?thesis apply (subst \<Phi>_simp)+ apply (subst leq) apply (subst sep) apply (subst (2) sep)
    apply (subst sum.union_disjoint[OF f1 f2 disj])+ apply (subst split)+
    using part1 partxy by linarith
qed


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

section\<open>Abstract definition of iterated path compression (UnionFind05IteratedCompression)\<close>

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
| BWIPCStep: "(x,y)\<in>(ufa_\<beta>_start l) \<Longrightarrow> bw_ipc l y i l' \<Longrightarrow> bw_ipc l x (Suc i) (l'[x:= rep_of l x])"

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

lemma ipc_defined_preliminary:
  assumes "ufa_invar l" "(x,r)\<in>(ufa_\<beta>_start l)\<^sup>*" "r=l!r"
  shows "\<exists> i l'. bw_ipc l x i l'"
  using assms(2,1,3) proof (induction rule: converse_rtrancl_induct)
  case base
  then show ?case using BWIPCBase by blast
next
  case (step y z)
  obtain i a where sg: "bw_ipc l z i a" using step by blast
  show ?case using BWIPCStep[OF step(1) sg] by blast
qed


lemma ipc_defined:
  assumes "ufa_invar l" "x<length l"
  shows "\<exists> i l'. bw_ipc l x i l'"
proof -
  have sg1: "(x,rep_of l x)\<in> (ufa_\<beta>_start l)\<^sup>*" unfolding ufa_\<beta>_def using assms rep_of_ufa_\<beta>_refl by blast
  have "rep_of l x = l!rep_of l x" by (simp add: assms rep_of_min)
  thus ?thesis  using sg1 ipc_defined_preliminary[OF assms(1)] by blast
qed



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



lemma compress_preserves_roots_other_than_x:
  assumes "r\<noteq>x" "r=l!r"
  shows "r=l[x:=z]!r"
  using assms by simp

lemma compress_preserves_paths_converse:
  assumes "(x,y)\<in>(ufa_\<beta>_start l)" "(y,z)\<in> (ufa_\<beta>_start l)\<^sup>*" 
          "(u,w)\<in> (ufa_\<beta>_start (l[x:=z]))\<^sup>*"
        shows "(u,w)\<in> (ufa_\<beta>_start l)\<^sup>*"
  using assms(3) thm converse_rtrancl_induct
proof (induction rule: converse_rtrancl_induct)
  case (step a b)
  show ?case 
  proof(cases "a=x")
    case True 
    with step(1) have bz: "b=z" unfolding ufa_\<beta>_start_def by auto
    from assms(1,2) have way: "(x, z) \<in> (ufa_\<beta>_start l)\<^sup>*"
      by simp
    from True bz way show ?thesis using step(3) by simp
  next
    case False
    then have "(a, b) \<in> ufa_\<beta>_start l" 
      using step(1) unfolding ufa_\<beta>_start_def by auto
    then show ?thesis 
      by (rule converse_rtrancl_into_rtrancl[OF _ step(3)])
  qed
qed blast

lemma compress_preserves_paths_weak:
  assumes "(y,r)\<in> (ufa_\<beta>_start l)\<^sup>*" "(y,x)\<notin> (ufa_\<beta>_start l)\<^sup>*"
  shows "(y,r)\<in>(ufa_\<beta>_start (l[x:=z]))\<^sup>*"
  using assms proof induction
  case base
  then show ?case by blast
next
  case (step y z)
  show ?case apply rule 
    using  step(3)[OF step(4)] apply blast
    using step using compress_preserves_other_edges by fast
qed

lemma compress_preserves_paths_weak_converse:
  assumes "(y,r)\<in>(ufa_\<beta>_start (l[x:=z]))\<^sup>*" "(y,x)\<notin>(ufa_\<beta>_start l)\<^sup>*"
  shows "(y,r)\<in>(ufa_\<beta>_start l)\<^sup>*"
  using assms proof induction
  case base
  then show ?case by blast
next
  case (step z0 z1)
  hence "z0\<noteq>x" by blast
  then show ?case using compress_preserves_other_edges_converse[OF step(2) \<open>z0\<noteq>x\<close>] step 
    by fastforce
qed


lemma compress_changes_parent_of_x_to_z:
  assumes "x<length l"  
  shows "(l[x:= rep_of l x])!x = rep_of l x"
  using assms by auto

lemma compress_preserves_roots_converse:
  assumes "ufa_invar l" "r = (l[x:= rep_of l x])!r"
  shows "r = l!r"
  using assms
  by (metis \<open>ufa_invar l\<close>  nth_list_update_neq nth_update_invalid
      rep_of_min rep_of_refl ufa_compress_aux(2))

lemma compress_preserves_roots_converse':
  assumes "r = (l[x:=z])!r"  "r\<noteq>x"
  shows "r = l!r"
  using assms by simp



lemma compress_preserves_rep_of_weak_converse:
  assumes "ufa_invar l"  "(y,x)\<notin>(ufa_\<beta>_start l)\<^sup>*" "x<length l" "y<length l" "z<length l"
          "(x,z)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "rep_of (l[x:=z]) y = rep_of l y"
proof -
  have path: "(y, rep_of l y) \<in> (ufa_\<beta>_start l)\<^sup>* " "l ! rep_of l y = rep_of l y" 
    using rep_of_path_iff[OF assms(1) rep_of_bound[OF assms(1,4)] assms(4)] by auto

  have pathcom: "(y, rep_of l y) \<in> (ufa_\<beta>_start (l[x:=z]))\<^sup>* " 
    using compress_preserves_paths_weak[OF path(1) assms(2)] .
  have rootcom: "l[x:=z] ! (rep_of l y) = rep_of l y" 
    using path(2) assms(2,4)  unfolding ufa_\<beta>_start_def 
    by (metis assms(2) compress_preserves_roots_other_than_x path(1))
  
  show ?thesis using rep_of_path_iff assms pathcom rootcom path 
      ufa_compress_generalized[OF _ _ _ assms(6)] rep_of_bound  by force    
qed



lemma compress_preserves_is_repr_weak_1:
  assumes "ufa_invar l" "x < length l" "y<length l" "z<length l" "(y,x)\<notin> (ufa_\<beta>_start l)\<^sup>*" 
          "is_repr l y r"
  shows "is_repr (l[x:=z]) y r"
proof -
  have "y\<noteq>x" using assms unfolding ufa_\<beta>_start_def by blast
  show ?thesis using assms(6,1-5) \<open>y\<noteq>x\<close> proof induction
    case (root l i)
    then show ?case by (auto intro: is_repr.intros)
  next
    case (child l i j)
    then show ?case 
      by (smt compress_preserves_paths_weak is_repr_pathI nth_list_update_neq rep_of_idx 
          rep_of_is_repr rep_of_min rep_of_ufa_\<beta>_refl)
  qed
qed


lemma compress_preserves_is_repr_weak_2:
  assumes "ufa_invar l" "x < length l" "y<length l" "z<length l" "(y,x)\<notin> (ufa_\<beta>_start l)\<^sup>*" 
          "is_repr (l[x:=z]) y r"
        shows "is_repr l y r"
proof -
  have sg0: "y\<noteq>x" using assms unfolding ufa_\<beta>_start_def by blast
  have sg1: "x<length (l[x:=z])" "y< length (l[x:=z])" "z<length (l[x:=z])"
    unfolding length_list_update
    using assms by auto
  have sg2: "(y,x) \<notin> (ufa_\<beta>_start (l[x:=z]))\<^sup>*" 
    using assms(5) compress_preserves_paths_weak_converse by blast
  obtain lc where abstr: "lc = l[x:=z]" by blast
  have sg3: "l[x:=z] = lc" unfolding abstr ..
  show ?thesis using assms(6) sg1 sg2 sg3 sg0 proof induction
    case (root l i)
    then show ?case unfolding abstr by (auto intro: is_repr.intros)
  next
    case (child l' i j)
    hence "l'!i < length l'" unfolding abstr by (auto simp add: assms(1) ufa_invarD(2)) 
    from child(6) have "(l' ! i, x) \<notin> (ufa_\<beta>_start l')\<^sup>*" unfolding ufa_\<beta>_start_def 
      by (metis (mono_tags, lifting) \<open>l' ! i < length l'\<close> child.prems(2)
          converse_rtrancl_into_rtrancl mem_Collect_eq old.prod.case)
    hence "l'!i\<noteq>x" by blast
    from child have "l'!i = l!i" unfolding abstr by (metis nth_list_update_neq)
    then show ?case unfolding abstr 
      using child(2)[OF \<open>x<length l'\<close> \<open>l'!i<length l'\<close> \<open>z<length l'\<close> 
                    \<open>(l' ! i, x) \<notin> (ufa_\<beta>_start l')\<^sup>*\<close> \<open>l'=lc\<close> \<open>l'!i\<noteq>x\<close>]
         by (auto simp: \<open>l'!i = l!i\<close> intro: is_repr.intros(2))
  qed 
qed

lemma compress_preserves_rep_of_weak:
  assumes "ufa_invar l" "x < length l" "y<length l" "z<length l" "(y,x)\<notin> (ufa_\<beta>_start l)\<^sup>*"
  shows "rep_of (l[x:=z]) y = rep_of l y"
  using assms compress_preserves_is_repr_weak_1 rep_of_is_repr ufa_invar_def by force


lemma fw_ipc_compress_preliminary:
  assumes "fw_ipc l y i l'" "(y,x)\<notin> (ufa_\<beta>_start l)\<^sup>*" "ufa_invar l" "x<length l" "z<length l" 
  shows "fw_ipc (l[x := z]) y i (l'[x := z])"
  using assms proof (induction l y i l' rule: fw_ipc.induct)
  case base: (FWIPCBase y0 l)
  show ?case apply (rule FWIPCBase)
    apply (rule compress_preserves_roots_other_than_x[OF _ base(1), of x z])
    using base.prems(1) by blast
next
  case step: (FWIPCStep y z' l i l')
  have sg1': "z'<length l" using step unfolding ufa_\<beta>_start_def by blast
  have sg1: "(z', rep_of l z') \<in> (ufa_\<beta>_start l)\<^sup>*" using 
      rep_of_path_iff[OF \<open>ufa_invar l\<close> rep_of_bound[OF \<open>ufa_invar l\<close> \<open>z'<length l\<close>] \<open>z'<length l\<close>] 
    by blast
  have sg2: "(y, z') \<in> ufa_\<beta>_start (l[x:=z])" using step 
    by (metis compress_preserves_other_edges rtrancl.simps)
  have sg3': "z'<length l" using step(1) unfolding ufa_\<beta>_start_def by blast
  have sg3'': "(z', x) \<notin> (ufa_\<beta>_start l)\<^sup>*" using step(1,4) 
    by (meson converse_rtrancl_into_rtrancl)
  have sg3: "rep_of (l[x := z]) z' = rep_of l z' " 
    using compress_preserves_rep_of_weak[OF \<open>ufa_invar l\<close> \<open>x<length l\<close>  sg3' \<open>z<length l\<close> sg3'' ] .
  have IHfw_ipc: "fw_ipc (l[y := rep_of l z', x := z]) z' i (l'[x := z])" 
    apply (rule step(3))
    subgoal apply (rule ccontr)
      using compress_preserves_paths_converse[OF step(1) sg1, of z' x] step(4)
      by (meson converse_rtrancl_into_rtrancl step.hyps(1))
    subgoal using rep_of_idx step assms ufa_compress_invar unfolding ufa_\<beta>_start_def 
      by force 
    subgoal using step(6) unfolding ufa_\<beta>_start_def length_list_update using step.prems(3) by blast
    subgoal using step(7) unfolding ufa_\<beta>_start_def length_list_update using step.prems(4) by blast   
    done
  show ?case 
    apply (rule FWIPCStep)
     apply (rule sg2)
    apply (subst sg3)
    using IHfw_ipc 
    by (metis list_update_swap rtrancl.simps step.prems(1))
qed


lemma fw_ipc_compress:
  assumes "ufa_invar l" "(x,y)\<in>(ufa_\<beta>_start l)" "fw_ipc l y i l'"
  shows "fw_ipc (l[x := rep_of l y]) y i (l'[x := rep_of l y])"
proof -
  have sg1: "rep_of l x = rep_of l y" using assms
    using rep_of_idx ufa_\<beta>_start_def by auto 
  have "(y,rep_of l y) \<in> (ufa_\<beta>_start l)\<^sup>*" using assms rep_of_path_iff[OF assms(1)]
      assms(2) rep_of_bound[OF assms(1)] unfolding ufa_\<beta>_start_def by blast
  with sg1 have sg2: "(x,rep_of l y) \<in> (ufa_\<beta>_start l)\<^sup>*" using assms rep_of_path_iff[OF assms(1)]
      assms(2) rep_of_bound[OF assms(1)] unfolding ufa_\<beta>_start_def by blast
  show ?thesis
    apply (rule fw_ipc_compress_preliminary[OF assms(3) _ assms(1), of x "rep_of l y"])
    using assms(2) acyclicity[OF assms(1)] unfolding ufa_\<beta>_def ufa_\<beta>_start_def
      apply (metis (no_types, lifting) mem_Collect_eq old.prod.case rtrancl_into_trancl1)
    using assms(1,2) rep_of_bound sg2 unfolding ufa_\<beta>_start_def 
    by auto
qed

lemma bw_ipc_fw_ipc:
  assumes "ufa_invar l" "bw_ipc l x i l'" 
  shows "fw_ipc l x i l'"
  using assms(2,1) proof induction
  case base: (BWIPCBase x l)
  show ?case using FWIPCBase[OF base(1)] .
next
  case step: (BWIPCStep x y l i l')
  have sg1: "rep_of l x = rep_of l y" using step(1) rep_of_idx[OF step.prems]
    unfolding ufa_\<beta>_start_def by force
  show ?case      
    apply (rule FWIPCStep[OF step(1)])
    using 
      fw_ipc_compress[OF step(4) step(1) step(3)[OF step(4)]] sg1 by argo
qed


lemma bw_ipc_compress_preliminary:
  assumes "ufa_invar l" "bw_ipc lxz y i lxz'"  "(y,x)\<notin> (ufa_\<beta>_start l)\<^sup>*" "lxz = (l[x:=z])" 
          "x<length l" "z<length l" "(x,z)\<in>(ufa_\<beta>_start l)\<^sup>*"
  shows "\<exists>l'. lxz' = l'[x:=z] \<and> bw_ipc l y i l'"
  using assms(2,1,3,4) proof (induction)
  case base: (BWIPCBase x l')
  show ?case apply (rule exI[where x = l]) using base BWIPCBase
    by (metis nth_list_update_neq rtrancl.simps)
next
  case step: (BWIPCStep x0 y0 l' i l'')
  have h2: "x\<noteq>x0" using step(5) by blast
  hence h3: "(x0, y0) \<in> ufa_\<beta>_start l'" using compress_preserves_other_edges_converse step by fast
  have sg: "\<exists>l'. l'' = l'[x := z] \<and> bw_ipc l y0 i l'" 
    apply (rule step(3)[OF assms(1) _ \<open>l'=l[x:=z]\<close>]) using compress_preserves_paths_converse step 
    by (metis (no_types, lifting) converse_rtrancl_into_rtrancl h2 length_list_update 
        mem_Collect_eq nth_list_update_neq prod.simps(2) ufa_\<beta>_start_def)
  obtain l'0 where IH': "l'' = l'0[x := z]" "bw_ipc l y0 i l'0" using sg by blast
  have "x0<length l" using h3 unfolding ufa_\<beta>_start_def step by auto
  have sg1: "rep_of l' x0 = rep_of l x0" apply (subst \<open>l' = l[x := z]\<close>) 
    using compress_preserves_rep_of_weak_converse
          [OF assms(1) step(5) \<open>x<length l\<close> \<open>x0<length l\<close> \<open>z<length l\<close> assms(7)] .
  have sg2': "(x0, y0) \<in> (ufa_\<beta>_start (l[x := z]))\<^sup>*" using step by blast
  have sg2: "(x0, y0) \<in> (ufa_\<beta>_start l)" using step 
          compress_preserves_other_edges_converse by blast
  show ?case                                           
    apply (subst IH'(1))
    apply (rule exI[where x = "l'0[x0 := rep_of l' x0]"])
    apply safe using list_update_swap[OF h2] apply fast
    apply (subst sg1)
    using BWIPCStep[of x0 y0 l i l'0, OF sg2 IH'(2)] .
qed

lemma bw_ipc_compress:
  assumes "ufa_invar l" "(x,y)\<in>(ufa_\<beta>_start l)" "z = rep_of l y" "bw_ipc (l[x:=z]) y i l''"
  shows "\<exists>l'. l'' = l'[x:=z] \<and> bw_ipc l y i l'"
proof -
  have "x<length l" using assms(2) unfolding ufa_\<beta>_start_def by blast
  have "z<length l" using rep_of_bound assms unfolding ufa_\<beta>_start_def by blast
  have sg1: "(x,z)\<in>(ufa_\<beta>_start l)\<^sup>*"  
    using assms(1-3) rep_of_idx rep_of_ufa_\<beta>_refl unfolding ufa_\<beta>_start_def by force
  show ?thesis  
    using assms bw_ipc_compress_preliminary[OF assms(1) _ _ _ \<open>x<length l\<close> \<open>z<length l\<close> sg1]
  by (metis (mono_tags, lifting) acyclicity case_prodD mem_Collect_eq
      rtrancl_into_trancl2 ufa_\<beta>_def ufa_\<beta>_start_def)
qed


lemma fw_ipc_bw_ipc:
  assumes "ufa_invar l" "fw_ipc l x i l'"
  shows "bw_ipc l x i l'" 
  using assms(2,1) proof induction
case base: (FWIPCBase x l)
  then show ?case using BWIPCBase by blast
next
  case step: (FWIPCStep x y l i l')
  have sg1: "ufa_invar (l[x := rep_of l y])" using \<open>ufa_invar l\<close> 
    using rep_of_idx step.hyps(1) ufa_\<beta>_start_def ufa_compress_invar by auto
  note h4 = bw_ipc_compress[OF \<open>ufa_invar l\<close> step(1) refl  step(3)[OF sg1]]
  with step show ?case using BWIPCStep rep_of_idx unfolding ufa_\<beta>_start_def by auto
qed



\<comment>\<open>One probably needs the lemmas of this file (equivalence of the two, properties about
  single step compressions and the predicates) to proceed. But without developing the proofs,
  the concrete required formulation is not yet clear.\<close>
  



section\<open>Lemmas about pleasantness (UnionFind24Pleasant)\<close>

\<comment>\<open> This section defines the notion of ``pleasantness'' -- the property of having
   a proper non-root ancestor with the same level -- and establishes several
   lemmas which establish an upper bound on the number of unpleasant vertices. \<close>

\<comment>\<open> This reasoning is usually not explicitly carried out on paper, yet it is
   quite lengthy and painful here. \<close>

\<comment>\<open> We parametrize these definitions and lemmas over a predicate ok and a
   level function, so that they work both for Tarjan's original proof and
   for Alstrup et al.'s proof. \<close>

\<comment>\<open>ok will be top_part and level will be level\<close>

locale Pleasant = \<comment>\<open>Pleasant\<close>
  fixes ok::"nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
    and level::"nat list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat" 
begin

context
  fixes l::"nat list"  and rkl::"nat list"
begin

definition pleasant where "pleasant x \<equiv> ok l rkl x \<and> x\<noteq>l!x 
    \<and> (\<exists>y. y\<noteq>l!y \<and> ((l!x),y) \<in> (ufa_\<beta>_start l)\<^sup>* \<and> (level l rkl x = level l rkl y) )"


definition unpleasant_ancestors where "unpleasant_ancestors x \<equiv> 
                                       (ancestors l x) \<inter> {y. (\<not>pleasant y) \<and> y\<noteq>l!y}"

definition displeasure where "displeasure x \<equiv> card (unpleasant_ancestors x)"


context \<comment>\<open>FK\<close>
 
assumes contextasm: "invar_rank l rkl" 
begin


\<comment>\<open> A non-root vertex @{term x} is pleasant if it is OK and if it has a proper non-root
   ancestor @{term y} such that @{term x} and @{term y} have the same level, 
   i.e., @{term "level l rkl x = level l rkl y"}. \<close>

lemma pleasant_non_root:
  assumes "pleasant x" shows "x\<noteq>l!x"
  using assms unfolding pleasant_def by fast

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
    by (metis (no_types, lifting) acyclicity case_prodD contextasm invar_rank_def
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
    and level_bounded: "ok l rkl x \<Longrightarrow> x<length l \<Longrightarrow>  x\<noteq>l!x \<Longrightarrow> (level l rkl x) < bound "

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
  assumes "ok l rkl x" "x<length l"
  shows "levels x \<le> bound"
proof -
  have *: "xa \<in> ancestors l x \<Longrightarrow> xa \<noteq> l ! xa \<Longrightarrow> level l rkl xa < bound" for xa
  proof goal_cases
    case 1
    have "xa<length l" using 1(1) ancestors_in_domain[OF assms(2)] by auto
    show ?case
      apply (rule level_bounded[OF _ \<open>xa<length l\<close> 1(2)])
      using 1 assms hereditary_property[OF ok_hereditary] by fast
  qed  
  have "levels x \<le> card {0..<bound}"
    unfolding levels_def
    apply (rule card_mono)  
    using * by (auto simp: subset_iff)     
  then show ?thesis by simp
qed
  

lemma levels_parent_if_pleasant:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)"
  shows "levels y \<le> levels x"
  unfolding levels_def
  apply (rule card_mono)
proof goal_cases
  case 1
  have "x<length l" using assms unfolding ufa_\<beta>_start_def by blast
  then show ?case using ancestors_in_domain[OF \<open>x<length l\<close>]
    using subset_eq_atLeast0_lessThan_finite by blast
next
  case 2
  then show ?case apply (rule image_mono) apply (rule Int_mono)
    using ancestors_of_parent_inclusion[OF assms] by auto
qed


lemma levels_parent_if_unpleasant:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)" "\<not>pleasant x" "ok l rkl x"
  shows "Suc (levels y) \<le> levels x"
proof -
  have "x<length l" "y<length l" using assms(1) unfolding ufa_\<beta>_start_def by blast+
  have fn: "finite (level l rkl ` (ancestors l y \<inter> {y. y \<noteq> l ! y}))"
    apply (rule finite_imageI)  using ancestors_in_domain[OF \<open>y<length l\<close>]
      subset_eq_atLeast0_lessThan_finite finite_Int by blast
  have fn': "finite (level l rkl ` (ancestors l x \<inter> {y. y \<noteq> l ! y}))"
    apply (rule finite_imageI)  using ancestors_in_domain[OF \<open>x<length l\<close>]
      subset_eq_atLeast0_lessThan_finite finite_Int by blast
  have sg: "level l rkl x \<notin> level l rkl ` ((ancestors l y) \<inter> {y. y\<noteq>l!y})"
    unfolding ancestors_def image_def 
  proof 
    assume limage: " level l rkl x \<in> {ya. \<exists>x\<in>{j. (y, j) \<in> (ufa_\<beta>_start l)\<^sup>*} \<inter> {y. y \<noteq> l ! y}.
                                      ya = level l rkl x}"
    obtain xa where hyps: "level l rkl x = level l rkl xa"
      "(y, xa) \<in> (ufa_\<beta>_start l)\<^sup>*" "xa \<noteq> l ! xa" using limage by auto
    show "False"    
      using assms hyps by(force simp: pleasant_def ufa_\<beta>_start_def)
  qed
  have subs: "{x} \<subseteq> {y. y\<noteq>l!y}" using assms(1) unfolding ufa_\<beta>_start_def by fast
  {
    fix A::"'a set" and B::"'a set"  and C
    assume "B \<subseteq> C"
    have "(A \<union> B) \<inter> C = A \<inter> C \<union> B" using \<open>B\<subseteq>C\<close> by blast
  } note inter_subs = this
  show ?thesis unfolding levels_def 
    apply (subst card_insert_disjoint[symmetric])
      apply (rule fn)
     apply (rule sg) 
    apply (rule card_mono[OF fn']) 
    apply (subst ancestors_of_parent[OF assms(1)])
    apply (subst inter_subs[OF subs]) by blast
qed


lemma bounded_displeasure_preliminary_1:
  assumes "(x,z)\<in> (ufa_\<beta>_start l)\<^sup>*" "z=l!z" "ok l rkl x" "x<length l"
  shows "displeasure x \<le> levels x"
  using assms
proof (induction rule: converse_rtrancl_induct)
  case base
  show ?case using displeasure_of_root[OF base(1)] by auto
next
  case (step x y)
  have yl: "y<length l" using step(1) unfolding ufa_\<beta>_start_def by blast
  have oky: "ok l rkl y" using ok_hereditary[OF step(5,1)] .
  show ?case
  proof (cases "pleasant x")
    case True
    have hd: "displeasure x \<le> displeasure y" 
      using displeasure_parent_if_pleasant[OF step(1) True] by simp
    have hc: "levels y \<le> levels x"
      using levels_parent_if_pleasant[OF step(1)] .
    show ?thesis using hd hc step(3)[OF step(4) oky yl] by linarith
  next
    case False
    have hd: "displeasure x \<le> Suc (displeasure y)" 
      using displeasure_parent_if_unpleasant[OF step(1) False] by simp
    have hc: "Suc (levels y) \<le> levels x" 
      using levels_parent_if_unpleasant[OF step(1) False step(5)] .
    show ?thesis using hd hc step(3)[OF step(4) oky yl] by linarith
  qed
qed

lemma bounded_displeasure_preliminary_2:
  assumes "ok l rkl x" "x<length l"
  shows "displeasure x \<le> bound"
proof -
  note path = path_from_parent_to_rep_of[OF invar_rank_ufa_invarI[OF contextasm] assms(2) refl] 
              rep_of_min[OF invar_rank_ufa_invarI[OF contextasm] assms(2), symmetric]
  show ?thesis using bounded_displeasure_preliminary_1[OF path assms] bounded_levels[OF assms]
    by simp
qed

end
end \<comment>\<open>Until here the assumptions about ok and level\<close>

end \<comment>\<open>FK\<close>

context \<comment>\<open>Preservation\<close>
  assumes compress_preserves_level_above_y:
    "\<lbrakk>invar_rank l rkl; (x,y)\<in> (ufa_\<beta>_start l); (y,z)\<in> (ufa_\<beta>_start l)\<^sup>* ; 
     (y,v)\<in> (ufa_\<beta>_start l)\<^sup>*; v\<noteq>l!v\<rbrakk> 
        \<Longrightarrow> level (l[x:= z]) rkl v = level l rkl v"
 and compress_preserves_ok_above_y:
    "\<lbrakk>invar_rank l rkl; (x,y)\<in> (ufa_\<beta>_start l); (y,z)\<in> (ufa_\<beta>_start l)\<^sup>*; 
      (y,v)\<in> (ufa_\<beta>_start l)\<^sup>*; v\<noteq>l!v; ok l rkl v \<rbrakk> 
        \<Longrightarrow> ok (l[x:= z]) rkl v"
begin



lemma compress_preserves_pleasant_above_y:
  assumes "invar_rank l rkl"
          "(x,y)\<in> (ufa_\<beta>_start l)" "(y,z)\<in> (ufa_\<beta>_start l)\<^sup>*" "(y,v)\<in> (ufa_\<beta>_start l)\<^sup>*" 
          "pleasant l rkl v"
  shows "pleasant (l[x:= z]) rkl v"
proof -
  have "x<length l" "y<length l" using assms(2) unfolding ufa_\<beta>_start_def by auto
  have "v<length l" using assms(4) \<open>y<length l\<close> unfolding ufa_\<beta>_start_def by induction auto
  have "z<length l" using assms(3) \<open>y<length l\<close> unfolding ufa_\<beta>_start_def by induction auto
  obtain av where asm: "ok l rkl v" " v \<noteq> l ! v" 
    " av \<noteq> l ! av" "(l ! v, av) \<in> (ufa_\<beta>_start l)\<^sup>* "
    "level l rkl v = level l rkl av" using assms(5) unfolding pleasant_def
    by blast

  have "x\<noteq>v" using  paths_have_distinct_endpoints[OF invar_rank_ufa_invarI[OF assms(1)] 
        \<open>x<length l\<close> \<open>v<length l\<close>] 
    by (metis assms(2,4) rtrancl_into_trancl2 ufa_\<beta>_def)

  have "(y,l!v)\<in>(ufa_\<beta>_start l)\<^sup>*" 
    using \<open>v<length l\<close> rep_of_bound invar_rank_ufa_invarI[OF assms(1)] assms(4)
    unfolding ufa_\<beta>_start_def
    by (metis (mono_tags, lifting) asm(2) case_prodI mem_Collect_eq rtrancl.simps ufa_invarD(2))

  show ?thesis unfolding pleasant_def 
    apply safe
    subgoal using compress_preserves_ok_above_y assms asm by blast
    subgoal using compress_preserves_roots_converse by (simp add: \<open>x \<noteq> v\<close> asm(2))
    subgoal
      apply (rule exI[where x = av])
      apply safe
      subgoal using compress_preserves_roots_converse 
        by (metis \<open>x < length l\<close> acyclicity asm(3) assms(2,3) invar_rank_ufa_invarI[OF assms(1)]
            nth_list_update_eq nth_list_update_neq rtrancl_into_trancl2 ufa_\<beta>_def)
      subgoal apply (rule compress_preserves_paths_out_of_y') 
        using assms  apply blast
           apply (rule invar_rank_ufa_invarI[OF assms(1)])
          apply (simp add: \<open>x \<noteq> v\<close> asm(4))
         apply (simp add: \<open>(y, l ! v) \<in> (ufa_\<beta>_start l)\<^sup>*\<close> \<open>x \<noteq> v\<close>)
        apply (rule assms(3))
        done
      subgoal 
        using compress_preserves_level_above_y assms asm 
        by (smt \<open>(y, l ! v) \<in> (ufa_\<beta>_start l)\<^sup>*\<close> rtrancl_trans)
      done
    done
qed



lemma compress_preserves_displeasure_of_y_preliminary:
  assumes "invar_rank l rkl" "(x,y) \<in> (ufa_\<beta>_start l)" "(y,z) \<in> (ufa_\<beta>_start l)\<^sup>*"
  shows "displeasure (l[x:= z]) rkl y \<le> displeasure l rkl y "
proof -
  have "x<length l" "y<length l" using assms unfolding ufa_\<beta>_start_def by auto
  show ?thesis
    unfolding displeasure_def
              unpleasant_ancestors_def
  proof (rule card_mono, goal_cases)
    case 1
    then show ?case
      apply (rule finite_Int)
      using subset_eq_atLeast0_lessThan_finite[OF ancestors_in_domain[OF \<open>y<length l\<close>]]
      by blast
  next
    case 2
    then show ?case
    proof (rule, goal_cases)
      case (1 x')
      have prems1: "(y, x') \<in> (ufa_\<beta>_start (l[x := z]))\<^sup>*" using 1 unfolding ancestors_def by blast
      have prems2: " \<not> pleasant (l[x := z]) rkl x'" " x' \<noteq> (l[x := z]) ! x'" using 1 
        unfolding ancestors_def by blast+
      have sg1: "(y, x') \<in> (ufa_\<beta>_start l)\<^sup>*" using prems1 
          compress_preserves_paths_converse[OF _ _ prems1] assms(2,3) by blast
      have sg2: "\<not> pleasant l rkl x'"  
        using compress_preserves_pleasant_above_y[OF assms(1,2,3)] sg1 prems2 by blast
      have sg3: "x' \<noteq> l!x'" using prems2(2) assms 
        by (metis \<open>x < length l\<close> acyclicity assms(1) invar_rank_ufa_invarI nth_list_update_neq 
            rtrancl_into_trancl2 sg1 ufa_\<beta>_def)
      show ?case using sg1 sg2 sg3 unfolding ancestors_def by blast
    qed
  qed
qed
        


lemma compress_preserves_displeasure_of_y:
  assumes "invar_rank l rkl" "(x,y) \<in> (ufa_\<beta>_start l)" 
  shows "displeasure (l[x:= rep_of l y]) rkl y \<le> displeasure l rkl y "
proof -
  have "x<length l" "y<length l" using assms unfolding ufa_\<beta>_start_def by auto
  show ?thesis
  using compress_preserves_displeasure_of_y_preliminary[OF assms(1,2)]
    rep_of_path_iff[OF invar_rank_ufa_invarI[OF assms(1)] 
      rep_of_bound[OF  invar_rank_ufa_invarI[OF assms(1)] \<open>y<length l\<close>] \<open>y<length l\<close> ]
  by blast
qed

 
end \<comment>\<open>Preservation\<close>

end \<comment>\<open>Pleasant\<close>


\<comment>\<open>The predicate top_part corresponds to the "top part of the path"
   mentioned in the proof of Lemma 4.11.\<close>
definition top_part where "top_part l rkl x \<equiv> \<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (rep_of l x))"

definition top_part' where "top_part' z l rkl x \<equiv> (rep_of l x = z) \<and> 
                                                  (\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (rep_of l x)))"

lemma top_part_alt:
  "top_part l rkl x = top_part' (rep_of l x) l rkl x"
  unfolding top_part_def top_part'_def by blast

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
  have "y<length l" using assms(2) unfolding ufa_\<beta>_start_def by blast
  have h2: "(x,y)\<in>(ufa_\<beta>_start l)\<^sup>*" using assms(2) by blast
  have h3: "(y, rep_of l x) \<in> (ufa_\<beta>_start l)\<^sup>*" 
    using rep_of_ufa_\<beta>_refl[OF \<open>ufa_invar l\<close> \<open>x<length l\<close>] assms(2) 
    by (smt \<open>ufa_invar l\<close> case_prodD mem_Collect_eq rep_of_bound rep_of_idx 
        rep_of_path_iff ufa_\<beta>_start_def)
  hence "rep_of l x < length l"  by (simp add: \<open>ufa_invar l\<close> \<open>x < length l\<close> rep_of_bound)
  have h4: "rep_of l x = rep_of l y" using assms \<open>ufa_invar l\<close> rep_of_idx 
    unfolding ufa_\<beta>_start_def by force
  show ?thesis unfolding top_part_def using assms(1) h4
        \<alpha>\<^sub>r_rankr_grows_along_a_path_refl[OF contextasm \<open>y<length l\<close> \<open>rep_of l x < length l\<close> h3]
        \<alpha>\<^sub>r_rankr_grows_along_a_path_refl[OF contextasm \<open>x<length l\<close> \<open>y<length l\<close> h2]
      unfolding top_part_def by simp
  qed
  

lemma compress_preserves_top_part_above_y:
  assumes "(x,y)\<in> (ufa_\<beta>_start l)" "(y,z)\<in> (ufa_\<beta>_start l)\<^sup>*" "v<length l" "top_part' z' l rkl v"
  shows "top_part' z' (l[x:=z]) rkl v"
proof -
  have "x<length l" "y<length l" using assms unfolding ufa_\<beta>_start_def by auto
  have "z<length l" using assms(2) \<open>y<length l\<close> unfolding ufa_\<beta>_start_def by induction auto
  have sg0: "(x,z)\<in>(ufa_\<beta>_start l)\<^sup>*"  using assms(1,2) by simp
  have sg1: "rep_of l v = z'" using assms  unfolding top_part'_def by blast
  show ?thesis unfolding top_part'_def
    apply safe
    subgoal 
      using compress_preserves_rep_of_direct'[OF _ invar_rank_ufa_invarI[OF contextasm] _]
        ufa_compress_generalized[OF invar_rank_ufa_invarI[OF contextasm] 
                                 \<open>x<length l\<close> \<open>z<length l\<close> sg0]
        assms sg1 
      by (metis \<open>x < length l\<close>  contextasm invar_rank_ufa_invarI 
          length_list_update list_update_overwrite  ufa_compress_aux(2))
    using \<open>rep_of (l[x := z]) v = z'\<close> assms(4) top_part'_def by auto
qed

lemma compress_preserves_top_part_above_y':
  assumes "(x,y)\<in> (ufa_\<beta>_start l)" "(y,z)\<in> (ufa_\<beta>_start l)\<^sup>*" "v<length l" "top_part' z l rkl v"
  shows "top_part' z (l[x:=z]) rkl v"
  using assms compress_preserves_top_part_above_y by blast


lemma compress_preserves_top_part_above_y'':
  assumes "(x,y)\<in> (ufa_\<beta>_start l)"   "(y,z)\<in> (ufa_\<beta>_start l)\<^sup>*" "v<length l" "top_part l rkl v"
  shows "top_part (l[x:=z]) rkl v"
proof -
  have "x<length l" "y<length l" using assms unfolding ufa_\<beta>_start_def by auto
  hence sg1: "(y,rep_of l y)\<in> (ufa_\<beta>_start l)\<^sup>*" 
    using rep_of_path_iff[OF invar_rank_ufa_invarI[OF contextasm]]
          rep_of_bound[OF invar_rank_ufa_invarI[OF contextasm] \<open>y<length l\<close>]
    by blast
  show ?thesis using compress_preserves_top_part_above_y'[OF assms(1,2) \<open>v<length l\<close>] assms(4)
    unfolding top_part'_def top_part_def 
    using assms(1) assms(2) assms(3) compress_preserves_top_part_above_y top_part'_def by blast
qed

end \<comment>\<open>invar_rank\<close>





context \<comment>\<open>invar_rank\<close>
  fixes l::"nat list" and rkl::"nat list" and x::nat
  assumes contextasm: "invar_rank l rkl"
begin

interpretation pl: Pleasant "top_part' (rep_of l x)" level .

\<comment>\<open>The proof of Lemma 4.11 says this is a strict inequality. This is
   true. Here, we do not exploit the fact that a level is at least 1,
   which is why we end up establishing a large inequality.\<close>

lemma bounded_displeasure_alstrup:
  assumes "top_part l rkl x" "x<length l"
  shows "pl.displeasure l rkl x \<le> \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
proof (rule pl.bounded_displeasure_preliminary_2[OF contextasm ], goal_cases)
  case (1 x' y)

  hence eq1: "rep_of l x' = rep_of l x" unfolding top_part'_def by blast
  have eq: "rep_of l x' = rep_of l y" using 1 unfolding ufa_\<beta>_start_def
    using invar_rank_ufa_invarI[OF contextasm] rep_of_idx  by auto
  show ?case  apply (subst eq1[symmetric]) apply (subst eq) apply (subst top_part_alt[symmetric])
    using top_part_hereditary[OF contextasm] 1 
    apply (subst (asm) eq1[symmetric]) 
    apply (subst (asm) top_part_alt[symmetric])
    by blast
next
  case (2 y)
  hence "l!y < length l" using  invar_rank_ufa_invarI[OF contextasm] ufa_invarD(2) by blast
  hence py: "(y,l!y) \<in> ufa_\<beta>_start l" unfolding ufa_\<beta>_start_def using 2 by blast
  have eq: "(rep_of l x) = rep_of l y" using 2 unfolding top_part'_def by auto
  hence eq': "rep_of l (l ! y) = (rep_of l x)" 
    using "2"(2) contextasm invar_rank_ufa_invarI rep_of_idx by auto
  have hrpy: "\<alpha>\<^sub>r (rankr rkl (l ! y)) = \<alpha>\<^sub>r (rankr rkl (rep_of l (l ! y)))" 
    using  top_part_hereditary[OF contextasm _ py] 2(1)  eq top_part_alt 
    unfolding top_part_def by simp
  show ?case
    using hrpy 2(1) assms(1) level_lt_\<alpha>\<^sub>r[OF contextasm 2(2) 2(3)[symmetric]] eq' unfolding top_part_def 
    by argo
qed (auto simp add: assms top_part_alt[symmetric])
end



interpretation pl: Pleasant top_part level .

context \<comment>\<open>invar_rank\<close>
  fixes l::"nat list" and rkl::"nat list" 
  assumes contextasm: "invar_rank l rkl"
begin



\<comment>\<open>During a path compression step at x, the vertex x is the only one whose
   potential changes. So, if the potential of x decreases, then the total
   potential \<Phi> decreases as well.\<close>

lemma from_\<phi>_to_\<Phi>:
  assumes "x\<noteq>l!x" "\<phi> (l[x:= rep_of l x]) rkl x < \<phi> l rkl x"
  shows "\<Phi> (l[x:= rep_of l x]) rkl < \<Phi> l rkl "
proof -
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
    apply (rule add_mono_thms_linordered_field(4))
    using assms(2) conteq sum_mono by blast
qed
    

lemma pleasant_\<phi>:
  assumes "x<length l" "pl.pleasant l rkl x"
  shows "\<phi> (l[x:= rep_of l x]) rkl x < \<phi> l rkl x"
proof -
  have sg1: "top_part l rkl x" "x \<noteq> l ! x"
    "(\<exists>y. y \<noteq> l ! y \<and> (l ! x, y) \<in> (ufa_\<beta>_start l)\<^sup>* \<and> level l rkl x = level l rkl y)" 
    using assms(2) unfolding pl.pleasant_def by blast+
  have hNonRoot: "x \<noteq> l ! x" using sg1(2) .
  have h2: "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (rep_of l x))" using sg1(1) unfolding top_part_def .
  obtain y where 
    h345: "y \<noteq> l ! y" "(l ! x, y) \<in> (ufa_\<beta>_start l)\<^sup>*" "level l rkl x = level l rkl y" 
    using sg1(3) by blast+
  have "y < length l" using h345(2)
    by (metis (no_types, lifting) assms(1) case_prodD contextasm invar_rank_ufa_invarI 
        mem_Collect_eq rtrancl.simps ufa_\<beta>_start_def ufa_invarD(2))
  have h6: "(l!x, rep_of l x)\<in> (ufa_\<beta>_start l)\<^sup>*"  using assms 
    using contextasm invar_rank_ufa_invarI rep_of_bound rep_of_idx rep_of_path_iff ufa_invarD(2) 
    unfolding pl.pleasant_def by auto
  have h7: "\<alpha>\<^sub>r (rankr rkl x) \<le> \<alpha>\<^sub>r (rankr rkl (l!x))"
    using \<alpha>\<^sub>r_rankr_grows_along_edges[OF contextasm assms(1)] using assms(2) 
    unfolding pl.pleasant_def by argo
  have h8: "\<alpha>\<^sub>r (rankr rkl (l!x)) \<le> \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
    using \<alpha>\<^sub>r_rankr_grows_along_a_path_refl[OF contextasm ufa_invarD(2)
        [OF invar_rank_ufa_invarI[OF contextasm] assms(1)]
        rep_of_bound[OF invar_rank_ufa_invarI[OF contextasm] \<open>x<length l\<close>] h6] .
  have h9: "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (l!x))" using h2 h7 h8 by simp
  have hxpx: "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl ((l[x:= rep_of l x])!x))"
    using compress_changes_parent_of_x_to_z[OF assms(1)] h2 by argo
  note h10 = compress_evolution[OF contextasm assms(1) hNonRoot]
  show ?thesis 
    apply (subst \<phi>_case_2[OF hNonRoot[symmetric] h9])
    apply (subst \<phi>_case_2[OF non_root_forever[OF contextasm h10 hNonRoot, symmetric] hxpx])
    apply (rule add_mono1)
  proof (rule lexpo_cannot_increase_and_decreases_if', goal_cases)
    case 1
    then show ?case using index_le_rank[OF contextasm assms(1) hNonRoot[symmetric]] .
  next
    case 2
    then show ?case using \<open>x<length l\<close>
        index_ge_1[OF invar_rank_evolution[OF contextasm h10] _ 
          non_root_forever[OF contextasm h10 hNonRoot, symmetric]] by fastforce
  next
    case 3
    then show ?case using \<open>x<length l\<close>
        index_le_rank[OF invar_rank_evolution[OF contextasm h10] _
          non_root_forever[OF contextasm h10 hNonRoot, symmetric]] by fastforce
  next
    case 4
    then show ?case using level_v_grows[OF contextasm h10 \<open>x<length l\<close> hNonRoot] .
  next
    case 5
    then show ?case apply (subst hxpx) using \<open>x<length l\<close>
        level_lt_\<alpha>\<^sub>r[OF invar_rank_evolution[OF contextasm h10] _ 
          non_root_forever[OF contextasm h10 hNonRoot, symmetric]]
      by fastforce
  next
    case 6
    then show ?case using index_v_grows_if_level_v_constant[OF contextasm h10 \<open>x<length l\<close> hNonRoot]
      by blast
  next
    case 7
    then show ?case apply (rule prove_lexpo_decreases) 
      subgoal using level_v_grows[OF contextasm h10 \<open>x<length l\<close> hNonRoot] .
      subgoal using 
          levelx_levely_compress[OF contextasm \<open>x<length l\<close> \<open>y<length l\<close> hNonRoot h345 refl ]
        by presburger
      done
  qed
qed

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
  unfolding pl.displeasure_def
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
    subgoal
      using step(1) rep_of_ufa_\<beta>_refl[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] \<open>x<length l\<close>]
      by (metis \<open>rep_of l x < length l\<close> \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI 
          r_into_rtrancl rep_of_invar_along_path rep_of_path_iff step.prems(2))
    subgoal using \<open>x < length l\<close> invar_rank_ufa_invarI rep_of_min step.prems by blast
    done

  have step': " (x, y) \<in> ufa_\<beta>_start l" "fw_ipc (l[x := rep_of l x]) y i l'"
            "\<lbrakk>top_part (l[x := rep_of l x]) rkl y; invar_rank (l[x := rep_of l x]) rkl\<rbrakk>
             \<Longrightarrow> \<Phi> l' rkl + i \<le> \<Phi> (l[x := rep_of l x]) rkl +
                                card
            (pl.unpleasant_ancestors (l[x := rep_of l y]) rkl y)" 
                "top_part l rkl x" "invar_rank l rkl" using step 
    by (auto simp add: eq)

  have dpleq: "pl.displeasure (l[x := rep_of l y]) rkl y
      \<le> pl.displeasure l rkl y"  
    apply (rule  pl.compress_preserves_displeasure_of_y[OF _ _ step(5) step'(1)])
  proof goal_cases
    case (1 l rkl x y z v)
    show ?case using compress_preserves_level_above_y[OF 1(1,2) 1(3,4,5)] .
  next
    case (2 l rkl x y z v)
    have "v<length l"  using 2(4) 2 unfolding ufa_\<beta>_start_def by induction auto
    show ?case using compress_preserves_top_part_above_y''[OF 2(1,2,3)  \<open>v<length l\<close> 2(6)] .
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
    have "x<length l" using step'(1) unfolding ufa_\<beta>_start_def by blast
    show ?thesis 
      using pl.displeasure_parent_if_pleasant[OF \<open>invar_rank l rkl\<close> step'(1) True]
      from_\<phi>_to_\<Phi>[OF \<open>invar_rank l rkl\<close> \<open>x\<noteq>l!x\<close> pleasant_\<phi>[OF \<open>invar_rank l rkl\<close> \<open>x<length l\<close> True]]
      IH' True dpleq 
      unfolding pl.displeasure_def
      using eq by linarith
  next
    case False
    show ?thesis unfolding pl.displeasure_def
      using pl.displeasure_parent_if_unpleasant[OF \<open>invar_rank l rkl\<close> step'(1) False]
        arbitrary_\<Phi>[OF \<open>invar_rank l rkl\<close> step'(1)] IH' False dpleq
      unfolding pl.displeasure_def
      using eq by linarith
  qed
qed

lemma amortized_cost_fw_ipc_top_part_inductive':
  assumes "fw_ipc l x i l'" "top_part' (rep_of l x) l rkl x"
  shows "\<Phi> l' rkl + i \<le> \<Phi> l rkl + pl.displeasure l rkl x"
  using assms amortized_cost_fw_ipc_top_part_inductive
      top_part_alt by blast

lemma displeasure_equiv:
  "Pleasant.displeasure (top_part' (rep_of l x)) level l rkl x = pl.displeasure l rkl x"
  unfolding Pleasant.displeasure_def
  unfolding Pleasant.unpleasant_ancestors_def
  unfolding Pleasant.pleasant_def
  apply (subst top_part_alt) apply auto
  apply (rule bij_betw_same_card[of id])
  apply (subst bij_betw_id_iff)
proof (rule Set.equalityI, safe, goal_cases)
  case (1 x' y)
  have "rep_of l x' = rep_of l x" using \<open>x'\<in>ancestors l x\<close> unfolding ancestors_def 
    by (metis (no_types, lifting) case_prodD contextasm converse_rtranclE' invar_rank_ufa_invarI 
        mem_Collect_eq rep_of_bound rep_of_invar_along_path rtrancl.simps ufa_\<beta>_start_def)
  with 1 show ?case unfolding top_part'_def by blast
next
  case (2 x' y)
  have "rep_of l x' = rep_of l x" using \<open>x'\<in>ancestors l x\<close> unfolding ancestors_def 
    by (metis (no_types, lifting) case_prodD contextasm converse_rtranclE' invar_rank_ufa_invarI 
        mem_Collect_eq rep_of_bound rep_of_invar_along_path rtrancl.simps ufa_\<beta>_start_def)
  with 2 show ?case unfolding top_part'_def by blast
qed


lemma amortized_cost_fw_ipc_top_part:
  assumes "fw_ipc l x i l'" "top_part l rkl x" "x<length l"
  shows "\<Phi> l' rkl + i \<le> \<Phi> l rkl + \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
  using amortized_cost_fw_ipc_top_part_inductive[OF assms(1,2)] 
        bounded_displeasure_alstrup[OF contextasm assms(2,3)]
  apply (subst(asm) displeasure_equiv)
  by linarith
  

\<comment>\<open>Say x is "easy" if @{term "alphar \<circ> (rankr rkl)"} is NOT constant all the way from x
   to its root z, but maps x and its parent to the same value. In this case,
   a path compression step at x causes the potential of x to decrease. This
   is Lemma 4.9 in Alstrup et al.'s paper.\<close>


lemma easy_\<phi>:
  assumes "x<length l" "x\<noteq>l!x" "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (l!x))" 
  "\<alpha>\<^sub>r (rankr rkl (l!x)) < \<alpha>\<^sub>r (rankr rkl (rep_of l x))"
shows "\<phi> (l[x:= rep_of l x]) rkl x < \<phi> l rkl x"
proof -
  have h4: "(l!x,rep_of l x)\<in>(ufa_\<beta>_start l)\<^sup>*" 
    using   rep_of_bound[OF invar_rank_ufa_invarI[OF contextasm] assms(1)] 
      rep_of_idx[OF invar_rank_ufa_invarI[OF contextasm] assms(1)] 
      rep_of_path_iff[OF invar_rank_ufa_invarI[OF contextasm] ]
      ufa_invarD(2)[OF invar_rank_ufa_invarI[OF contextasm] assms(1)] 
    by blast
  note h = \<phi>_case_2_lower_bound[OF contextasm \<open>x<length l\<close> assms(2)[symmetric] assms(3)]
  have h5: "\<alpha>\<^sub>r (rankr rkl x) \<noteq> \<alpha>\<^sub>r (rankr rkl ((l[x := rep_of l x])!x))" 
    apply (subst compress_changes_parent_of_x_to_z[OF assms(1)])
    using assms(3,4) by linarith
  show ?thesis using  h5 
    apply (subst(asm) compress_changes_parent_of_x_to_z[OF assms(1)])
    using \<phi>_case_3 h
      compress_changes_parent_of_x_to_z[OF assms(1), symmetric]
      compress_preserves_roots_converse[of l "rep_of l x" x]
    by (metis One_nat_def \<phi>_case_3 h less_eq_Suc_le)
qed

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
    subgoal 
      using step(1) rep_of_ufa_\<beta>_refl[OF invar_rank_ufa_invarI[OF \<open>invar_rank l rkl\<close>] \<open>x<length l\<close>]
      by (metis \<open>rep_of l x < length l\<close> \<open>x < length l\<close> \<open>y < length l\<close> invar_rank_ufa_invarI 
          r_into_rtrancl rep_of_invar_along_path rep_of_path_iff step.prems)
    subgoal
      using \<open>x < length l\<close> invar_rank_ufa_invarI rep_of_min step.prems by blast
    done

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

  with step' show ?case
  proof (cases " \<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (rep_of l x))")
    case True
    hence "top_part l rkl x" unfolding top_part_def .
    show ?thesis using amortized_cost_fw_ipc_top_part[OF \<open>invar_rank l rkl\<close> 
          FWIPCStep[OF step(1) step(2)] \<open>top_part l rkl x\<close> \<open>x<length l\<close>] True 
      by linarith
  next
    case False
    have ir':"invar_rank (l[x := rep_of l x]) rkl" using  
        invar_rank_evolution[OF \<open>invar_rank l rkl\<close> EvCompress[OF step'(1), of rkl]] eq by argo
    note IH' = step'(3)[OF ir']

    then show ?thesis proof (cases "\<alpha>\<^sub>r (rankr rkl x) = \<alpha>\<^sub>r (rankr rkl (l!x))")
      case True 
      have "x\<noteq>l!x" using step(1) unfolding ufa_\<beta>_start_def by blast
      have "x<length l" using step(1) unfolding ufa_\<beta>_start_def by blast
      have "y = l!x" using step'(1) unfolding ufa_\<beta>_start_def by blast
      have ineq: "\<alpha>\<^sub>r (rankr rkl (l ! x)) < \<alpha>\<^sub>r (rankr rkl (rep_of l x))" using False 
        apply (subst (asm) True) using True aleq by linarith
      note \<Phi>ineq = from_\<phi>_to_\<Phi>[OF \<open>invar_rank l rkl\<close>  \<open>x\<noteq>l!x\<close> 
                          easy_\<phi>[OF \<open>invar_rank l rkl\<close> \<open>x<length l\<close> \<open>x\<noteq>l!x\<close> True ineq]] 
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
    using ipc_defined[OF _ assms] by presburger
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

end