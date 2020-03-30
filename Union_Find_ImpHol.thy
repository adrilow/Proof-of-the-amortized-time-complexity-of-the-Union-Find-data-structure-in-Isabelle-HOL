theory Union_Find_ImpHol
imports
  Union_Find_Fun
  "Separation_Logic_Imperative_HOL.Sep_Main"
  "HOL-Library.Code_Target_Numeral"
begin

thm nth_list_update'


subsection \<open>Implementation with Imperative/HOL\<close>
text \<open>In this section, we implement the union-find data-structure with
  two arrays, one holding the next-pointers, and another one holding the size
  information. Note that we do not prove that the array for the 
  size information contains any reasonable values, as the correctness of the
  algorithm is not affected by this. We leave it future work to also estimate
  the complexity of the algorithm.
\<close>

type_synonym uf = "nat array \<times> nat array"

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al szl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>aszl 
    * \<up>(ufa_invar l \<and> ufa_\<alpha> l = R \<and> length szl = length l)"

definition uf_init :: "nat \<Rightarrow> uf Heap" where 
  "uf_init n \<equiv> do {
    l \<leftarrow> Array.of_list [0..<n];
    szl \<leftarrow> Array.new n (1::nat);
    return (szl,l)
  }"

lemma uf_init_rule[sep_heap_rules]: 
  "<emp> uf_init n <is_uf {(i,i) |i. i<n}>"
  unfolding uf_init_def is_uf_def[abs_def]
  by (sep_auto simp: ufa_init_correct ufa_init_invar)

partial_function (heap) uf_rep_of :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "uf_rep_of p i = do {
    n \<leftarrow> Array.nth p i;
    if n=i then return i else uf_rep_of p n
  }"

lemma uf_rep_of_rule[sep_heap_rules]: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>"
  apply (induct rule: rep_of_induct)
  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_refl)

  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_step)
  done

text \<open>We chose a non tail-recursive version here, as it is easier to prove.\<close>
partial_function (heap) uf_compress :: "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" 
  where [code]: 
  "uf_compress i ci p = (
    if i=ci then return ()
    else do {
      ni\<leftarrow>Array.nth p i;
      uf_compress ni ci p;
      Array.upd i ci p;
      return ()
    })"

lemma uf_compress_rule: "\<lbrakk> ufa_invar l; i<length l; ci=rep_of l i \<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al> uf_compress i ci p 
  <\<lambda>_. \<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' * \<up>(ufa_invar l' \<and> length l' = length l 
     \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>"
proof (induction rule: rep_of_induct)
  case (base i) thus ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: rep_of_refl)
    done
next
  case (step i)
  note SS = \<open>ufa_invar l\<close> \<open>i<length l\<close> \<open>l!i\<noteq>i\<close> \<open>ci = rep_of l i\<close>

  from step.IH 
  have IH': 
    "<p \<mapsto>\<^sub>a l> 
       uf_compress (l ! i) (rep_of l i) p
     <\<lambda>_. \<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * 
        \<up> (ufa_invar l' \<and> length l = length l' 
           \<and> (\<forall>i<length l'. rep_of l i = rep_of l' i))
     >"
    apply (simp add: rep_of_idx SS)
    apply (erule 
      back_subst[OF _ cong[OF cong[OF arg_cong[where f=hoare_triple]]]])
    apply (auto) [2]
    apply (rule ext)
    apply (rule ent_iffI)
    apply sep_auto+
    done

  show ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: SS)

    apply (rule IH')
    
    using SS apply (sep_auto (plain)) 
    using ufa_compress_invar apply fastforce []
    apply simp
    using ufa_compress_aux(2) apply fastforce []
    done
qed

definition uf_rep_of_c :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap"
  where "uf_rep_of_c p i \<equiv> do {
    ci\<leftarrow>uf_rep_of p i;
    uf_compress i ci p;
    return ci
  }"

lemma uf_rep_of_c_rule[sep_heap_rules]: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al> uf_rep_of_c p i <\<lambda>r. \<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l'
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>"
  unfolding uf_rep_of_c_def
  by (sep_auto heap: uf_compress_rule)

definition uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where 
  "uf_cmp u i j \<equiv> do {
    let (s,p)=u;
    n\<leftarrow>Array.len p;
    if (i\<ge>n \<or> j\<ge>n) then return False
    else do {
      ci\<leftarrow>uf_rep_of_c p i;
      cj\<leftarrow>uf_rep_of_c p j;
      return (ci=cj)
    }
  }"

lemma cnv_to_ufa_\<alpha>_eq: 
  "\<lbrakk>(\<forall>i<length l. rep_of l' i = rep_of l i); length l = length l'\<rbrakk> 
  \<Longrightarrow> (ufa_\<alpha> l = ufa_\<alpha> l')"
  unfolding ufa_\<alpha>_def by auto

lemma uf_cmp_rule[sep_heap_rules]:
  "<is_uf R u> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>"
  unfolding uf_cmp_def is_uf_def
  apply (sep_auto dest: ufa_\<alpha>_lenD simp: not_le split: prod.split)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (subst ufa_find_correct)
  apply (auto simp add: )
  done
  

definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union u i j \<equiv> do {
    let (s,p)=u;
    ci \<leftarrow> uf_rep_of p i;
    cj \<leftarrow> uf_rep_of p j;
    if (ci=cj) then return (s,p) 
    else do {
      si \<leftarrow> Array.nth s ci;
      sj \<leftarrow> Array.nth s cj;
      if si<sj then do {
        Array.upd ci cj p;
        Array.upd cj (si+sj) s;
        return (s,p)
      } else do { 
        Array.upd cj ci p;
        Array.upd ci (si+sj) s;
        return (s,p)
      }
    }
  }"

lemma uf_union_rule[sep_heap_rules]: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u> uf_union u i j <is_uf (per_union R i j)>"
  unfolding uf_union_def
  apply (cases u)
  apply (simp add: is_uf_def[abs_def])
  apply (sep_auto 
    simp: per_union_cmp ufa_\<alpha>_lenD ufa_find_correct
    rep_of_bound
    ufa_union_invar
    ufa_union_correct
  )
  done


export_code uf_init uf_cmp uf_union checking SML_imp

export_code uf_init uf_cmp uf_union checking Scala_imp

(*
ML_val {*
  val u = @{code uf_init} 10 ();

  val u = @{code uf_union} u 1 2 ();
  val u = @{code uf_union} u 3 4 ();
  val u = @{code uf_union} u 5 6 ();
  val u = @{code uf_union} u 7 8 ();

  val u = @{code uf_union} u 1 3 ();
  val u = @{code uf_union} u 5 7 ();

  val u = @{code uf_union} u 1 5 ();

  val b = @{code uf_cmp} u 8 4 ();
  val it = u;
*}*)


end