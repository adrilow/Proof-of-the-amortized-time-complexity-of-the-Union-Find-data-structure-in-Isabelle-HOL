theory Union_Find_Time_alpha_fix
  imports Union_Find_Time_alpha_abstract_analysis
begin

subsection {* Implementation with Imperative/HOL *}
text {* In this section, we implement the union-find data-structure with
  two arrays, one holding the next-pointers, and another one holding the size
  information. Note that we do not prove that the array for the 
  size information contains any reasonable values, as the correctness of the
  algorithm is not affected by this. We leave it future work to also estimate
  the complexity of the algorithm.
*}


text_raw\<open>\DefineSnippet{uf_definition}{\<close>

type_synonym uf = "nat array \<times> nat array"

text_raw\<open>}\<close>

subsection{*Imperative HOL implementation*}

text_raw\<open>\DefineSnippet{uf_init}{\<close>

definition uf_init :: "nat \<Rightarrow> uf Heap" where 
  "uf_init n \<equiv> do {
    l \<leftarrow> Array_Time.of_list [0..<n];
    szl \<leftarrow> Array_Time.new n (0::nat);
    return (szl,l)
  }"

text_raw\<open>}\<close>

text_raw\<open>\DefineSnippet{uf_cmp}{\<close>

partial_function (heap_time) uf_rep_of :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "uf_rep_of p i = do {
    n \<leftarrow> Array_Time.nth p i;
    if n=i then return i else uf_rep_of p n
  }"


partial_function (heap_time) uf_compress :: "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" 
  where [code]: 
  "uf_compress i ci p = (
    if i=ci then return ()
    else do {
      ni\<leftarrow>Array_Time.nth p i;
      uf_compress ni ci p;
      Array_Time.upd i ci p;
      return ()
    })"

definition uf_rep_of_c :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap"
  where "uf_rep_of_c p i \<equiv> do {
    ci\<leftarrow>uf_rep_of p i;
    uf_compress i ci p;
    return ci
  }"


definition uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where 
  "uf_cmp u i j \<equiv> do {
    let (s,p)=u;
    n\<leftarrow>Array_Time.len p;
    if (i\<ge>n \<or> j\<ge>n) then return False
    else do {
      ci\<leftarrow>uf_rep_of_c p i;
      cj\<leftarrow>uf_rep_of_c p j;
      return (ci=cj)
    }
  }"

text_raw\<open>}\<close>

(* OLD union, with merge by size
definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union u i j \<equiv> do {
    let (s,p)=u;
    ci \<leftarrow> uf_rep_of p i;
    cj \<leftarrow> uf_rep_of p j;
    if (ci=cj) then return (s,p) 
    else do {
      si \<leftarrow> Array_Time.nth s ci;
      sj \<leftarrow> Array_Time.nth s cj;
      if si<sj then do {
        Array_Time.upd ci cj p;
        Array_Time.upd cj (si+sj) s;
        return (s,p)
      } else do { 
        Array_Time.upd cj ci p;
        Array_Time.upd ci (si+sj) s;
        return (s,p)
      }
    }
  }"
*)

text_raw\<open>\DefineSnippet{uf_union}{\<close>

definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union u i j \<equiv> do {
    let (r,p)=u;
    ci \<leftarrow> uf_rep_of_c p i;
    cj \<leftarrow> uf_rep_of_c p j;
    if (ci=cj) then return (r,p) 
    else do {
      ri \<leftarrow> Array_Time.nth r ci;
      rj \<leftarrow> Array_Time.nth r cj;
      if ri<rj then do {
        Array_Time.upd ci cj p;
        (if (ri=rj) then do {
            Array_Time.upd cj (ri+1) r
           } else return r);
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

text_raw\<open>}\<close>

end