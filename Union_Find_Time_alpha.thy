theory Union_Find_Time_alpha
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

type_synonym uf = "nat array \<times> nat array"

subsection{*Imperative HOL implementation*}

definition uf_init :: "nat \<Rightarrow> uf Heap" where 
  "uf_init n \<equiv> do {
    l \<leftarrow> Array.of_list [0..<n];
    szl \<leftarrow> Array.new n (1::nat);
    return (szl,l)
  }"


partial_function (heap) uf_rep_of :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "uf_rep_of p i = do {
    n \<leftarrow> Array.nth p i;
    if n=i then return i else uf_rep_of p n
  }"


text {* We chose a non tail-recursive version here, as it is easier to prove. *}
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

definition uf_rep_of_c :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap"
  where "uf_rep_of_c p i \<equiv> do {
    ci\<leftarrow>uf_rep_of p i;
    uf_compress i ci p;
    return ci
  }"


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

(* OLD union, with merge by size
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
*)

definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union u i j \<equiv> do {
    let (r,p)=u;
    ci \<leftarrow> uf_rep_of p i;
    cj \<leftarrow> uf_rep_of p j;
    if (ci=cj) then return (r,p) 
    else do {
      ri \<leftarrow> Array.nth r ci;
      rj \<leftarrow> Array.nth r cj;
      if ri<rj then do {
        Array.upd ci cj p;
        (if (ri=rj) then do {
            Array.upd cj (ri+1) r
           } else return r);
         return (r,p)
      } else do { 
        Array.upd cj ci p;
        if (ri=rj) then do {
            Array.upd ci (ri+1) r;
            return (r,p)
        } else return (r,p)
      }
    }
  }"

end