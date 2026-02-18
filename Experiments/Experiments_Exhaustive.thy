theory Experiments_Exhaustive
  imports Main
begin

definition subseqs_upto_k :: "'a list => nat => 'a list list" where
  "subseqs_upto_k xs k = filter (%ys. length ys <= k) (List.subseqs xs)"

definition argmax_list ::
  "('a set => 'b::linorder) => 'a list list => 'a list" where
  "argmax_list f cands =
     foldl (%best cand. if f (set best) <= f (set cand) then cand else best) [] cands"

definition enum_opt_set ::
  "('a set => 'b::linorder) => 'a list => nat => 'a set" where
  "enum_opt_set f Vlist k = set (argmax_list f (subseqs_upto_k Vlist k))"

end