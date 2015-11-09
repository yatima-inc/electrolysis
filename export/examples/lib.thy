theory lib
imports "../../Rustabelle" "../core/iter"
begin



definition examples_fac_16 where "examples_fac_16 res = (\<lambda>(res, iter). let t_8 = core_iter_ops_Range_A__Iterator_next in
let t_10 = iter in
let t_9 = t_10 in
let (t_7, t_9) = (t_8 t_9) in
case t_7 of core_option_Option_None  => ((res, iter), False) | core_option_Option_Some _ => let i = (case t_7 of core_option_Option_Some x => x) in
let t_12 = i in
let res = (res * t_12) in
let t_10 = t_9 in
let iter = t_10 in
((res, iter), True))"

definition examples_fac :: "u32 => u32" where
"examples_fac n = (let n = n in
let res = 1 in
let t_3 = core_iter_I_IntoIterator_into_iter in
let t_6 = n in
let t_5 = (t_6 + 1) in
let t_4 = (core_ops_Range 2 t_5) in
let (t_2) = (t_3 t_4) in
let iter = t_2 in
let (res, iter) = loop (examples_fac_16 res) (res, iter) in
let t_14 = res in
let ret = t_14 in
ret)"

end
