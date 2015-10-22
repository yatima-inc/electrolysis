theory Export
imports Rustabelle
begin

datatype Any =
Any_0 "u32"
| Any_1 "u32"
| Any_2 "unit"
| Any_3 "core_ops_Range"
| Any_4 "u32"
| Any_5 "unit"
| Any_6 "unit"
| Any_7 "core_ops_Range"
| Any_8 "(core_ops_Range => core_ops_Range)"
| Any_9 "core_ops_Range"
| Any_10 "u32"
| Any_11 "core_option_Option"
| Any_12 "(core_ops_Range => core_option_Option \<times> core_ops_Range)"
| Any_13 "core_ops_Range"
| Any_14 "core_ops_Range"
| Any_15 "unit"
| Any_16 "u32"
| Any_17 "unit"
| Any_18 "u32"
| Any_19 "u32"

type_synonym state = "nat \<rightharpoonup> Any"



definition fac_16 where "fac_16 cont_27 s = ((\<lambda>cont s. cont (s(12 \<mapsto> Any_12 core_iter_ops_Range_A__Iterator_next)));
(\<lambda>cont s. cont (s(14 \<mapsto> Any_14 (case s 3 of Some (Any_3 x) => x))));
(\<lambda>cont s. cont (s(13 \<mapsto> Any_13 (case s 14 of Some (Any_14 x) => x))));
(\<lambda>cont s. cont (let (t11, t13) = ((case s 12 of Some (Any_12 x) => x) (case s 13 of Some (Any_13 x) => x)) in s(11 \<mapsto> Any_11 t11, 13 \<mapsto> Any_13 t13)));
(\<lambda>cont s. case (case s 11 of Some (Any_11 x) => x) of core_option_Option_None  => (cont_27) cont s | core_option_Option_Some _ => ((\<lambda>cont s. cont (s(4 \<mapsto> Any_4 (case (case s 11 of Some (Any_11 x) => x) of core_option_Option_Some x => x))));
(\<lambda>cont s. cont (s(16 \<mapsto> Any_16 (case s 4 of Some (Any_4 x) => x))));
(\<lambda>cont s. cont (s(1 \<mapsto> Any_1 ((case s 1 of Some (Any_1 x) => x) * (case s 16 of Some (Any_16 x) => x)))));
(\<lambda>cont s. cont (s(15 := None)));
(\<lambda>cont s. cont (s(13 := None)));
(\<lambda>cont s. cont (s(14 := None)));
id) cont s)) (\<lambda>s. (s, None)) s"

definition fac :: "u32 => u32" where
"fac n = ((\<lambda>cont s. cont (s(0 \<mapsto> Any_0 n)));
(\<lambda>cont s. cont (s(1 \<mapsto> Any_1 1)));
(\<lambda>cont s. cont (s(8 \<mapsto> Any_8 core_iter_I_IntoIterator_into_iter)));
(\<lambda>cont s. cont (s(10 \<mapsto> Any_10 (case s 0 of Some (Any_0 x) => x))));
(\<lambda>cont s. cont (s(9 \<mapsto> Any_9 (core_ops_Range 2 (case s 10 of Some (Any_10 x) => x)))));
(\<lambda>cont s. cont (let (t7) = ((case s 8 of Some (Any_8 x) => x) (case s 9 of Some (Any_9 x) => x)) in s(7 \<mapsto> Any_7 t7)));
(\<lambda>cont s. cont (s(3 \<mapsto> Any_3 (case s 7 of Some (Any_7 x) => x))));
(\<lambda>cont. loop (fac_16 ((\<lambda>cont s. cont (s(13 := None)));
(\<lambda>cont s. cont (s(14 := None)));
(\<lambda>cont s. cont (s(3 := None)));
(\<lambda>cont s. cont (s(7 := None)));
(\<lambda>cont s. cont (s(9 := None)));
(\<lambda>cont s. cont (s(17 \<mapsto> Any_17 (case s 2 of Some (Any_2 x) => x))));
(\<lambda>cont s. cont (s(6 \<mapsto> Any_6 (case s 17 of Some (Any_17 x) => x))));
(\<lambda>cont s. cont (s(6 := None)));
(\<lambda>cont s. cont (s(18 \<mapsto> Any_18 (case s 1 of Some (Any_1 x) => x))));
(\<lambda>cont s. cont (s(19 \<mapsto> Any_19 (case s 18 of Some (Any_18 x) => x))));
id)))) (\<lambda>s. (case s 19 of Some (Any_19 x) => x)) Map.empty"

end
