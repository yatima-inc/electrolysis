theory alloc_export
imports core_export
begin

datatype 'T alloc_rc_Rc =
  alloc_rc_Rc 'T

datatype 'T alloc_raw_vec_RawVec =
  alloc_raw_vec_RawVec "'T list"

end