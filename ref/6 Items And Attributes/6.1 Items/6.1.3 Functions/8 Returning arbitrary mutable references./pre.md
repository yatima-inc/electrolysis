In general, we would have to return a sum type of lenses that represents which argument the return value points into. The callee would then match on the sum and combine the return value with the corresponding argument lens.