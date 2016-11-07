let arr_of_string s =
  let listl = (Str.split (Str.regexp " ") s) in
  (Array.of_list listl)
