open ImpPrelude

val make_dict : 'a1 Dict.hash_params -> ('a1, 'a2) Dict.t
val xhCons: (('a -> 'a -> bool) * ('a pre_hashV -> 'a hashV)) -> 'a hashConsing
