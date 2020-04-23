type pset
val qnode : pset -> bool -> pset -> pset
val node : pset * bool * pset -> pset
val empty : pset
val pset_match : (unit -> 'a) -> (pset -> bool -> pset -> 'a) -> pset -> 'a
val eq : pset -> pset -> bool
