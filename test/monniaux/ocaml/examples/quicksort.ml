let rec quicksort gt = function
  | [] -> []
  | x::xs ->
      let ys, zs = List.partition (gt x) xs in
      (quicksort gt ys) @ (x :: (quicksort gt zs));;
 
let l =
  quicksort ( > ) [4; 65; 2; -31; 0; 99; 83; 782; 1]
in
List.iter (fun x -> Printf.printf "%d; " x) l;
print_newline();
