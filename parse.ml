
(* open Base *)
open Core
(* open Stdio *)

(* Annoyingly Ocaml requires definitions to occur in reverse order from how the are dreamed up when following HTDP's process *)

let ddir = "data"

(* Ocaml refuses to work without this for some unknown reason *)
let pass s = match s with () -> true


(* String Stream → Stream
	Takes a stream and skips a constant string at the beginning.  If string does not occur do nothing.*)
let skip_const r p =
	let rec lop s = (* Note partial matches will still result in skipped chars *)
		match Stream.peek p with
		| None -> p
		| Some k ->
			match s with
			| [] -> p
			| hd::tl -> if Char.equal k hd && pass (Stream.junk p) then lop tl else p
	in
	lop (String.to_list r)

(* (Char → Bool) Stream → Stream
	Skip characters as long as predidate holds *)
let rec skip e p =
	match Stream.peek p with
	| None -> p
	| Some k -> if e k && pass (Stream.junk p)
		          then skip e p
		          else p


(* (Char → Bool) Stream → List of Char
	Reads characters as long as predicate holds *)
let read e p =
	let rec lop p =
		match Stream.peek p with
		| None -> []
		| Some k -> if e k && pass (Stream.junk p) then k::(lop p) else []
	in
	String.of_char_list (lop p)

(* List (α → Bool) → (α → Bool)
	Create predicate that checks that things are in a list of things *)
let inp l e x = List.mem l x ~equal:e

(* List (α → Bool) → (α → Bool)
	Create predicate that checks that things are not in a list of things *)
let nip l e x = not (List.mem l x ~equal:e)


(* List → Stream
	Skip while char is in a list *)
let skip_while x = skip (inp x Char.equal)

(* List → Stream
	Skip unless char is in a list *)
let skip_until x = skip (nip x Char.equal)


(* List → List of Char
	Read while char is in list *)
let read_while x = read (inp x Char.equal)

(* List → List of Char
	Read while char is in list *)
let read_until x = read (nip x Char.equal)

(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)
(* Printing functions for debugging *)

(* α List of α → void
	Print a list of things *)
let print_list f l =
	let rec print_elements = function
		| [] -> ()
		| h::t -> f h ; print_string ";" ; print_elements t
	in
	print_string "["; print_elements l; print_string "]"

(* Char → Void
	Print a char *)
let printc = Out_channel.output_char stdout

(* Int → Void
	Print an Int *)
let printi i = Out_channel.output_string stdout (Int.to_string i)

(* List of List of Int → Void
	Print a DIMACS equation *)
let print_equation = print_list (print_list printi)

(* → Void
	Print a newline *)
let pnl = Out_channel.newline

(* El → Void
	Print an El *)
let printel = function
	| Top -> print_string "T"
	| Bot -> print_string "B"
	| Sig -> print_string "S"
	| Rep k -> printi k


(* <><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><> *)

(* A DIMACS is a string with the following grammar
	wsp = SP | NL | TAB
	num = 1..9 (ε|+ 0..9)
	format = "cnf"
	vcount = int
	ccount = int
	comment = "c" +¬(NL|EOS)
	problem = "p" wsp format wsp vcount wsp ccount NL
	clause = +(ε|"-" num wsp) "0"|EOS
	dimacs = BOS *comment problem + clause|comment
	I: a CNF formula
	Ex: *)
let dex = "c A sample CNF file
c
p cnf 4 3
1 3 -4 0
4 0 2
-3"
let coex = "c A sample CNF file\nc"
let pex = "p cnf 4 3\n"
let clex = "1 3 -4 0\n4 0 2\n-3"

let nms = ['-';'0';'1';'2';'3';'4';'5';'6';'7';'8';'9']
let wsp = ['\n';'\t';' ']

(* Stream → List of Char
	Skip until a number appears, then read the number *)
let read_count p =
	read_while nms (skip_until nms p)

(* Stream → (Int Int)
	Read the problem statement and return var/clause counts *)
let problem p =
	match Stream.peek p with
	| None -> (0,0)
	| Some k -> if Char.equal k 'p'
		          then
			          let v = Int.of_string (read_count p) in
			          let c = Int.of_string (read_count p) in
			          ignore (skip_while ['\n'] (skip_until ['\n'] p));
			          (v,c)
		          else (0,0)

(* Stream → Stream
	Skip comments *)
let rec comments p =
	match Stream.peek p with
	| None -> p
	| Some k -> if Char.equal k 'c'
		          then comments (skip_while ['\n'] (skip_until ['\n'] p))
	            else p

(* Stream → List of Int
	Read clause and return in sorted order *)
let clause p =
	let rec lop p =
		match Stream.peek (skip_while wsp p) with
		| None -> []
		| Some _ ->
			let r = (Int.of_string (read_count p)) in
				if r = 0
				then []
				else r :: (lop p)
	in
	let cmp x y = compare (abs x) (abs y) in
	List.sort (lop p) ~compare:cmp

(* Stream → (Int Int) (List of List of Int)
	Takes a Port to read from and parses the contents into a
	list of equations
	*)
let parse_dimacs p =
	let rec lop r p =
		match Stream.peek p with
		| None -> r
		| Some k -> if Char.equal k '0' && pass (Stream.junk p)
			          then lop r p
			          else let c = clause (comments p) in lop (c::r) (skip_while ('0'::wsp) p)
	in
	let n = problem (comments p) in
	(n, (lop [] p))

(* String → (Int Int) (List of List of Int)
	Takes a filename and returns a list of equations
	Calls: parse_dimacs *)
let filename_to_list f =
	In_channel.with_file f ~f:(fun p -> parse_dimacs (Stream.of_channel p))


(* let () = print_equation (parse_dimacs (Stream.of_string dex))
let () = print_list (print_list printel) (conv (filename_to_list (ddir ^ "/test.cnf"))); pnl stdout
let () = look (filename_to_list (ddir ^ "/test.cnf")); pnl stdout
let () = print_list (print_list printel) (conv (filename_to_list (ddir ^ "/simple_v3_c2.cnf"))); pnl stdout
let () = look (filename_to_list (ddir ^ "/simple_v3_c2.cnf")); pnl stdout
 *)
(* let () = print_equation (filename_to_list (ddir ^ "/simple_v3_c2.cnf")); pnl *)

