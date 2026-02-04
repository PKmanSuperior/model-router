(* file: list_util.sml *)
(* description: utility functions for list *)
(* author: Takahito Aoto *)

signature LIST_UTIL = 
sig 
    (* functions for set *)
    val elm: 'a list -> 'a option
    val pair: 'a list -> ('a * 'a) option
    val find: (''a -> bool) -> ''a list -> ''a option
    val member: ''a  -> ''a list -> bool
    val add: ''a  -> ''a list -> ''a list
    val union: ''a list * ''a list -> ''a list
    val unions: ''a list list -> ''a list
    val unionMap: (''a -> ''b list) -> ''a list -> ''b list
    val isSubset: ''a list * ''a list -> bool
						       
    val toStringBuilt: ('a -> string) -> (string * string * string) -> 'a list -> string
    val toStringCommaSpaceBrace: ('a -> string) -> 'a list  -> string
    val toStringCommaLnSquare: string -> ('a -> string) -> 'a list -> string
    val toStringCommaLnSquareSpace: ('a -> string) -> 'a list -> string
    val maxLength: 'a list list -> int
    val selectLengthN: int -> 'a list list -> 'a list list
    val sortOrderLargeLength: 'a list list -> 'a list list
    val mapAppend: ('a -> 'b list) -> 'a list -> 'b list
    val delete: ''a -> ''a list -> ''a list
    val elimDup: ''a list -> ''a list
    val allSame: ''a list -> bool
				 
    val combinations: int -> 'a list -> 'a list list
    val allCombinations: 'a list list -> 'a list list
    val transpose: ''a list list -> ''a list list
end

structure ListUtil : LIST_UTIL =
struct

fun elm [a] = SOME a 
  | elm _ = NONE

fun pair [x, y] = SOME (x, y)
  | pair _ = NONE

fun find f xs =
    let val cands = (List.filter (fn x => f x) xs)
    in if null cands then NONE else SOME (hd cands)
    end 

fun member x ys = List.exists (fn y => x = y) ys

(* 集合としての演算 *)
fun add x ys = if member x ys then ys else x::ys

fun union ([],ys) = ys
  | union (x::xs,ys) = add x (union (xs,ys))

fun unions [] = []
  | unions (xs::xss) = union (xs,unions xss)

fun unionMap f [] = []
  | unionMap f (x::xs) = union (f x, unionMap f xs)

fun isSubset (xs, ys) = List.all (fn x => member x ys) xs

fun toStringBuilt prElm (start,sep,stop) xs =
    let fun toStringSub [] = ""
          | toStringSub [x] = (prElm x)
          | toStringSub (x::xs)= (prElm x) ^ sep ^ (toStringSub xs)
    in  start ^ (toStringSub xs) ^ stop
    end

fun toStringCommaSpaceBrace prElm xs = toStringBuilt prElm ("{",", ","}") xs

fun iterate (str, n) = if n = 0 then "" else str ^ iterate (str, n - 1)
fun toStringCommaLnSquare str prElm xs = str ^ (toStringBuilt prElm ("[ ",",\n" ^ iterate (" ", size str) ^ "  "," ]\n") xs)
						     
fun toStringCommaLnSquareSpace prElm xs = "    " ^ (toStringBuilt prElm ("[ ",",\n      "," ]\n") xs)


(*リストのリストを受け取り、長さの最大値を返す関数*)
fun maxLength xs =
    let	fun main ml [] = ml
	  | main ml (x::xs) = if ml < length x then main (length x) xs else main ml xs
    in main 0 xs
    end

(*長さがnのリストのみを残す関数*)
fun selectLengthN n xs = List.filter (fn x => length x = n) xs

(*リストのリストを受け取り、長さの大きい順に並べる関数*)
fun sortOrderLargeLength xs =
    let val max = maxLength xs
	fun main 0 xs = [[]]
	  | main n xs = (selectLengthN n xs) @ main (n-1) xs
    in main max xs
    end

fun mapAppend f [] = []
  | mapAppend f (x::xs) = (f x) @ (mapAppend f xs)

fun delete e xs =
    let fun main e [] ys = ys
	  | main e (x::xs) ys = if e = x
				then main e xs ys
				else main e xs (ys @ [x])
    in main e xs []
    end

fun elimDup [] = []
  | elimDup (x::xs) = x::(elimDup(delete x xs))

fun allSame [] = true
  | allSame (x::xs) = foldl (fn (y,acc) => acc andalso y = x) true xs

fun combinations k xs = if k = 0 then [[]]
			 else let val smaller = combinations (k-1) xs
			      in List.concat (List.map (fn comb => List.map (fn c => comb @ [c]) xs) smaller)
			      end

fun allCombinations [] = [[]]
  | allCombinations (xs::rest) =
      let val restComb = allCombinations rest
      in List.concat (List.map (fn x => List.map (fn ys => x::ys) restComb) xs)
      end
				  
fun transpose [] = []
  | transpose rows = if List.exists (fn row => null row) rows
		     then []
		     else List.map List.hd rows::transpose (List.map List.tl rows)

end
