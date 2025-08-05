(* file: list_util.sml *)
(* description: utility functions for list *)
(* author: Takahito Aoto *)

signature LIST_UTIL = 
sig 
    (* functions for set *)
    val member: ''a  -> ''a list -> bool
    val add: ''a  -> ''a list -> ''a list
    val union: ''a list * ''a list -> ''a list
    val unions: ''a list list -> ''a list
    val toStringBuilt: ('a -> string) -> (string * string * string) -> 'a list -> string
    val toStringCommaSpaceBrace: ('a -> string) -> 'a list  -> string
    val toStringCommaLnSquare: ('a -> string) -> 'a list -> string
    val maxLength: 'a list list -> int
    val selectLengthN: int -> 'a list list -> 'a list list
    val sortOrderLargeLength: 'a list list -> 'a list list
    val mapAppend: ('a -> 'b list) -> 'a list -> 'b list
    val delete: ''a -> ''a list -> ''a list
    val elimDup: ''a list -> ''a list
    val combinations: int -> 'a list -> 'a list list
    val stirlingComb: int -> int -> int list list
    val combPair: 'a list -> 'a list  list
    val pairUp: 'a list -> ('a * 'a) list
    val transpose: ''a list list -> ''a list list
    val decimalToBase: int -> int -> int -> int list
    val baseToDecimal: int list -> int -> int
end

structure ListUtil : LIST_UTIL =
struct 

fun member x ys = List.exists (fn y => x = y) ys

(* 集合としての演算 *)
fun add x ys = if member x ys then ys else x::ys

fun union ([],ys) = ys
  | union (x::xs,ys) = add x (union (xs,ys))

fun unions [] = []
  | unions (xs::xss) = union (xs,unions xss)

fun toStringBuilt prElm (start,sep,stop) xs =
    let fun toStringSub [] = ""
          | toStringSub [x] = (prElm x)
          | toStringSub (x::xs)= (prElm x) ^ sep ^ (toStringSub xs)
    in  start ^ (toStringSub xs) ^ stop
    end

fun toStringCommaSpaceBrace prElm xs = toStringBuilt prElm ("{",", ","}") xs

fun toStringCommaLnSquare prElm xs = "   " ^ (toStringBuilt prElm ("[ ",",\n     "," ]\n") xs)

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

fun combinations k dom = if k = 0 then [[]]
			 else let val smaller = combinations (k-1) dom
			      in List.concat (List.map (fn comb => List.map (fn c => comb @ [c]) dom) smaller)
			      end

fun stirlingComb r n =
    let fun extend used current =
	    if length current = r
	    then [rev current]
	    else
		let val nextConst = length used
		    fun try i = if i < nextConst then extend used (i :: current)
				else if i = nextConst andalso nextConst < n then extend (nextConst :: used) (i :: current)
				else []
		    fun loop i = if i > nextConst then []
				 else try i @ loop (i + 1)
		in loop 0
		end
    in extend [] []
    end
	
fun combPair [] = []
  | combPair (x::xs) =
    let val pairs = List.map (fn y => [x,y]) xs
    in pairs @ combPair xs
    end

fun pairUp [] = []
  | pairUp [_] = raise Fail "Error: List has an odd number of elements"
  | pairUp (x::y::rest) = (x, y) :: pairUp rest

fun transpose [] = []
  | transpose rows = if List.exists (fn row => null row) rows
		     then []
		     else List.map List.hd rows::transpose (List.map List.tl rows)

fun decimalToBase num base k =
    let fun toBase (0, base) = [0]
	  | toBase (number, base) =
	    let fun loop (0, acc) = acc
		  | loop (n, acc) = loop (n div base, (n mod base)::acc)
	    in loop (number, [])
	    end
	val baseList = toBase (num,base)
	val paddingLength = if k > 0 then k - length baseList else 0
	val padding = List.tabulate (paddingLength,fn _ => 0)
    in padding @ baseList
    end

fun baseToDecimal xs base =
    let fun main [] base sum = sum
	  | main (x::xs) base sum = main xs base (sum * base + x)
    in main xs base 0
    end 

end
