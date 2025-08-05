signature PRED =
sig
    eqtype key
    val toString: key -> string
    val fromString: string -> key
end

structure Pred : PRED =
struct
type key = string
fun toString key = if String.isPrefix "?" key
		   then raise Fail "Error: Pred.toString: invalid pred name"
		   else key

fun fromString str = str
end
