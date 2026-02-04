signature IN =
sig
    val read: string -> (Trs.ctrs * Trs.reach list)
    val encode: string -> unit
end

structure In : IN =
struct
local
    structure SU = StringUtil
    structure LU = ListUtil
    structure T = Term
in

fun pair [s,t] = SOME (s,t)
  | pair _ = NONE

fun getTerms str =
    let fun main [] (acc, ts) n = if null acc then rev ts else rev (String.implode (rev acc)::ts)
	  | main (c::cs) (acc, ts) 0 = if c = #"(" then if null acc then main cs (acc, ts) 1 else main cs ([], String.implode (rev acc)::ts) 1
				       else if Char.isGraph c then main cs (c::acc, ts) 0
				       else if null acc then main cs (acc, ts) 0
				       else main cs ([], String.implode (rev acc)::ts) 0
	  | main (c::cs) (acc, ts) 1 = if c = #")" then main cs ([], String.implode (rev acc)::ts) 0
				       else if c = #"(" then main cs (c::acc, ts) 2
				       else main cs (c::acc, ts) 1
	  | main (c::cs) (acc, ts) n = if c = #"(" then main cs (c::acc, ts) (n + 1)
				       else if c = #")" then main cs (c::acc, ts) (n - 1)
				       else main cs (c::acc, ts) n
    in main (String.explode str) ([], []) 0
    end

fun fromString funs str = case SU.find str #"(" of
			      SOME pos => let val (symbol, args) = valOf (List.getItem (getTerms str))
					  in T.Fun (symbol, List.map (fn t => fromString funs t) args)
					  end 
			    | NONE => let val list = SU.split str #" "
					  val symbol = hd list
					  val args = tl list
				      in if LU.member symbol funs
					 then T.Fun (symbol, List.map (fn t => fromString funs t) args)
					 else T.Var (Var.fromString symbol)
				      end

fun getRule symbols rule =
    let val (condsStr, rlStr) = List.partition (fn str => String.isPrefix "=" str) (tl (getTerms rule))
	val rl = valOf (pair (List.map (fn t => fromString symbols t) rlStr))
	val conds = List.map (fn cond => valOf (pair (List.map (fn t => fromString symbols t) (tl (getTerms cond))))) condsStr
    in (rl, conds)
    end

fun getReachs symbols problem =
    let val reachs = tl (getTerms problem)
    in List.map (fn reach => valOf (pair (List.map (fn t => fromString symbols t) (tl (getTerms reach))))) reachs
    end 

fun splitInput [] (opt, funs, rules, problem) = (hd opt, rev funs, rev rules, hd problem)
  | splitInput (line::rest) (opt, funs, rules, problem) = if String.isPrefix "format" line then splitInput rest (line::opt, funs, rules, problem)
							  else if String.isPrefix "fun" line then splitInput rest (opt, line::funs, rules, problem)
							  else if String.isPrefix "rule" line then splitInput rest (opt, funs, line::rules, problem)
							  else splitInput rest (opt, funs, rules, line::problem)

fun read filename =
    let val inStream = TextIO.openIn filename
	fun loop acc = case TextIO.inputLine inStream of
			   NONE => List.rev acc
			 | SOME line => if String.isPrefix ";" line then loop acc else loop ((String.substring (line, 1, size line - 3))::acc)
	val lines = loop []
	val _ = TextIO.closeIn inStream
	val (opt, funs, rules, problem) = splitInput lines ([],[],[],[])
	val symbols = List.map (fn str => List.nth (SU.split str #" ", 1)) funs
	val ctrs = List.map (fn rule => getRule symbols rule) rules
	val problems = getReachs symbols problem
    in (ctrs, problems)
    end 

fun encode filename =
    let val (ctrs, reachs) = read filename
	val _ = print (Trs.prCRules ctrs)
	val _ = print (Trs.prReachs reachs ^ "\n")
    in ()
    end 
	
end
end 
