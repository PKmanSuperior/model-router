(* file: term.sml *)
(* description: first-order terms *)
(* author: Takahito Aoto *)

signature TERM = 
sig 
    type var_key = Var.key
    type fun_key = Fun.key
    type position = int list
    datatype term = Var of var_key | Fun of fun_key * term list
    type context = term -> term

    val root: term -> Symbol.symbol 
    val args: term -> term list 
    val isVar: term -> bool 
    val isFun: term -> bool 
    val vars: term -> var_key list
    val varsNum: term -> (var_key * int) list
    val funs: term -> fun_key list
    val funsNum: term -> int
    val isConst: term -> bool
    val isGround: term -> bool
    val arity: term -> (fun_key * int) option

    val toString: term -> string
    val fromString: string -> term

    val cropId: string -> (string * string) option
    val cropTerm: string -> (term * string) option
    val cropKeySeparatedTermPair: string -> string -> ((term * term) * string) option
    val readKeySeparatedTermPair: string -> string -> (term * term)
    val readMultipleKeySepartedTermPairs: string * string * string -> string -> string -> (term * term) list

    exception PositionNotInTerm
    val prPos: position -> string
    val pos: term -> position list
    val symbol: term -> position -> Symbol.symbol
    val subterm: term -> position -> term
    val getAllSubterm: term -> term list
    val getAllSubtermProper: term -> term list

    val makeContext: term -> position -> context
    val fillContext: context -> term -> term
    val replaceSubterm: term -> position -> term -> term

    val getAr: term -> (fun_key * int) list
end

structure Term : TERM =
struct
local
    structure LP = ListPair
    structure SU = StringUtil
in

type var_key = Var.key
type fun_key = Fun.key
type position = int list
datatype term = Var of var_key | Fun of fun_key * term list
type context = term -> term

exception PositionNotInTerm

fun root (Var x) = Symbol.V x
  | root (Fun (f,ts)) = Symbol.F f

fun args (Var x) = []
  | args (Fun (f,ts)) = ts

fun isVar (Var x) = true
  | isVar _ = false

fun isFun (Fun (f,ts)) = true
  | isFun _ = false

fun vars (Var x) = [x]
  | vars (Fun (f,ts)) = varsList ts
and varsList [] = []
  | varsList (t::ts) = ListUtil.union (vars t, varsList ts)

fun varsNum term =
    let val vars = vars term
	fun varNum var (Var x) = if x = var then 1 else 0
	  | varNum var (Fun (f,ts)) = varNumList var ts
	and varNumList var [] = 0
	  | varNumList var (t::ts) = varNum var t + varNumList var ts
    in List.map (fn x => (x, varNum x term)) vars
    end 

fun funs (Var x) = []
  | funs (Fun (f,ts)) = ListUtil.add f (funsList ts)
and funsList [] = []
  | funsList (t::ts) = ListUtil.union (funs t, funsList ts)

fun funsNum (Var x) = 0
  | funsNum (Fun (f,ts)) = 1 + funsNumList ts
and funsNumList [] = 0
  | funsNumList (t::ts) = funsNum t + funsNumList ts

fun isConst (Var x) = false
  | isConst (Fun (f,ts)) = null ts

fun isGround t = null (vars t)

fun arity (Var x) = NONE
  | arity (Fun (f,ts)) = SOME (f,length ts)

fun toString (Var x) =  "?" ^ (Var.toString x)
  | toString (Fun (f,[])) = (Fun.toString f)
  | toString (Fun (f,ts)) = (Fun.toString f) ^ "(" ^ (toStringList ts)
and toStringList [] = "" (* does not reach here *)
  | toStringList ([t]) = (toString t) ^ ")"
  | toStringList (t::ts) = (toString t) ^ "," ^ (toStringList ts)

structure TermSpecialSymbols = struct val special = [#"(", #")", #","]  end
structure TermLex = Lexical (TermSpecialSymbols)
structure TermParsing = Parsing (TermLex)

local
    fun makeFun (id, ts) = (case Symbol.fromString id of
			    Symbol.F f => Fun (f, ts)
			  | Symbol.V _ => raise Fail "Syntax error: function symbol expected")
    fun makeList (t, ts) = t::ts
    fun makeList1 t = t::nil
    fun makeAtom id  = (case Symbol.fromString id of
			    Symbol.F c => Fun (c, []) 
			  | Symbol.V x => Var x)

    open TermParsing
    infix 6 $--
    infix 5 --
    infix 3 >>
    infix 0 ||

    fun term toks =
        ( id --  "(" $-- termlist >> makeFun || atom ) toks
    and termlist toks =
        ( termseq -- $ ")" >> #1 ) toks
    and termseq toks =
        ( term -- "," $-- termseq >> makeList || term >> makeList1 ) toks
    and atom toks  =
        ( id >> makeAtom ) toks
in 
fun fromString str = reader term str
end (* of local *)

fun cropId str = TermLex.cropId str

fun cropTerm str = case cropId str of
		       NONE => NONE
		     | SOME (id,body) => let val (init, rest) = SU.scanBalancedPar body
					     val t = fromString (id ^ init)
					 in SOME (t, rest) end
					

fun cropKeySeparatedTermPair key str 
    = case cropTerm str of
	  NONE => NONE
	| SOME (lhs, str1) => (case SU.scanKey key str1 of 
				   NONE => raise Fail ("Syntax error: " ^ key ^ " expected after term" )
				 | SOME str2 => (case cropTerm str2 of
						     NONE => raise Fail ("Syntax error: term expected after " ^ key)
						   | SOME (rhs, rest) => SOME ((lhs,rhs), rest)))

(* term key term の形の文字列から，項の対を読み込む *)
fun readKeySeparatedTermPair key str = 
    case cropKeySeparatedTermPair key str of
	SOME (tp,rest) => if SU.ending rest then tp
			  else raise Fail ("Syntax error: trailing " ^ rest)
      | NONE => raise Fail ("Syntax error: not a " ^ key ^ " separated term pair")

(* start term key term sep ... sep term key term stop の形の文字列から *)
(* 項の対のリストを読み込む *)
fun readMultipleKeySepartedTermPairs (start,sep,stop) key str =
    let fun rdFirstItem s = cropKeySeparatedTermPair key s
	fun rdRemainingItems ans s = 
	    case SU.scanKey sep s of
		SOME rest => (case rdFirstItem rest of 
				 SOME (new,s2) => rdRemainingItems (new::ans) s2
			       | NONE => raise Fail ("Syntax error: starting term pair expected " ^ rest))
	      | NONE => if SU.ending s
			then rev ans
			else raise Fail ("Syntax error: trailing " ^ s)
    in case SU.scanBeginEnd (start,stop) str of
	   NONE => raise Fail ("Syntax error: " ^ start ^ "..." ^ stop ^ " expected")
	 | SOME str1 => (case rdFirstItem str1 of 
			    NONE => []
			  | SOME (tp,rest) => rdRemainingItems [tp] rest)
    end

fun prPos [] = "e"
  | prPos [x] =	Int.toString x
  | prPos (x::xs) = (Int.toString x) ^ "." ^ (prPos xs)

fun pos (Var x) = [[]]
  | pos (Fun (f,ts)) = []::(posList 1 ts)
and posList i [] = []
  | posList i (t::ts) = map (fn xs => i::xs) (pos t) @ (posList (i+1) ts)

fun symbol (Var x) [] = Symbol.V x
  | symbol (Var x) _ = raise PositionNotInTerm
  | symbol (Fun (f,ts)) [] = Symbol.F f
  | symbol (Fun (f,ts)) (x::xs) = if x > 0 andalso x <= length ts
				  then symbol (List.nth (ts,x-1)) xs
				  else raise PositionNotInTerm

fun subterm (Var x) [] = Var x
  | subterm (Var x) _ = raise PositionNotInTerm
  | subterm (Fun (f,ts)) [] = Fun (f,ts)
  | subterm (Fun (f,ts)) (x::xs) = if x > 0 andalso x <= length ts
				   then subterm (List.nth (ts,x-1)) xs
				   else raise PositionNotInTerm

fun getAllSubterm t = List.map (fn p => subterm t p) (pos t)

fun getAllSubtermProper t = List.drop (getAllSubterm t, 1)

fun makeContext (Var x) [] = (fn t => t)
  | makeContext (Var x) _ = raise PositionNotInTerm
  | makeContext (Fun (f,ts)) [] = (fn t => t)
  | makeContext (Fun (f,ts)) (x::xs) = if x > 0 andalso x <= length ts
				       then (fn t => Fun (f,(List.take (ts,x-1))@((makeContext (List.nth (ts,(x-1))) xs) t)::List.drop (ts,x)))
				       else raise PositionNotInTerm

fun fillContext context t = context t

fun replaceSubterm t p u = fillContext (makeContext t p) u

fun getAr term =
    let val ps = pos term
	val subterms = List.map (fn p => subterm term p) ps
	val nonVarSubterms = List.filter isFun subterms
    in ListUtil.unions (List.map (fn t => [valOf (arity t)]) nonVarSubterms)
    end
		    
end (* of local *)	

end


