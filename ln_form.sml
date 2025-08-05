signature LN =
sig
    type const = string
    type coef = const list list
    datatype term = Var of Var.key | Fun of (coef * term) list
    datatype atom = Eq of term * term | Geq of term * term

    val makeConstPred: Form.pred_key * int -> const list list
    val makeConstFun: Term.fun_key * int -> const list
    val vars: term -> Var.key list
    val isContainVar: atom -> bool
    val makeTerm: Term.term -> term
    val toStringTerm: term -> string
    val toStringForm: atom -> string
    val concatTerm: (term * term) -> term
    val negateTerm: term -> term
    val expandCoef: (coef * coef) -> coef
    val expandTerm: term -> term
    val combineTerm: term -> term
    val makeForm: Form.atom -> atom list
    val makeFormNeg: Form.atom -> atom list
    val moveTerm: atom -> atom

    val getCoef: term -> coef list
    val calcMatrix: coef list list -> coef list list -> coef list list
end
    
structure Ln : LN =
struct
local
    structure F = Form
    structure T = Term
    structure LU = ListUtil
in
type const = string
type coef = const list list
datatype term = Var of Var.key | Fun of (coef * term) list
datatype atom = Eq of term * term | Geq of term * term
		  
fun makeConstPred (p, n) =
    let val enum = List.tabulate (n, fn x => x + 1) @ [0]
	val consts = [List.map (fn x => p ^ "_1_" ^ Int.toString x) enum, List.map (fn x => p ^ "_2_" ^ Int.toString x) enum]
    in if p <> "=" then consts else [["1", "-1", "0"],["-1", "1", "0"]]
    end
				 
fun makeConstFun (f, k) =
    let val enum = List.tabulate (k, fn x => x + 1) @ [0]
	val consts = List.map (fn x => f ^ "_" ^ (Int.toString x)) enum
    in consts
    end

fun vars (Var x) = if x <> ("0", 0) then [x] else []
  | vars (Fun ts) = varsList ts
and varsList [] = []
  | varsList ((c, t)::ts) = LU.union (vars t, varsList ts)

fun isContainVar (Eq (l,r)) = not (null (vars l @ vars r))
  | isContainVar (Geq (l,r)) = not (null (vars l @ vars r))
	
fun makeTerm (T.Var x) = Fun [([["1"]],Var x)]
  | makeTerm (T.Fun (f,ts)) =
    let val consts = makeConstFun (valOf (T.arity (T.Fun (f,ts))))
	val (fi,f0) = (List.take (consts,length consts-1),List.last consts)
	val termList = List.map (fn (const,t) => ([[const]],makeTerm t)) (ListPair.zip (fi,ts)) @ [([[f0]],Var ("0",0))]
    in Fun termList
    end

fun toStringCoefVar [] = ""
  | toStringCoefVar [consts] = String.concatWith "*" (List.filter (fn c => c <> "1") consts)
  | toStringCoefVar (consts::rest) = (String.concatWith "*" (List.filter (fn c => c <> "1") consts)) ^ "+" ^ (toStringCoefVar rest)
										
fun toStringCoefConst [] = ""
  | toStringCoefConst [consts] = if length consts > 1 then String.concatWith "*" (List.filter (fn c => c <> "1") consts) else String.concatWith "*" consts
  | toStringCoefConst (consts::rest) = if length consts > 1 then (String.concatWith "*" (List.filter (fn c => c <> "1") consts))  ^ "+" ^ (toStringCoefConst rest) else (String.concatWith "*" consts) ^ "+" ^ (toStringCoefConst rest)

fun toStringTerm (Var x) = if x = ("0",0) then "" else Var.toString x
  | toStringTerm (Fun ts) = "(" ^ (toStringTermList ts) ^ ")"
and toStringTermList [] = ""
  | toStringTermList [(coef,t)] = (case t = Var ("0",0) of
				      true => if length coef > 1 then "(" ^ (toStringCoefConst coef) ^ ")" ^ (toStringTerm t) else (toStringCoefConst coef) ^ (toStringTerm t)
				    | false => if length coef > 1 then "(" ^ (toStringCoefVar coef) ^ ")" ^ (toStringTerm t) else (toStringCoefVar coef) ^ (toStringTerm t))
  | toStringTermList ((coef,t)::ts) = (case t = Var ("0",0) of
					   true => if length coef > 1 then "(" ^ (toStringCoefConst coef) ^ ")" ^ (toStringTerm t) ^ "+" ^ (toStringTermList ts) else (toStringCoefConst coef) ^ (toStringTerm t) ^ "+" ^ (toStringTermList ts)
					 | false => if length coef > 1 then "(" ^ (toStringCoefVar coef) ^ ")" ^ (toStringTerm t) ^ "+" ^ (toStringTermList ts) else (toStringCoefVar coef) ^ (toStringTerm t) ^ "+" ^ (toStringTermList ts))

fun toStringForm (Eq (l,r)) = toStringTerm l ^ "=" ^ toStringTerm r
  | toStringForm (Geq (l,r)) = toStringTerm l ^ ">=" ^ toStringTerm r

fun concatTerm (Fun ss,Fun ts) = Fun (ss @ ts)
  | concatTerm _ = raise Fail "Error: invalid input"
			 
fun negateTerm (Fun ts) =
    let fun main ([],t) = raise Fail "Error: invalid input"
	  | main ((c::cs),t) = (((("-" ^ hd c) :: tl c)::cs),t)
    in Fun (List.map main ts)
    end
  | negateTerm _ = raise Fail "Error: invalid input"

fun expandCoef (xs, ys) = List.concat (List.map (fn x => List.map (fn y => x @ y) ys) xs)
			 
fun expandTerm (Var x) = Var x
  | expandTerm (Fun ts) =
    let fun main (coef,Var x) = [(coef,Var x)]
	  | main (coef,Fun sub) =
	    let val margedSub = List.map (fn (c,t) => (expandCoef (coef,c),t)) sub
	    in List.concat (List.map main margedSub)
	    end
    in Fun (List.concat (List.map main ts))
    end

fun combineTerm (Var x) = Var x
  | combineTerm (Fun ts) =
    let val vars = LU.elimDup (#2 (ListPair.unzip ts))
	fun group [] cs _ = rev cs
	  | group ((coef,x)::ts) cs var = if var = x
					  then group ts (coef @ cs) var
					  else group ts cs var
	fun removeOne cs = if length cs > 1
			   then List.filter (fn const => const <> "1") cs
			   else cs
    in Fun (List.map (fn var => (List.map removeOne (group ts [] var),var)) vars)
    end 

fun makeForm (F.Pred (p,ts)) =
    let val consts = makeConstPred (F.arity (F.Pred (p,ts)))
	fun concatConst consts terms =
	    let val pairs = ListPair.zip (List.map (fn c => [[c]]) consts,terms)
	    in Fun pairs
	    end 
    in List.map (fn const => Geq (concatConst (List.take (const,length const - 1)) (List.map makeTerm ts),Fun [([[List.last const]],Var ("0",0))])) consts
    end 
  | makeForm (F.Eq (l, r)) = [Geq (concatTerm (makeTerm l,negateTerm (makeTerm r)),Fun [([["0"]],Var ("0",0))]),Geq (concatTerm (negateTerm (makeTerm l),makeTerm r),Fun [([["0"]],Var ("0",0))])]
  | makeForm (F.Neq (l, r)) = raise Fail "Error: invalid form"

fun makeFormNeg atom =
    let fun main (Eq (lhs,rhs)) =
	    let val negLhs = negateTerm lhs
		val negRhs = concatTerm (negateTerm rhs,Fun [([["1"]],Var ("0",0))])
	    in Eq (negLhs,negRhs)
	    end
	  | main (Geq (lhs,rhs)) =
	    let val negLhs = negateTerm lhs
		val negRhs = concatTerm (negateTerm rhs,Fun [([["1"]],Var ("0",0))])
	    in Geq (negLhs,negRhs)
	    end  
    in List.map main (makeForm atom)
    end 
	
fun moveTerm (Eq (Fun lhs,Fun rhs)) =
    let val (Fun exLhs,Fun exRhs) = (expandTerm (Fun lhs),expandTerm (Fun rhs))
	val (lvars,lconsts) = List.partition (fn (coef,var) => var <> Var ("0",0)) exLhs
	val (rvars,rconsts) = List.partition (fn (coef,var) => var <> Var ("0",0)) exRhs
    in if null (vars (Fun lhs) @ vars (Fun rhs)) then Eq (combineTerm (Fun exLhs),combineTerm (Fun exRhs)) else Eq (combineTerm (concatTerm (Fun lvars,negateTerm (Fun rvars))),combineTerm (concatTerm (Fun rconsts,negateTerm (Fun lconsts))))
    end
  | moveTerm (Geq (Fun lhs,Fun rhs)) =
    let val (Fun exLhs,Fun exRhs) = (expandTerm (Fun lhs),expandTerm (Fun rhs))
	val (lvars,lconsts) = List.partition (fn (coef,var) => var <> Var ("0",0)) exLhs
	val (rvars,rconsts) = List.partition (fn (coef,var) => var <> Var ("0",0)) exRhs
    in if null (vars (Fun lhs) @ vars (Fun rhs)) then Geq (combineTerm (Fun exLhs),combineTerm (Fun exRhs)) else Geq (combineTerm (concatTerm (Fun lvars,negateTerm (Fun rvars))),combineTerm (concatTerm (Fun rconsts,negateTerm (Fun lconsts))))
    end 
  | moveTerm _ = raise Fail "Error: invalid input"

fun getCoef (Var x) = []
  | getCoef (Fun ts) = List.map (fn (c,t) => c) ts
				
fun calcMatrix A B =
    let val AT = LU.transpose A
	val BT = LU.transpose B
	fun getElm ([],[])  = []
	  | getElm ([],_) = raise Fail "Error: longer A"
	  | getElm (_,[]) = raise Fail "Error: longer B"
	  | getElm (a::restA,b::restB) = expandCoef (a,b) @ getElm (restA,restB)
    in if length AT = length B then List.map (fn Ai => List.map (fn Bj => getElm (Ai,Bj)) BT) A else raise Fail ("Error: impossible calclation (length AT:" ^ Int.toString (length A) ^ ",length B:" ^ Int.toString (length BT) ^ ")")
    end

end
end
    
