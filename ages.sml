signature AGES =
sig
    val makeGeq: Ln.coef list -> Var.key list -> Ln.coef -> Ln.atom
    val toLnForm: Form.form list -> (Ln.atom list * Ln.atom) list
    val toStringConstraints: (Ln.atom list * Ln.atom) -> string
    val applyFarkas: (Ln.atom list * Ln.atom) -> int -> Ln.atom list

    val getConst: Ln.atom list -> Ln.const list
    val cutCoef: Ln.coef -> Ln.coef
				
    val toStringSMT: Ln.atom -> string
    val printSMT: Ln.atom list -> unit
    val runZ3: int -> string option
    val readModel: unit -> (string * int) list
    val printModel: ((Term.fun_key * int) list * (Form.pred_key * int) list) -> (string * int) list -> unit
    val ages: Form.form list -> int -> bool

    exception NotFound
end
    
structure Ages : AGES =
struct
local
    structure T = Term
    structure F = Form
    structure LU = ListUtil		      
in

exception NotFound

fun makeGeq lefts vars right =
    let val terms = ListPair.zip (lefts,vars)
	fun getTerm (coef,var) = (coef,Ln.Var var)
    in Ln.Geq (Ln.Fun (List.map getTerm terms),Ln.Fun [(right,Ln.Var ("0",0))])
    end

fun makeEq lefts vars right =
    let val terms = ListPair.zip (lefts, vars)
	fun getTerm (coef, var) = (coef, Ln.Var var)
    in Ln.Eq (Ln.Fun (List.map getTerm terms), Ln.Fun [(right, Ln.Var ("0",0))])
    end 
			
fun makeSubDom vars = List.concatMap (fn x => [makeGeq [[["1"]]] [x] [["0"]]]) vars

fun closure forms =
    let val arities = F.getArsFun forms
	fun main [] = []
	  | main (arity::rest) =
	    let val constsGeq = List.map (fn fi => ([], makeGeq [[[fi]]] [("0", 0)] [["0"]])) (Ln.makeConstFun arity)
	    in constsGeq @ main rest
	    end 
    in main arities
    end
	
fun toLnForm forms =
    let val cnf = List.concatMap (F.cnfList o F.cnf o F.toQF o F.skolem o F.nnf) forms
	fun toConstraints cl =
	    let fun abs (F.Pos p) = p
		  | abs (F.Neg p) = p
		fun moveTerms (eqs, eq) = (List.map Ln.moveTerm eqs, Ln.moveTerm eq)
		fun conv1 pos conds =
		    let val (conseq, ant) = valOf (List.getItem pos)
			val exAnt = LU.allCombinations (List.map (fn a => Ln.makeFormNegAnt (abs a)) ant)
		    in List.concatMap (fn ci => List.map (fn a => moveTerms (conds @ a, ci)) exAnt) (Ln.makeForm (abs conseq))
		    end
		fun conv2 neg conds =
		    let val (conseq, ant) = valOf (List.getItem neg)
			val ant' = List.concatMap (fn a => Ln.makeForm (abs a)) ant
			val (c1, c2) = Ln.makeFormNegConseq (abs conseq)
		    in [moveTerms (conds @ c1::ant', c2)]
		    end
		fun conv3 (pos, neg) conds =
		    let val (conseq, ant) = valOf (List.getItem pos)
			val antNeg = List.concatMap (fn a => Ln.makeForm (abs a)) neg
			val exAnt = LU.allCombinations (List.map (fn a => Ln.makeFormNegAnt (abs a)) ant)
			val ant' = List.map (fn a => conds @ antNeg @ a) exAnt
		    in List.concatMap (fn ci => List.map (fn a => moveTerms (a, ci)) ant') (Ln.makeForm (abs conseq))
		    end
		val vars = LU.elimDup (List.concatMap F.varsAtom (List.map abs cl))
		val conds = makeSubDom vars
		val (pos, neg) = List.partition (fn (F.Pos _) => true | (F.Neg _) => false) cl
	    in if null neg then conv1 pos conds
	       else if null pos then conv2 neg conds
	       else conv3 (pos, neg) conds
	    end 
    in List.concatMap toConstraints cnf
    end

fun NatCriteria forms =
    let fun main form =
	    let val atom = hd (F.getAtom form)
		val eqs = List.map (fn p => Ln.moveTerm p) (Ln.makeForm atom)
		fun getCoefGeq (Ln.Eq (s, t)) =
		    let val aList = Ln.getCoef s
			val a0 = hd (Ln.getCoef t)
		    in ([], makeGeq [[["0"]]] [("0", 0)] a0) :: (List.map (fn ai => ([], makeGeq [ai] [("0", 0)] [["0"]])) aList)
		    end 
		  | getCoefGeq (Ln.Geq (s, t)) =
		    let val aList = Ln.getCoef s
			val a0 = hd (Ln.getCoef t)
		    in ([], makeGeq [[["0"]]] [("0", 0)] a0) :: (List.map (fn ai => ([], makeGeq [ai] [("0", 0)] [["0"]])) aList)
		    end
	    in List.concatMap getCoefGeq eqs
	    end
    in List.concatMap main forms
    end
	
fun toStringConstraints (eqs,eq) = if null eqs then Ln.toStringForm eq else (String.concatWith "&" (List.map Ln.toStringForm eqs)) ^ "=>" ^ (Ln.toStringForm eq)

fun applyFarkas (eqs,eq) i =
    let fun findCoef (Ln.Fun ts) var = (case List.find (fn (_, Ln.Var v') => var = v' | _ => false) ts of
					 SOME (c, _) => SOME c
				       | NONE => SOME [["0"]])
	  | findCoef (Ln.Var x) var = NONE
    	fun getMatrixVarFromEq (Ln.Eq (l,r)) vars = List.map (fn var => valOf (findCoef l var)) vars
	  | getMatrixVarFromEq (Ln.Geq (l,r)) vars = List.map (fn var => valOf (findCoef l var)) vars
	fun makeLambda i k = List.tabulate (k,(fn x => [[["$L_" ^ Int.toString i ^ "_" ^ Int.toString (x + 1)]]]))
	fun getConstraintsLambda ls = List.map (fn [lambda] => Ln.Geq (Ln.Fun [(lambda,Ln.Var ("0",0))],Ln.Fun [([["0"]],Ln.Var ("0",0))]) | _ => raise Fail "Error: invalid lambda") ls
	fun getConstraints A b c beta lambda =
	    let fun makeEq1 c A lambda =
		    let val lhMatrix = LU.transpose c
			val rhMatrix = Ln.calcMatrix (LU.transpose A) lambda
		    in (lhMatrix,rhMatrix)
		    end 
		fun makeEq2 lambda b beta =
		    let val lhMatrix = Ln.calcMatrix (LU.transpose lambda) b
			val rhMatrix = beta
		    in (lhMatrix,rhMatrix)
		    end
		fun toEq ([],[]) = []
		  | toEq ([],_) = raise Fail "Error: longer A (eq)"
		  | toEq (_,[]) = raise Fail "Error: longer B (eq)"
		  | toEq (ai::A,bi::B) = (List.map (fn (x,y) => Ln.Eq (Ln.Fun [(x,Ln.Var ("0",0))],Ln.Fun [(y,Ln.Var ("0",0))])) (ListPair.zip (ai,bi))) @ toEq (A,B)
		fun toGeq ([],[]) = []
		  | toGeq ([],_) = raise Fail "Error: longer A (geq)"
		  | toGeq (_,[]) = raise Fail "Error: longer B (geq)"
		  | toGeq (ai::A,bi::B) = (List.map (fn (x,y) => Ln.Geq (Ln.Fun [(x,Ln.Var ("0",0))],Ln.Fun [(y,Ln.Var ("0",0))])) (ListPair.zip (ai,bi))) @ toGeq (A,B)
	    in toEq (makeEq1 c A lambda) @ toGeq (makeEq2 lambda b beta)
	    end 
    	val vars = LU.unions (List.map (fn Ln.Eq (l,r) => Ln.vars l @ Ln.vars r | Ln.Geq (l,r) => (Ln.vars l @ Ln.vars r)) eqs)
	val A = List.map (fn eq => getMatrixVarFromEq eq vars) eqs
	val b = List.map (fn Ln.Eq (l,r) => Ln.getCoef r | Ln.Geq (l,r) => Ln.getCoef r) eqs
	val c = [getMatrixVarFromEq eq vars]
	val beta = [(fn Ln.Eq (l,r) => Ln.getCoef r | Ln.Geq (l,r) => Ln.getCoef r) eq]
	val lambda = makeLambda i (length b)	
    in getConstraints A b c beta lambda @ getConstraintsLambda lambda
    end
												
fun getConst forms =
    let fun removeSign const =
	    let fun dropSign [] = []
		  | dropSign (#"-"::rest) = dropSign rest
		  | dropSign chars = chars
	    in String.implode (dropSign (String.explode const))
	    end 
	fun getConstFromTerm (Ln.Var x) = []
	  | getConstFromTerm (Ln.Fun ts) = getConstFromTermList ts
	and getConstFromTermList [] = []
	  | getConstFromTermList ((c,t)::ts) = (List.map (fn const => removeSign const) (List.concat c)) @ (getConstFromTerm t) @ (getConstFromTermList ts)
    in List.filter (fn const => case String.explode const of
      c :: _ => Char.isDigit c = false
    | [] => true) (LU.unions (List.map (fn Ln.Eq (l,r) => getConstFromTerm l @ getConstFromTerm r | Ln.Geq (l,r) => getConstFromTerm l @ getConstFromTerm r) forms))
    end

fun cutCoef coef =
    let fun cutZero coef = List.filter (fn consts => List.all (fn c => c <> "0") consts) coef
	val coef' = cutZero coef 
    in if null coef' then [["0"]] else coef'
    end
			 
fun toStringSMT form =
    let fun normalizeSign const =
	    let fun process (#"-" :: #"-" :: rest) = process rest
		  | process (c :: rest) = c :: process rest
		  | process [] = []
		val constList = (process (String.explode const))
	    in if hd constList = #"-" then "(- " ^ (String.implode (tl constList)) ^ ")" else String.implode constList
	    end
	fun getCutTerm (Ln.Var x) = Ln.Var x
	  | getCutTerm (Ln.Fun ts) = Ln.Fun (List.map (fn (c,t) => (cutCoef c,t)) ts)
	fun getCutForm (Ln.Eq (l,r)) = Ln.Eq (getCutTerm l,getCutTerm r)
	  | getCutForm (Ln.Geq (l,r)) = Ln.Geq (getCutTerm l,getCutTerm r)
	fun toStringMult [] = ""
	  | toStringMult [const] = normalizeSign const
	  | toStringMult constList =  "(* " ^ (String.concatWith " " (List.map normalizeSign constList)) ^ ")"
	fun toStringAdd [] = ""
	  | toStringAdd [coef] = toStringMult coef
	  | toStringAdd coefList = "(+ " ^ (String.concatWith " " (List.map toStringMult coefList)) ^ ")"
	fun toString (Ln.Eq (l,r)) = "(= " ^ ((fn [coef] => toStringAdd coef | _ => "") (Ln.getCoef l)) ^ " " ^ ((fn [coef] => toStringAdd coef | _ => "") (Ln.getCoef r)) ^ ")"
	  | toString (Ln.Geq(l,r)) = "(>= " ^ ((fn [coef] => toStringAdd coef | _ => "") (Ln.getCoef l)) ^ " " ^ ((fn [coef] => toStringAdd coef | _ => "") (Ln.getCoef r)) ^ ")"	 
    in toString (getCutForm form)
    end 

fun printSMT forms =
    let val outStream = TextIO.openOut "in.smt2"
	val _ =  TextIO.output (outStream,"(set-logic QF_NIA)\n")
	fun declare consts = List.map (fn const => TextIO.output (outStream,"(declare-const " ^ const ^ " Int)\n")) consts
	fun assert forms = List.map (fn form => TextIO.output (outStream,"(assert " ^ form ^ ")\n")) forms
	val _ = declare (getConst forms)
	val _ = assert (List.map toStringSMT forms)
	val _ = TextIO.output (outStream,"(check-sat)\n")
	val _ = TextIO.output (outStream,"(get-model)\n")
	val _ = TextIO.closeOut outStream
    in ()
    end

fun runZ3 timeout =
    let val command = "z3 -T:" ^ Int.toString timeout  ^ " in.smt2 > out.txt"
	val status = OS.Process.system command
    in case status of
	   0 => SOME "satisfiable"
         | _ => NONE
    end

fun readModel () =
    let val inStream = TextIO.openIn "out.txt"
	val result = TextIO.inputLine inStream
	fun loop () = case TextIO.inputLine inStream of
			  NONE => []
			| SOME line => line::(loop ())
	val lines = case result of
			SOME "sat\n" => loop ()
		      | _ => raise NotFound
	val _ = TextIO.closeIn inStream
	val l = List.take (List.drop (lines,1),length lines - 2)
	fun splitSpace str = String.tokens (fn c => c = #" ") str
	fun extractIntTokenFromLine str =
	    let val value = String.concatWith "" (splitSpace str)
		fun clean s = String.translate (fn c => if Char.isDigit c orelse c = #"-" then String.str c else "") s
	    in case Int.fromString (clean value) of
		   SOME s => s
		 | NONE => raise Fail ("No int found in line: " ^ str)
	    end	
	fun parseDefineFuns [] acc = acc
	  | parseDefineFuns (l1::l2::rest) acc =
	    let val toks = splitSpace l1
	    in case toks of
		   "(define-fun"::name::_ =>
		   if String.isPrefix "$L" name
		   then parseDefineFuns rest acc
		   else 
		       let val value = extractIntTokenFromLine l2
		       in parseDefineFuns rest ((name, value)::acc)
		       end
		 | _ => parseDefineFuns (l2::rest) acc
	    end
	  | parseDefineFuns _ acc = acc
	fun extractDefineFuns lines =
	    List.rev (parseDefineFuns lines [])
    in extractDefineFuns l
    end

fun extractIndex s =
  let val parts = String.tokens (fn c => c = #"_") s
  in case List.rev parts of
         [] => 0
       | last::_ => Option.getOpt (Int.fromString last, 0)
  end

fun sortByIndex lst =
  ListMergeSort.sort (fn ((s1, _), (s2, _)) =>
			 case Int.compare (extractIndex s1, extractIndex s2) of
			     GREATER => true
			   | _ => false
  ) lst

fun printModel (funs,preds) assignments =
    let fun gcd (a, 0) = abs a
	  | gcd (a, b) = gcd (b, a mod b)
	fun gcdList [] = 0
	  | gcdList (x::xs) = List.foldl (fn (y, acc) => gcd (acc, y)) (abs x) xs
	fun divide params =
	    let val (_, xs) = ListPair.unzip params
		val g = gcdList xs
	    in if g = 0 then params
	       else List.map (fn (p, n) => (p, n div g)) params
	    end
	fun deleteDummy str =
	    let val str' = Substring.full str
	    in case Substring.getc str' of
		   SOME (c, rest) => if c = #"$" then Substring.string rest else str
		 | NONE => ""
	    end 
	fun groupByKeys keys assigns = List.map (fn (key,arity) => ((key,arity), List.filter (fn (symbol, _) => String.isPrefix key symbol) assigns)) keys
	fun printDom dom =
	    let val c1 = #2 (valOf (List.find (fn (c,_) => c = "$c_1") dom))
		val c2 = #2 (valOf (List.find (fn (c,_) => c = "$c_2") dom))
		val b1 = #2 (valOf (List.find (fn (c,_) => c = "$b_1") dom))
		val b2 = #2 (valOf (List.find (fn (c,_) => c = "$b_2") dom))
		val dom1 = (Int.toString c1) ^ "*x >= " ^ (Int.toString b1)
		val dom2 = (Int.toString c2) ^ "*x >= " ^ (Int.toString b2)
	    in print (dom1 ^ " & " ^ dom2 ^ "\n")
	    end
	fun printDom2 dom =
	    let val c = #2 (valOf (List.find (fn (c,_) => c = "$c") dom))
		val b = #2 (valOf (List.find (fn (c,_) => c = "$b") dom))
	    in if c = ~1 then print ("{" ^ String.concatWith "," (List.tabulate (~b + 1, fn x => Int.toString x)) ^ "}\n")  else print "Nat\n"
	    end 
	fun printFun [] = ()
	  | printFun (((f,k),assignment)::rest) =
	    let val args = List.tabulate (k,fn x => "x_" ^ Int.toString (x + 1))
		val sortedAssignment = sortByIndex assignment
		val largs = List.map (fn (x,(f,n)) => case n of
							  1 => x
							| ~1 => "~" ^ x
							| n' => (Int.toString n') ^ "*" ^ x) (List.filter (fn (x,(f,n)) => n <> 0) (ListPair.zip (args,(tl sortedAssignment))))
		val func = if k = 0 then f else f ^ "(" ^ (String.concatWith "," args) ^ ")"
		val lfunc = if null largs then (fn (f,n) => Int.toString n) (hd sortedAssignment) else (String.concatWith "+" largs) ^ ((fn (f,n) => if n = 0 then "" else "+" ^ Int.toString n) (hd sortedAssignment))
		val _ = print (func ^ " = " ^ lfunc ^ "\n")
	    in printFun rest
	    end
	fun printPred [] = ()
	  | printPred (((p,n),assignment)::rest) =
	    let val (p1,p2) = List.partition (fn (sym,num) => String.isPrefix (p ^ "_1") sym) assignment
		val sortedP1 = divide (sortByIndex p1)
		val sortedP2 = divide (sortByIndex p2)
		val args = List.tabulate (n,fn x => "x_" ^ Int.toString (x + 1))
		val largs1 = List.map (fn (x,(p,n)) => case n of
							   1 => x
							 | ~1 => "~" ^ x
							 | n' => (Int.toString n') ^ "*" ^ x) (List.filter (fn (x,(p,n)) => n <> 0) (ListPair.zip (args,(tl sortedP1))))
		val largs2 = List.map (fn (x,(p,n)) => case n of
							   1 => x
							 | ~1 => "~" ^ x
							 | n' => (Int.toString n') ^ "*" ^ x) (List.filter (fn (x,(p,n)) => n <> 0) (ListPair.zip (args,(tl sortedP2))))
		val pred = if n = 0 then p else p ^ "(" ^ (String.concatWith "," args) ^ ")"
		val lpred1 = if null largs1
			     then if #2 (hd sortedP1) <= 0 then "" else "0 >= " ^ (Int.toString (#2 (hd sortedP1)))
			     else (String.concatWith " + " largs1) ^ ((fn (f,n) => if n = 0 then " >= 0" else " >= " ^ Int.toString n) (hd sortedP1))
		val lpred2 = if null largs2 then
				 if #2 (hd sortedP2) <= 0 then "" else "0 >= " ^ (Int.toString (#2 (hd sortedP2)))
			     else (String.concatWith " + " largs2) ^ ((fn (f,n) => if n = 0 then " >= 0" else " >= " ^ Int.toString n) (hd sortedP2))
		val _ = if lpred1 ^ lpred2 = "" then print (pred ^ " <=> true\n")
			else if lpred1 <> "" andalso lpred2 <> "" then print (pred ^ " <=> " ^ lpred1 ^ " & " ^ lpred2 ^ "\n")
			else print (pred ^ " <=> " ^ lpred1 ^ lpred2 ^ "\n")
	    in printPred rest
	    end
	val _ = print "==> SUCCESS\n"
	val assignments' = List.map (fn (key, num) => (deleteDummy key, num)) assignments
	val funGroups = groupByKeys funs assignments'
	val predGroups = groupByKeys preds assignments'
	val dom = List.filter (fn (sym, _) => not (List.exists (fn (key,_) => String.isPrefix key sym) (funs @ preds))) assignments'
	val _ = print "domain:\nNat\n"
	val _ = if null funGroups then () else print ("\n" ^ "function:\n")
	val _ = printFun funGroups
	val _ = if null predGroups then () else print ("\n" ^ "predicate:\n")
	val _ = printPred predGroups
    in ()
    end

fun getLnForms forms =
    let val cond = closure forms
	val (atom, imp) = List.partition (fn F.Atom _ => true | _ => false) (List.map F.toQF forms)
	val formsAtom = NatCriteria atom
	val formsImp = toLnForm imp
    in formsAtom @ formsImp @ cond
    end 
	
fun ages input timeout =
    let val _ = print ("model finding using AGES:\n" ^ Form.prForms input)
	val forms = getLnForms input
	val funs = Form.getArsFun input
	val preds = List.filter (fn (p,n) => p <> "=") (Form.getArsPred input)
	val (constraintsVar,constraintsConst) = List.partition (fn (eqs,eq) => List.exists Ln.containVar (eq::eqs)) forms
	fun iterateFarkas [] _ = []
	  | iterateFarkas (form::rest) i = applyFarkas form i @ iterateFarkas rest (i + 1)
	val constraintsConst' = List.map (fn (eqs,eq) => eq) constraintsConst
	val constraintsVar' = iterateFarkas constraintsVar 1
	val constraints = constraintsConst' @ constraintsVar'
	val _ = printSMT constraints
	val _ = runZ3 timeout
	val _ = printModel (funs,preds) (readModel ())
    in true
    end
    handle NotFound => let val _ = print "==> FAILURE\n"
		       in false
		       end 
end
end 
