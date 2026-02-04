signature CRITERION =
sig
    type skelton = Fun.key
    type decSym = Fun.key
    type anker = Fun.key
    type cluster = (Trs.rl * Term.term list) list * Fun.key list
    
    val findDecRules: Trs.ctrs -> Trs.rl list
    val getSkelton: Term.term -> skelton option
    val getDecSymbol: Term.term -> decSym option
    val isIterateTerm: decSym -> Term.term -> bool
    val isLevelTerm: anker list -> decSym -> Term.term -> bool
    val findTerRules: Trs.rl -> Trs.ctrs -> Trs.rl list
    val getTerTerms: Trs.rl * Trs.rl list -> Trs.rl * Term.term list
    val getCluster: decSym option -> anker option -> Trs.ctrs -> cluster
    val getClusters: Trs.ctrs -> cluster list
    val printCluster: cluster -> unit
					       
    val match: Trs.ctrs -> Term.term * Term.term -> bool
    val proc: Trs.ctrs -> Trs.reach list -> bool 
end

structure Criterion : CRITERION =
struct
local
    structure LU = ListUtil
    structure T = Term
in
type skelton = Fun.key
type decSym = Fun.key
type anker = Fun.key
type cluster = (Trs.rl * Term.term list) list * Fun.key list   

fun isDec (T.Fun (f, ts), T.Var x) = length ts = 1 andalso hd ts = T.Var x
  | isDec _ = false

fun getSkelton (T.Var x) = NONE
  | getSkelton (T.Fun (f, _)) = SOME f

fun getDecSymbol (T.Var x) = NONE
  | getDecSymbol (T.Fun (f, ts)) = if null ts then NONE else getSkelton (hd ts)
									
fun getAnker (T.Var x) = NONE
  | getAnker (T.Fun (f, ts)) =
    let val ankerTerm = LU.find T.isConst ts
    in case ankerTerm of
	   SOME c => getSkelton c
	 | NONE => NONE
    end 								

fun findDecRules [] = []
  | findDecRules (((l,r),conds)::rest) =
    let val (skl, skr) = (T.root l, T.root r)
	val (argsl, argsr) = (T.args l, T.args r)
	val roots = List.map T.root argsl
	val isAllDec = List.all (fn (argl, argr) => isDec (argl,argr)) (ListPair.zip (argsl, argsr))
    in if null conds andalso not (null argsl orelse null argsr) andalso skl = skr andalso LU.allSame roots andalso isAllDec then (l,r)::findDecRules rest else findDecRules rest
    end
	
fun isIterateTerm dec (T.Var x) = true
  | isIterateTerm dec (T.Fun (f, ts)) = if dec = f then List.all (fn t => isIterateTerm dec t) ts else false

fun findTerRules _ [] = []
  | findTerRules rule (((l, r), conds)::rest) =
    let val (skel, dec) = (fn (l', r') => (valOf (getSkelton l'), valOf (getDecSymbol l'))) rule
	val argsl = T.args l
	val (consts, others) = List.partition T.isConst argsl
	val cond1 = length consts = 1
	val cond2 = List.all (fn t => isIterateTerm dec t) others andalso length (LU.unions (List.map T.vars others)) = length others
	val cond3 = T.isConst r orelse List.exists (fn t => t = r) argsl
    in if null conds andalso T.root l = Symbol.F skel andalso cond1 andalso cond2 andalso cond3 then (l,r)::findTerRules rule rest else findTerRules rule rest
    end

fun getTerTerms (decRule, terRules) = (decRule, List.map (fn (l, r) => r) terRules)

fun getLevelFun [] = []
  | getLevelFun (((l, r), terTerms)::rest) = if List.exists (fn t => not (T.isConst t)) terTerms
					      then valOf (getSkelton l)::getLevelFun rest
					      else getLevelFun rest
				    
fun isLevelTerm funs dec (T.Var x) = false
  | isLevelTerm funs dec (T.Fun (f, ts)) = if LU.member f funs
					   then List.all (fn t => isIterateTerm dec t) ts orelse List.all (fn t => isLevelTerm funs dec t) ts
					   else false

fun getCluster dec ank ctrs =
    let fun groupDecRules dec rules = List.filter (fn (l, r) => getDecSymbol l = dec) rules
	fun groupTerRules ank (decRule, rules) = (decRule, List.filter (fn (l, r) => getAnker l = ank) rules)
	val dg = groupDecRules dec (findDecRules ctrs)
	val terRules = List.map (fn rules => groupTerRules ank rules) (List.map (fn rule => (rule, findTerRules rule ctrs)) dg)
	val terTerms = List.map getTerTerms terRules
	val levelFun = getLevelFun terTerms
    in (terTerms, levelFun)
    end

fun getClusters ctrs =
    let val decRules = findDecRules ctrs
	val terRules = List.concatMap (fn rule => findTerRules rule ctrs) decRules
	val allDecSyms = LU.elimDup (List.map (fn (l, r) => getDecSymbol l) decRules)
	val allAnkers = LU.elimDup (List.map (fn (l, r) => getAnker l) terRules)
    in List.concatMap (fn dec => List.map (fn ank => getCluster dec ank ctrs) allAnkers) allDecSyms
    end 

fun printCluster (pairs, funs) =
    let fun printPair [] = ()
	  | printPair ((rule, ts)::rest) = 
	let val _ = print ("[" ^ Trs.prRule rule ^ "]\n")
	    val _ = print ("[" ^ String.concatWith ", " (List.map T.toString ts) ^ "]\n")
	in printPair rest
	end
	val _ = printPair pairs
	val _ = print ("[" ^ String.concatWith "," funs ^ "]\n\n")
    in ()
    end

fun match ctrs (s,t) =
    let fun main ([], funs) (s, t) = false
	  | main ((((l, r), ts)::rest), funs) (s, t) = 
	    let val dec = valOf (getDecSymbol l)
		val cond1 = T.root l = T.root s
		val cond2 = if List.exists (fn f => Symbol.F f = T.root l) funs
			    then isLevelTerm funs dec s andalso (LU.member t ts orelse isIterateTerm dec t)
			    else List.all (fn u => isLevelTerm funs dec u orelse isIterateTerm dec u) (T.args s) andalso LU.member t ts
	    in if cond1 andalso cond2 then true else main (rest, funs) (s, t)
	    end 
	val clusters = getClusters ctrs
    in List.exists (fn cluster => main cluster (s,t)) clusters
    end 
	
fun proc ctrs reachs =
    let val _ = print "sufficient condition check:\n"
    in if List.all (fn reach => match ctrs reach) reachs
       then
	   let val _ = print "==> No finite model exists (sufficient condition is satisfied).\n--------------------\n"
	   in true
	   end 
       else
	   let val _ = print "==> Finite model existence is unknown (sufficient condition is not satisfied).\n--------------------\n"
	   in false
	   end 
    end 

end
end
