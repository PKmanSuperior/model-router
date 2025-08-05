signature TEST =
sig
    type pred_key = Pred.key
    datatype atom = Pred of pred_key * Term.term list
		  | Eq of Term.term * Term.term
		  | Neq of Term.term * Term.term
    datatype token = ATOM of string
		   | NOT
		   | AND
		   | OR
		   | IMP
		   | IFF
		   | ALL of string
		   | EXISTS of string
		   | LPAREN
		   | RPAREN
    datatype form = Atom of atom
		  | Not of form
		  | And of form * form
		  | Or of form * form
		  | Imp of form * form
		  | Iff of form * form
		  | All of Var.key * form
		  | Exists of Var.key * form
				      
    exception SyntaxErr
    exception ParseErr
    val toStringAtom: atom -> string
    val fromStringAtom: string -> atom
    val tokenize: string -> token list
    val parse: token list -> form
    val toString: form -> string 
    val fromString: string -> form
end

structure Test : TEST =
struct
local
    structure T = Term
    structure LU = ListUtil
    structure SU = StringUtil
in
type pred_key = Pred.key
datatype atom = Pred of pred_key * T.term list
	      | Eq of T.term * T.term
	      | Neq of T.term * T.term
datatype token = ATOM of string
	       | NOT
	       | AND
	       | OR
	       | IMP
	       | IFF
	       | ALL of string
	       | EXISTS of string
	       | LPAREN
	       | RPAREN
datatype form = Atom of atom
	      | Not of form
	      | And of form * form
	      | Or of form * form
	      | Imp of form * form
	      | Iff of form * form
	      | All of Var.key * form
	      | Exists of Var.key * form
		     
exception SyntaxErr
exception ParseErr
				    
fun paren s = "(" ^ s ^ ")"
				    
fun toStringAtom (Pred (p, ts)) = Pred.toString p ^ paren (String.concatWith "," (List.map T.toString ts))
  | toStringAtom (Eq (l, r)) = T.toString l ^ "=" ^ T.toString r
  | toStringAtom (Neq (l, r)) = T.toString l ^ "!=" ^ T.toString r

fun fromStringAtom str =
    let fun parseEq str =
	    let val (lhs, rhs) = (fn [x, y] => (x, y) | _ => raise SyntaxErr) (SU.split str #"=")
	    in Eq (T.fromString lhs, T.fromString rhs)
	    end
	fun parseNeq str =
	    let val (lhs, rhs) = (fn [x, y] => (x, y) | _ => raise SyntaxErr) (SU.split str #"=")
	    in Neq (T.fromString (String.substring (lhs, 0, size lhs - 1)),T.fromString rhs)
	    end
	fun parsePred str =
	    let fun splitArgs (args, []) = rev args
		  | splitArgs (args, cs) =
		    let fun main (t, []) i = (String.implode (rev t),[])
			  | main (t, c::cs) i = if c = #"(" then main (c::t, cs) (i + 1)
						else if c = #")" then main (c::t, cs) (i - 1)
						else if c = #"," andalso i = 0 then (String.implode (rev t), cs)
						else main (c::t, cs) i
			val (term,rest) = main ([],cs) 0 
		    in splitArgs (term::args, rest)
		    end 
		val pos = valOf (SU.find str #"(")
		val symbol = String.substring (str, 0, pos)
		val argsStr = if symbol = str
			   then ""
			   else String.substring (str, pos + 1, size str - pos - 2)
		val args = splitArgs ([], String.explode argsStr)
	    in Pred (Pred.fromString symbol, List.map T.fromString args)
	    end
	val str' = String.implode (List.filter Char.isGraph (String.explode str))
    in if String.isSubstring "!=" str'
       then parseNeq str'
       else if String.isSubstring "=" str'
       then parseEq str'
       else parsePred str'
    end

fun bindVars form =
    let fun replaceTerm var (T.Var x) = T.Var x
	  | replaceTerm var (T.Fun (f, [])) = if Var.toString var = Fun.toString f then T.Var var else T.Fun (f, [])
	  | replaceTerm var (T.Fun (f, ts)) = T.Fun (f, List.map (fn t => replaceTerm var t) ts)
	fun replace var (Atom (Pred (p, ts))) = Atom (Pred (p, List.map (fn t => replaceTerm var t) ts))
	  | replace var (Atom (Eq (l, r))) = Atom (Eq (replaceTerm var l, replaceTerm var r))
	  | replace var (Atom (Neq (l, r))) = Atom (Neq (replaceTerm var l, replaceTerm var r))
	  | replace var (Not p) = Not (replace var p)
	  | replace var (And (p, q)) = And (replace var p, replace var q)
	  | replace var (Or (p, q)) = Or (replace var p, replace var q)
	  | replace var (Imp (p, q)) = Imp (replace var p, replace var q)
	  | replace var (Iff (p, q)) = Iff (replace var p, replace var q)
	  | replace var (All (x, p)) = All (x, (replace var p))
	  | replace var (Exists (x,p)) = Exists (x, (replace var p))
	fun getBoundVars (Atom atom) = []
	  | getBoundVars (Not p) = getBoundVars p
	  | getBoundVars (And (p, q)) = getBoundVars p @ getBoundVars q
	  | getBoundVars (Or (p, q)) = getBoundVars p @ getBoundVars q
	  | getBoundVars (Imp (p, q)) = getBoundVars p @ getBoundVars q
	  | getBoundVars (Iff (p, q)) = getBoundVars p @ getBoundVars q
	  | getBoundVars (All (x, p)) = x :: getBoundVars p
	  | getBoundVars (Exists (x, p)) = x :: getBoundVars p
	fun main [] form = form
	  | main (var::rest) form = main rest (replace var form)
    in main (getBoundVars form) form
    end

fun toVars form =
    let fun replaceTerm (T.Var x) = T.Fun (Fun.fromString (Var.toString x),[]) 
	  | replaceTerm (T.Fun (f, ts)) = T.Fun (f, List.map replaceTerm ts)
	fun replace (Atom (Pred (p, ts))) = Atom (Pred (p, List.map replaceTerm ts))
	  | replace (Atom (Eq (l, r))) = Atom (Eq (replaceTerm l, replaceTerm r))
	  | replace (Atom (Neq (l, r))) = Atom (Neq (replaceTerm l, replaceTerm r))
	  | replace (Not p) = Not (replace p)
	  | replace (And (p, q)) = And (replace p, replace q)
	  | replace (Or (p, q)) = Or (replace p, replace q)
	  | replace (Imp (p, q)) = Imp (replace p, replace q)
	  | replace (Iff (p, q)) = Iff (replace p, replace q)
	  | replace (All (x, p)) = All (x, (replace p))
	  | replace (Exists (x,p)) = Exists (x, (replace p))
    in replace form
    end

fun toString (Atom atom) = toStringAtom atom
  | toString (Not p) = "~" ^ paren (toString p)
  | toString (And (p, q)) = paren (toString p ^ "&" ^ toString q)
  | toString (Or (p, q)) = paren (toString p ^ "|" ^ toString q)
  | toString (Imp (p, q)) = paren (toString p ^ "->" ^ toString q)
  | toString (Iff (p, q)) = paren (toString p ^ "<->" ^ toString q)
  | toString (All (x, p)) = "all " ^ Var.toString x ^ " " ^ paren (toString p)
  | toString (Exists (x, p)) = "exists " ^ Var.toString x ^ " " ^ paren (toString p)
									   
fun tokenize str =	
    let fun lex [] = []
	  | lex (#" "::rest) = lex rest
	  | lex (#"("::rest) = LPAREN::lex rest
	  | lex (#")"::rest) = RPAREN::lex rest
	  | lex (#"~"::rest) = NOT::lex rest
	  | lex (#"&"::rest) = AND::lex rest
	  | lex (#"|"::rest) = OR::lex rest
	  | lex ((#"-")::(#">")::rest) = IMP::lex rest
	  | lex ((#"<")::(#"-")::(#">")::rest) = IFF::lex rest
	  | lex cs =
	    let val str' = String.implode cs
		fun skipPrefixWS [] = []
		  | skipPrefixWS (c::cs) = if Char.isGraph c
					   then c::cs
					   else skipPrefixWS cs
		fun getVar ([], var) = String.implode (rev var)
		  | getVar (c::cs, var) = if Char.isGraph c
					  then getVar (cs, c::var)
					  else String.implode (rev var)
		fun readAtom ([], atom) i = (String.implode (rev atom), [])
		  | readAtom ((c::cs), atom) i =
		    let fun countParens c i = case c of
						  #"(" => i + 1
						| #")" => i - 1
						| _ => i
		    in if i  = 0 andalso LU.member c [#")", #"~", #"&", #"|", #"-", #"<", #">"]
		       then (String.implode (rev atom), c::cs)
		       else readAtom (cs, c::atom) (countParens c i)
		       end 
	    in if String.isPrefix "all " str'
	       then let val sub = skipPrefixWS (List.drop (cs, 3))
			val var = getVar (sub, [])
			val rest = skipPrefixWS (List.drop (sub, size var))
		    in ALL var::lex rest
		    end 
	       else if String.isPrefix "exists " str'
	       then let val sub = skipPrefixWS (List.drop (cs, 6))
			val var = getVar (sub, [])
			val rest = skipPrefixWS (List.drop (sub, size var))
		    in EXISTS var::lex rest
		    end 
	       else let val (atom, rest) = readAtom (cs, []) 0
		    in ATOM atom::lex rest
		    end
	    end 		      
    in lex (String.explode str)
    end

fun parse tokens =
    let fun parseIff toks =
	    let val (lhs, rest1) = parseImp toks
	    in case rest1 of
		   IFF::rest2 => let val (rhs, rest3) = parseIff rest2
				 in (Iff (lhs, rhs), rest3)
				 end
		 | _ => (lhs, rest1)
	    end
	and parseImp toks =
	    let val (lhs, rest1) = parseOr toks
	    in case rest1 of
		   IMP::rest2 => let val (rhs, rest3) = parseImp rest2
				 in (Imp (lhs, rhs), rest3)
				 end
		| _ => (lhs, rest1)
	    end
	and parseOr toks =
            let val (lhs, rest1) = parseAnd toks
		fun loop (lhs, OR::rest2) =
                    let val (rhs, rest3) = parseAnd rest2
                    in loop (Or (lhs, rhs), rest3)
		    end
                  | loop result = result
            in loop (lhs, rest1)
            end
	and parseAnd toks =
            let val (lhs, rest1) = parseNot toks
		fun loop (lhs, AND::rest2) =
                    let val (rhs, rest3) = parseNot rest2
                    in loop (And (lhs, rhs), rest3)
		    end
                  | loop result = result
            in loop (lhs, rest1)
            end
	and parseNot toks = case toks of
				NOT::rest =>
				let val (p, rest') = parseNot rest
				in (Not p, rest')
				end
			      | _ => parseQuants toks
	and parseQuants toks =
	    let fun loop (ALL var :: rest) acc = loop rest (ALL var :: acc)
		  | loop (EXISTS var :: rest) acc = loop rest (EXISTS var :: acc)
		  | loop rest acc = (rev acc, rest)
	    in case toks of
		   ALL var::rest => let val (quants, toks1) = loop toks []
					val (body, toks2) = parseAtom toks1
					val result = List.foldr (fn (ALL var, acc) => All (Var.fromString var, acc) | (EXISTS var, acc) => Exists (Var.fromString var, acc)) body quants
				    in (result, toks2)
				    end 
		 | EXISTS var::rest => let val (quants, toks1) = loop toks []
					   val (body, toks2) = parseAtom toks1
					   val result = List.foldr (fn (ALL var, acc) => All (Var.fromString var, acc) | (EXISTS var, acc) => Exists (Var.fromString var, acc)) body quants
				       in (result, toks2)
				       end 
		 | _ => parseAtom toks
	    end 
	and parseAtom toks = case toks of
				 ATOM p::rest => (Atom (fromStringAtom p), rest)
			       | LPAREN::rest => let val (p, rest1) = parseIff rest
						 in case rest1 of
							RPAREN::rest2 => (p, rest2)
						      | _ => raise ParseErr
						 end
			       | _ => raise ParseErr
    in case parseIff tokens of
	   (result,[]) => result
	 | (_,rest) => raise ParseErr
    end

fun fromString str = bindVars (parse (tokenize str))
		
end 
end 
